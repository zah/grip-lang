#
#
#           The Nim Compiler
#        (c) Copyright 2015 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

import
  os, strutils, strtabs, osproc, sets

const
  hasTinyCBackend* = defined(tinyc)
  useEffectSystem* = true
  useWriteTracking* = false
  hasFFI* = defined(useFFI)
  newScopeForIf* = true
  useCaas* = not defined(noCaas)
  noTimeMachine* = defined(avoidTimeMachine) and defined(macosx)
  copyrightYear* = "2018"

type                          # please make sure we have under 32 options
                              # (improves code efficiency a lot!)
  TOption* = enum             # **keep binary compatible**
    optNone, optObjCheck, optFieldCheck, optRangeCheck, optBoundsCheck,
    optOverflowCheck, optNilCheck,
    optNaNCheck, optInfCheck,
    optAssert, optLineDir, optWarns, optHints,
    optOptimizeSpeed, optOptimizeSize, optStackTrace, # stack tracing support
    optLineTrace,             # line tracing support (includes stack tracing)
    optEndb,                  # embedded debugger
    optByRef,                 # use pass by ref for objects
                              # (for interfacing with C)
    optProfiler,              # profiler turned on
    optImplicitStatic,        # optimization: implicit at compile time
                              # evaluation
    optPatterns,              # en/disable pattern matching
    optMemTracker,
    optHotReloading

  TOptions* = set[TOption]
  TGlobalOption* = enum       # **keep binary compatible**
    gloptNone, optForceFullMake, optDeadCodeElim,
    optListCmd, optCompileOnly, optNoLinking,
    optCDebug,                # turn on debugging information
    optGenDynLib,             # generate a dynamic library
    optGenStaticLib,          # generate a static library
    optGenGuiApp,             # generate a GUI application
    optGenScript,             # generate a script file to compile the *.c files
    optGenMapping,            # generate a mapping file
    optRun,                   # run the compiled project
    optCaasEnabled            # compiler-as-a-service is running
    optSkipConfigFile,        # skip the general config file
    optSkipProjConfigFile,    # skip the project's config file
    optSkipUserConfigFile,    # skip the users's config file
    optSkipParentConfigFiles, # skip parent dir's config files
    optNoMain,                # do not generate a "main" proc
    optUseColors,             # use colors for hints, warnings, and errors
    optThreads,               # support for multi-threading
    optStdout,                # output to stdout
    optThreadAnalysis,        # thread analysis pass
    optTaintMode,             # taint mode turned on
    optTlsEmulation,          # thread var emulation turned on
    optGenIndex               # generate index file for documentation;
    optEmbedOrigSrc           # embed the original source in the generated code
                              # also: generate header file
    optIdeDebug               # idetools: debug mode
    optIdeTerse               # idetools: use terse descriptions
    optNoCppExceptions        # use C exception handling even with CPP
    optExcessiveStackTrace    # fully qualified module filenames

  TGlobalOptions* = set[TGlobalOption]

const
  harmlessOptions* = {optForceFullMake, optNoLinking, optRun,
                      optUseColors, optStdout}

type
  TCommands* = enum           # Nim's commands
                              # **keep binary compatible**
    cmdNone, cmdCompileToC, cmdCompileToCpp, cmdCompileToOC,
    cmdCompileToJS,
    cmdCompileToPHP,
    cmdCompileToLLVM, cmdInterpret, cmdPretty, cmdDoc,
    cmdGenDepend, cmdDump,
    cmdCheck,                 # semantic checking for whole project
    cmdParse,                 # parse a single file (for debugging)
    cmdScan,                  # scan a single file (for debugging)
    cmdIdeTools,              # ide tools
    cmdDef,                   # def feature (find definition for IDEs)
    cmdRst2html,              # convert a reStructuredText file to HTML
    cmdRst2tex,               # convert a reStructuredText file to TeX
    cmdInteractive,           # start interactive session
    cmdRun,                   # run the project via TCC backend
    cmdJsonScript             # compile a .json build file
  TStringSeq* = seq[string]
  TGCMode* = enum             # the selected GC
    gcNone, gcBoehm, gcGo, gcRegions, gcMarkAndSweep, gcRefc,
    gcV2, gcGenerational

  IdeCmd* = enum
    ideNone, ideSug, ideCon, ideDef, ideUse, ideDus, ideChk, ideMod,
    ideHighlight, ideOutline, ideKnown, ideMsg

  ConfigRef* = ref object ## eventually all global configuration should be moved here
    cppDefines*: HashSet[string]
    headerFile*: string

proc newConfigRef*(): ConfigRef =
  result = ConfigRef(cppDefines: initSet[string](),
    headerFile: "")

proc cppDefine*(c: ConfigRef; define: string) =
  c.cppDefines.incl define

var
  gIdeCmd*: IdeCmd
  gOldNewlines*: bool

const
  ChecksOptions* = {optObjCheck, optFieldCheck, optRangeCheck, optNilCheck,
    optOverflowCheck, optBoundsCheck, optAssert, optNaNCheck, optInfCheck}

var
  gOptions*: TOptions = {optObjCheck, optFieldCheck, optRangeCheck,
                         optBoundsCheck, optOverflowCheck, optAssert, optWarns,
                         optHints, optStackTrace, optLineTrace,
                         optPatterns, optNilCheck}
  gGlobalOptions*: TGlobalOptions = {optThreadAnalysis}
  gExitcode*: int8
  gCmd*: TCommands = cmdNone  # the command
  gSelectedGC* = gcRefc       # the selected GC
  searchPaths*: seq[string] = @[]
  lazyPaths*: seq[string]   = @[]
  outFile*: string = ""
  docSeeSrcUrl*: string = ""  # if empty, no seeSrc will be generated. \
  # The string uses the formatting variables `path` and `line`.
  #headerFile*: string = ""
  gVerbosity* = 1             # how verbose the compiler is
  gNumberOfProcessors*: int   # number of processors
  gWholeProject*: bool        # for 'doc2': output any dependency
  gEvalExpr* = ""             # expression for idetools --eval
  gLastCmdTime*: float        # when caas is enabled, we measure each command
  gListFullPaths*: bool
  gPreciseStack*: bool = false
  gNoNimblePath* = false
  gExperimentalMode*: bool
  newDestructors*: bool
  gDynlibOverrideAll*: bool

type
  SymbolFilesOption* = enum
    disabledSf, enabledSf, writeOnlySf, readOnlySf, v2Sf

var gSymbolFiles*: SymbolFilesOption

proc importantComments*(): bool {.inline.} = gCmd in {cmdDoc, cmdIdeTools}
proc usesNativeGC*(): bool {.inline.} = gSelectedGC >= gcRefc
template preciseStack*(): bool = gPreciseStack

template compilationCachePresent*: untyped =
  gSymbolFiles in {enabledSf, writeOnlySf}
#  {optCaasEnabled, optSymbolFiles} * gGlobalOptions != {}

template optPreserveOrigSource*: untyped =
  optEmbedOrigSrc in gGlobalOptions

const
  genSubDir* = "nimcache"
  NimExt* = "nim"
  RodExt* = "rod"
  HtmlExt* = "html"
  JsonExt* = "json"
  TagsExt* = "tags"
  TexExt* = "tex"
  IniExt* = "ini"
  DefaultConfig* = "nim.cfg"
  DocConfig* = "nimdoc.cfg"
  DocTexConfig* = "nimdoc.tex.cfg"

# additional configuration variables:
var
  gConfigVars* = newStringTable(modeStyleInsensitive)
  gDllOverrides = newStringTable(modeCaseInsensitive)
  gModuleOverrides* = newStringTable(modeStyleInsensitive)
  gPrefixDir* = "" # Overrides the default prefix dir in getPrefixDir proc.
  libpath* = ""
  gProjectName* = "" # holds a name like 'nim'
  gProjectPath* = "" # holds a path like /home/alice/projects/nim/compiler/
  gProjectFull* = "" # projectPath/projectName
  gProjectIsStdin* = false # whether we're compiling from stdin
  gProjectMainIdx*: int32 # the canonical path id of the main module
  nimcacheDir* = ""
  command* = "" # the main command (e.g. cc, check, scan, etc)
  commandArgs*: seq[string] = @[] # any arguments after the main command
  gKeepComments*: bool = true # whether the parser needs to keep comments
  implicitImports*: seq[string] = @[] # modules that are to be implicitly imported
  implicitIncludes*: seq[string] = @[] # modules that are to be implicitly included

const oKeepVariableNames* = true

template compilingLib*: bool =
  gGlobalOptions * {optGenGuiApp, optGenDynLib} != {}

proc mainCommandArg*: string =
  ## This is intended for commands like check or parse
  ## which will work on the main project file unless
  ## explicitly given a specific file argument
  if commandArgs.len > 0:
    result = commandArgs[0]
  else:
    result = gProjectName

proc existsConfigVar*(key: string): bool =
  result = hasKey(gConfigVars, key)

proc getConfigVar*(key: string): string =
  result = gConfigVars.getOrDefault key

proc setConfigVar*(key, val: string) =
  gConfigVars[key] = val

proc getOutFile*(filename, ext: string): string =
  if options.outFile != "": result = options.outFile
  else: result = changeFileExt(filename, ext)

proc getPrefixDir*(): string =
  ## Gets the prefix dir, usually the parent directory where the binary resides.
  ##
  ## This is overridden by some tools (namely nimsuggest) via the ``gPrefixDir``
  ## global.
  if gPrefixDir != "": result = gPrefixDir
  else:
    result = splitPath(getAppDir()).head

proc setDefaultLibpath*() =
  # set default value (can be overwritten):
  if libpath == "":
    # choose default libpath:
    var prefix = getPrefixDir()
    when defined(posix):
      if prefix == "/usr": libpath = "/usr/lib/nim"
      elif prefix == "/usr/local": libpath = "/usr/local/lib/nim"
      else: libpath = joinPath(prefix, "lib")
    else: libpath = joinPath(prefix, "lib")

    # Special rule to support other tools (nimble) which import the compiler
    # modules and make use of them.
    let realNimPath = findExe("nim")
    # Find out if $nim/../../lib/system.nim exists.
    let parentNimLibPath = realNimPath.parentDir().parentDir() / "lib"
    if not fileExists(libpath / "system.nim") and
        fileExists(parentNimlibPath / "system.nim"):
      libpath = parentNimLibPath

proc canonicalizePath*(path: string): string =
  # on Windows, 'expandFilename' calls getFullPathName which doesn't do
  # case corrections, so we have to use this convoluted way of retrieving
  # the true filename (see tests/modules and Nimble uses 'import Uri' instead
  # of 'import uri'):
  when defined(windows):
    result = path.expandFilename
    for x in walkFiles(result):
      return x
  else:
    result = path.expandFilename

proc shortenDir*(dir: string): string =
  ## returns the interesting part of a dir
  var prefix = gProjectPath & DirSep
  if startsWith(dir, prefix):
    return substr(dir, len(prefix))
  prefix = getPrefixDir() & DirSep
  if startsWith(dir, prefix):
    return substr(dir, len(prefix))
  result = dir

proc removeTrailingDirSep*(path: string): string =
  if (len(path) > 0) and (path[len(path) - 1] == DirSep):
    result = substr(path, 0, len(path) - 2)
  else:
    result = path

proc disableNimblePath*() =
  gNoNimblePath = true
  lazyPaths.setLen(0)

include packagehandling

proc getNimcacheDir*: string =
  result = if nimcacheDir.len > 0: nimcacheDir else: gProjectPath.shortenDir /
                                                         genSubDir


proc pathSubs*(p, config: string): string =
  let home = removeTrailingDirSep(os.getHomeDir())
  result = unixToNativePath(p % [
    "nim", getPrefixDir(),
    "lib", libpath,
    "home", home,
    "config", config,
    "projectname", options.gProjectName,
    "projectpath", options.gProjectPath,
    "projectdir", options.gProjectPath,
    "nimcache", getNimcacheDir()])
  if "~/" in result:
    result = result.replace("~/", home & '/')

proc toGeneratedFile*(path, ext: string): string =
  ## converts "/home/a/mymodule.nim", "rod" to "/home/a/nimcache/mymodule.rod"
  var (head, tail) = splitPath(path)
  #if len(head) > 0: head = shortenDir(head & dirSep)
  result = joinPath([getNimcacheDir(), changeFileExt(tail, ext)])
  #echo "toGeneratedFile(", path, ", ", ext, ") = ", result

when noTimeMachine:
  var alreadyExcludedDirs = initSet[string]()
  proc excludeDirFromTimeMachine(dir: string) {.raises: [].} =
    ## Calls a macosx command on the directory to exclude it from backups.
    ##
    ## The macosx tmutil command is invoked to mark the specified path as an
    ## item to be excluded from time machine backups. If a path already exists
    ## with files before excluding it, newer files won't be added to the
    ## directory, but previous files won't be removed from the backup until the
    ## user deletes that directory.
    ##
    ## The whole proc is optional and will ignore all kinds of errors. The only
    ## way to be sure that it works is to call ``tmutil isexcluded path``.
    if alreadyExcludedDirs.contains(dir): return
    alreadyExcludedDirs.incl(dir)
    try:
      var p = startProcess("/usr/bin/tmutil", args = ["addexclusion", dir])
      discard p.waitForExit
      p.close
    except Exception:
      discard

proc completeGeneratedFilePath*(f: string, createSubDir: bool = true): string =
  var (head, tail) = splitPath(f)
  #if len(head) > 0: head = removeTrailingDirSep(shortenDir(head & dirSep))
  var subdir = getNimcacheDir() # / head
  if createSubDir:
    try:
      createDir(subdir)
      when noTimeMachine:
        excludeDirFromTimeMachine(subdir)
    except OSError:
      writeLine(stdout, "cannot create directory: " & subdir)
      quit(1)
  result = joinPath(subdir, tail)
  #echo "completeGeneratedFilePath(", f, ") = ", result

proc rawFindFile(f: string): string =
  for it in searchPaths:
    result = joinPath(it, f)
    if existsFile(result):
      return result.canonicalizePath
  result = ""

proc rawFindFile2(f: string): string =
  for i, it in lazyPaths:
    result = joinPath(it, f)
    if existsFile(result):
      # bring to front
      for j in countDown(i,1):
        swap(lazyPaths[j], lazyPaths[j-1])

      return result.canonicalizePath
  result = ""

template patchModule() {.dirty.} =
  if result.len > 0 and gModuleOverrides.len > 0:
    let key = getPackageName(result) & "_" & splitFile(result).name
    if gModuleOverrides.hasKey(key):
      let ov = gModuleOverrides[key]
      if ov.len > 0: result = ov

proc findFile*(f: string): string {.procvar.} =
  if f.isAbsolute:
    result = if f.existsFile: f else: ""
  else:
    result = f.rawFindFile
    if result.len == 0:
      result = f.toLowerAscii.rawFindFile
      if result.len == 0:
        result = f.rawFindFile2
        if result.len == 0:
          result = f.toLowerAscii.rawFindFile2
  patchModule()

proc findModule*(modulename, currentModule: string): string =
  # returns path to module
  when defined(nimfix):
    # '.nimfix' modules are preferred over '.nim' modules so that specialized
    # versions can be kept for 'nimfix'.
    block:
      let m = addFileExt(modulename, "nimfix")
      let currentPath = currentModule.splitFile.dir
      result = currentPath / m
      if not existsFile(result):
        result = findFile(m)
        if existsFile(result): return result
  let m = addFileExt(modulename, NimExt)
  let currentPath = currentModule.splitFile.dir
  result = currentPath / m
  if not existsFile(result):
    result = findFile(m)
  patchModule()

proc findProjectNimFile*(pkg: string): string =
  const extensions = [".nims", ".cfg", ".nimcfg", ".nimble"]
  var candidates: seq[string] = @[]
  for k, f in os.walkDir(pkg, relative=true):
    if k == pcFile and f != "config.nims":
      let (_, name, ext) = splitFile(f)
      if ext in extensions:
        let x = changeFileExt(pkg / name, ".nim")
        if fileExists(x):
          candidates.add x
  for c in candidates:
    # nim-foo foo  or  foo  nfoo
    if (pkg in c) or (c in pkg): return c
  if candidates.len >= 1:
    return candidates[0]
  return ""

proc canonDynlibName(s: string): string =
  let start = if s.startsWith("lib"): 3 else: 0
  let ende = strutils.find(s, {'(', ')', '.'})
  if ende >= 0:
    result = s.substr(start, ende-1)
  else:
    result = s.substr(start)

proc inclDynlibOverride*(lib: string) =
  gDllOverrides[lib.canonDynlibName] = "true"

proc isDynlibOverride*(lib: string): bool =
  result = gDynlibOverrideAll or gDllOverrides.hasKey(lib.canonDynlibName)

proc binaryStrSearch*(x: openArray[string], y: string): int =
  var a = 0
  var b = len(x) - 1
  while a <= b:
    var mid = (a + b) div 2
    var c = cmpIgnoreCase(x[mid], y)
    if c < 0:
      a = mid + 1
    elif c > 0:
      b = mid - 1
    else:
      return mid
  result = - 1

proc parseIdeCmd*(s: string): IdeCmd =
  case s:
  of "sug": ideSug
  of "con": ideCon
  of "def": ideDef
  of "use": ideUse
  of "dus": ideDus
  of "chk": ideChk
  of "mod": ideMod
  of "highlight": ideHighlight
  of "outline": ideOutline
  of "known": ideKnown
  of "msg": ideMsg
  else: ideNone

proc `$`*(c: IdeCmd): string =
  case c:
  of ideSug: "sug"
  of ideCon: "con"
  of ideDef: "def"
  of ideUse: "use"
  of ideDus: "dus"
  of ideChk: "chk"
  of ideMod: "mod"
  of ideNone: "none"
  of ideHighlight: "highlight"
  of ideOutline: "outline"
  of ideKnown: "known"
  of ideMsg: "msg"
