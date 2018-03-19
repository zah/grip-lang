## v0.X.X - XX/XX/2018

### Changes affecting backwards compatibility

#### Breaking changes in the standard library

- ``re.split`` for empty regular expressions now yields every character in
  the string which is what other programming languages chose to do.

#### Breaking changes in the compiler

### Library additions

- ``re.split`` now also supports the ``maxsplit`` parameter for consistency
  with ``strutils.split``.

### Library changes

### Language additions

### Language changes

### Tool changes

- ``jsondoc2`` has been renamed ``jsondoc``, similar to how ``doc2`` was renamed
  ``doc``. The old ``jsondoc`` can still be invoked with ``jsondoc0``.

### Compiler changes

- Support for code hot reloading has been implemented for the JavaScript
  target. To use it, compile your code with `--hotReloading:on` and use a
  helper library such as LiveReload or BrowserSync.

### Bugfixes

- The `importcpp` pragma now allows importing the listed fields of generic
  C++ types. Support for numeric parameters have also been added through
  the use of `static[T]` types.
  (#6415)
