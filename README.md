<p align="center">
  <a href="" rel="noopener">
 <img height=96px src="assets/logo.png" alt="Project logo"></a>
</p>

<h1 align="center">Protonscript Programming Language</h1>
<p align="center">
A Typescript dialect that compiles to C
</p> 
<br />

```js
function main() {
  printf("Hello, world!")
  return 0
}
```
<br />

<div align="center">

[![Status](https://img.shields.io/badge/status-active-success.svg)]()
[![GitHub Issues](https://img.shields.io/github/issues/thomasvergne/protonscript.svg)](https://github.com/thomasvergne/protonscript/issues)
[![GitHub Pull Requests](https://img.shields.io/github/issues-pr/thomasvergne/protonscript.svg)](https://github.com/thomasvergne/protonscript/pulls)
[![License](https://img.shields.io/badge/license-MIT-blue.svg)](/LICENSE)
</div>

## Modern and powerful features
- **Statically typed** for safe and clean programming
- **Javascript inheritance** for simple and rapid prototyping.
- **Compilation step** for almost native performances

## How to build Protonscript
### Requirements
- GCC or CLang compiler
- Cabal 3.0
- GHC 9.4.2

### Build from sources
```bash
$ git clone https://github.com/thomasvergne/protonscript.git
$ cd protonscript
$ cabal install # install in path
```

## How to use Protonscript
### Compile a file
```bash
$ protonscript compile <file>
```