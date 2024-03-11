# Clause-Level MCSAT
## 目前焦点
![](https://cdn.nlark.com/yuque/0/2024/jpeg/26979990/1709640289984-3ff1fc0b-e3d5-49b7-bcc4-3c3d88924eaf.jpeg)

在选择到path case之后，仍然需要decide literal，但是这个时候的decide是伪decide （任何一种选择不会产生path）。
z3原生产生子句后，会回退到decide层面的trail，然后尝试选择其他literal,这一点在cls-lvl可以避免。
问题是cls-lvl要回退到哪一层？
## Set Path for Arithmetic Variable
One-Level Path:
![](https://cdn.nlark.com/yuque/0/2024/jpeg/26979990/1709705681160-97a5da0a-8928-4fc0-a9f9-cdb31343de04.jpeg)
Two-Level Path:
![](https://cdn.nlark.com/yuque/0/2024/jpeg/26979990/1709706890966-efe234ff-7a09-49cd-b749-e4797d3f9e1a.jpeg)
## shortcut for unsat (只有一个变量)
当前process的clauses只还有一个变量(max var)，并且组成的satisfying interval为空集，直接返回unsat
## common case (仍然含有多个变量，此时应该怎么学习子句？)
![](https://cdn.nlark.com/yuque/0/2024/jpeg/26979990/1709711558096-a333b6ea-42ac-4a68-906d-4f05e825b95a.jpeg)
目前做法：
在found decision之后，回退到block状态，然后继续尝试其他选择，以生成完整的多path下的lemma
undo_until_block()
## 第一版算法(with bug)
### Search:
![](https://cdn.nlark.com/yuque/0/2024/jpeg/26979990/1709718473151-d10851cd-1d5a-4922-b4a2-114e2bc83a1c.jpeg)

### Conflict Analysis
这里主要有四种分类

- 布尔冲突
   - 之前有decide
   - 之前没有decide
- 算术冲突
   - 存在semantic decision
   - 不存在semantic decision （完全由arithmetic value造成）

此时应该对应四种算法，假定我们目前和z3一样，尝试回退到decision level，然后选择其他路径（虽然这在cls-lvl的做法中是不被提倡的）

1. 布尔冲突
   1. 之前有decide: 回退到decision level，然后尝试process clause
   2. 之前没有decide?
2. 算术冲突
   1. 存在semantic decision，此时的lemma应该含有一个decision literal，回退到decision level，然后process lemma，为了得到decision literal否定的赋值
   2. 不存在semantic decision，回退到stage，然后根据新的lemma从新计算clause-infeasible，继续path case和full case的分支
### Search with lemma:
当新的lemma生成之后，分两种情况

1. 之前是path case，用clause infeasible去计算和lemma的不可行区域union
   1. path case，赋值并继续search
   2. full case，重新process并回到resolve
2. 之前是full case

重新process并回到resolve
## 冲突分析时的几种情况
### only previous stage
![](https://cdn.nlark.com/yuque/__latex/06c5464eabd97ffce1721708772d7ab2.svg#card=math&code=x%5E2%20-%209x%2B20%20%5Cle%200%5C%5C%0Ay%5E2%20%5Cle%20-x%20-%201&id=Tu1Bw)
var order: [x, y]
[x -> 4.5, !(x + 1 > 0), empty lemma]
### conflict is caused by curr decision
![](https://cdn.nlark.com/yuque/__latex/f2ef7e4ad6dbf3b83ef603eb7471c48d.svg#card=math&code=x%5E2%20-%209x%2B20%20%5Cle%200%20%5Cvee%20x%5E2%20-5x%2B6%5Cle0%5C%5C%0Ay%5E2%20%5Cle%20-x%20-%201&id=AYmaH)
### conflict is not caused by curr decision, but still in curr stage
### 
## Debug (/home/wangzh/z3/build/z3 /pub/data/wangzh/smt_benchmark/QF_NRA/20180501-Economics-Mulligan/MulliganEconomicsModel0055c.smt2)


<<<<<<< HEAD
If you are not familiar with Z3, you can start [here](https://github.com/Z3Prover/z3/wiki#background).

Pre-built binaries for stable and nightly releases are available from [here](https://github.com/Z3Prover/z3/releases).

Z3 can be built using [Visual Studio][1], a [Makefile][2] or using [CMake][3]. It provides
[bindings for several programming languages][4]. 

See the [release notes](RELEASE_NOTES.md) for notes on various stable releases of Z3.

## Build status

| Azure Pipelines | Code Coverage | Open Bugs | Android Build | WASM Build | Windows Build |
| --------------- | --------------|-----------|---------------|------------|---------------|
| [![Build Status](https://dev.azure.com/Z3Public/Z3/_apis/build/status/Z3Prover.z3?branchName=master)](https://dev.azure.com/Z3Public/Z3/_build/latest?definitionId=1&branchName=master) | [![CodeCoverage](https://github.com/Z3Prover/z3/actions/workflows/coverage.yml/badge.svg)](https://github.com/Z3Prover/z3/actions/workflows/coverage.yml) | [![Open Issues](https://github.com/Z3Prover/z3/actions/workflows/wip.yml/badge.svg)](https://github.com/Z3Prover/z3/actions/workflows/wip.yml) |[![Android Build](https://github.com/Z3Prover/z3/actions/workflows/android-build.yml/badge.svg)](https://github.com/Z3Prover/z3/actions/workflows/android-build.yml) | [![WASM Build](https://github.com/Z3Prover/z3/actions/workflows/wasm.yml/badge.svg)](https://github.com/Z3Prover/z3/actions/workflows/wasm.yml) | [![Windows](https://github.com/Z3Prover/z3/actions/workflows/Windows.yml/badge.svg)](https://github.com/Z3Prover/z3/actions/workflows/Windows.yml)

<a href="https://github.com/z3prover/z3/pkgs/container/z3">Docker image</a>.

[1]: #building-z3-on-windows-using-visual-studio-command-prompt
[2]: #building-z3-using-make-and-gccclang
[3]: #building-z3-using-cmake
[4]: #z3-bindings

## Building Z3 on Windows using Visual Studio Command Prompt

32-bit builds, start with:

```bash
python scripts/mk_make.py
```

or instead, for a 64-bit build:

```bash
python scripts/mk_make.py -x
```

then:

```bash
cd build
nmake
```

Z3 uses C++17. The recommended version of Visual Studio is therefore VS2019. 

## Building Z3 using make and GCC/Clang

Execute:

```bash
python scripts/mk_make.py
cd build
make
sudo make install
```

Note by default ``g++`` is used as the C++ compiler if it is available. If you
would prefer to use Clang change the ``mk_make.py`` invocation to:

```bash
CXX=clang++ CC=clang python scripts/mk_make.py
```

Note that Clang < 3.7 does not support OpenMP.

You can also build Z3 for Windows using Cygwin and the Mingw-w64 cross-compiler.
To configure that case correctly, make sure to use Cygwin's own python and not
some Windows installation of Python.

For a 64 bit build (from Cygwin64), configure Z3's sources with
```bash
CXX=x86_64-w64-mingw32-g++ CC=x86_64-w64-mingw32-gcc AR=x86_64-w64-mingw32-ar python scripts/mk_make.py
```
A 32 bit build should work similarly (but is untested); the same is true for 32/64 bit builds from within Cygwin32.

By default, it will install z3 executable at ``PREFIX/bin``, libraries at
``PREFIX/lib``, and include files at ``PREFIX/include``, where ``PREFIX``
installation prefix is inferred by the ``mk_make.py`` script. It is usually
``/usr`` for most Linux distros, and ``/usr/local`` for FreeBSD and macOS. Use
the ``--prefix=`` command line option to change the install prefix. For example:

```bash
python scripts/mk_make.py --prefix=/home/leo
cd build
make
make install
```

To uninstall Z3, use

```bash
sudo make uninstall
```

To clean Z3 you can delete the build directory and run the ``mk_make.py`` script again.

## Building Z3 using CMake

Z3 has a build system using CMake. Read the [README-CMake.md](README-CMake.md)
file for details. It is recommended for most build tasks, 
except for building OCaml bindings.

## Building Z3 using vcpkg

vcpkg is a full platform package manager, you can easily install libzmq with vcpkg.
 
Execute:

```bash
git clone https://github.com/microsoft/vcpkg.git
./bootstrap-vcpkg.bat # For powershell
./bootstrap-vcpkg.sh # For bash
./vcpkg install z3
```

## Dependencies
Z3 itself has few dependencies. It uses C++ runtime libraries, including pthreads for multi-threading.
It is optionally possible to use GMP for multi-precision integers, but Z3 contains its own self-contained 
multi-precision functionality. Python is required to build Z3. To build Java, .Net, OCaml, 
Julia APIs requires installing relevant tool chains.

## Z3 bindings

Z3 has bindings for various programming languages.

### ``.NET``

You can install a nuget package for the latest release Z3 from [nuget.org](https://www.nuget.org/packages/Microsoft.Z3/).

Use the ``--dotnet`` command line flag with ``mk_make.py`` to enable building these.


See [``examples/dotnet``](examples/dotnet) for examples.

### ``C``

These are always enabled.

See [``examples/c``](examples/c) for examples.

### ``C++``

These are always enabled.

See [``examples/c++``](examples/c++) for examples.

### ``Java``

Use the ``--java`` command line flag with ``mk_make.py`` to enable building these.

See [``examples/java``](examples/java) for examples.

### ``OCaml``

Use the ``--ml`` command line flag with ``mk_make.py`` to enable building these.

See [``examples/ml``](examples/ml) for examples.

### ``Python``

You can install the Python wrapper for Z3 for the latest release from pypi using the command

```bash
   pip install z3-solver
```

Use the ``--python`` command line flag with ``mk_make.py`` to enable building these.

Note that it is required on certain platforms that the Python package directory
(``site-packages`` on most distributions and ``dist-packages`` on Debian based
distributions) live under the install prefix. If you use a non standard prefix
you can use the ``--pypkgdir`` option to change the Python package directory
used for installation. For example:

```bash
python scripts/mk_make.py --prefix=/home/leo --python --pypkgdir=/home/leo/lib/python-2.7/site-packages
```

If you do need to install to a non standard prefix a better approach is to use
a [Python virtual environment](https://virtualenv.readthedocs.org/en/latest/)
and install Z3 there. Python packages also work for Python3.
Under Windows, recall to build inside the Visual C++ native command build environment.
Note that the ``build/python/z3`` directory should be accessible from where python is used with Z3 
and it depends on ``libz3.dll`` to be in the path.

```bash
virtualenv venv
source venv/bin/activate
python scripts/mk_make.py --python
cd build
make
make install
# You will find Z3 and the Python bindings installed in the virtual environment
venv/bin/z3 -h
...
python -c 'import z3; print(z3.get_version_string())'
...
```

See [``examples/python``](examples/python) for examples.

### ``Julia``

The Julia package [Z3.jl](https://github.com/ahumenberger/Z3.jl) wraps the C++ API of Z3. Information about updating and building the Julia bindings can be found in [src/api/julia](src/api/julia).

### ``Web Assembly`` / ``TypeScript`` / ``JavaScript``

A WebAssembly build with associated TypeScript typings is published on npm as [z3-solver](https://www.npmjs.com/package/z3-solver). Information about building these bindings can be found in [src/api/js](src/api/js).

### Smalltalk (``Pharo`` / ``Smalltalk/X``)

Project [MachineArithmetic](https://github.com/shingarov/MachineArithmetic) provides Smalltalk interface
to Z3's C API. For more information, see [MachineArithmetic/README.md](https://github.com/shingarov/MachineArithmetic/blob/pure-z3/MachineArithmetic/README.md)

## System Overview

![System Diagram](https://github.com/Z3Prover/doc/blob/master/programmingz3/images/Z3Overall.jpg)

## Interfaces

* Default input format is [SMTLIB2](http://smtlib.cs.uiowa.edu)

* Other native foreign function interfaces:
* [C++ API](https://z3prover.github.io/api/html/group__cppapi.html)
* [.NET API](https://z3prover.github.io/api/html/namespace_microsoft_1_1_z3.html)
* [Java API](https://z3prover.github.io/api/html/namespacecom_1_1microsoft_1_1z3.html)
* [Python API](https://z3prover.github.io/api/html/namespacez3py.html) (also available in [pydoc format](https://z3prover.github.io/api/html/z3.html))
* [Rust](https://github.com/prove-rs/z3.rs)
* C
* OCaml
* [Julia](https://github.com/ahumenberger/Z3.jl)
* [Smalltalk](https://github.com/shingarov/MachineArithmetic/blob/pure-z3/MachineArithmetic/README.md) (supports Pharo and Smalltalk/X)
=======
>>>>>>> 6bc3af889a5eb4d73c0c0674dc12cca55887e2b5


