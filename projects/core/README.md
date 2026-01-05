# Core 基础模块库

## 项目简介

Core 是一个基础功能模块库，为其他项目提供可复用的核心模块。其他项目在使用时需要引入头文件并编译源文件。

## 快速配置

在使用本模块的项目中，需要配置以下文件：

### 1. 配置 `.vscode/tasks.json`（编译任务）

在编译命令中添加头文件路径和源文件：

```json
{
    "tasks": [
        {
            "type": "shell",
            "label": "clang++ build active file",
            "command": "clang++",
            "args": [
                // 其他编译参数...
                "-I${workspaceFolder}/../core/include",       // 包含 Core 头文件
                "${workspaceFolder}/../core/src/*.cpp",        // 编译 Core 源文件
                "${workspaceFolder}/src/*.cpp",                     // 编译您的源文件
            ],
            // 其他配置...
        }
    ]
}
```

### 2. 配置 `.vscode/settings.json`（编辑器设置）

为 clangd 添加头文件搜索路径：

```json
{
    "clangd.fallbackFlags": [
        // 其他编译参数...
        "-I${workspaceFolder}/../core/include"  // 添加 Core 头文件路径
    ]
}
```

## 使用方法

在代码中包含需要的头文件：

```cpp
#include "core_module.h"  // 自动在配置的路径中查找
```

## 项目结构

```
project/
├── .vscode/
│   ├── tasks.json    # 需配置编译命令
│   └── settings.json # 需配置 clangd
├── src/
│   └── main.cpp
└── ...
```

```
../core/              # Core 项目
    ├── include/      # 头文件目录
    └── src/          # 源文件目录
```

## 注意事项

- 路径假设 Core 项目在您项目的同级目录中
- 如路径不同，请相应调整 `${workspaceFolder}/../core`
- 编译时 Core 的所有源文件都会参与编译