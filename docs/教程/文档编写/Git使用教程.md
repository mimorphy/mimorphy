# Git 贡献者指南：从克隆到 PR

## 一、简介
作为项目贡献者，您将通过 Git 为开源项目贡献代码。本指南聚焦于**如何为现有项目贡献代码**，从获取代码到提交 Pull Request 的完整流程。

---

## 二、准备工作

### 1. 配置 Git
```bash
git config --global user.name "Your Name" # 你在Git中打算使用的名称
git config --global user.email "your.email@example.com" # 你的Github账户所使用的邮箱，如果没有Github账户，可以去创建一个
git config --global core.editor "code" # 例如 VS Code
```

---

## 三、获取项目代码（核心步骤）

### 1. Fork 仓库（GitHub/GitLab）
- 访问目标项目仓库（如 `https://github.com/original-owner/project`）
- 点击右上角 **Fork** 按钮 → 选择您的账号
- *效果：您获得自己的 `https://github.com/your-username/project` 仓库*

### 2. 克隆您的 Fork
```bash
git clone https://github.com/your-username/project.git
cd project
```

### 3. 设置上游仓库（关联原项目）
```bash
git remote add upstream https://github.com/original-owner/project.git
git fetch upstream
```

> ✅ 验证：`git remote -v` 应显示 `origin`（您的仓库）和 `upstream`（原项目）

---

## 四、开发工作流程

### 1. 创建新分支（必须！）
```bash
# 切换到最新上游主分支
git checkout main
git pull upstream main

# 创建并切换新分支（命名规范：feature/描述 或 bugfix/编号）
git checkout -b fix-login-error
```

### 2. 开发与提交
```bash
# 修改代码
# ...（编写代码/修复问题）

# 添加变更到暂存区
git add .  # 或指定文件：git add src/file.js

# 提交（关键！描述需清晰）
git commit -m "Fix: Login fails with invalid email format (#123)" # -m 后面的字符串说明这次提交修改了什么内容
```

### 3. 推送分支到您的 Fork
```bash
git push origin fix-login-error
```

> 💡 提示：首次推送需关联分支：`git push -u origin fix-login-error`

---

## 五、提交 Pull Request (PR)

### 1. 创建 PR
1. 访问您的 Fork 仓库（`https://github.com/your-username/project`）
2. 点击 **Compare & pull request**
3. 选择：
   - **Base**: `main`（原项目主分支）
   - **Compare**: `fix-login-error`（您的分支）
4. 添加详细描述：
   - 问题描述（如：`#123` 修复登录邮箱验证问题）
   - 测试步骤
   - 相关截图/链接

### 2. PR 审核流程
| 状态 | 操作 |
|------|------|
| **等待审核** | 维护者查看代码 |
| **需要修改** | 修改代码 → `git add .` → `git commit -m "Fix review comments"` → `git push origin fix-login-error` |
| **已合并** | 您的分支自动删除（可选） |

---

## 六、常见问题解决

### 1. 本地分支落后上游
```bash
# 同步原项目最新代码
git checkout main
git pull upstream main

# 重新基于最新代码创建分支
git checkout -b new-feature
git pull origin main  # 确保同步
```

### 2. PR 中出现合并冲突
```bash
# 1. 同步上游代码
git pull upstream main

# 2. 解决冲突（打开冲突文件，删除 <<<<<<<, =======, >>>>>>> 标记）
# 3. 添加解决后的文件
git add . 

# 4. 提交并推送
git commit -m "Resolve merge conflict"
git push origin fix-login-error
```

### 3. 需要更新 PR 但不想重新提交
```bash
# 在本地分支修改后
git add .
git commit --amend  # 修正提交信息
git push -f origin fix-login-error  # 强制推送
```

> ⚠️ 注意：`-f` 仅用于更新自己的 PR，不要用于公共分支

---

## 七、最佳实践（贡献者必备）

| 事项 | 做法 |
|------|------|
| **分支命名** | `feature/checkout-flow` 或 `bugfix/404-page` |
| **提交信息** | 使用 [Conventional Commits](https://www.conventionalcommits.org/)：<br> `feat: add user profile page`<br> `fix: handle null user data` |
| **提交频率** | 每日多次小提交（避免大而全的提交） |
| **PR 描述** | 包含：问题编号、影响范围、测试验证步骤 |
| **冲突处理** | 优先拉取上游更新，避免长期未同步 |
| **清理分支** | PR 合并后删除本地分支：`git branch -d fix-login-error` |

---

## 八、关键命令速查表

| 操作 | 命令 |
|------|------|
| 查看分支状态 | `git status` |
| 检查远程仓库 | `git remote -v` |
| 拉取上游更新 | `git pull upstream main` |
| 强制推送更新 | `git push -f origin branch-name` |
| 查看提交历史 | `git log --oneline -5` |
| 丢弃未提交更改 | `git checkout .` |

---

> 💡 **记住**：Git 是协作的桥梁，不是障碍。  
> **每次 PR 都应包含可验证的变更**（如：修复了 #123 问题，测试通过）  
> **保持分支整洁**：一个 PR 一个功能/修复，避免混杂无关修改  
> **求助AI**：对于不了解的命令，可以询问AI以获取相关信息