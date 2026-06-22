# Formal Software Verification in Lean 4

This repository accompanies the paper _"Formal software verification: AI-generated code to check AI-generated code"_. It contains three self-contained Lean 4 projects of increasing complexity, each demonstrating a formally verified property proved with the assistance of a large language model.

| Directory     | What is verified                                                   |
| ------------- | ------------------------------------------------------------------ |
| `zip-unzip/`  | `List.unzip` followed by `List.zip` is the identity                |
| `assoc-list/` | `insert`/`get?` algebraic specification of an associative-list map |
| `aes/`        | AES-128 decryption is the left inverse of AES-128 encryption       |

---

## Prerequisites

### 1 — Install `elan` (the Lean version manager)

`elan` manages Lean toolchains automatically and is the only tool you need to install manually. Once it is present, it will download the exact Lean version required by each project on first use.

**Linux / macOS**

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

Follow the on-screen prompts (accepting the defaults is fine). Then restart your shell or run:

```bash
source ~/.profile   # or ~/.bash_profile / ~/.zshrc depending on your shell
```

**Windows**

Open a PowerShell or Git Bash terminal and run:

```powershell
curl -O --location https://elan.lean-lang.org/elan-init.ps1
powershell -ExecutionPolicy Bypass -f elan-init.ps1
del elan-init.ps1
```

**Verify the installation**

```bash
elan --version
lean --version   # should print the stable toolchain version
```

### 2 — Install `git` and `curl` (if not already present)

These are standard tools available through any package manager (`apt`, `brew`, `pacman`, `winget`, etc.) and are typically already installed on most development machines.

### 3 — (Optional) VS Code with the Lean 4 extension

For an interactive proof environment with real-time feedback, install [Visual Studio Code](https://code.visualstudio.com/) and search for the **Lean 4** extension (`leanprover.lean4`) in the Extensions panel. The extension will use the toolchain specified by each project's `lean-toolchain` file automatically.

---

## Building the projects

### `zip-unzip` and `assoc-list`

These are single-file projects with no external dependencies. You can check them directly with `lean`:

```bash
# Lean will be downloaded by elan if not already present
lean zip-unzip/ZipUnzip.lean
lean assoc-list/AssocList.lean
```

### `aes` (the main project)

The AES project is a full Lake package and depends on [Mathlib](https://github.com/leanprover-community/mathlib4). Building it for the first time will download Mathlib's pre-built cache, which may take a few minutes depending on your connection.

```bash
cd aes

# Download Lean toolchain for this project (done automatically by elan)
# and fetch the Mathlib cache (saves re-compiling Mathlib from scratch)
lake exe cache get

# Build everything: library, proofs, and tests
lake build
```

If `lake exe cache get` is not available or fails, you can build without the cache — it will just take longer as Mathlib is compiled locally:

```bash
lake build
```

**Expected output on success**

```
Build completed successfully.
```

The `#eval` checks in `Test/CypherTest.lean` and `Test/KeyExpansionTest.lean` are
evaluated during elaboration and will print any failures to the build log. All checks
should pass silently.

---

## Troubleshooting

**`elan` not found after installation**

Make sure `~/.elan/bin` is on your `PATH`. You can add it manually:

```bash
export PATH="$HOME/.elan/bin:$PATH"
```

**`lake exe cache get` fails**

This sometimes happens with network issues or if the Mathlib cache for the exact toolchain version is not yet available. Run `lake build` directly instead — it will compile Mathlib from source.

**Build fails with "unknown package" or dependency errors**

Make sure you are inside the `aes/` directory when running `lake` commands, and that `lake-manifest.json` has not been modified. If the manifest is out of sync, run:

```bash
lake update
lake build
```

**Heartbeat limit errors during build**

Some proofs use `native_decide` over large finite types and may be slow on older hardware. If you see heartbeat warnings, they are non-fatal and the build will still succeed. Actual heartbeat _errors_ (which would cause a build failure) should not occur in the released version.

---

## Reference

- [Lean 4 documentation](https://lean-lang.org)
- [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Lake build system](https://github.com/leanprover/lake)
