# Verus Specification Generator Skill

This skill generates Verus specifications from a Rust implementation and an
abstract specification, then proves a target property. It is designed to keep
the resulting spec aligned with the implementation while producing proof
obligations that Verus can check.

## About Verus

[Verus](https://verus-lang.github.io/verus/guide/) is a verification tool for
Rust. You write specifications (`requires`, `ensures`, `spec fn`, `proof fn`)
alongside executable code inside a `verus! { ... }` block, and Verus statically
checks that the code satisfies those specs for all possible executions. Proofs
are discharged by an SMT solver (Z3), so many properties are checked
automatically; harder obligations may need explicit lemmas or invariants. Verus
adds no runtime checks — verification happens at compile/verify time.

## Setup

To use this skill, you need:

1. **Verus installed and on your PATH**

   Download a [binary release](https://github.com/verus-lang/verus/releases)
   for your platform. On the releases page, open **Assets** and pick the
   archive for Linux (`x86-linux`) or Windows (`x86-win`). See the official
   [installation guide](https://github.com/verus-lang/verus/blob/main/INSTALL.md)
   for details.

   **Linux**

   ```bash
   # From your download directory (adjust the zip name to match the release)
   unzip verus-*.x86-linux.zip
   mv verus-x86-linux verus
   cd verus

   # First run — follow any prompts to install rustup / the required toolchain
   ./verus

   # Add Verus to PATH for future shells (adjust the path if you moved the folder)
   echo 'export PATH="$HOME/verus:$PATH"' >> ~/.bashrc
   source ~/.bashrc

   # Confirm
   verus --version
   ```

   **Windows (PowerShell)**

   ```powershell
   # From your download directory (adjust the zip name to match the release)
   Expand-Archive -Path verus-*.x86-win.zip -DestinationPath .
   Rename-Item verus-x86-win verus
   Set-Location verus

   # First run — follow any prompts to install rustup / the required toolchain
   .\verus.exe

   # Add Verus to your user PATH for future sessions (adjust if you moved the folder)
   $verusDir = (Get-Location).Path
   [Environment]::SetEnvironmentVariable("Path", "$verusDir;" + [Environment]::GetEnvironmentVariable("Path", "User"), "User")

   # Open a new terminal, then confirm
   verus --version
   ```

   After installation, the agent runs `verus <path_to_file>` during spec
   generation. If `verus` is not found, restart your terminal (or IDE) so the
   updated PATH is picked up.

2. **Rust familiarity**
   - Verus extends Rust syntax; the skill assumes you have a Rust implementation
     (typically a doubly linked list) to verify.

3. **This skill available to your AI IDE**
   - This skill follows the portable [Agent Skills](https://agentskills.io/)
     (`SKILL.md`) format and works in Cursor, Claude Code, Windsurf, GitHub
     Copilot, and other agents that support it.
   - Copy or clone this folder into your IDE’s skills directory:

     **Linux / macOS**

     ```bash
     # Project-level (recommended — share with the repo)
     mkdir -p .cursor/skills
     cp -r /path/to/generate-verus-specification .cursor/skills/

     # Or global (available in all projects)
     mkdir -p ~/.cursor/skills
     cp -r /path/to/generate-verus-specification ~/.cursor/skills/
     ```

     **Windows (PowerShell)**

     ```powershell
     # Project-level (recommended — share with the repo)
     New-Item -ItemType Directory -Force -Path .cursor\skills
     Copy-Item -Recurse -Force D:\path\to\generate-verus-specification .cursor\skills\

     # Or global (available in all projects)
     New-Item -ItemType Directory -Force -Path "$env:USERPROFILE\.cursor\skills"
     Copy-Item -Recurse -Force D:\path\to\generate-verus-specification "$env:USERPROFILE\.cursor\skills\"
     ```

     Other common locations (same folder layout on both platforms):
     - Claude Code: `.claude/skills/` or `~/.claude/skills/` (`%USERPROFILE%\.claude\skills\` on Windows)
     - Windsurf: `.windsurf/skills/`
     - Any agent: `.agents/skills/` at the project root

   - Alternatively, install with a skills CLI (e.g. `npx skills add`) if your
     IDE supports it.

4. **An output location for the generated spec**
   - Provide a path to a `.rs` file — ideally in a Rust crate where you can run
     `verus <path_to_file>` to verify the result. The agent runs Verus during
     generation and will fix verification errors iteratively.

## When to Use
- You have a Rust implementation and want to verify it with Verus.
- You have an abstract/mathematical specification you want to formalize.
- You need to prove a specific property (e.g., reachability-based chain validity).

## Required Inputs
1. Rust implementation (file path or snippet).
2. Target property to prove.
3. Output file path for the generated Verus spec.

## Example Prompt
```
/generate-verus-specification for @d:\path\to\index_impl.rs:1-230
targeting reachability-based chain validity and writing the solution to @src/main.rs
```

## Workflow (What the Skill Does)
1. **Analyze inputs**: Identify functions, types, loops/recursion, and the
   abstract list model (nodes, first/last, next/prev, list view).
2. **Map to Verus constructs**: Translate preconditions to `requires`,
   postconditions to `ensures`, and abstract helpers to `spec fn`.
3. **Generate the spec**: Preserve structure, define helpers, and encode all
   behavior for each function, not only the target property.
4. **Add invariants** (if loops/recursion exist): Provide loop invariants and
   `decreases` clauses.
5. **Verify the target property**: Strengthen ensures or add proof functions.
6. **Debug failures**: If verification fails, determine whether the spec is
   weak, incorrect, or if there is a real bug.
7. **Report discrepancies**: If the implementation is actually wrong, report
   the mismatch instead of masking it.
8. **Report proof status**: Summarize what was demonstrated, what still relies
   on assumptions or axioms, and where the proof was difficult.

## Key Rules
- Preserve concrete fields when modeling structs; add ghost fields only as
  additions, not replacements.
- Model full behavior of functions, not just the target property.
- For doubly linked lists, define chain validity via reachability: every node
  reachable from `first` via `next`, and `last` reachable from every node.
- Prove properties against the actual implementation code (exec functions).
- Avoid `#[verifier::external_body]` unless the user provides an explicit axiom.
- Always run `verus <file>` and fix any errors.

## Output
The skill produces:
- A complete annotated Verus file in this repository (specified by the user).
- An explanation of each spec clause.
- Proof obligations addressed.
- A **proof status report** (`{spec}_proof_status.md`) covering:
  - what was fully demonstrated (verified functions, lemmas, target property),
  - what is still assumed (`assume`, `external_body`, restricted `requires`),
  - proof struggles (failures encountered, tactics tried, resolutions).
- A discrepancy report if any bugs or mismatches are found.

## Result Examples
The `result_examples/` folder contains full, generated Verus artifacts from
prior runs. Each file illustrates a distinct implementation model and proof
strategy:
- `result_examples/1.index_codex_5.2_high.rs` shows a baseline index‑based DLL
  spec with explicit reachability predicates and placeholder `assume`‑based
  proof stubs for some mutation obligations.
- `result_examples/2.index_claude_4.8_max.rs` provides a detailed index‑based
  specification with reachability lemmas, link consistency, and a free‑list
  well‑formedness invariant.
- `result_examples/3.index_claude_4.8_max.rs` presents a stronger invariant
  variant that introduces a ghost `order` sequence and proves `valid_chain`
  as a consequence of the inductive representation invariant.
- `result_examples/4.index_claude_4.6_high.rs` emphasizes traversal‑based
  reasoning (e.g., `chain_seq`, `no_dups`, and traversal frame lemmas) for
  reachability‑based validity.
- `result_examples/5.standard_claude_4.6_high.rs` models a pointer‑based DLL as
  an axiom boundary, using a ghost chain plus consistency lemmas for
  `push_back`/`push_front`.
- `result_examples/6.slotmap_claude_4.6_high.rs` models a slotmap‑backed DLL
  with ghost chain and link maps, treating SlotMap operations as external
  bodies while proving link‑consistency lemmas.

## Notes
The generated spec is intentionally storage‑agnostic unless the user asks for
implementation details. It focuses on abstract correctness and proof
obligations that Verus can verify.
