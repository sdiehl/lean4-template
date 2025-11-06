# Lean 4 Template

A well-structured starting template for Lean 4 projects with Mathlib support.

-  **Lean 4 v4.24.0** with Mathlib and Batteries
-  **Unit testing framework** with example tests
-  **Lint and validation scripts** for checking
-  **Pre-configured lakefile** with sensible defaults

### Prerequisites

- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html)

### Setup

1. **Clone or copy this template:**

   ```bash
   cp -r lean-template my-new-project
   cd my-new-project
   ```

2. **Update project name:**

   - Edit `lakefile.lean` and change `package MyProject` to your project name
   - Rename `src/MyProject.lean` and `src/MyProject/` accordingly
   - Update imports in all files to use your new project name

3. **Build the project:**

   ```bash
   lake build
   ```

4. **Run tests:**

   ```bash
   lake test
   ```

5. **Run the main executable:**

   ```bash
   lake exe myproject
   ```

## Development

### Building

```bash
# Build everything
lake build

# Build specific target
lake build MyProject

# Clean build artifacts
lake clean
```

### Testing

```bash
# Run all tests
lake test

# Run tests directly
.lake/build/bin/tests
```

### Linting

```bash
# Run all lint checks
lake lint
```

## LLM Integration

Install [lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp).

Then add the Lean 4 Skills plugin and install desired skills:

```bash
/plugin marketplace add cameronfreer/lean4-skills
/plugin install lean4-theorem-proving    # Core skill + commands (REQUIRED)
/plugin install lean4-memories           # Optional: adds persistent memory (requires lean4-theorem-proving)
/plugin install lean4-subagents          # Optional: adds specialized agents (requires lean4-theorem-proving)
```

## License

This template is provided as-is for use in your own projects. Just do whatever you want with it!
