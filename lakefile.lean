import Lake
open Lake DSL

package «lean-emerald» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «LeanEmerald» where
  srcDir := "."

lean_exe «smoke» where
  root := `Smoke
