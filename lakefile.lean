import Lake
open Lake DSL

package «fexpr-trivial-mechanized» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «FexprTrivial» where
  srcDir := "."
