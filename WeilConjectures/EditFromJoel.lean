module  -- shake: keep-all --deprecated_module: ignore

public import WeilConjectures.EditFromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives
public import WeilConjectures.EditFromJoel.Algebra.Homology.DerivedCategory.Monoidal
public import WeilConjectures.EditFromJoel.Algebra.Homology.HomotopyCategory.PreservesQuasiIso
public import WeilConjectures.EditFromJoel.CategoryTheory.Abelian.Flat.KFlat

/-!
# `EditFromJoel`: the `FromJoel` files rewritten on top of the opaque `DerivedCategory'`

The modules under `WeilConjectures.EditFromJoel` are ports of the corresponding
`WeilConjectures.FromJoel` modules in which `DerivedCategory` is replaced by the `@[no_expose]`
wrapper `DerivedCategory'` (see
`WeilConjectures.EditMathlib.Algebra.Homology.DerivedCategory.Basic`). They are built on
`WeilConjectures.EditMathlib` rather than on `Mathlib.Algebra.Homology.DerivedCategory.*`.

These are the only four `FromJoel` modules that mention `DerivedCategory`; every other
`FromJoel` module is used unchanged.

Like `WeilConjectures.EditMathlib`, this is a tree of *drop-in replacements*: a ported module
declares the same names as the `FromJoel` module it replaces, so it must never end up in the
same import closure as that module, and this tree is therefore kept out of the
`WeilConjectures` root module. It is consequently not covered by a bare `lake build`; build it
with `lake build WeilConjectures.EditFromJoel`.
-/
