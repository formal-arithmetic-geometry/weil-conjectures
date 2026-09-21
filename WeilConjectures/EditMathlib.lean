module  -- shake: keep-all --deprecated_module: ignore

public import WeilConjectures.EditMathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.EditMathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.EditMathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import WeilConjectures.EditMathlib.Algebra.Homology.DerivedCategory.Fractions
public import WeilConjectures.EditMathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilConjectures.EditMathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.EditMathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.EditMathlib.Algebra.Homology.DerivedCategory.KProjective
public import WeilConjectures.EditMathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.EditMathlib.Algebra.Homology.DerivedCategory.Plus
public import WeilConjectures.EditMathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.EditMathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.EditMathlib.Algebra.Homology.DerivedCategory.SmallShiftedHom
public import WeilConjectures.EditMathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.EditMathlib.Algebra.Homology.Factorizations.CM5a

/-!
# `EditMathlib`: mathlib files rewritten on top of the opaque `DerivedCategory'`

The modules under `WeilConjectures.EditMathlib` are ports of the corresponding `Mathlib.*`
modules in which `DerivedCategory` is replaced by the `@[no_expose]` wrapper
`DerivedCategory'` (see `WeilConjectures.EditMathlib.Algebra.Homology.DerivedCategory.Basic`).

They are *drop-in replacements*, not extensions: a ported module declares the same names as the
mathlib module it replaces (for the declarations that live outside the `DerivedCategory`
namespace, e.g. `CochainComplex.homologyδOfTriangle`). So a ported module must never end up in
the same import closure as the mathlib module it replaces, and this library is therefore kept
out of the `WeilConjectures` root module.
-/
