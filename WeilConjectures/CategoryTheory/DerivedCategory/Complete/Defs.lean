/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.RingTheory.AdicCompletion.Basic

/-!

# Derived complete objects of the derived category of sheaves of modules

Let `(C, J)` be an (essentially small) site, let `R` be a commutative ring and let `I` be
an ideal of `R`, the intended case being that `R` is `I`-adically complete — for instance
the ring of integers `𝒪_E` of a finite extension of `ℚ_ℓ`, with `I` its maximal ideal.
This file defines what it means for an object `K` of the derived category

```
  D(J, R) := DerivedCategory (Sheaf J (ModuleCat R))
```

of sheaves of `R`-modules on `(C, J)` to be *derived complete*: that `K` is the homotopy
limit `R lim` of its reductions `K ⊗ᴸ R/Iⁿ` (Stacks, Tags 091N and 091Z).

The tower of reductions and the maps into it are built as a chain of cones, each the image
of the previous one under a functor:

* `Ideal.quotPowCone I`, the quotient maps `R ⟶ R ⧸ Iⁿ`, a cone over the tower
  `Ideal.quotPowFunctor I` in `ModuleCat R` whose point is the monoidal unit
  `𝟙_ (ModuleCat R) = R`. If `R` is `I`-adically complete this cone is a limit cone
  (`Ideal.isLimitQuotPowCone`), which is the classical completeness of `R` in the language
  of limits;
* `CategoryTheory.Sheaf.quotPowCone J I`, its image under `constantSheaf J (ModuleCat R)`,
  whose point is the monoidal unit of `Sheaf J (ModuleCat R)`, the constant sheaf on
  `R = 𝟙_ (ModuleCat R)` being that unit;
* `DerivedCategory.quotPowCone J I`, the image of the previous cone under
  `DerivedCategory.singleFunctor _ 0` — a cone over the tower
  `DerivedCategory.quotPowFunctor J I` — whose point is moved to the monoidal unit
  `𝟙_ D(J, R)` along `DerivedCategory.εSingleFunctorZero : 𝟙_ D(J, R) ⟶ (R in degree 0)`
  (the unit comparison of `DerivedCategory.sheafTensorStructure`);
* `DerivedCategory.derivedCompletionCone J I K`, the image of the previous cone under
  `K ⊗ᴸ -` — a cone over the tower `DerivedCategory.derivedCompletionDiagram J I K` —
  whose point is moved to `K` itself along the inverse right unitor
  `K ≅ K ⊗ᴸ 𝟙_ D(J, R)`. Its legs are therefore the reduction maps `K ⟶ K ⊗ᴸ R/Iⁿ`, and
  its point is `K`.

The object `K` is *derived complete* when this last cone is a homotopy limit
(`CategoryTheory.Pretriangulated.IsHomotopyLimit`), i.e. when its legs induce an isomorphism

```
  K ≅ R lim_n (K ⊗ᴸ R/Iⁿ)
```

onto the homotopy limit of the tower: the triangle
`K ⟶ ∏ₙ K ⊗ᴸ R/Iⁿ ──1 - t──▶ ∏ₙ K ⊗ᴸ R/Iⁿ ⟶ K⟦1⟧` is distinguished (the Milnor triangle,
Stacks, Tag 08TB). The homotopy limit is not the categorical limit of the tower, which need
not exist in a triangulated category and, when it exists, is not the derived limit.
Derived completeness of `K` does not presuppose completeness of `R`, and the definition does
not assume `IsAdicComplete I R`.

## Main definitions

- `Ideal.quotPowFunctor` and `Ideal.quotPowCone` : the tower `n ↦ R ⧸ Iⁿ` in `ModuleCat R`
  and the cone over it given by the quotient maps out of the monoidal unit.
- `CategoryTheory.Sheaf.quotPowFunctor` and `CategoryTheory.Sheaf.quotPowCone` : the same
  tower and cone in the category of sheaves of `R`-modules, through the constant sheaf
  functor.
- `DerivedCategory.TensorStructure` and `DerivedCategory.sheafTensorStructure` : the derived
  tensor product of `D(J, R)` with its additivity, linearity, compatibility with shifts and
  triangulatedness in each variable, bundled once (see the implementation notes).
- `DerivedCategory.quotPowFunctor` and `DerivedCategory.quotPowCone` : the tower
  `n ↦ R/Iⁿ` in the derived category and the cone over it out of the monoidal unit.
- `DerivedCategory.derivedCompletionDiagram` : the tower `n ↦ K ⊗ᴸ R/Iⁿ` of reductions
  of `K`.
- `DerivedCategory.derivedCompletionCone` : the cone `K ⟶ K ⊗ᴸ R/Iⁿ`, with point `K`.
- `DerivedCategory.derivedComplete` : the object property of being derived complete.

## Main results

- `Ideal.isLimitQuotPowCone` : if `R` is `I`-adically complete then `R` is the limit of the
  tower `n ↦ R ⧸ Iⁿ`.
- `DerivedCategory.derivedComplete_iff_exists_iso` : given any homotopy limit
  `R lim_n (K ⊗ᴸ R/Iⁿ)` of the tower, `K` is derived complete exactly when it is isomorphic
  to it compatibly with the reduction maps.

## Implementation notes

Mathlib's `IsAdicComplete` API is phrased in terms of the quotients `M ⧸ (Iⁿ • ⊤)` of a
module `M`, whereas the tower here is phrased in terms of the ideal quotients `R ⧸ Iⁿ`,
which is the form in which it is tensored downstream. The two are compared by
`Ideal.quotSmulTopEquiv`, which is where `Iⁿ • (⊤ : Submodule R R) = Iⁿ` is used; every
compatibility with it holds by `rfl`, both sides being quotients of `R` by propositionally
equal submodules.

Every piece of structure the constructions below need is found by instance search, for any
essentially small site and with no local activation or hypothesis: `Sheaf J (ModuleCat R)`
is Grothendieck abelian and has a derived category; it is monoidal by
`CategoryTheory.GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall` (the
sheafification of the objectwise tensor product) and monoidal closed by
`…monoidalClosed_sheaf_of_essentiallySmall` (Day's reflection theorem); and it has
functorial flat resolutions because `ModuleCat R` does
(`ModuleCat.hasFunctorialFlatResolution`), which through
`DerivedCategory.hasDerivedMonoidalCategory` supplies the K-flat derived monoidal structure
`DerivedCategory.Qh.HasDerivedMonoidalCategory` and hence the monoidal structure of
`DerivedCategory (Sheaf J (ModuleCat R))`.

That convenience has a cost which the declarations below are written to avoid, and which is
the reason `DerivedCategory.derivedCompletionDiagram` exists as a definition of its own.
The elaborated `MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat R)))` instance is an
expression carrying `HasSheafify`, `IsGrothendieckAbelian`, `MonoidalPreadditive` and
`Qh.HasDerivedMonoidalCategory` proofs inside it. When such an expression occurs in the
*declared type* of a definition, `Lean.Meta.abstractNestedProofs` — which lifts the proofs
occurring in a definition's **value** into auxiliary theorems, but does not touch its
declared type — makes the inferred and the declared type differ in every one of those proof
positions; the kernel then has to reconcile them through proof irrelevance, which means
comparing propositions whose own instance arguments differ in the same way, and the descent
fans out. In practice it does not terminate: stating `derivedCompletionCone` directly over
`DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K` does not compile even with `sorry` for
its value, whereas the version below, whose type mentions only the constant
`DerivedCategory.derivedCompletionDiagram` applied to `J`, `I` and `K`, compiles in a few
seconds. Keeping the monoidal structure of the derived category inside definition *bodies*
and out of the types stated here is what makes this file check; the `Aux` section above
does the same for `DerivedCategory.εSingleFunctorZero`.

The same mechanism also makes the *bodies* expensive to compare with freshly elaborated
terms: elaborating a definition abstracts the proofs nested in the monoidal instance, so the
instance in the body of `derivedCompletionDiagram` is no longer syntactically the one
elaborated in a later file, and unfolding it there makes the kernel run the same descent.
For this reason the monoidal structure used here is not the one found by instance search at
each use, but the field `monoidalCategory` of the constant
`DerivedCategory.sheafTensorStructure J R`, which bundles once the derived monoidal structure
together with the instances the proofs about derived completeness need (additivity and
`R`-linearity in each variable, compatibility with shifts, triangulatedness). Files proving
results about derived completeness use the fields of this constant as their instances, so
that every comparison is between applications of the same constant.
The constant is the specialization of `DerivedCategory.tensorStructure`, which is built for an
arbitrary category `A`: building the structure directly for sheaves would check its fields
against types containing the concrete monoidal instance, with the same cost.

-/

@[expose] public section

universe w v' u' u

open CategoryTheory Limits MonoidalCategory Opposite

namespace Ideal

variable {R : Type u} [CommRing R] (I : Ideal R)

variable {I}

variable (I) [IsAdicComplete I R]

end Ideal

section Aux

variable (A : Type u') [Category.{v'} A] [Abelian A] [HasColimitsOfSize.{0, 0} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [HasDerivedCategory.{w} A]
  [DerivedCategory.Qh.HasDerivedMonoidalCategory
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]

end Aux

section TensorStructure

variable (A : Type u') [Category.{v'} A] [Abelian A] [IsGrothendieckAbelian.{v'} A]
  [HasDerivedCategory.{v'} A] [MonoidalCategory A] [MonoidalClosed A] [MonoidalPreadditive A]
  [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  (R : Type*) [Ring R] [Linear R A] [MonoidalLinear R A]

end TensorStructure

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R] (I : Ideal R)

section Derived

namespace DerivedCategory

variable {J I}

end DerivedCategory

end Derived
