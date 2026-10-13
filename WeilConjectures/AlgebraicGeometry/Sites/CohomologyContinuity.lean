/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Continuity of étale cohomology at inverse limits

Let `(Xᵢ)` be a cofiltered system of quasi-compact quasi-separated schemes over a scheme `S`, with
affine transition maps and limit `X`, and let `F` be an étale sheaf on `S`. Then
`H^q(X, F|_X) = colimᵢ H^q(Xᵢ, F|_{Xᵢ})` ([Stacks, Tag 09YQ]). For sheaves of `Λ`-modules this is
blueprint `lemma-weil-pbc-etale-cohomology-continuity`, proved in
`WeilConjectures.AlgebraicGeometry.Sites.CohomologyLimit`
(`AlgebraicGeometry.Etale.exists_cohomologyRestrictOver_eq_of_isLimit`,
`AlgebraicGeometry.Etale.exists_cohomologyRestrictOver_eq_zero_of_isLimit`), and for abelian
sheaves in `WeilConjectures.AlgebraicGeometry.Sites.CohomologyLimitAddCommGrp`
(`AlgebraicGeometry.Etale.cohomologyMap_isColimit_of_isLimit`).

This file records a generalisation to sheaves with values in an arbitrary Grothendieck abelian
category `A`, in the form in which the pro-étale comparison uses it: if all the
`H^q(Xᵢ, F|_{Xᵢ})` vanish, so does `H^q(X, F|_X)`. The blueprint proof (cocycles on hypercovers,
descended section by section) is elementwise and does not apply to a general `A`; this
generalisation is not proved here.

## Main definitions

- `AlgebraicGeometry.Etale.sectionsFunctor`: the global sections functor of the small étale
  site, the sections over the terminal object.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The global sections functor `Γ(X, -)` on étale sheaves: the sections over the terminal
object `X` of the small étale site. Its right derived functors are the étale cohomology groups
(blueprint `def-weil-pbc-etale-cohomology`). -/
noncomputable abbrev sectionsFunctor (X : Scheme.{u}) : Sheaf X.smallEtaleTopology A ⥤ A :=
  sheafToPresheaf _ A ⋙
    (evaluation _ A).obj (op (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X)))

/-- Etale cohomology continuity with coefficients in a Grothendieck abelian category, in vanishing
form. For sheaves of modules this is blueprint `lemma-weil-pbc-etale-cohomology-continuity`
(`AlgebraicGeometry.Etale.exists_cohomologyRestrictOver_eq_of_isLimit`); the generalisation to an
arbitrary Grothendieck abelian category `A` goes beyond the blueprint.

Let `(Dᵢ)` be a cofiltered system of quasi-compact quasi-separated schemes over `S` with affine
transition maps, with limit `X = c.pt`, and let `F` be an étale sheaf on `S`. Then
`H^q(X, F|_X) = colimᵢ H^q(Dᵢ, F|_{Dᵢ})`; in particular `H^q(X, F|_X)` vanishes as soon as all
the `H^q(Dᵢ, F|_{Dᵢ})` do. -/
theorem isZero_rightDerived_sectionsFunctor_upperStar_of_isLimit {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology A) {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over S) [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left] [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g).left]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c)) (q : ℕ)
    (h : ∀ i, IsZero (((sectionsFunctor A (D.obj i).left).rightDerived q).obj
      ((Etale.upperStar A (D.obj i).hom).obj F))) :
    IsZero (((sectionsFunctor A c.pt.left).rightDerived q).obj
      ((Etale.upperStar A c.pt.hom).obj F)) :=
  sorry

end AlgebraicGeometry.Etale
