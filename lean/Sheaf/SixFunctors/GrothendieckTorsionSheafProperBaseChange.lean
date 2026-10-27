/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B9
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded

/-! # Proper base change for a torsion sheaf with Grothendieck abelian coefficients -/

@[expose] public section
set_option autoImplicit false
universe u' u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [HasSmallSiteSheafify A]

/-- Proper base change for a sheaf with finite-exponent geometric stalks.

Source: SGA 4 XII, 5.1 and XVII, 4.3.2(ii). The extension from module coefficients
to Grothendieck abelian coefficients uses Gabriel--Popescu and finite-hypercover
cohomology; it is a separate coefficient argument, rather than a specialization of
the module theorem.

Proof in words: the assertion is local on the two bases, so restrict to affine bases;
the proper sources are then qcqs. Write F as the filtered union of the kernels of
(m! : F → F). Exactness and preservation of filtered colimits by geometric stalks,
together with the given positive stalk annihilators, show that this union is F.
On a qcqs scheme finite split etale hypercovers compute sheaf cohomology. Their
cochains use finite products in each degree; exact filtered colimits therefore commute
with their cohomology and its filtered refinement colimit. Consequently higher direct
images commute with filtered colimits locally on the base. It suffices to treat F
annihilated by one positive integer n.

Choose a Gabriel--Popescu exact localization L : Mod R → A with fully faithful right
adjoint U. Compose with L and sheafify to obtain an exact localization on sheaves,
with sectionwise right adjoint U. On the coherent etale basis this left localization
is computed sectionwise: L preserves the finite limits in the sheaf condition.
The same hypercover computation shows that it commutes with derived sections on
qcqs schemes, hence locally with the derived direct image of a proper morphism.
It also commutes with inverse image, by the adjunctions and sectionwise direct image.
The sheaf UF is annihilated by n and its localized image is F by the counit.
Proper base change for R-module sheaves follows from the abelian torsion theorem
by forgetting the R-action. Apply the exact localization L to this comparison and
use the preceding compatibilities. Naturality of the units and counits identifies
the transported map with the canonical exchange for F. Finally pass to the filtered
union, and use the canonical comparison of bounded-below and unbounded derived
functors at F[0]. These comparisons compute the same resolutions and adjunction mate.
(blueprint: lem-sf-grothendieck-torsion-sheaf-proper-base-change). -/
theorem isIso_derivedBaseChangeMap_single_of_stalkwise_finite_exponent
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} [IsProper f] (sq : IsPullback g' f' f g)
    (F : Sheaf X.smallEtaleTopology A)
    (hT : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      ∃ N : ℕ, 0 < N ∧ N • (𝟙 ((Scheme.pointSmallEtale s).sheafFiber.obj F)) = 0) :
    IsIso ((derivedBaseChangeMap A sq.toCommSq).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) := by
  sorry

end AlgebraicGeometry.Etale
