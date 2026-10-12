/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.BaseChange.Square

/-! # Global homology of base change to a chosen strict-local model

Source: Stacks Project, Tags 03Q9 and 03QO.
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
open Scheme

/-- Global sections of homology of base change to any strict-henselization model
are invertible. No geometric stalk or choice of its field occurs in this assertion.
Source: Stacks Project, Tag 03Q9 (theorem-higher-direct-images), and Tag 03QO.
(blueprint: lem-weil-pbc-strict-local-base-change-model-global-homology).

Proof:
1. Apply `isIso_strictHenselization_baseChange_globalHomology` to f, s, K and n.
Compare the mate in that theorem with `derivedBaseChangeMapPlus` on injective
representatives using `Adjunction.derivedPlus_mateEquiv_app_fac` and
`pullbackSquareComparison_hom_app_factorsh`. Their equality follows from
`derivedBaseChangeMapPlus_ext`.
2. Set j = strictHenselizationStructuralMap s and P = pullback f j. The map
b = pullback.lift p₀ (f₀ ≫ eA.hom) sq₀.w is an isomorphism: the square with b,
f₀, pullback.snd f j and eA.hom is cartesian by pullback cancellation, and its
bottom edge is an isomorphism. Its derived mate is invertible, by the formula
`derivedBaseChangeMapPlus_fac_app` on injectives and exact inverse-image equivalences.
3. Use `derivedBaseChangeMapPlus_paste_horiz` for the canonical square and this
isomorphism square. It expresses the chosen mate as the canonical mate pulled back
along eA.hom, composed with the isomorphism mate and composition isomorphisms.
Homology commutes with exact inverse image via `mapDerivedCategoryPlusHomologyFunctorIso`.
Global sections are invariant under inverse image along eA.hom: use the invertible
adjunction unit and `lowerStarCompGlobalSectionsIso`. Therefore the canonical factor
is invertible on global homology by step 1; every other factor is the functorial
image of an isomorphism. Their composite is invertible. This works in every integer
degree, for zero complexes and for empty total spaces, without a torsion hypothesis. -/
theorem isIso_strictHenselization_baseChange_modelGlobalHomology
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    (eA : Spec (.of A) ≅ strictHenselizationScheme s)
    {X₀ : Scheme.{u}} (p₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (.of A))
    (sq₀ : IsPullback p₀ f₀ f (eA.hom ≫ strictHenselizationStructuralMap s))
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (n : ℤ) :
    IsIso ((Sheaf.Γ (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((DerivedCategory.Plus.homologyFunctor _ n).map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₀.toCommSq).app K))) := by sorry

end AlgebraicGeometry.Etale
