/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2 -/
module

public import Sheaf.AlgebraicGeometry.OverSquare

public import Sheaf.Paper.FiniteDiscreteDerivedCoefficientData
import Sheaf.CategoryTheory.ThreeStepAdjunctionComparison
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB

/-! # The specified exchange from coherent coefficient comparisons -/

@[expose] public section
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
private theorem reverse_step {C : Type*} [Category C]
    {A A' D D' : C} {a : A ⟶ A'} {d : D ⟶ D'}
    (p : A ≅ D) (q : A' ≅ D') (h : a ≫ q.hom = p.hom ≫ d) :
    d ≫ q.inv = p.inv ≫ a := by
  apply (p.eq_inv_comp).2
  rw [← Category.assoc, ← h, Category.assoc, q.hom_inv_id, Category.comp_id]

private def reverse_comparison {C : Type*} [Category C]
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : C}
    {a : A₀ ⟶ A₁} {b : A₁ ⟶ A₂} {c : A₂ ⟶ A₃}
    {d : B₀ ⟶ B₁} {e : B₁ ⟶ B₂} {f : B₂ ⟶ B₃}
    (h : FiniteDiscreteThreeStepComparison a b c d e f) :
    FiniteDiscreteThreeStepComparison d e f a b c where
  e0 := h.e0.symm
  e1 := h.e1.symm
  e2 := h.e2.symm
  e3 := h.e3.symm
  first := reverse_step h.e0 h.e1 h.first
  second := reverse_step h.e1 h.e2 h.second
  third := reverse_step h.e2 h.e3 h.third

private theorem transport_app {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (h : F = G) (K : C) :
    (eqToIso h).app K = eqToIso (congrArg (fun T : C ⥤ D ↦ T.obj K) h) := by
  subst h
  rfl

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
private lemma restricted_unit_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ U)) :
    ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ (h.asOver (Spec (.of k)))).unit.app K).hom =
      (derivedUpperStarLowerStarAdjunction Λ h).unit.app K.obj := by
  change (boundedConstructible _).ι.map
    ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ (h.asOver (Spec (.of k)))).unit.app K) = _
  rw [boundedConstructibleUpperStarLowerStarAdjunction,
    Adjunction.map_restrictFullyFaithful_unit_app]
  dsimp only [boundedConstructibleUpperStar, boundedConstructibleLowerStar,
    ObjectProperty.lift, Functor.comp_obj, ObjectProperty.ι_obj]
  simp [boundedConstructibleUpperStarCompatibility,
    boundedConstructibleLowerStarCompatibility, ObjectProperty.liftCompιIso,
    Iso.symm, Iso.refl, NatTrans.id_app]
-/

/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
private lemma restricted_counit_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ T)) :
    ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ (h.asOver (Spec (.of k)))).counit.app K).hom =
      (derivedUpperStarLowerStarAdjunction Λ h).counit.app K.obj := by
  change (boundedConstructible _).ι.map
    ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ (h.asOver (Spec (.of k)))).counit.app K) = _
  rw [boundedConstructibleUpperStarLowerStarAdjunction,
    Adjunction.map_restrictFullyFaithful_counit_app]
  dsimp only [boundedConstructibleUpperStar, boundedConstructibleLowerStar,
    ObjectProperty.lift, Functor.comp_obj, ObjectProperty.ι_obj]
  simp [boundedConstructibleUpperStarCompatibility,
    boundedConstructibleLowerStarCompatibility, ObjectProperty.liftCompιIso,
    Iso.symm, Iso.refl, NatTrans.id_app]
-/

private lemma restricted_comp_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]
    {V : Scheme.{u}} [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))] (j : U ⟶ V) [j.IsOver (Spec (.of k))]
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ V)) :
    ((boundedConstructibleUpperStarComp Λ ℓ (h.asOver (Spec (.of k))) (j.asOver (Spec (.of k)))).hom.app K).hom =
      (leftDerivedUpperStarComp Λ h j).hom.app K.obj := by
  change (boundedConstructible _).ι.map
    ((boundedConstructibleUpperStarComp Λ ℓ (h.asOver (Spec (.of k))) (j.asOver (Spec (.of k)))).hom.app K) = _
  simp only [ObjectProperty.ι_obj, Functor.comp_obj, boundedConstructibleUpperStarComp,
    Functor.FullyFaithful.preimageIso, Functor.whiskeringRight_obj_obj,
    boundedConstructibleUpperStarCompatibility, ObjectProperty.liftCompιIso, Iso.trans_hom,
    Iso.refl_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Iso.refl_inv, Functor.FullyFaithful.preimage_comp, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Category.assoc, Functor.isoWhiskerRight_inv, NatTrans.comp_app,
    Functor.FullyFaithful.whiskeringRight_preimage_app, NatTrans.id_app,
    ObjectProperty.lift_obj_obj, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, CategoryTheory.Functor.map_id,
    Functor.associator_hom_app, Category.comp_id,
    ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom]
  exact Category.id_comp ((leftDerivedUpperStarComp Λ h j).hom.app K.obj)

private lemma restricted_square_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (sq : CommSq g' f' f g)
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ Y)) :
    (boundedConstructible _).ι.mapIso
      ((boundedConstructiblePullbackSquareComparison Λ ℓ (sq.asOver (Spec (.of k)))).app K) =
      (coefficientAmbientSquare Λ sq).app K.obj := by
  have h₁ : (boundedConstructible _).ι.mapIso
      ((boundedConstructibleUpperStarComp Λ ℓ (f'.asOver (Spec (.of k))) (g.asOver (Spec (.of k)))).app K) =
      (leftDerivedUpperStarComp Λ f' g).app K.obj :=
    Iso.ext (restricted_comp_hom ℓ k Λ f' g K)
  have h₂ : (boundedConstructible _).ι.mapIso
      ((boundedConstructibleUpperStarComp Λ ℓ (g'.asOver (Spec (.of k))) (f.asOver (Spec (.of k)))).app K) =
      (leftDerivedUpperStarComp Λ g' f).app K.obj :=
    Iso.ext (restricted_comp_hom ℓ k Λ g' f K)
  rw [boundedConstructiblePullbackSquareComparison_app, coefficientAmbientSquare_app]
  simp only [Functor.mapIso_trans, Functor.mapIso_symm, h₁, h₂,
    transport_app, eqToIso_map]

private lemma restricted_square_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (sq : CommSq g' f' f g)
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ Y)) :
    ((boundedConstructiblePullbackSquareComparison Λ ℓ (sq.asOver (Spec (.of k)))).hom.app K).hom =
      (coefficientAmbientSquare Λ sq).hom.app K.obj := by
  exact congrArg Iso.hom (restricted_square_iso ℓ k Λ sq K)

private lemma unit_step_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ X)) :
    ((boundedConstructibleBaseChangeUnitStep Λ ℓ (f.asOver (Spec (.of k))) (g.asOver (Spec (.of k))) (f'.asOver (Spec (.of k)))).app K).hom =
      (coefficientDerivedAdjunction Λ f').unit.app
        ((coefficientDerivedUpperStar Λ g).obj
          ((coefficientDerivedLowerStar Λ f).obj K.obj)) := by
  sorry

private lemma square_step_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (sq : CommSq g' f' f g)
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ X)) :
    ((boundedConstructibleBaseChangeSquareStep Λ ℓ (sq.asOver (Spec (.of k)))).hom.app K).hom =
      (coefficientDerivedLowerStar Λ f').map
        ((coefficientAmbientSquare Λ sq).hom.app
          ((coefficientDerivedLowerStar Λ f).obj K.obj)) := by
  have hs : (boundedConstructibleBaseChangeSquareStep Λ ℓ (sq.asOver (Spec (.of k)))).app K =
      (boundedConstructibleLowerStar Λ ℓ (f'.asOver (Spec (.of k)))).mapIso
        ((boundedConstructiblePullbackSquareComparison Λ ℓ (sq.asOver (Spec (.of k)))).app
          ((boundedConstructibleLowerStar Λ ℓ (f.asOver (Spec (.of k)))).obj K)) := by
    simp only [boundedConstructibleBaseChangeSquareStep, Functor.squareTransport_app]
  have ht := congrArg (fun z ↦ ((boundedConstructible _).ι.mapIso z).hom) hs
  exact ht.trans (congrArg ((coefficientDerivedLowerStar Λ f').map)
    (restricted_square_hom ℓ k Λ sq ((boundedConstructibleLowerStar Λ ℓ (f.asOver (Spec (.of k)))).obj K)))

private lemma counit_step_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ X)) :
    ((boundedConstructibleBaseChangeCounitStep Λ ℓ (f.asOver (Spec (.of k))) (f'.asOver (Spec (.of k))) (g'.asOver (Spec (.of k)))).app K).hom =
      (coefficientDerivedLowerStar Λ f').map
        ((coefficientDerivedUpperStar Λ g').map
          ((coefficientDerivedAdjunction Λ f).counit.app K.obj)) := by
  sorry

/-- Coherent coefficient comparisons identify the three specified exchange factors.
Source: Mathlib adjunction restriction and mates; the specified exchange definitions
(blueprint: lem-weil-pbc-coefficient-exchange-from-comparisons).

Proof in words. The coefficient is the continuous-function condensed ring of the
finite discrete ring B, killed by ell. These hypotheses put the restricted direct
images in the prime-to-characteristic finite-coefficient setting.
The morphisms f and f-prime are qcqs: use the qcqs structure maps
and the separated targets over Spec k. Apply threeStepComparison to the two etale
and two internal derived adjunctions, with the four pullback isomorphisms and the
two direct-image isomorphisms supplied by P. Its hypotheses are exactly P.unit,
P.counit and P.square. The four vertex isomorphisms are the composites displayed
in that categorical theorem; take their inverses to orient the comparison here.

For a bounded constructible realized object N, fully faithful adjunction restriction
identifies the underlying restricted unit and counit with the ambient unit and
counit. The inclusion compatibility isomorphisms are identities, so the restriction
formulas simplify using map_id. Likewise the underlying restricted pullback
composition isomorphism is leftDerivedUpperStarComp. Inclusion preserves the
composition, inverse, and equality-transport isomorphisms, so the restricted square
has underlying coefficientAmbientSquare. The component formulas for whiskering,
unitors and squareTransport now identify the three specified restricted factors
with the three ambient factors, and the etale component lemmas identify the other
three factors. Substitute these six component identities in the categorical
comparison. Finally apply boundedConstructibleBaseChange_eq_unit_square_counit,
project to underlying morphisms, and use Etale.baseChange_app followed by map_comp
to supply the two required total-arrow factorizations. None of these steps asserts
that exchange is invertible, or requires a Cartesian square or properness. Empty
schemes and zero objects are included. -/
theorem coefficientComparisonData_exchangeSteps [DiscreteTopology B] [Finite B]
    (hB : (ℓ : B) = 0) (sq : CommSq g' f' f g)
    (F : ∀ T : Scheme.{u}, FiniteDiscreteEtalePlus B T ⥤
      DerivedCategory (FiniteDiscreteInternalModules B T))
    (P : CoefficientComparisonData B (Profinite.continuousMapRingObj B) F) :
    finiteDiscreteExchangeSteps B ℓ k sq (F X) (F Y') := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
