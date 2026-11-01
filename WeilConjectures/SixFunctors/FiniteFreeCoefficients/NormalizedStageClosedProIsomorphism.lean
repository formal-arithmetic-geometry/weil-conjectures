/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.NormalizedStageComparisonObligations
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageClosedEtaleIsomorphism
import all WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageFiniteRingFoundations
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOrigin

/-! Pro-etale closed stage comparison helper.

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraph 2.
(blueprint: new-lem-sf-normalized-stage-closed-pro-isomorphism).

The helper isolates the pro-etale transport.  Its proof uses the constructible finite-Tor etale
origin of the ctf predicate, reflection of the Tor interval, the comparison unit and counit,
invertibility of the ordinary closed mate at `Rν_* M`, and the three factors in
`Sites.proClosedMap`. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.FiniteCoefficientAdjoints
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.pbcFixedScalarExtension
  AlgebraicGeometry.ProEtale.pbcFixedScalarExtensionComp
  AlgebraicGeometry.ProEtale.pbcComparisonReduction
  _root_.DerivedCategory.monoidalClosed
  _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.Etale.derivedTensor AlgebraicGeometry.Etale.derivedHom
  AlgebraicGeometry.ProEtale.derivedHom

private theorem closed_pro_rnu_ctf
    {A : Type (u + 1)} [CommRing A] [Finite A] (X : Scheme.{u})
    (K : Sites.D true A X) (hK : Sites.Ctf true A X K) :
    Ctf A X ((Sites.rnu A X).obj K) := by
  obtain ⟨⟨K', hbc, ⟨e⟩⟩, a, b, ht⟩ := hK
  have ht' := (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b K').1
    ((ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) X a b).prop_of_iso
      e.symm ht)
  have hu := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} A) X K' hbc.1.1
  let e' : K' ≅ (Sites.rnu A X).obj K :=
    (@asIso _ _ _ _
      ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) X).unit.app K') hu) ≪≫
        (Sites.rnu A X).mapIso e
  apply (ctf_iff_source A X _).2
  exact (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X).prop_of_iso
    e' ⟨hbc, a, b, ht'⟩

/--
The proof unpacks the etale origin `ν_A K ≅ M` of the pro-etale ctf object `M`, reflects its Tor
interval, and identifies `K` with `N = Rν_A M` by the invertible comparison unit, so `N` is
ordinary ctf. Scalar extension of `N` stays ctf (finite-ring foundations), so the comparison unit
there is invertible; the comparison counit at `M` is invertible since `M` has etale origin; hence
`rnuScalar`, expanded by `Adjunction.homEquiv_unit`, is invertible. The ordinary closed comparison
at `N` is invertible, so all three factors of `Sites.proClosedMap` are, and so is their composite.
(blueprint: new-lem-sf-normalized-stage-closed-pro-isomorphism)
-/
theorem normalized_stage_closed_pro_isomorphism
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    (Z : Scheme.{u}) [Z.Over (Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    (i : Z ⟶ X) [IsClosedImmersion i]
    [i.IsOver (Spec (.of D.k))]
    {s t : Stage l E} (a : Arrow s t)
    (M : Sites.D true s.ring X) :
    Sites.Ctf true s.ring X M → IsIso (Sites.stageClosedMap true a i M) := by
  intro hM
  have hr := closed_pro_rnu_ctf X M hM
  have hs := (finite_ring_scalar_direct_foundations D a.ringMap X X (𝟙 X)).1 false
    ((Sites.rnu s.ring X).obj M) hr
  have hunit := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} t.ring) X
    ((Sites.scalar false a.ringMap X).obj ((Sites.rnu s.ring X).obj M))
    ((ctf_iff_source t.ring X _).1 hs).1.1.1
  have hcounit := (ProEtale.DerivedCategory.plusEtaleOrigin_iff M).1
    (ProEtale.DerivedCategory.constructibleFiniteTor.plusEtaleOrigin hM) |>.2
  have hrscalar : IsIso (Sites.rnuScalar a.ringMap X M) := by
    rw [Sites.rnuScalar, Adjunction.homEquiv_unit]
    infer_instance
  have hclosed := normalized_stage_closed_etale_isomorphism D l hl E X Z i a
    ((Sites.rnu s.ring X).obj M) hr
  change IsIso (Sites.proClosedMap a.ringMap i M)
  dsimp only [Sites.proClosedMap]
  change IsIso (closedMap a.ringMap i ((Sites.rnu s.ring X).obj M)) at hclosed
  infer_instance

end WeilConjectures.FiniteFreeCoefficients
