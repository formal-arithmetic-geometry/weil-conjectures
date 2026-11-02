/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SupportedHomAdjunctionClass
import WeilConjectures.AlgebraicGeometry.SupportedHomPairAdjunctionCocycle
import all WeilConjectures.AlgebraicGeometry.Supported.SupportedHomPullback

/-! # Agreement of the two cocycle-normalized supported-Hom comparisons

Source: latest blueprint, `lem-pur-supported-hom.proof.md`, derived closed adjunction
(blueprint: lem-pur-supported-hom-pair-adjunction-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A comparison normalized on the unbounded derived supported-adjunction model agrees
with every normalized pair identification, after the specified coefficient and
bounded-below derived comparisons.
Source: Milne, Etale Cohomology, Theorem 9.4 and Example 9.5; the supported-Hom
identification in `lem-pur-gysin-structure.proof.md`
(blueprint: lem-pur-supported-hom-pair-adjunction-comparison).

Proof:
1. On a bounded-below complex of injectives, every supported cohomology class lifts
   through the homology projection to a cycle. The ordinary evaluation isomorphism
   supplies its unique Hom cocycle. Thus the normalization determines the comparison
   on every such class.
2. Transport the coefficient object along lowerStar.mapIso(comparisonUpperStarUnitIso).
   The constant restriction of proEtaleSupportHomPair already contains the inverse
   of this comparison. Their composite cancels. The evaluation equation for the
   supported adjunction therefore identifies its adjoint section with the section
   obtained by evaluating the pair's actual constant restriction on one.
3. The D+/unbounded right-derived compatibility is characterized by its derived-unit
   equation. Applying H^a to that equation identifies supportSequenceModelIso with
   supportedHomCycleClass. Inserting the same cycle in the two normalization formulas
   gives the asserted equality, including the source single-object comparison.
4. Choose a bounded-below injective representative of arbitrary K. Both comparisons
   are natural in K, as are the coefficient-source and derived compatibility maps.
   Postcomposition with the shifted inverse resolution isomorphism transports the
   equality to K. This proves the result for every integer degree and every class,
   including zero classes and empty support. -/
theorem supportedHomPairAdjunctionComparison
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]
    (a : ℤ)
    (χ : ProEtale.supportedHomCohomologyFunctor P.Coefficient i a ≅
      ProEtale.supportedHomMorphismFunctor P.Coefficient i a)
    (hχ : ProEtale.SupportedHomEvaluationNormalization P.Coefficient i a χ)
    (chi : (proEtaleSupportHomPair P i).Identification)
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (x : (proEtaleSupportHomPair P i).group K a) :
    chi.chi K a x =
      (DerivedCategory.singleFunctor
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) 0).map
        (supportedHomPairCoefficientIso P i).hom ≫
      χ.hom.app K ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) a).map
        ((ProEtale.supportSections i P.Coefficient).rightDerivedFunctorPlusCompatibility.hom.app K)
          x) := by
  let S := proEtaleSupportHomPair P i
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) a
  let e := (ProEtale.supportSections i P.Coefficient).rightDerivedFunctorPlusCompatibility
  let z := (DerivedCategory.singleFunctor
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) 0).map
      (supportedHomPairCoefficientIso P i).hom
  let rhs (L : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
      (y : S.group L a) := z ≫ χ.hom.app L (H.map (e.hom.app L) y)
  have hnat {L M : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))}
      (v : L ⟶ M) (y : S.group L a) :
      rhs M ((Sheaf.supportHypercohomologyFunctor S.topology
        (ModuleCat.{u + 1} P.Coefficient) S.restriction a).map v y) =
        rhs L y ≫ (DerivedCategory.Plus.ι.map v)⟦a⟧' := by
    have he := congrArg H.map (e.hom.naturality v)
    have hy := ConcreteCategory.congr_hom he y
    simp only [Functor.map_comp, ModuleCat.comp_apply] at hy
    have hχn := ConcreteCategory.congr_hom (χ.hom.naturality v) (H.map (e.hom.app L) y)
    change χ.hom.app M
        ((ProEtale.supportedHomCohomologyFunctor P.Coefficient i a).map v
          (H.map (e.hom.app L) y)) =
      χ.hom.app L (H.map (e.hom.app L) y) ≫ (DerivedCategory.Plus.ι.map v)⟦a⟧' at hχn
    dsimp only [rhs]
    erw [hy, hχn, Category.assoc]
  obtain ⟨N⟩ := (supportHomNormalizedPairs P i).2
  have hQ (I : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
      [∀ n : ℤ, Injective (I.obj.X n)] (y : S.group (DerivedCategory.Plus.Q.obj I) a) :
      chi.chi _ a y = rhs _ y := by
    let E := Sheaf.supportSequenceModelIso S.topology (ModuleCat.{u + 1} P.Coefficient)
      S.sections I (DerivedCategory.Plus.Q.obj I) (Iso.refl _) a
    obtain ⟨s, hs⟩ := (ModuleCat.epi_iff_surjective
      ((S.complex I).homologyπ a)).mp inferInstance (E.inv y)
    have hx : S.cycleClass I a s = y := by
      change E.hom ((S.complex I).homologyπ a s) = y
      rw [hs]
      exact ConcreteCategory.congr_hom E.inv_hom_id y
    obtain ⟨f, ⟨hf, ⟨hdf, _⟩⟩, _⟩ := N.cocycle I I (𝟙 I) a s
    have heval : kernel.ι ((I.obj.X a).obj.map S.restriction.op)
        ((S.complex I).iCycles a s) =
        ((constantSheafAdj S.topology (ModuleCat.{u + 1} P.Coefficient)
          S.isTerminal).homEquiv _ _ (S.constantRestriction ≫ f)) 1 := by
      rw [← hf]
      exact N.evaluation _ f
    rw [← hx, chi.normalization I a f hdf s heval]
    exact (supportedHomPairAdjunctionCocycle P i a χ hχ I f hdf s heval).symm
  obtain ⟨m, hm⟩ := K.2
  have : K.IsGE m := (K.isGE_ι_obj_iff m).mp hm
  obtain ⟨J, _, ⟨r⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K m
  let I := (InjectiveObject.ι
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))).mapCochainComplexPlus.obj J
  have hi (n : ℤ) : Injective (I.obj.X n) := (J.obj.X n).2
  change chi.chi K a x = rhs K x
  apply (cancel_mono ((DerivedCategory.Plus.ι.map r.inv)⟦a⟧')).mp
  rw [← chi.naturality, ← hnat]
  exact hQ I _

end AlgebraicGeometry
