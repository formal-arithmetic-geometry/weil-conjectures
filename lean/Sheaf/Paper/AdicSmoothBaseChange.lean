/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.IntrinsicCompletionCompleted
public import Sheaf.Paper.CompletedPullback
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
public import Sheaf.Paper.SbcCompletedOperations
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.RefinementCoefficientRealization
public import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf

import Sheaf.Paper.SbcFiniteExchangeCoefficientRealization
import Sheaf.Paper.PbcActualStrictPullback
import Sheaf.Paper.PbcActualRingedExchange
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.Paper.LevelwiseAdicTruncations
import Sheaf.AlgebraicGeometry.FiniteProetaleSmoothBaseChange
import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients

/-! # Adic smooth base change

Source: blueprint, sec-smooth-base-change/sk-rem-rest, order 1443;
Stacks Tags 0EYU, 099N, 099M and 09AL
(blueprint: sbc-thm-adic-smooth-base-change).

The exchange is the published completed adjunction mate. The conditional clause
retains all four finite outputs and a single interval for every level.

## Main definitions and statements

- `sbcAdicFiniteCohomology`: the canonical finite coefficient presentation of cohomology.
- `adicSmoothBaseChange`: invertibility and conditional constructible landing.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

private theorem evaluations_conservative
    {C : Type v} [Category.{w} C] [Abelian C] [HasDerivedCategory C]
    [HasDerivedCategory (ℕᵒᵖ ⥤ C)]
    {K L : DerivedCategory (ℕᵒᵖ ⥤ C)} (f : K ⟶ L)
    (hf : ∀ n : ℕᵒᵖ,
      IsIso ((((CategoryTheory.evaluation ℕᵒᵖ C).obj n).mapDerivedCategory).map f)) :
    IsIso f := by
  apply (DerivedCategory.isIso_iff _ f).2
  intro i
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro n
  have : IsIso (((DerivedCategory.homologyFunctor _ i).map f).app n) := by
    have := hf n
    exact (NatIso.isIso_map_iff
      (((CategoryTheory.evaluation ℕᵒᵖ C).obj n).mapDerivedCategoryHomologyFunctorIso i) f).2
        (by rw [Functor.comp_map]; infer_instance)
  exact this

/-- Canonical quotient reductions jointly detect isomorphisms of intrinsically complete
objects, with the coefficient universe independent of the site's Hom universe.
Source: Stacks 099M and 099Q; blueprint adic smooth base change, proof step 5
(blueprint: lem-weil-pbc-levelwise-isomorphism-cones).

Proof: form the canonical strict quotient tower. Its derived evaluation is the
actual quotient reduction followed by exact scalar restriction, so every evaluated map
is invertible. Exact evaluation commutes with cohomology, and a map of module diagrams
is invertible if all its components are. The homology criterion in the derived category
therefore makes the strict tower map invertible. Apply the strict completed pullback
functor for the identity morphism, which is this tower followed by tower pullback and
derived limit. The unit-normalized comparison with the completion reflector, restricted
to intrinsically complete objects, identifies this functor with completed identity
pullback. The recorded identity comparison identifies the latter with the full inclusion.
Naturality of both comparisons transfers invertibility back to the original map. This
works for different completeness representatives and generating lists, and also for the
zero ideal, the unit ideal when permitted by the datum, and the empty scheme. -/
private theorem pbcCompleteReduction_conservative
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {K L : PbcCompletedDerived X d} (v : K ⟶ L)
    (hK : PbcIsIntrinsicallyComplete X d K)
    (hL : PbcIsIntrinsicallyComplete X d L)
    (hv : ∀ n : ℕ, IsIso ((pbcCompletedReduction X d n).map v)) : IsIso v := by
  let P : ObjectProperty (PbcCompletedDerived X d) := PbcIsIntrinsicallyComplete X d
  let v' : (⟨K, hK⟩ : P.FullSubcategory) ⟶ ⟨L, hL⟩ := ObjectProperty.homMk v
  have ht : IsIso ((completedReductionTower X d).map v) := by
    apply evaluations_conservative
    intro n
    have : IsIso ((pbcCompletedReduction X d n.unop).map v) := hv n.unop
    have : IsIso (((reductionDerivedChange X (completedReductionProjection X d n.unop) ⋙
        reductionDerivedRestrict X (completedReductionProjection X d n.unop))).map v) :=
      by
        rw [Functor.comp_map]
        change IsIso ((reductionDerivedRestrict X _).map
          ((pbcCompletedReduction X d n.unop).map v))
        infer_instance
    exact (NatIso.isIso_map_iff (asIso (completedReductionEvaluation X d n.unop)) v).2 this
  have hs : IsIso ((P.ι ⋙ pbcActualStrictCompletedPull d (𝟙 X)).map v') := by
    change IsIso ((completedTowerRlim d X).map
      ((completedTowerPullback (𝟙 X) d).map ((completedReductionTower X d).map v)))
    infer_instance
  let e := (pbcActualCompletedPullback_tower d (𝟙 X)).exists.choose
  have hc : IsIso ((P.ι ⋙ pbcActualCompletedPull (𝟙 X) d).map v') :=
    (NatIso.isIso_map_iff e v').1 hs
  let eId := (pbcActualCompletedPullIdIso_exists d X).exists.choose
  exact (NatIso.isIso_map_iff eId v').1 hc

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

private noncomputable def fixedId
    (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R] :
    Sheaf.restrictScalars (ProEt.topology X) (RingHom.id R) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun F ↦ (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (Functor.isoWhiskerLeft F.obj (ModuleCat.restrictScalarsId R)))

private noncomputable def functionComparison
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    pbcFunctionRealization X d n ≅
      ProEtale.finiteCoefficientRealization X (ProEtale.PbcQuotient d n) ⋙
        SheafOfModules.restrictScalars
          (AdicCoefficients.finiteRingComparison X (ProEtale.PbcQuotient d n)).hom := by
  let R := ProEtale.PbcQuotient d n
  let r := (AdicCoefficients.finiteRingComparison X R).hom
  have hs : pbcFunctionScalars X d n ≫
      r.hom =
        (Functor.const X.ProEtᵒᵖ).map (RingCat.ofHom (RingHom.id R)) ≫
          ProEtale.finiteCoefficientScalarMap X R := by
    change ProEtale.finiteCoefficientScalarMap X R ≫
        (sheafToPresheaf _ _).map (AdicCoefficients.finiteRingComparison X R).inv ≫
        (sheafToPresheaf _ _).map (AdicCoefficients.finiteRingComparison X R).hom = _
    rw [← Functor.map_comp, Iso.inv_hom_id]
    rw [(sheafToPresheaf _ _).map_id]
    change _ ≫ 𝟙 _ = (Functor.const X.ProEtᵒᵖ).map (𝟙 (RingCat.of R)) ≫ _
    rw [(Functor.const X.ProEtᵒᵖ).map_id, Category.comp_id, Category.id_comp]
  let e := (pbcAssociatedRestriction_exists X R R _ _
    (pbcFunctionScalars X d n) (ProEtale.finiteCoefficientScalarMap X R)
    (RingHom.id R) r hs).exists.choose
  exact (Functor.isoWhiskerRight (fixedId X R).symm (pbcFunctionRealization X d n)) ≪≫ e

private theorem plus_of_map
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Faithful] (K : DerivedCategory C)
    (hK : DerivedCategory.TStructure.t.plus (F.mapDerivedCategory.obj K)) :
    DerivedCategory.TStructure.t.plus K := by
  obtain ⟨a, ha⟩ := hK
  refine ⟨a, (DerivedCategory.isGE_iff K a).2 ?_⟩
  intro i hi
  exact F.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    ((DerivedCategory.isGE_iff _ a).1 ha i hi)

/-- A common constructible cohomological interval for the canonical reductions supplies
both the uniform local models and the compatible retained origins of membership.
Source: Stacks 09AL, 09C1 and 099M; blueprint adic smooth base change, proof steps 6--8
(blueprint: sbc-thm-adic-smooth-base-change).

Proof: use the actual canonical reduction tower of J, whose evaluation isomorphisms,
normalizations and quotient cocycles are fixed by tensor balancing on one K-flat model.
The hypotheses are intrinsic constructibility in constant-to-function coordinates and
one interval for every quotient. Exact restriction along each coefficient isomorphism
reflects zero, so the stated cohomological bound is also a bound before restriction.
Normalized constructible local effectivity applied to this tower supplies its common
finite stratification, covering, bounded adic-lisse finite-type complexes and compatible
local reduction isomorphisms. Taking the identity level comparisons gives the uniform
reduction predicate, with precisely the canonical semilinear transition equations.
Its other conclusion supplies bounded constructible etale origins at every level.
Pass through the exact function realization equivalence to fixed-scalar coordinates.
These origins are bounded below. Pullback commutes with derived quotient tensor, and
exact faithful site comparison reflects cohomological vanishing. Consequently each
successive etale tensor is bounded below. Full faithfulness of bounded-below comparison
uniquely lifts the canonical normalization and its inverse; faithfulness gives their
inverse identities and all quotient cocycles. Package the adjacent lifts and their
compatibility equations as the retained witnessed tower. Transporting back by function
realization gives exactly the canonical reduction-normalization equation in the origin
predicate. Combining these two predicates with hJ proves the three membership clauses.
The empty scheme is handled by the local-effectivity convention for an empty stratum;
no finite Tor dimension of a quotient over an earlier quotient is assumed. -/
private theorem pbcConstructibleReduction_criterion
    (X : Scheme.{u}) [IsNoetherian X] {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (J : PbcCompletedDerived X d)
    (hJ : PbcIsIntrinsicallyComplete X d J)
    (a b : ℤ) (hab : a ≤ b)
    (hfinite : ∀ (n : ℕ) (i : ℤ),
      IsConstructibleProEtaleCoefficientModuleSheaf X (ProEtale.PbcQuotient d n)
        ((pbcRestrict (pbcLevelConstantComparison X d n).hom).obj
          ((DerivedCategory.homologyFunctor _ i).obj ((pbcCompletedReduction X d n).obj J))) ∧
      ((i < a ∨ b < i) → IsZero
        ((pbcRestrict (pbcLevelConstantComparison X d n).hom).obj
          ((DerivedCategory.homologyFunctor _ i).obj
            ((pbcCompletedReduction X d n).obj J))))) :
    PbcIsBoundedConstructibleComplete X d J := by
  classical
  have hvan (n : ℕ) (i : ℤ) (hi : i < a ∨ b < i) :
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((pbcCompletedReduction X d n).obj J)) := by
    let F := pbcRestrict (pbcLevelConstantComparison X d n).hom
    apply (IsZero.iff_id_eq_zero _).2
    have : F.Faithful := by
      constructor
      intro V W f g h
      apply (SheafOfModules.fullyFaithfulForget _).map_injective
      apply (PresheafOfModules.restrictScalars _).map_injective
      exact congrArg (fun q ↦ q.val) h
    apply F.map_injective
    rw [F.map_id, F.map_zero]
    exact ((hfinite n i).2 hi).eq_of_src _ _
  let M := pbcReductionAdicTower X d J
  obtain ⟨horigin, huniform⟩ := normalizedConstructibleTower_local_effectivity X d M
    (fun n i ↦ (hfinite n i).1) a b hab hvan
  refine ⟨hJ, ?_, ?_⟩
  · refine ⟨M, fun _ ↦ Iso.refl _, huniform, ?_⟩
    intro m n hnm
    dsimp only [Iso.refl_hom]
    rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
    exact Equiv.apply_symm_apply
      ((pbcDerivedScalarAdjunction (pbcAdicQuotient X d m n hnm)).homEquiv _ _) _
  · have hex (n : ℕ) : ∃ L : DerivedCategory
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n))),
        DerivedCategory.TStructure.t.plus L ∧
        Nonempty ((pbcDerivedFunctionRealization X d n).obj
          ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) X).mapDerivedCategory.obj L) ≅
          (pbcCompletedReduction X d n).obj J) := by
      obtain ⟨C, ⟨L, hL, ⟨eL⟩⟩, ⟨eC⟩⟩ := horigin n
      obtain ⟨c, z, _, hbound⟩ := hL.2
      refine ⟨L, ⟨c, (DerivedCategory.isGE_iff L c).2
        (fun i hi ↦ hbound i (Or.inl hi))⟩, ⟨?_⟩⟩
      let R := SheafOfModules.restrictScalars
        (AdicCoefficients.finiteRingComparison X (ProEtale.PbcQuotient d n)).hom
      let S := ProEtale.finiteCoefficientRingSheaf X (ProEtale.PbcQuotient d n)
      let T := X.adicLisseForget.obj
        (AdicCoefficients.coefficientRing X (ProEtale.PbcQuotient d n))
      let e : R ⋙ SheafOfModules.toSheaf.{u + 1} T ≅
          SheafOfModules.toSheaf.{u + 1} S := Iso.refl _
      have : PreservesFiniteLimits R := by
        have : PreservesFiniteLimits (R ⋙ SheafOfModules.toSheaf.{u + 1} T) :=
          preservesFiniteLimits_of_natIso e.symm
        exact preservesFiniteLimits_of_reflects_of_preserves R
          (SheafOfModules.toSheaf.{u + 1} T)
      have : PreservesFiniteColimits R := by
        have : ReflectsFiniteColimits (SheafOfModules.toSheaf.{u + 1} T) :=
          { reflects := fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
        have : PreservesFiniteColimits (R ⋙ SheafOfModules.toSheaf.{u + 1} T) :=
          preservesFiniteColimits_of_natIso e.symm
        exact preservesFiniteColimits_of_reflects_of_preserves R
          (SheafOfModules.toSheaf.{u + 1} T)
      let D : pbcDerivedFunctionRealization X d n ≅
          (ProEtale.finiteCoefficientRealization X
            (ProEtale.PbcQuotient d n)).mapDerivedCategory ⋙ R.mapDerivedCategory :=
        Functor.mapDerivedCategoryNatIso (functionComparison X d n) ≪≫
          Functor.mapDerivedCategoryCompIso _ _
      exact D.app _ ≪≫ R.mapDerivedCategory.mapIso
        ((Functor.mapDerivedCategoryCompIso _ _).symm.app L ≪≫ eL) ≪≫
          R.mapDerivedCategoryFactors.app C ≪≫ eC
    choose L hL q using hex
    let N (n : ℕ) := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) X).mapDerivedCategory.obj (L n)
    let alpha (n : ℕ) := (q n).some
    let theta (n : ℕ) : (ProEtale.pbcWitnessReduction X d n).obj (N (n + 1)) ≅ N n :=
      (pbcDerivedFunctionRealization X d n).preimageIso
        ((pbcFunctionReduction X d n).symm.app (N (n + 1)) ≪≫
          (pbcDerivedExtend (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))).mapIso
            (alpha (n + 1)) ≪≫
          pbcReductionNormalization (pbcAdicProjection X d (n + 1))
            (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection X d n)
            (pbcAdicProjection_comp X d (n + 1) n (Nat.le_succ n)) J ≪≫
          (alpha n).symm)
    have hN (n : ℕ) : DerivedCategory.TStructure.t.plus
        ((ProEtale.finiteCoefficientRealization X
          (ProEtale.PbcQuotient d n)).mapDerivedCategory.obj (N n)) := by
      exact DerivedCategory.TStructure.t.plus.prop_of_iso
        ((Functor.mapDerivedCategoryCompIso _ _).app (L n))
        ((ProEtale.finiteCoefficientComparison X
          (ProEtale.PbcQuotient d n)).mapDerivedCategoryPlus.obj ⟨L n, hL n⟩).property
    let W (n : ℕ) : ProEtale.EtaleOriginWitness X (ProEtale.PbcQuotient d n)
        ⟨_, hN n⟩ :=
      { L := ⟨L n, hL n⟩
        alpha := ObjectProperty.isoMk _ ((Functor.mapDerivedCategoryCompIso _ _).app (L n)) }
    have hb (n : ℕ) : ∃ beta :
        (ProEtale.pbcWitnessEtaleReduction X d n).obj (W (n + 1)).L.obj ≅ (W n).L.obj,
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) X).mapDerivedCategory.map beta.hom ≫
          (ProEtale.pbcFixedOriginAlpha X _ (N n) (hN n) (W n)).hom =
        (ProEtale.pbcComparisonReduction X
          (ProEtale.pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).inv.app (W (n + 1)).L.obj ≫
          (ProEtale.pbcWitnessReduction X d n).map
            (ProEtale.pbcFixedOriginAlpha X _ (N (n + 1)) (hN (n + 1)) (W (n + 1))).hom ≫
          (theta n).hom := by
      let C := (ProEtale.pbcWitnessEtaleReduction X d n).obj (W (n + 1)).L.obj
      let F := (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) X).mapDerivedCategory
      let e0 : F.obj C ≅ N n :=
        (ProEtale.pbcComparisonReduction X
          (ProEtale.pbcWitnessQuotientMap d
            (n + 1) n (Nat.le_succ n))).symm.app (W (n + 1)).L.obj ≪≫
          (ProEtale.pbcWitnessReduction X d n).mapIso
            (ProEtale.pbcFixedOriginAlpha X _ (N (n + 1)) (hN (n + 1)) (W (n + 1))) ≪≫
          theta n
      have hC : DerivedCategory.TStructure.t.plus C := by
        apply plus_of_map (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) X)
        apply plus_of_map (ProEtale.finiteCoefficientRealization X (ProEtale.PbcQuotient d n))
        exact DerivedCategory.TStructure.t.plus.prop_of_iso
          ((ProEtale.finiteCoefficientRealization X
            (ProEtale.PbcQuotient d n)).mapDerivedCategory.mapIso e0).symm (hN n)
      let e : F.obj C ≅ F.obj (W n).L.obj :=
        e0 ≪≫ (ProEtale.pbcFixedOriginAlpha X _ (N n) (hN n) (W n)).symm
      obtain ⟨f, hf⟩ :=
        (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
          C (W n).L.obj (W n).L.property).2 e.hom
      obtain ⟨g, hg⟩ :=
        (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
          (W n).L.obj C hC).2 e.inv
      change F.map f = e.hom at hf
      change F.map g = e.inv at hg
      have hfg : f ≫ g = 𝟙 C :=
        (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map C C hC).1 (by
          change F.map (f ≫ g) = F.map (𝟙 C)
          simp only [CategoryTheory.Functor.map_comp, hf, hg, Iso.hom_inv_id]
          exact (F.map_id _).symm)
      have hgf : g ≫ f = 𝟙 (W n).L.obj :=
        (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
          _ _ (W n).L.property).1 (by
          change F.map (g ≫ f) = F.map (𝟙 (W n).L.obj)
          simp only [CategoryTheory.Functor.map_comp, hf, hg, Iso.inv_hom_id]
          exact (F.map_id _).symm)
      refine ⟨⟨f, g, hfg, hgf⟩, ?_⟩
      change F.map f ≫ _ = _
      rw [hf]
      simp [e, e0]
    choose beta hbeta using hb
    refine ⟨⟨N, hN, W, theta, beta, hbeta⟩, alpha, ?_⟩
    intro n
    change (pbcDerivedFunctionRealization X d n).map (theta n).hom ≫ _ = _
    simp only [theta, CategoryTheory.Functor.preimageIso_hom,
      CategoryTheory.Functor.map_preimage, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Functor.mapIso_hom, Iso.inv_hom_id, Category.comp_id]
    rfl

end AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The finite smooth exchange is invertible in the actual quotient-ring presentation.
Source: Stacks 0EYU and 0F09; blueprint adic smooth base change, proof step 2
(blueprint: sbc-thm-finite-proetale-smooth-base-change).

Proof: put Lambda equal to the positive quotient. An etale origin L and its given
isomorphism identify the input with derived site inverse image followed by the canonical
function realization. The finite pro-etale smooth base-change theorem applies to L,
with the stated positive annihilator invertible on S. Restrict along the normalized
finite-ring presentation isomorphisms at all four corners. Their coefficient squares
commute since every map sends a constant section to that same section. The associated
module realizations are exact equivalences. The inverse-image comparisons preserve
tensor units, and their conjugate direct-image comparisons preserve the adjunction
units and counits. Thus expanding unit, square comparison and counit conjugates the
specified finite mate to the exchange in the finite theorem. Every conjugating map is
invertible; the finite theorem therefore proves invertibility of this very mate.
No boundedness of either exchange endpoint is used. -/
private theorem sbcFiniteSmoothExchange_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
    (sq : ChosenCartesianSquare h e f g)
    [IsNoetherian X] [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]
    [Smooth f] [QuasiCompact g] [QuasiSeparated g]
    (n N : ℕ)
    (hcoeff : Etale.IsSmoothBaseChangeCoefficients N
      (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) S)
    (J : DerivedCategory (pbcModules T
      ((pbcAdicRings T (pbcIntegralDatum l E)).obj (Opposite.op n))))
    (horigin : ∃ L : Etale.BoundedConstructibleDerivedCategory
        (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) T,
      Nonempty ((pbcDerivedFunctionRealization T (pbcIntegralDatum l E) n).obj
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ProEtale.PbcQuotient (pbcIntegralDatum l E) n))
          T).mapDerivedCategory.obj L.obj) ≅ J)) :
    IsIso (sbcFiniteExchangeApp l E sq n J) := by
  let Λ := ProEtale.PbcQuotient (pbcIntegralDatum l E) n
  let R := (ProEtale.finiteCoefficientRealization T Λ).mapDerivedCategory
  let F := pbcDerivedFunctionRealization T (pbcIntegralDatum l E) n
  let B := ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq.flip
  obtain ⟨L, ⟨α⟩⟩ := horigin
  let M := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategory.obj L.obj
  let K := (ProEtale.finiteCoefficientDerivedComparison T Λ).obj L.obj
  have hK : ProEtale.isBoundedConstructibleFiniteCoefficient T Λ K :=
    ⟨L.obj, ⟨fun i ↦ by
      obtain ⟨S, hS⟩ := L.property.1 i
      exact ⟨S, S.isConstructible_stratum, hS⟩, L.property.2⟩, ⟨Iso.refl _⟩⟩
  have hfinite := (ProEtale.isIso_finite_proetale_smooth_base_change Λ sq N hcoeff K hK).1
  have hfixed : IsIso (B.app (R.asEquivalence.inverse.obj K)) := by
    exact isIso_of_reflects_iso _
      (ProEtale.finiteCoefficientRealization X Λ).mapDerivedCategory
  let β : M ≅ R.asEquivalence.inverse.obj K :=
    R.asEquivalence.unitIso.app M ≪≫ R.asEquivalence.inverse.mapIso
      ((Functor.mapDerivedCategoryCompIso
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T)
        (ProEtale.finiteCoefficientRealization T Λ)).symm.app L.obj)
  have hM : IsIso (B.app M) := (NatTrans.isIso_app_iff_of_iso B β).2 hfixed
  let γ : M ≅ F.asEquivalence.inverse.obj J :=
    F.asEquivalence.unitIso.app M ≪≫ F.asEquivalence.inverse.mapIso α
  have hJ : IsIso (B.app (F.asEquivalence.inverse.obj J)) :=
    (NatTrans.isIso_app_iff_of_iso B γ).1 hM
  obtain ⟨δ⟩ := sbcFiniteExchange_coefficient_realization l E sq n J
  exact (Arrow.isIso_iff_isIso_of_isIso δ.hom).2 (by infer_instance)


/-- Cohomology of a finite output, restricted along the canonical constant-to-function
coefficient isomorphism. This changes the coefficient presentation only and introduces
no constructibility or etale-origin condition.
Source: blueprint order 1443, finite-output clause; Stacks 09AJ
(blueprint: sbc-thm-adic-smooth-base-change). -/
def sbcAdicFiniteCohomology (W : Scheme.{u}) (n : ℕ)
    (J : DerivedCategory (pbcModules W ((pbcAdicRings W (pbcIntegralDatum l E)).obj
      (op n)))) (i : ℤ) :
    pbcModules W (adicLisseConstantRing W (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)) :=
  (pbcRestrict (pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom).obj
    ((DerivedCategory.homologyFunctor _ i).obj J)

private theorem finiteCohomology_property_of_iso
    (W : Scheme.{u}) (n : ℕ)
    {J J' : DerivedCategory (pbcModules W
      ((pbcAdicRings W (pbcIntegralDatum l E)).obj (op n)))}
    (v : J ≅ J') (i a b : ℤ)
    (hJ' : IsConstructibleProEtaleCoefficientModuleSheaf W
        (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
        (sbcAdicFiniteCohomology l E W n J' i) ∧
      ((i < a ∨ b < i) → IsZero (sbcAdicFiniteCohomology l E W n J' i))) :
    IsConstructibleProEtaleCoefficientModuleSheaf W
        (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
        (sbcAdicFiniteCohomology l E W n J i) ∧
      ((i < a ∨ b < i) → IsZero (sbcAdicFiniteCohomology l E W n J i)) := by
  let z := (pbcRestrict (pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom).mapIso
    ((DerivedCategory.homologyFunctor _ i).mapIso v)
  constructor
  · obtain ⟨S, hS, hSc, hSl⟩ := hJ'.1
    refine ⟨S, hS, hSc, ?_⟩
    intro j
    obtain ⟨V, hV, hVl⟩ := hSl j
    refine ⟨V, hV, ?_⟩
    intro U f hf
    obtain ⟨M, hM, ⟨q⟩⟩ := hVl U f hf
    refine ⟨M, hM, ⟨?_⟩⟩
    exact (SheafOfModules.overFunctor _ U).mapIso
      ((proEtaleModuleInverseImage (S.immersion j)
        (adicLisseConstantRing W (ProEtale.PbcQuotient (pbcIntegralDatum l E) n))).mapIso z)
      ≪≫ q
  · intro hi
    exact (hJ'.2 hi).of_iso z

/-- Smooth base change for the actual completed adjunction-mate exchange, and
constructible landing under one uniform interval for the four finite systems.
Source: blueprint order 1443, sec-smooth-base-change/sk-rem-rest;
Stacks Tags 0EYU, 099N, 099M and 09AL
(blueprint: sbc-thm-adic-smooth-base-change).

Proof:
1. Membership gives intrinsic completeness. Reindex the positive quotient tower by
   n+1. Choose each assumed bounded constructible etale origin solely for applying
   the finite theorem; the integral exchange remains the specified canonical map.
2. Apply sbc-thm-finite-proetale-smooth-base-change at each finite quotient. Smoothness,
   qcqs, noetherianity and invertibility of its order give invertible finite exchange.
   Further uniformizer quotients are earlier levels, by canonical normalization.
3. Use prop-weil-pbc-direct-image-limits for completeness of both direct images and
   lemma-weil-pbc-completed-pullback-reduction for the two completed pullbacks.
   Apply lemma-weil-pbc-perfect-projection-formula to the perfect quotient on g and h.
   The canonical coefficient squares and ring-sheaf change adjunction identify these
   reductions with the four displayed finite operations after scalar restriction.
4. lem-sbc-completed-operations-linear-natural-exchange identifies the reduction of
   this very mate with finite exchange under those comparisons. Scalar restriction
   reflects isomorphisms, so each actual quotient reduction of the mate is invertible.
5. lem-weil-pbc-levelwise-isomorphism-cones detects invertibility between the two
   complete endpoints from these reductions. Both endpoints are over X.
6. Under the interval hypothesis their actual reductions have constructible cohomology
   in that same interval. The constant-completion quotient identification makes the
   cohomology comparisons quotient-linear: locally lift a quotient scalar to A_X,
   apply A_X-linearity, and use that the ideal power kills both cohomology sheaves.
   Normalized constructible local effectivity supplies the common stratified local
   bounded adic-lisse models for each endpoint's canonical tower.
7. Finite-ring constructible derived origin supplies bounded constructible etale
   origins of those endpoint reductions. K-flat tensor pullback and exact comparison
   inverse image identify successive reductions. Exactness and the sheaf unit reflect
   vanishing, so the etale tensors remain bounded below. Bounded-below comparison is
   fully faithful: uniquely lift the quotient normalization and its inverse. Applying
   comparison inverse image to the two composites gives the normalization cocycle;
   cancel the origin isomorphism and use faithfulness to get the witness cocycle and
   identity normalization.
8. Completeness, uniform local models and compatible origins give both membership
   witnesses in the integral constructible category. Fullness puts the same mate and
   its inverse in that category, giving the final IsIso assertion.
-/
theorem adicSmoothBaseChange
    {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
    (sq : ChosenCartesianSquare h e f g)
    [IsNoetherian X] [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]
    [Smooth f] [QuasiCompact g] [QuasiSeparated g]
    (_hT : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (_hl : IsUnit (l : Γ(S, ⊤)))
    (_horder : ∀ n : ℕ,
      IsUnit (Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) : Γ(S, ⊤)) ∧
      IsUnit (Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) : Γ(X, ⊤)) ∧
      IsUnit (Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) : Γ(T, ⊤)) ∧
      IsUnit (Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) : Γ(Y, ⊤)))
    (K : PbcIntegralConstructible l E T)
    (_horigin : ∀ n : ℕ,
      ∃ L : Etale.BoundedConstructibleDerivedCategory
          (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) T,
        Nonempty ((pbcDerivedFunctionRealization T (pbcIntegralDatum l E) n).obj
          ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1}
              (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)) T).mapDerivedCategory.obj L.obj) ≅
          (sbcReduction l E T n).obj K.obj)) :
    IsIso (sbcExchangeApp l E sq ((pbcConstructibleInclusion l E T).obj K)) ∧
    ((∃ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞)) →
      (∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ, ∀ i : ℤ,
        (IsConstructibleProEtaleCoefficientModuleSheaf S
          (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
          (sbcAdicFiniteCohomology l E S n
          ((sbcFinitePush l E g n).obj ((sbcReduction l E T n).obj K.obj)) i) ∧
        ((i < a ∨ b < i) → IsZero
          (sbcAdicFiniteCohomology l E S n
          ((sbcFinitePush l E g n).obj ((sbcReduction l E T n).obj K.obj)) i))) ∧
        (IsConstructibleProEtaleCoefficientModuleSheaf X
          (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
          (sbcAdicFiniteCohomology l E X n
          ((sbcFinitePull l E f n).obj
            ((sbcFinitePush l E g n).obj ((sbcReduction l E T n).obj K.obj))) i) ∧
        ((i < a ∨ b < i) → IsZero
          (sbcAdicFiniteCohomology l E X n
          ((sbcFinitePull l E f n).obj
            ((sbcFinitePush l E g n).obj ((sbcReduction l E T n).obj K.obj))) i))) ∧
        (IsConstructibleProEtaleCoefficientModuleSheaf Y
          (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
          (sbcAdicFiniteCohomology l E Y n
          ((sbcFinitePull l E e n).obj ((sbcReduction l E T n).obj K.obj)) i) ∧
        ((i < a ∨ b < i) → IsZero
          (sbcAdicFiniteCohomology l E Y n
          ((sbcFinitePull l E e n).obj ((sbcReduction l E T n).obj K.obj)) i))) ∧
        (IsConstructibleProEtaleCoefficientModuleSheaf X
          (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
          (sbcAdicFiniteCohomology l E X n
          ((sbcFinitePush l E h n).obj
            ((sbcFinitePull l E e n).obj ((sbcReduction l E T n).obj K.obj))) i) ∧
        ((i < a ∨ b < i) → IsZero
          (sbcAdicFiniteCohomology l E X n
          ((sbcFinitePush l E h n).obj
            ((sbcFinitePull l E e n).obj ((sbcReduction l E T n).obj K.obj))) i)))) →
      ∃ (hB : PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
          ((sbcPull l E f).obj ((sbcPush l E g).obj
            ((pbcConstructibleInclusion l E T).obj K))).obj)
        (hD : PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
          ((sbcPush l E h).obj ((sbcPull l E e).obj
            ((pbcConstructibleInclusion l E T).obj K))).obj),
        IsIso (ObjectProperty.homMk
          (P := PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E))
          (X := ⟨((sbcPull l E f).obj ((sbcPush l E g).obj
            ((pbcConstructibleInclusion l E T).obj K))).obj, hB⟩)
          (Y := ⟨((sbcPush l E h).obj ((sbcPull l E e).obj
            ((pbcConstructibleInclusion l E T).obj K))).obj, hD⟩)
          (sbcExchangeApp l E sq ((pbcConstructibleInclusion l E T).obj K)).hom)) := by
  let Kc := (pbcConstructibleInclusion l E T).obj K
  have hfinite (n : ℕ) :
      IsIso (sbcFiniteExchangeApp l E sq n ((sbcReduction l E T n).obj K.obj)) := by
    let Λ := ProEtale.PbcQuotient (pbcIntegralDatum l E) n
    let : Fintype Λ := Fintype.ofFinite Λ
    have hcoeff : Etale.IsSmoothBaseChangeCoefficients (Nat.card Λ) Λ S := by
      refine ⟨Nat.card_pos, inferInstance, ?_, (_horder n).1⟩
      simpa only [Nat.card_eq_fintype_card] using Nat.cast_card_eq_zero Λ
    exact sbcFiniteSmoothExchange_isIso l E sq n (Nat.card Λ) hcoeff _ (_horigin n)
  have hreduction (n : ℕ) :
      IsIso ((sbcReduction l E X n).map (sbcExchangeApp l E sq Kc).hom) := by
    let := (sbcReductionComparisons_isIso l E f n).1 ((sbcPush l E g).obj Kc)
    let := (sbcReductionComparisons_isIso l E g n).2 Kc
    let := (sbcReductionComparisons_isIso l E h n).2 ((sbcPull l E e).obj Kc)
    let := (sbcReductionComparisons_isIso l E e n).1 Kc
    have hfin : IsIso (sbcFiniteExchangeApp l E sq n
        ((sbcReduction l E T n).obj Kc.obj)) := hfinite n
    have heq := sbcCompletedOperations_linear_natural_exchange l E sq Kc n
    have : IsIso
        ((sbcReduction l E X n).map (sbcExchangeApp l E sq Kc).hom ≫
          sbcPushReduction l E h n ((sbcPull l E e).obj Kc) ≫
          (sbcFinitePush l E h n).map (sbcPullReduction l E e n Kc)) := by
      rw [heq]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (sbcPushReduction l E h n ((sbcPull l E e).obj Kc) ≫
        (sbcFinitePush l E h n).map (sbcPullReduction l E e n Kc))
  have hmate : IsIso (sbcExchangeApp l E sq Kc).hom :=
    pbcCompleteReduction_conservative X (pbcIntegralDatum l E) _
      ((sbcPull l E f).obj ((sbcPush l E g).obj Kc)).property
      ((sbcPush l E h).obj ((sbcPull l E e).obj Kc)).property hreduction
  have hcomplete : IsIso (sbcExchangeApp l E sq Kc) := by
    have : IsIso ((ObjectProperty.ι (IsPbcComplete l E X)).map
        (sbcExchangeApp l E sq Kc)) := hmate
    exact isIso_of_reflects_iso _ (ObjectProperty.ι (IsPbcComplete l E X))
  refine ⟨hcomplete, ?_⟩
  intro _hX hbounds
  obtain ⟨a, b, hab, hbounds⟩ := hbounds
  have hB : PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
      ((sbcPull l E f).obj ((sbcPush l E g).obj Kc)).obj := by
    apply pbcConstructibleReduction_criterion X (pbcIntegralDatum l E) _
      ((sbcPull l E f).obj ((sbcPush l E g).obj Kc)).property a b hab
    intro n i
    let := (sbcReductionComparisons_isIso l E f n).1 ((sbcPush l E g).obj Kc)
    let := (sbcReductionComparisons_isIso l E g n).2 Kc
    exact finiteCohomology_property_of_iso l E X n
      (asIso (sbcPullReduction l E f n ((sbcPush l E g).obj Kc) ≫
        (sbcFinitePull l E f n).map (sbcPushReduction l E g n Kc)))
      i a b (hbounds n i).2.1
  have hD : PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
      ((sbcPush l E h).obj ((sbcPull l E e).obj Kc)).obj := by
    apply pbcConstructibleReduction_criterion X (pbcIntegralDatum l E) _
      ((sbcPush l E h).obj ((sbcPull l E e).obj Kc)).property a b hab
    intro n i
    let := (sbcReductionComparisons_isIso l E h n).2 ((sbcPull l E e).obj Kc)
    let := (sbcReductionComparisons_isIso l E e n).1 Kc
    exact finiteCohomology_property_of_iso l E X n
      (asIso (sbcPushReduction l E h n ((sbcPull l E e).obj Kc) ≫
        (sbcFinitePush l E h n).map (sbcPullReduction l E e n Kc)))
      i a b (hbounds n i).2.2.2
  refine ⟨hB, hD, ?_⟩
  have : IsIso ((ObjectProperty.ι
      (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E))).map
        (ObjectProperty.homMk
          (P := PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E))
          (X := ⟨_, hB⟩) (Y := ⟨_, hD⟩) (sbcExchangeApp l E sq Kc).hom)) := hmate
  exact isIso_of_reflects_iso _
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)))

end WeilConjectures
