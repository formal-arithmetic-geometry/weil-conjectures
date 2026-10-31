/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TraceFormulaCoefficientConventions
public import WeilConjectures.AlgebraicGeometry.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtaleExtensionZeroComparison

/-!
# Explicit etale-origin witnesses under pullback and open extension

Source: literature/blueprint/latest/blueprint/sec-trace-formula/
sk-thm-tf-coefficient-morphism-formula/lem-trf-compactification-graph-operator.proof.md,
step (3), first sentence; Stacks Tags 015F, 099R and 03DJ
(blueprint: lem-trf-witnessed-open-pullback).

The comparison maps retain their termwise-localization normalization. The witness records
retain both their antecedents and their isomorphisms. All objects lie in the cohomologically
bounded-below categories, with no condition on an arbitrary representing complex.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures

/-- The two natural derived comparisons and the three specified transported witnesses.
The normalization fields identify the comparisons with the localization of the actual sheaf
comparisons. The `HEq` fields express equality of isomorphisms whose antecedents have already
been identified by the preceding complex fields; no arbitrary replacement witness is allowed.
Source: blueprint, compactification graph operator, proof (3), first sentence, with its
pullback and open-extension refinement; Stacks Tags 015F, 099R and 03DJ
(blueprint: lem-trf-witnessed-open-pullback). -/
structure WitnessedOpenPullbackData (A : Type (u + 1)) [CommRing A]
    {U X V Y : Scheme.{u}} (f : U ⟶ X) (j : X ⟶ Y) (i : U ⟶ V)
    [IsOpenImmersion j] [IsOpenImmersion i]
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (w : Scheme.FixedEtaleOriginWitness X A K) where
  /-- The natural comparison κ on the bounded-below source. -/
  pullbackComparison :
    DerivedCategory.Plus.ι ⋙ (Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory ≅
      DerivedCategory.Plus.ι ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
  /-- κ is precisely the termwise comparison descended through localization. -/
  pullback_normalization : pullbackComparison =
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      ((Functor.mapDerivedCategoryCompIso
          (Etale.upperStar (ModuleCat.{u + 1} A) f)
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) U)).symm ≪≫
        @Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _ _
          (Etale.upperStar (ModuleCat.{u + 1} A) f ⋙
            ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) U)
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X ⋙
            ProEtale.upperStar (ModuleCat.{u + 1} A) f)
          inferInstance inferInstance
          (comp_preservesFiniteLimits _ _) (comp_preservesFiniteColimits _ _)
          (comp_preservesFiniteLimits _ _) (comp_preservesFiniteColimits _ _)
          (ProEtale.supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) f) ≪≫
        Functor.mapDerivedCategoryCompIso
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X)
          (ProEtale.upperStar (ModuleCat.{u + 1} A) f))
  /-- The natural comparison δ for j. -/
  jComparison :
    DerivedCategory.Plus.ι ⋙
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ≅
      DerivedCategory.Plus.ι ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ⋙
        (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory
  /-- δ for j has the prescribed termwise-localization normalization. -/
  j_normalization : jComparison =
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      ((Functor.mapDerivedCategoryCompIso
          (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j)
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y)).symm ≪≫
        @Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _ _
          (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j ⋙
            ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y)
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X ⋙
            ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j)
          inferInstance inferInstance
          (comp_preservesFiniteLimits _ _) (comp_preservesFiniteColimits _ _)
          (comp_preservesFiniteLimits _ _) (comp_preservesFiniteColimits _ _)
          (ProEtale.openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) j) ≪≫
        Functor.mapDerivedCategoryCompIso
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X)
          (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j))
  /-- The natural comparison δ for i. -/
  iComparison :
    DerivedCategory.Plus.ι ⋙
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) i).mapDerivedCategory ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategory ≅
      DerivedCategory.Plus.ι ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory ⋙
        (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) i).mapDerivedCategory
  /-- δ for i has the prescribed termwise-localization normalization. -/
  i_normalization : iComparison =
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      ((Functor.mapDerivedCategoryCompIso
          (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) i)
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) V)).symm ≪≫
        @Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _ _
          (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) i ⋙
            ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) V)
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) U ⋙
            ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) i)
          inferInstance inferInstance
          (comp_preservesFiniteLimits _ _) (comp_preservesFiniteColimits _ _)
          (comp_preservesFiniteLimits _ _) (comp_preservesFiniteColimits _ _)
          (ProEtale.openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) i) ≪≫
        Functor.mapDerivedCategoryCompIso
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) U)
          (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) i))
  /-- The retained witness for M = Lf* K. -/
  pulled : Scheme.FixedEtaleOriginWitness U A
    ((ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus.obj K)
  /-- Its antecedent is exactly L_f = f_et^{-1} L. -/
  pulled_complex : pulled.complex =
    (Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus.obj w.complex
  /-- Its isomorphism is exactly (Lf* α) after κ. -/
  pulled_iso : HEq pulled.iso
    (pullbackComparison.app w.complex ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.mapIso w.iso)
  /-- The retained witness for j_! K. -/
  extended : Scheme.FixedEtaleOriginWitness Y A
    ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus.obj K)
  /-- Its antecedent is exactly j_et,! L. -/
  extended_complex : extended.complex =
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus.obj
      w.complex
  /-- Its isomorphism is exactly j_! α after δ_j. -/
  extended_iso : HEq extended.iso
    (jComparison.app w.complex ≪≫
      (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.mapIso
        w.iso)
  /-- The retained witness for i_! M. -/
  pulledExtended : Scheme.FixedEtaleOriginWitness V A
    ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus.obj
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus.obj K))
  /-- Its antecedent is exactly i_et,! L_f. -/
  pulledExtended_complex : pulledExtended.complex =
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus.obj
      ((Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus.obj w.complex)
  /-- Its isomorphism is exactly i_! α_f after δ_i. -/
  pulledExtended_iso : HEq pulledExtended.iso
    (iComparison.app pulled.complex ≪≫
      (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) i).mapDerivedCategory.mapIso
        pulled.iso)

private theorem witnessed_open_pullback_aux (A : Type (u + 1)) [CommRing A]
    {U X V Y : Scheme.{u}} (f : U ⟶ X) (j : X ⟶ Y) (i : U ⟶ V)
    [IsOpenImmersion j] [IsOpenImmersion i]
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (w : Scheme.FixedEtaleOriginWitness X A K) :
    Nonempty (WitnessedOpenPullbackData A f j i K w) := by
  let κ :=
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      ((Functor.mapDerivedCategoryCompIso
          (Etale.upperStar (ModuleCat.{u + 1} A) f)
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) U)).symm ≪≫
        @Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _ _
          (Etale.upperStar (ModuleCat.{u + 1} A) f ⋙
            ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) U)
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X ⋙
            ProEtale.upperStar (ModuleCat.{u + 1} A) f)
          inferInstance inferInstance
          (comp_preservesFiniteLimits _ _) (comp_preservesFiniteColimits _ _)
          (comp_preservesFiniteLimits _ _) (comp_preservesFiniteColimits _ _)
          (ProEtale.supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) f) ≪≫
        Functor.mapDerivedCategoryCompIso
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X)
          (ProEtale.upperStar (ModuleCat.{u + 1} A) f))
  let δj :=
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      ((Functor.mapDerivedCategoryCompIso
          (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j)
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y)).symm ≪≫
        @Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _ _
          (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j ⋙
            ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y)
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X ⋙
            ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j)
          inferInstance inferInstance
          (comp_preservesFiniteLimits _ _) (comp_preservesFiniteColimits _ _)
          (comp_preservesFiniteLimits _ _) (comp_preservesFiniteColimits _ _)
          (ProEtale.openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) j) ≪≫
        Functor.mapDerivedCategoryCompIso
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X)
          (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j))
  let δi :=
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      ((Functor.mapDerivedCategoryCompIso
          (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) i)
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) V)).symm ≪≫
        @Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _ _
          (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) i ⋙
            ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) V)
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) U ⋙
            ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) i)
          inferInstance inferInstance
          (comp_preservesFiniteLimits _ _) (comp_preservesFiniteColimits _ _)
          (comp_preservesFiniteLimits _ _) (comp_preservesFiniteColimits _ _)
          (ProEtale.openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) i) ≪≫
        Functor.mapDerivedCategoryCompIso
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) U)
          (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) i))
  let pulled : Scheme.FixedEtaleOriginWitness U A
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus.obj K) :=
    { complex := (Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus.obj
        w.complex
      iso := κ.app w.complex ≪≫
        (ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.mapIso w.iso }
  let extended : Scheme.FixedEtaleOriginWitness Y A
      ((ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus.obj K) :=
    { complex := (Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus.obj w.complex
      iso := δj.app w.complex ≪≫
        (ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} A) j).mapDerivedCategory.mapIso w.iso }
  let pulledExtended : Scheme.FixedEtaleOriginWitness V A
      ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus.obj
        ((ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus.obj K)) :=
    { complex := (Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus.obj pulled.complex
      iso := δi.app pulled.complex ≪≫
        (ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} A) i).mapDerivedCategory.mapIso pulled.iso }
  exact ⟨{
    pullbackComparison := κ
    pullback_normalization := rfl
    jComparison := δj
    j_normalization := rfl
    iComparison := δi
    i_normalization := rfl
    pulled := pulled
    pulled_complex := rfl
    pulled_iso := HEq.rfl
    extended := extended
    extended_complex := rfl
    extended_iso := HEq.rfl
    pulledExtended := pulledExtended
    pulledExtended_complex := rfl
    pulledExtended_iso := HEq.rfl }⟩

/-- Derived pullback and the two open extensions transport the specified etale-origin pair.
Source: literature/blueprint/latest/blueprint/sec-trace-formula/
sk-thm-tf-coefficient-morphism-formula/lem-trf-compactification-graph-operator.proof.md,
step (3), first sentence; Stacks Tags 015F, 099R and 03DJ
(blueprint: lem-trf-witnessed-open-pullback).

Proof: (1) The published fixed-scalar etale, pro-etale and comparison inverse images are
exact, as are both open extensions. (2) Apply each exact functor degreewise. Its induced
functor on the localization preserves the same cohomological lower bounds, so restricts
to D+. (3) Apply the canonical sheaf pullback comparison in each degree. Naturality for
the differentials gives a chain isomorphism. Descend it uniquely through localization,
conjugating by the two composition factorization isomorphisms. This gives κ, with the
normalization in the record, independently of representatives. (4) Apply the identical
construction to the canonical open-extension sheaf comparison, once for j and once for i,
to get δ_j and δ_i. (5) Retain f_et^{-1} L and compose κ_L with Lf* α. Its inverse is
κ_L^{-1} after Lf*(α^{-1}). (6) Retain j_et,! L and compose δ_j,L with j_! α.
(7) Retain i_et,! L_f and compose δ_i,L_f with i_! α_f. These are the displayed witness
pairs; their inverses are the reverse composites of the inverse isomorphisms. Exactness
retains a common cohomological lower bound for all the objects. All normalization,
antecedent and heterogeneous isomorphism equalities follow from these explicit choices.
-/
theorem witnessed_open_pullback (T : TraceFormulaCoefficientConventions.{u})
    (U X V Y : Over (Spec (CommRingCat.of T.datum.k)))
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : U ⟶ X) (j : X ⟶ Y) (i : U ⟶ V)
    [IsOpenImmersion j.left] [IsOpenImmersion i.left]
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X.left)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing))))
    (w : Scheme.FixedEtaleOriginWitness X.left (ULift.{u + 1, u} T.coefficientRing) K) :
    Nonempty (WitnessedOpenPullbackData (ULift.{u + 1, u} T.coefficientRing)
      f.left j.left i.left K w) := by
  exact witnessed_open_pullback_aux _ f.left j.left i.left K w

end WeilConjectures
