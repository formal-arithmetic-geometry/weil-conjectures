/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerShriekData
import WeilConjectures.AlgebraicGeometry.SmoothPurityStrictCompactificationComparisonRealization
import WeilConjectures.AlgebraicGeometry.SmoothPurityFiniteLevelProjectionCriterion
import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerLocalization
import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerExchange

/-! # Compact-support laws on varying-coefficient towers

Source: blueprint operations proof (1)--(3)
(blueprint: det-sp-tower-shriek-levels).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor HasDerivedCategory.standard
  Padic Padic.coefficientExtensionIntegers
  SheafOfModules.OpenTensorNormalization.finiteTensor


universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem isIso_of_comp_eq {C : Type*} [Category C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] (h : X ⟶ Z) (hh : IsIso h)
    (w : f ≫ g = h) : IsIso f := by
  have := hh
  have : IsIso (f ≫ g) := by rw [w]; infer_instance
  exact IsIso.of_isIso_comp_right f g

private theorem tower_detects (b : Base l E) (T : Scheme.{u})
    {K L : D l E T} (v : K ⟶ L) :
    IsIso v ↔ ∀ n : ℕ, IsIso ((Ev l E T n).map v) := by
  constructor
  · intro hv n
    exact Functor.map_isIso (Ev l E T n) v
  · exact (b.calculus T).detects v

private theorem tower_bounded (b : Base l E) (o : Operations l E b)
    (h : ∀ T : Scheme.{u}, EnoughInjectives (S l E T))
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (C : DerivedCategory.Plus (S l E X)) :
    ∃ m : ℤ, ((F l E b o c).obj C.obj).IsGE m := by
  let _ := h c.Z
  let C' := (o.openOp c.i).extension.mapDerivedCategoryPlus.obj C
  let P := (o.geometry c.g).push.rightDerivedFunctorPlus.obj C'
  obtain ⟨m, hm⟩ := P.property
  have : (((o.geometry c.g).push.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).obj
      C').IsGE m := hm
  refine ⟨m, ?_⟩
  exact DerivedCategory.TStructure.t.isGE_of_iso
    ((o.geometry c.g).push.rightDerivedFunctorPlusCompatibility.app C') m

/-- Compact-support operations and comparisons on the actual varying-ring towers.
All comparison data are fixed before the finite-level hypotheses of Laws are tested.
The ordinary unbounded tensor and its quotient transitions, including tensor with any
specified Tate-twist tower, are those of Base.calculus, with its tensorEvaluation and
reduction_cocycle, not a completed tensor. Source: blueprint clauses (1)--(3)
(blueprint: det-sp-tower-shriek-levels).

Proof:
1. Identify the two strict semilinear system presentations sectionwise using
   det-sp-coefficient-towers-abelian. The existing semilinear-derived-sections calculus
   supplies the ordinary unbounded K-flat tensor, inverse image, direct image and their
   coherences, including the quotient-transition mates and normalized adjunctions.
2. Apply exact open extension termwise. The bounded-below injective-components comparison
   gives Fcomparison, naturally, and preserves a lower cohomological bound.
3. Construct projection as the proper counit transpose followed by the open tensor mate;
   construct exchange as the proper square mate followed by the open square mate. These
   are actual maps of derived towers. Their evaluations are the identical finite mate
   words, since the generic calculus preserves units, counits, tensor and composition.
4. Finite projection invertibility applies in the finite-field setting to both bounded
   constructible finite-Tor inputs. Finite base change applies with arbitrary base map
   to every specified origin witness; no witness transition compatibility is needed.
5. For an actual derived map, a cone with zero evaluations has zero cohomology at every
   level. Componentwise kernels and cokernels make each cohomology tower zero. The cone
   criterion therefore proves unbounded joint conservativity and hence both iso claims.
6. On one bounded-below strict representative, apply the ringed open--closed exact
   counit--unit sequence in each degree. Naturality and compatibility with restriction
   of scalars make one short exact sequence of tower complexes. Its SES triangle is
   distinguished. Exact triangulated evaluation preserves that triangle and its boundary.
   Closed immersion direct image and open extension are exact, so their operations here
   are termwise. Tensor evaluation applies also to the specified finite twist towers.
-/
theorem tower_shriek_levels :
    ∃ b : Base l E, ∃ o : Operations l E b, ∃ x : OpenExchange l E b o,
      Laws l E b o x := by
  obtain ⟨b, o, x, levels, hsystem, hinj, hplus, hlevelinj, heval, hwords,
    coordinates, hexchange, hprojection⟩ := strictCompactificationComparisonRealization l E
  refine ⟨b, o, x, ?_⟩
  refine
    { bounded := tower_bounded l E b o hinj
      projection_iso := ?_
      exchange_iso := ?_
      localization := tower_localization_realization l E b o
      detects := tower_detects l E b }
  · intro k hlp X Y _ _ _ _ _ _ f c K L wK wL hK hL
    have : IsSeparated (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
    have : IsSeparated f.left := IsSeparated.of_comp f.left Y.hom
    have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
    have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
    have : QuasiCompact (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
    have : QuasiCompact f.left := QuasiCompact.of_comp f.left Y.hom
    apply (tower_detects l E b Y.left _).2
    intro n
    let : Finite (R l E n) := b.finite n
    have hlevel := finite_level_projection_criterion l E b o levels coordinates hprojection
      k hlp X Y f c n K L (wK n) (wL n) (hK n) (hL n)
    have hh := hwords.2.1 c n K.obj L.obj
    let a := ((o.geometry f.left).pullEvaluation n).app L.obj
    let q := (Iso.refl ((Ev l E X.left n).obj K.obj)).prod a
    let t := ((b.calculus X.left).tensorEvaluation n).app
      (K.obj, (pull l E b (o.geometry f.left)).obj L.obj)
    let comparison := (Fcomparison l E b o c n).app
        ((tensor l E b X.left).obj
          (K.obj, (pull l E b (o.geometry f.left)).obj L.obj)) ≪≫
      (finiteF l E b c n).mapIso
        (t ≪≫ (comparisonLevelTensor l E b X.left n).mapIso q)
    have hg : IsIso comparison.hom := comparison.isIso_hom
    let sourceComparison := ((b.calculus Y.left).tensorEvaluation n).app
        ((F l E b o c).obj K.obj, L.obj) ≪≫
      (comparisonLevelTensor l E b Y.left n).mapIso
        (((Fcomparison l E b o c n).app K.obj).prod
          (Iso.refl ((Ev l E Y.left n).obj L.obj)))
    have hr : IsIso (sourceComparison.hom ≫ comparisonLevelProjection l E b o levels c n
        ((Ev l E X.left n).obj K.obj) ((Ev l E Y.left n).obj L.obj)) := by
      exact IsIso.comp_isIso' sourceComparison.isIso_hom hlevel
    apply isIso_of_comp_eq _ comparison.hom _ hr
    simpa only [comparison, sourceComparison, t, q, a, Iso.trans_hom,
      Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom, Iso.app_hom,
      Functor.map_comp, Category.assoc] using hh
  · exact tower_exchange_laws l E b o x levels coordinates hwords hexchange
end AlgebraicGeometry.ProEtale.SpTowerShriek

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
