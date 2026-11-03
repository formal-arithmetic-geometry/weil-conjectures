/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityEtaleNormalization
public import WeilConjectures.AlgebraicGeometry.VaryingRingGraph.VaryingRingGraphSummand
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Etale extension by zero on the recorded coefficient towers

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-prop-sp-tower-geometric/
sk-prop-sp-tower-geometric-gluing.proof.md, Local pairs ("composing with the etale
adjunction e_! -| e^*, levelwise extension by zero, counit the fibre sum")
(blueprint: def-sp-tower-etale-extension).

For fixed tower operations `b`, `o` of det-sp-tower-shriek-levels and a section-preserving
graph presentation `g` (SpTowerGluing.GraphCoordinates, def-sp-tower-gluing-interfaces), the
tower extension `e_!` along an etale map is the sheafified lift-sum extension of
def-sp-varying-ring-graph-comparison, transported through `g`. Its adjunction to the
recorded inverse image `(o.geometry e).pull` is fixed by the unique section-normalized
pullback comparison; hence its counit is the fibre sum. The comparison with the actual
compact-support functor `SpTowerShriek.F l E b o c` is the transported graph
transformation `theta`. No `FiniteCoordinates`, `EtaleOperation`, `Calculus` or
`Preservation` datum is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open AlgebraicGeometry.ProEtale.SpTowerGluing

namespace AlgebraicGeometry.ProEtale.SpTowerEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The etale extension by zero on strict coefficient systems: present the source in
graph coordinates, take the sheafified direct sum over lifts, and return.
Source: Local pairs, etale adjunction (blueprint: def-sp-tower-etale-extension). -/
def extension (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (g : GraphCoordinates l E b o) {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    SpTowerShriek.S l E U ⥤ SpTowerShriek.S l E T :=
  (g.presentation U).functor ⋙
    VaryingRingGraph.sum (graphRings l E) (graphTransitions l E) e ⋙
    (g.presentation T).inverse

/-- The transported model inverse image is the recorded inverse image, via the unique
comparison preserving the section-normalized geometric adjunction.
Source: Local pairs, etale adjunction (blueprint: def-sp-tower-etale-extension). -/
def pullComparison (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (g : GraphCoordinates l E b o) {U T : Scheme.{u}} (e : U ⟶ T) :
    (g.presentation T).functor ⋙
        SemilinearProperOpen.pull (graphRings l E) (graphTransitions l E) e ⋙
        (g.presentation U).inverse ≅ (o.geometry e).pull :=
  Functor.isoWhiskerLeft (g.presentation T).functor
      (Functor.isoWhiskerRight (graphPullCoordinates l E b o g e).symm
          (g.presentation U).inverse ≪≫
        Functor.associator (g.presentation T).inverse
          ((o.geometry e).pull ⋙ (g.presentation U).functor) (g.presentation U).inverse) ≪≫
    (Functor.associator (g.presentation T).functor (g.presentation T).inverse
      (((o.geometry e).pull ⋙ (g.presentation U).functor) ⋙ (g.presentation U).inverse)).symm ≪≫
    Functor.isoWhiskerRight (g.presentation T).unitIso.symm
      (((o.geometry e).pull ⋙ (g.presentation U).functor) ⋙ (g.presentation U).inverse) ≪≫
    Functor.leftUnitor _ ≪≫
    Functor.associator (o.geometry e).pull (g.presentation U).functor (g.presentation U).inverse ≪≫
    Functor.isoWhiskerLeft (o.geometry e).pull (g.presentation U).unitIso.symm ≪≫
    Functor.rightUnitor _

/-- The etale adjunction `e_! -| e^*` with the recorded inverse image. Its unit is the
transported summand inclusion of the structural lift.
Source: Local pairs, etale adjunction (blueprint: def-sp-tower-etale-extension). -/
def adjunction (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (g : GraphCoordinates l E b o) {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    extension l E b o g e ⊣ (o.geometry e).pull :=
  (((g.presentation U).toAdjunction.comp
      (VaryingRingGraph.geometricSumAdjunction (graphRings l E) (graphTransitions l E) e)).comp
    (g.presentation T).symm.toAdjunction).ofNatIsoRight (pullComparison l E b o g e)

/-- The etale counit `e_! e^* -> id`: the fibre sum, folding the lift summands
by restriction. Source: Local pairs, "counit the fibre sum"
(blueprint: def-sp-tower-etale-extension). -/
def counit (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (g : GraphCoordinates l E b o) {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    (o.geometry e).pull ⋙ extension l E b o g e ⟶ 𝟭 (SpTowerShriek.S l E T) :=
  (adjunction l E b o g e).counit

instance extension_additive (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b)
    (g : GraphCoordinates l E b o) {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    (extension l E b o g e).Additive := by
  unfold extension
  infer_instance

instance extension_preservesFiniteLimits (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b)
    (g : GraphCoordinates l E b o) {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    PreservesFiniteLimits (extension l E b o g e) := by
  unfold extension
  infer_instance

instance extension_preservesFiniteColimits (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b)
    (g : GraphCoordinates l E b o) {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    PreservesFiniteColimits (extension l E b o g e) := by
  unfold extension
  infer_instance

/-- Exact derived etale extension on unbounded tower complexes.
Source: Local pairs, levelwise extension by zero (blueprint: def-sp-tower-etale-extension). -/
abbrev extensionD (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (g : GraphCoordinates l E b o) {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :=
  (extension l E b o g e).mapDerivedCategory

/-- The derived etale adjunction, the exact localization of the ordinary one; its right
adjoint is the recorded derived inverse image.
Source: Local pairs, etale adjunction (blueprint: def-sp-tower-etale-extension). -/
def derivedAdjunction (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (g : GraphCoordinates l E b o) {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    extensionD l E b o g e ⊣ SpTowerShriek.pull l E b (o.geometry e) :=
  (adjunction l E b o g e).mapExactDerivedCategory

/-- The derived fibre-sum counit `e_! e^* K -> K`.
Source: Local pairs, "counit the fibre sum" (blueprint: def-sp-tower-etale-extension). -/
def derivedCounit (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (g : GraphCoordinates l E b o) {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    SpTowerShriek.pull l E b (o.geometry e) ⋙ extensionD l E b o g e ⟶
      𝟭 (SpTowerShriek.D l E T) :=
  (derivedAdjunction l E b o g e).counit

/-- The ordinary sum square, by the presentation counit.
Source: Local pairs, graph coordinates (blueprint: def-sp-tower-etale-extension). -/
def sumSquare (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (g : GraphCoordinates l E b o) {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    extension l E b o g e ⋙ (g.presentation T).functor ≅
      (g.presentation U).functor ⋙
        VaryingRingGraph.sum (graphRings l E) (graphTransitions l E) e :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (g.presentation U).functor
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (g.presentation T).counitIso ≪≫ Functor.rightUnitor _)

/-- The exact sum square descended termwise to unbounded complexes.
Source: Local pairs, graph coordinates (blueprint: def-sp-tower-etale-extension). -/
def derivedSumSquare (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (g : GraphCoordinates l E b o) {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    extensionD l E b o g e ⋙ (g.presentation T).functor.mapDerivedCategory ≅
      (g.presentation U).functor.mapDerivedCategory ⋙
        (VaryingRingGraph.sum (graphRings l E) (graphTransitions l E) e).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (sumSquare l E b o g e) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The etale comparison `e_! -> F_c` with the actual compact-support functor of
det-sp-tower-shriek-levels: the transported clopen-graph transformation `theta`
(open unit on each lift graph, zero on its complement, then the derived direct-image
unit), pulled back along the fully faithful derived presentation.
Source: Local pairs; def-sp-varying-ring-graph-comparison
(blueprint: def-sp-tower-etale-extension). -/
def comparison (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (g : GraphCoordinates l E b o) {U T : Scheme.{u}} (e : U ⟶ T) [Etale e]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] (c : Compactification e) :
    extensionD l E b o g e ⟶ SpTowerShriek.F l E b o c :=
  (((g.presentation T).mapDerivedCategory.fullyFaithfulFunctor).whiskeringRight
    (SpTowerShriek.D l E U)).preimage
      ((derivedSumSquare l E b o g e).hom ≫
        Functor.whiskerLeft (g.presentation U).functor.mapDerivedCategory
          (VaryingRingGraph.theta (graphRings l E) (graphTransitions l E) e c) ≫
        (graphSupportCoordinates l E b o g c).inv)

/-- The etale comparison `e_! ≅ F_c` holds on bounded-below towers with finite etale
origins at every level, for separated finite-type schemes over a field of characteristic
prime to `l`.
Source: Local pairs and Levels; Stacks 0F4L, 0GKM, 03S5
(blueprint: def-sp-tower-etale-extension).
Proof: by `laws.detects` it suffices to check each level. The level of `theta` is the
single-ring graph comparison (lem-sp-varying-ring-graph-summand), which is invertible on
finite etale-origin complexes. -/
theorem comparison_isIso (pchar : ℕ) (hp : 0 < pchar) (hne : pchar ≠ l)
    (k : Type u) [Field k] [CharP k pchar]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (x : SpTowerShriek.OpenExchange l E b o) (laws : SpTowerShriek.Laws l E b o x)
    (g : GraphCoordinates l E b o) {U T : Scheme.{u}}
    [U.Over (Spec (.of k))] [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [T.Over (Spec (.of k))] [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    (e : U ⟶ T) [e.IsOver (Spec (.of k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] [Etale e]
    (c : Compactification e) (C : DerivedCategory.Plus (SpTowerShriek.S l E U))
    (hC : ∀ n : ℕ, SpTowerShriek.Origin l E b U n C.obj) :
    IsIso ((comparison l E b o g e c).app C.obj) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerEtale

end
