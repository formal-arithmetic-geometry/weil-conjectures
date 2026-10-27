/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Constructible
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Mathlib.RingTheory.Finiteness.Cardinality
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.ConstructibleSheaf.FiniteConstantModel
import Mathlib.Data.Int.Interval

/-! # Stratified finite cohomology models on actual etale slice sites

Source: Stacks Project, Tags 095E and 03RZ, common partition argument;
`FiniteFieldStratifiedPerfectModels.lean`, commonStratification and finiteLocalModels
(blueprint: lem-weil-pbc-stratified-cohomology-slice-models).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Base change a locally constant trivializing cover to V, extract finite module values
on its members, and lift the models through the equivalences with the actual slice sites.
Source: Stacks Project, Tag 095A and the finite constant model theorem. -/
private theorem finiteSliceModels
    {X : Scheme.{u}} {B : Type (u + 1)} [CommRing B] [Finite B]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    [Scheme.IsFiniteLocallyConstantSheaf F] (V : X.Etale) :
    ∃ (I : Type (u + 1)) (U : I → X.Etale) (f : ∀ t, U t ⟶ V),
      Sieve.ofArrows U f ∈ X.smallEtaleTopology V ∧
      ∀ t : I, ∃ M : ModuleCat.{u + 1} B, Finite M ∧ Nonempty
        (F.over (U t) ≅
          (constantSheaf (X.smallEtaleTopology.over (U t)) (ModuleCat.{u + 1} B)).obj M) := by
  classical
  obtain ⟨d⟩ := Scheme.IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
  have hi (i : d.cover.I₀) : AlgebraicGeometry.Etale (d.cover.f i) := d.cover.map_prop i
  let U (i : ULift.{u + 1} d.cover.I₀) := Scheme.Etale.baseChange (d.cover.f i.down) V
  let f (i : ULift.{u + 1} d.cover.I₀) := Scheme.Etale.baseChangeHom (d.cover.f i.down) V
  refine ⟨ULift.{u + 1} d.cover.I₀, U, f, ?_, ?_⟩
  · apply Scheme.Etale.ofArrows_baseChange_mem_smallEtaleTopology
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, y, hy⟩ := d.cover.exists_eq x
    exact Set.mem_iUnion.mpr ⟨⟨i⟩, y, hy⟩
  · intro i
    let W := U i
    have hc : ((upperStar (ModuleCat.{u + 1} B) (d.cover.f i.down)).obj F).IsConstant
        (d.cover.X i.down).smallEtaleTopology :=
      (Scheme.isConstant_over_iff_upperStar _ (d.cover.etalePrecoverageToEtale i.down) F).mp
        (d.isConstant i.down)
    have hc' := Sheaf.IsConstant.upperStar (ModuleCat.{u + 1} B)
      (pullback.snd V.hom (d.cover.f i.down))
      ((upperStar (ModuleCat.{u + 1} B) (d.cover.f i.down)).obj F)
    have e : (upperStar (ModuleCat.{u + 1} B) (pullback.snd V.hom
        (d.cover.f i.down))).obj
        ((upperStar (ModuleCat.{u + 1} B) (d.cover.f i.down)).obj F) ≅
        (upperStar (ModuleCat.{u + 1} B) W.hom).obj F :=
      ((upperStarComp _ _ _).app F).symm ≪≫
        eqToIso (congrArg (fun g ↦ (upperStar (ModuleCat.{u + 1} B) g).obj F)
          pullback.condition.symm)
    have hcW := Sheaf.isConstant_congr _ e
    have hfW := Scheme.IsFiniteLocallyConstantSheaf.upperStar W.hom F
    obtain ⟨M, hM, ⟨eM⟩⟩ := Scheme.exists_finite_constant_model
      ((upperStar (ModuleCat.{u + 1} B) W.hom).obj F) hcW hfW.toIsFiniteSheaf
    have := hM
    refine ⟨M, Module.finite_of_finite B, ⟨?_⟩⟩
    exact (Scheme.Etale.overSheafEquiv W
      (ModuleCat.{u + 1} B)).fullyFaithfulFunctor.preimageIso
      (Scheme.overSheafEquivFunctorObjOverIso _ W F ≪≫ eM ≪≫
        (((Scheme.Etale.overEquiv W).constantSheafSheafCongrIso
          (X.smallEtaleTopology.over W) W.left.smallEtaleTopology
          (ModuleCat.{u + 1} B) Over.mkIdTerminal).app M).symm)

/-- A bounded constructible complex over a finite commutative ring has a common finite
constructible locally closed stratification on which every cohomology sheaf has finite
constant module models on every actual localized etale site.

Source: Stacks Project, Tags 095E and 03RZ; derived and slice transport extracted from
`FiniteFieldStratifiedPerfectModels.lean`, commonStratification and finiteLocalModels
(blueprint: lem-weil-pbc-stratified-cohomology-slice-models).

Proof plan:
1. Use constant-coefficient module inverse image and its exactness
   (prop-weil-pbc-inverse-image-modules-exact). The constant-left-module theorem,
   etale inverse-image restriction and module-linear composition core identify iterated
   pullbacks with composite pullbacks, B-linearly. Linearity for each constant scalar
   extends locally to sections of the constant ring sheaf.
2. Pull a finite constant trivializing cover back along any scheme morphism, using
   lem-weil-pbc-etale-covering-base-change. Composition, etale restriction and
   lem-sfb-geometric-inverse-image-constant-module keep the same finite module values.
3. Enumerate the finite interval [a,b]. Choose a constructible stratification for its
   first cohomology sheaf, then intersect it successively with the stratifications for
   the remaining degrees using lem-weil-pbc-constructible-stratification-intersection.
   The strata are actual fibre products. Pull the existing models along both projections
   by step 2; their composites into X agree. Retain empty fibre products.
4. Exact inverse image induces the ordinary unbounded derived inverse image. By
   lem-pur-exact-derived-cohomology-coherence its cohomology is the inverse image of
   the original cohomology. Thus the bounds persist and the models in [a,b] transport.
5. For an arbitrary etale object V over a stratum, base change its trivializing cover
   along V. The resulting etale maps cover V, and step 2 retains the finite models.
6. By lem-weil-pbc-etale-site-localization-open the actual slice site over each member
   is equivalent to that member's small etale site. Restrict and transport module
   operations sectionwise. The geometric constant-module comparison identifies the
   transported constants with sheafifications of constant module presheaves. This gives
   the asserted module-sheaf isomorphisms on the actual slices.
7. Outside [a,b], use the identity cover and the zero module. Finite sets of elements
   generate each finite module. If necessary, choose a covering member above each point
   of V and reindex by its point set, lifted to the coefficient universe. This preserves
   all models and joint surjectivity. The empty scheme, empty strata and empty objects
   impose no nonemptiness condition; the identity cover still works for an empty V. -/
theorem stratified_cohomology_slice_models
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (B : Type (u + 1)) [CommRing B] [Finite B]
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (a b : ℤ) (hab : a ≤ b)
    (hvan : ∀ q : ℤ, q < a ∨ b < q → IsZero
      ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) q).obj L))
    (hconstructible : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) q).obj L)) :
    ∃ S : Scheme.FiniteLocallyClosedStratification X,
      (∀ s : Fin S.n, Topology.IsConstructible (S.stratum s)) ∧
      ∀ s : Fin S.n,
        (∀ q : ℤ, q < a ∨ b < q → IsZero
          ((DerivedCategory.homologyFunctor
            (Sheaf (S.domain s).smallEtaleTopology (ModuleCat.{u + 1} B)) q).obj
            ((upperStar (ModuleCat.{u + 1} B) (S.immersion s)).mapDerivedCategory.obj L))) ∧
        ∀ (q : ℤ) (V : (S.domain s).Etale),
          ∃ (I : Type (u + 1)) (U : I → (S.domain s).Etale) (f : ∀ t, U t ⟶ V),
            Sieve.ofArrows U f ∈ (S.domain s).smallEtaleTopology V ∧
            ∀ t : I, ∃ M : ModuleCat.{u + 1} B, Finite M ∧ Nonempty
              (((DerivedCategory.homologyFunctor
                (Sheaf (S.domain s).smallEtaleTopology (ModuleCat.{u + 1} B)) q).obj
                ((upperStar (ModuleCat.{u + 1} B)
                  (S.immersion s)).mapDerivedCategory.obj L)).over (U t) ≅
                (constantSheaf ((S.domain s).smallEtaleTopology.over (U t))
                  (ModuleCat.{u + 1} B)).obj M) := by
  classical
  let H (q : ℤ) := (DerivedCategory.homologyFunctor
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) q).obj L
  have hcommon (t : Finset ℤ) : ∃ S : Scheme.Stratification X,
      ∀ q ∈ t, ∀ s : Fin S.n,
        Scheme.IsFiniteLocallyConstantSheaf
          ((upperStar (ModuleCat.{u + 1} B) (S.immersion s)).obj (H q)) := by
    induction t using Finset.induction_on with
    | empty =>
        obtain ⟨q₀, _⟩ := Finset.nonempty_Icc.mpr hab
        obtain ⟨S, _⟩ := hconstructible q₀
        exact ⟨S, by simp⟩
    | @insert q t hqt ih =>
        obtain ⟨S, hS⟩ := ih
        have hc := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf
          (H q)).mp
          (hconstructible q)
        obtain ⟨T, hT⟩ := hc.exists_stratification
        refine ⟨S.inter T, ?_⟩
        intro r hr s
        rcases Finset.mem_insert.mp hr with rfl | hr
        · exact (S.inter_refines_right T).isFiniteLocallyConstantSheaf_upperStar
            (H r) hT s
        · exact (S.inter_refines_left T).isFiniteLocallyConstantSheaf_upperStar
            (H r) (hS r hr) s
  obtain ⟨S, hS⟩ := hcommon (Finset.Icc a b)
  let T : Scheme.FiniteLocallyClosedStratification X :=
    { n := S.n
      stratum := S.stratum
      isLocallyClosed_stratum := S.isLocallyClosed_stratum
      iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
      pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
      domain := S.domain
      immersion := S.immersion
      isImmersion := S.isImmersion
      range_immersion := S.range_immersion }
  refine ⟨T, S.isConstructible_stratum, ?_⟩
  intro s
  let F := upperStar (ModuleCat.{u + 1} B) (S.immersion s)
  have hzero (q : ℤ) (hq : q < a ∨ b < q) : IsZero
      ((DerivedCategory.homologyFunctor
        (Sheaf (S.domain s).smallEtaleTopology (ModuleCat.{u + 1} B)) q).obj
        (F.mapDerivedCategory.obj L)) :=
    (F.map_isZero (hvan q hq)).of_iso ((F.mapDerivedCategoryHomologyFunctorIso q).symm.app L)
  refine ⟨hzero, ?_⟩
  intro q V
  have hflc : Scheme.IsFiniteLocallyConstantSheaf
      ((DerivedCategory.homologyFunctor
        (Sheaf (S.domain s).smallEtaleTopology (ModuleCat.{u + 1} B)) q).obj
        (F.mapDerivedCategory.obj L)) := by
    by_cases hq : q ∈ Finset.Icc a b
    · have : Scheme.IsFiniteLocallyConstantSheaf (F.obj (H q)) := hS q hq s
      exact Scheme.IsFiniteLocallyConstantSheaf.of_iso (F := F.obj (H q))
        ((F.mapDerivedCategoryHomologyFunctorIso q).app L)
    · apply Scheme.IsFiniteLocallyConstantSheaf.of_isZero
      apply hzero
      simpa only [Finset.mem_Icc, not_and_or, not_le] using hq
  exact finiteSliceModels _ V

end AlgebraicGeometry.Etale
