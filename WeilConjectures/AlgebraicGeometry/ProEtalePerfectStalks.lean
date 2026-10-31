/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleExceptionalOriginTransfer
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.AlgebraicGeometry.FixedModuleGeometricStalkFunctors
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonStalk
import WeilConjectures.AlgebraicGeometry.EtaleStalkTorTest
import WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import WeilConjectures.RingTheory.RingPseudoCoherent
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.FiniteFreeResolution
import WeilConjectures.RingTheory.PseudoCoherentOfCohomology
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Single
import WeilConjectures.RingTheory.PseudoCoherentIffAllM
import WeilConjectures.RingTheory.MPseudoCoherentVanishingBase
import WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import WeilConjectures.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleFiniteStalks
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! Perfectness of geometric stalks for a classical pro-etale finite-ring object.
(blueprint: lem-sf-proetale-perfect-stalks)

The proof transports a cochain representative through the classical comparison, applies the
finite-projective stalk argument on the etale model, and descends the result through exact
stalk comparison and quasi-isomorphisms. It is an independent part of the node's zero-complex
statement, so it is exposed as its own theorem.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme
open _root_.DerivedCategory


-- Realize the specified neighbourhood colimit as a site-point fiber. This gives exactness
-- for module coefficients, rather than only for the underlying abelian-group stalk.
private theorem stalk_cover_lift
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {V : T.ProEt} (R : Sieve V) (hR : R ∈ ProEt.topology T V)
    (v : Spec (.of Ω) ⟶ V.left) :
    ∃ (W : T.ProEt) (g : W ⟶ V) (_ : R g) (w : Spec (.of Ω) ⟶ W.left),
      w ≫ g.left = v := by
  obtain ⟨S, hS, hSR⟩ := ProEt.mem_topology_iff.1 hR
  obtain ⟨ι, Z, f, rfl⟩ := S.exists_eq_ofArrows
  have hS' : Presieve.ofArrows (fun i ↦ (Z i).left) (fun i ↦ (f i).left) ∈
      proetalePrecoverage V.left := by
    simpa only [ProEt.mem_precoverage_iff, Presieve.map_ofArrows,
      Functor.comp_obj, Functor.comp_map, ProEt.forget, MorphismProperty.Over.forget,
      MorphismProperty.Comma.forget, Over.forget, Comma.fst] using hS
  have hb := Precoverage.mem_coverings_of_isPullback (fun i ↦ (f i).left) hS' v
    (fun i ↦ pullback.snd (f i).left v) (fun i ↦ pullback.fst (f i).left v)
    (fun i ↦ (IsPullback.of_hasPullback (f i).left v).flip)
  obtain ⟨i, z, hz⟩ :=
    ((ofArrows_mem_precoverage_iff _).1 (propQCPrecoverage_le_precoverage _ hb)).1
      (IsLocalRing.closedPoint Ω)
  have : WeaklyEtale (f i).left :=
    ((ofArrows_mem_precoverage_iff _).1 (propQCPrecoverage_le_precoverage _ hS')).2 i
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale
    (pullback.snd (f i).left v) z
  refine ⟨Z i, f i, hSR _ _ ⟨i⟩, σ ≫ pullback.fst (f i).left v, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]

private noncomputable def stalkPoint
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) : (ProEt.topology T).Point.{u + 1} where
  fiber := (ProEt.forget T ⋙ coyoneda.obj (op (Over.mk t))) ⋙ uliftFunctor.{u + 1}
  isCofiltered := by
    have : IsCofiltered (ProEt.forget T ⋙ coyoneda.obj (op (Over.mk t))).Elements :=
      Functor.isCofiltered_elements _
    exact .of_equivalence
      (Functor.Elements.uliftEquivalence.{u + 1}
        (ProEt.forget T ⋙ coyoneda.obj (op (Over.mk t)))).symm
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective R hR x := by
    obtain ⟨W, g, hg, w, hw⟩ := stalk_cover_lift R hR x.down.left
    refine ⟨W, g, hg, ULift.up (Over.homMk w ?_), ?_⟩
    · change w ≫ W.hom = t
      rw [← MorphismProperty.Over.w g, ← Category.assoc, hw]
      exact Over.w x.down
    · apply ULift.ext
      apply Over.OverMorphism.ext
      exact hw

private noncomputable def stalkPointElements
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) :
    ProEtaleGeometricNeighbourhood t ≌ (stalkPoint t).fiber.Elements where
  functor.obj n := ⟨n.right, ULift.up n.hom⟩
  functor.map f := ⟨f.right, congrArg ULift.up f.w⟩
  inverse.obj n := StructuredArrow.mk n.2.down
  inverse.map f := StructuredArrow.homMk f.1 (congrArg ULift.down f.2)
  unitIso := Iso.refl _
  counitIso := Iso.refl _

private noncomputable def stalkPointIso
    (A : Type (u + 1)) [CommRing A]
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) :
    geometricModuleStalkFunctor A t ≅
      (stalkPoint t).sheafFiber (A := ModuleCat.{u + 1} A) :=
  Functor.isoWhiskerLeft (sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} A))
    (Functor.isoWhiskerLeft
      ((Functor.whiskeringLeft _ _ (ModuleCat.{u + 1} A)).obj
        (CategoryOfElements.π (stalkPoint t).fiber).op)
      (Functor.Final.colimIso (stalkPointElements t).functor.op))

/-- Every geometric stalk of a classical pro-etale finite-ring object is perfect.

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-lem-sf-kunneth-star/
sk-lem-sf-kunneth-star.proof.md, geometric-stalk perfectness component
(blueprint: lem-sf-proetale-perfect-stalks).

Proof: transport a representative through the etale/pro-etale comparison. Termwise stalk
comparison and exactness descend through quasi-isomorphisms. The etale stalk has bounded finite
cohomology and finite Tor amplitude, so Noetherian pseudo-coherence plus finite Tor dimension
gives a bounded finite-projective representative. Transporting this representative back yields
the claimed perfect stalk for every cochain representative. -/
theorem proEtale_perfect_stalks_of_classical
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    (C : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)))
    (_hC : exceptionalTransportProEtaleObjects A S C)
    (_hclassicalC : ∃ E : Etale.DerivedCategoryModule A S,
      _root_.DerivedCategory.TStructure.t.plus E ∧
        Nonempty ((comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.obj E ≅ C)) :
    ∀ (P : CochainComplex
        (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)) ℤ),
        Nonempty (_root_.DerivedCategory.Q.obj P ≅ C) →
          ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
            _root_.DerivedCategory.IsPerfectRingComplex (_root_.DerivedCategory.Q.obj
              (((geometricModuleStalkFunctor A s).mapHomologicalComplex (.up ℤ)).obj P)) := by
  classical
  obtain ⟨E, hE, _, ⟨eE⟩⟩ :=
    exceptional_etale_origin_of_pro_origin A S _hC _hclassicalC
  intro P ⟨eP⟩ Ω _ _ s
  let F := geometricModuleStalkFunctor A s
  let G := (pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} A)
  have : PreservesFiniteLimits F := preservesFiniteLimits_of_natIso (stalkPointIso A s).symm
  have : PreservesFiniteColimits F :=
    preservesFiniteColimits_of_natIso (stalkPointIso A s).symm
  let N := comparisonUpperStar (ModuleCat.{u + 1} A) S
  obtain ⟨c, _⟩ := (proEtale_comparison_stalk S Ω s).2.2 A
  let c' : N ⋙ F ≅ G := c
  let e : F.mapDerivedCategory.obj C ≅ G.mapDerivedCategory.obj E :=
    F.mapDerivedCategory.mapIso eE.symm ≪≫
      (Functor.mapDerivedCategoryCompIso N F).symm.app E ≪≫
      (Functor.mapDerivedCategoryNatIso c').app E
  let e' : _root_.DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (.up ℤ)).obj P) ≅ G.mapDerivedCategory.obj E :=
    (F.mapDerivedCategoryFactors.app P).symm ≪≫ F.mapDerivedCategory.mapIso eP ≪≫ e
  let D := G.mapDerivedCategory.obj E
  obtain ⟨a, b, hab, htor⟩ := hE.2
  have htest := (Etale.geometricStalk_torAmplitude_test A S E a b hab).1.mp htor Ω s
  have hTor : _root_.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) a b D := by
    intro M
    exact ⟨(_root_.DerivedCategory.isGE_iff _ a).mpr
      (fun i hi ↦ htest M i (Or.inl hi)),
      (_root_.DerivedCategory.isLE_iff _ b).mpr
        (fun i hi ↦ htest M i (Or.inr hi))⟩
  have hfin (i : ℤ) : Module.Finite A
      ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) i).obj D) := by
    have : Module.Finite A (G.obj ((_root_.DerivedCategory.homologyFunctor _ i).obj E)) :=
      (constructibleModule_finite_geometric_stalk _ (hE.1.1 i) Ω s).2
    let eH : G.obj ((_root_.DerivedCategory.homologyFunctor _ i).obj E) ≅
        (_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) i).obj D :=
      (G.mapDerivedCategoryHomologyFunctorIso i).app E
    exact Module.Finite.equiv eH.toLinearEquiv
  have hPC : _root_.DerivedCategory.IsPseudoCoherent D := by
    apply (isPseudoCoherent_iff_boundedAbove_finite_homology.{u + 1, u + 1, u + 1}
      A D).mpr
    refine ⟨⟨b, ?_⟩, hfin⟩
    exact fun i hi ↦ (_root_.DerivedCategory.isLE_iff D b).mp
      (_root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hTor).2 i hi
  obtain ⟨T, ⟨l, r, hzero⟩, hfinite, hproj, ⟨eT⟩⟩ :=
    _root_.DerivedCategory.isPerfect_of_pseudoCoherent_finiteTorAmplitude D hPC
      ⟨a, b, hab, hTor⟩
  exact ⟨T, l, r, (T.isStrictlyGE_iff l).mpr (fun i hi ↦ hzero i (Or.inl hi)),
    (T.isStrictlyLE_iff r).mpr (fun i hi ↦ hzero i (Or.inr hi)),
    fun i ↦ ⟨hproj i, hfinite i⟩, ⟨e' ≪≫ eT.symm⟩⟩

end AlgebraicGeometry.ProEtale
