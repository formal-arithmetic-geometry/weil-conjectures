/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Over
import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
import WeilConjectures.AlgebraicGeometry.Modules.AmpleFamily
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism

/-!
# Embedding a quasi-coherent module into an acyclic quasi-coherent module

Source: Stacks Project, Cohomology of Schemes, Tag 0BDY, Lemma 30.4.3 (1)
(blueprint: lem-weil-pbc-qcqs-quasicoherent-pure-acyclic-embedding).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Modules.pullback

private theorem jointlyFaithful_restrict_cover {X : Scheme.{u}} (C : X.OpenCover) :
    JointlyFaithful (fun i ↦ Modules.restrictFunctor (C.f i)) := by
  apply JointlyReflectIsomorphisms.jointlyFaithful
  constructor
  intro P Q φ hφ
  apply Modules.isIso_of_isIso_pullback_map C.f
    (fun x ↦ by obtain ⟨y, hy⟩ := C.covers x; exact ⟨C.idx x, y, hy⟩) φ
  intro i
  exact (NatIso.isIso_map_iff (Modules.restrictFunctorIsoPullback (C.f i)) φ).mp (hφ i)

private theorem faithful_pullback_cover {X : Scheme.{u}} (C : X.OpenCover) :
    (Modules.pullback (Sigma.desc C.f)).Faithful := by
  constructor
  intro P Q φ ψ h
  apply (jointlyFaithful_restrict_cover C).map_injective
  intro i
  let e : Modules.restrictFunctor (C.f i) ≅
      Modules.pullback (Sigma.desc C.f) ⋙ Modules.pullback (Sigma.ι C.X i) :=
    Modules.restrictFunctorIsoPullback (C.f i) ≪≫
      Modules.pullbackCongr (Sigma.ι_desc C.f i).symm ≪≫
      (Modules.pullbackComp (Sigma.ι C.X i) (Sigma.desc C.f)).symm
  apply (cancel_epi (e.inv.app P)).mp
  apply (cancel_mono (e.hom.app Q)).mp
  rw [Category.assoc, Category.assoc, NatIso.naturality_1 e φ, NatIso.naturality_1 e ψ]
  exact congrArg ((Modules.pullback (Sigma.ι C.X i)).map) h

private theorem cover_unit_universally_mono {X : Scheme.{u}} (C : X.OpenCover)
    (F : X.Modules) {Y : Scheme.{u}} (g : Y ⟶ X) :
    Mono ((Modules.pullback g).map
      ((Modules.pullbackPushforwardAdjunction (Sigma.desc C.f)).unit.app F)) := by
  classical
  let D := C.pullback₁ g
  let j := Sigma.desc C.f
  let k := Sigma.desc D.f
  let a : (∐ D.X) ⟶ (∐ C.X) := Sigma.desc
    (fun i ↦ C.pullbackHom g i ≫ Sigma.ι C.X i)
  have ha : a ≫ j = k ≫ g := by
    apply Sigma.hom_ext
    intro i
    dsimp only [a, j, k]
    simp only [Sigma.ι_desc_assoc, Category.assoc, Sigma.ι_desc,
      Cover.pullbackHom_map]
    rfl
  let L := Modules.pullback j
  let adj := Modules.pullbackPushforwardAdjunction j
  let i := adj.unit.app F
  have : IsSplitMono (L.map i) := IsSplitMono.mk'
    { retraction := adj.counit.app (L.obj F)
      id := adj.left_triangle_components F }
  let e : Modules.pullback g ⋙ Modules.pullback k ≅
      L ⋙ Modules.pullback a :=
    Modules.pullbackComp k g ≪≫ Modules.pullbackCongr ha.symm ≪≫
      (Modules.pullbackComp a j).symm
  have : IsSplitMono ((L ⋙ Modules.pullback a).map i) := by
    change IsSplitMono ((Modules.pullback a).map (L.map i))
    exact IsSplitMono.mk'
      { retraction := (Modules.pullback a).map (retraction (L.map i))
        id := by
          rw [← (Modules.pullback a).map_comp, IsSplitMono.id]
          exact (Modules.pullback a).map_id _ }
  have : Mono ((Modules.pullback g ⋙ Modules.pullback k).map i) := by
    have hmono : Mono ((Modules.pullback g ⋙ Modules.pullback k).map i ≫
        e.hom.app ((Modules.pushforward j).obj (L.obj F))) := by
      change Mono (_ ≫ e.hom.app ((Modules.pullback j ⋙ Modules.pushforward j).obj F))
      rw [e.hom.naturality i]
      infer_instance
    let : Mono ((Modules.pullback g ⋙ Modules.pullback k).map i ≫
        e.hom.app ((Modules.pushforward j).obj (L.obj F))) := hmono
    exact mono_of_mono _ (e.hom.app ((Modules.pushforward j).obj (L.obj F)))
  let : (Modules.pullback k).Faithful := faithful_pullback_cover D
  apply (Modules.pullback k).mono_of_mono_map
  change Mono ((Modules.pullback g ⋙ Modules.pullback k).map i)
  infer_instance

/-- Acyclic effacement which remains monic under every scheme pullback.
Source: Stacks Project, Tags 0BDY and 01E7.
(blueprint: lem-weil-pbc-qcqs-quasicoherent-pure-acyclic-embedding)

Proof: Choose a finite affine open cover and let j be the map from its disjoint
union to X. Embed F into j_*j^*F by the adjunction unit. Separatedness makes
intersections of affine opens affine, so j is affine; its source is affine.
Affine pushforward preserves quasicoherence, and the affine cohomology edge
and affine vanishing give zero positive cohomology of j_*j^*F.
After pulling back along j the unit splits by the triangle identity. For any
base change g, the pulled-back open cover has disjoint union k and a map a
into the original disjoint union with a followed by j equal to k followed by g.
Pullback composition identifies k^*g^* of the embedding with a^*j^* of it,
which is split monic. Pullback along an open cover is faithful, so g^* of the
embedding is monic. The empty cover is included by faithfulness. -/
theorem exists_qcqs_quasicoherent_pure_acyclic_embedding (X : Scheme.{u})
    [CompactSpace X] [X.IsSeparated]
    (F : X.Modules) [F.IsQuasicoherent] :
    ∃ F' : X.Modules,
      F'.IsQuasicoherent ∧ ∃ i : F ⟶ F', Mono i ∧
        (∀ (Y : Scheme.{u}) (g : Y ⟶ X), Mono ((Modules.pullback g).map i)) ∧
        ∀ p : ℕ, 1 ≤ p → IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F') := by
  classical
  let C := X.affineCover.finiteSubcover
  have hC (i : C.I₀) : IsAffine (C.X i) := by
    dsimp [C, OpenCover.finiteSubcover]
    infer_instance
  have hf (i : C.I₀) : IsAffineHom (C.f i) := by
    constructor
    intro V hV
    apply (Hom.isAffineOpen_iff_of_isOpenImmersion (C.f i)).mp
    rw [Hom.image_preimage_eq_opensRange_inf]
    exact (isAffineOpen_opensRange (C.f i)).inf hV
  have hj : IsAffineHom (Sigma.desc C.f) := isAffineHom_sigmaDesc C.f
  have : (Modules.pullback (Sigma.desc C.f)).Faithful := faithful_pullback_cover C
  let U := ∐ C.X
  let j : U ⟶ X := Sigma.desc C.f
  let G := (Modules.pullback j).obj F
  have hU : IsAffine U := inferInstance
  have hG : G.IsQuasicoherent := inferInstance
  let i : F ⟶ (Modules.pushforward j).obj G :=
    (Modules.pullbackPushforwardAdjunction j).unit.app F
  have hi : Mono i := inferInstance
  have : IsAffine U := hU
  have : IsAffineHom j := hj
  have : G.IsQuasicoherent := hG
  refine ⟨(Modules.pushforward j).obj G,
    Modules.isQuasicoherent_pushforward_of_isAffineHom j G, i, hi,
    (fun _ g ↦ cover_unit_universally_mono C F g), ?_⟩
  intro p hp
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  have : Subsingleton (Modules.H G (q + 1)) :=
    Modules.subsingleton_H_succ_of_isAffine G q
  obtain ⟨e, _⟩ := Modules.exists_moduleCohomology_source_comparison U (q + 1)
  have : Subsingleton ((RingedSpace.moduleCohomology U.toRingedSpace (q + 1)).obj G) :=
    (e G).toEquiv.injective.subsingleton
  have : IsIso (Modules.moduleCohomologyEdgeMap j G (q + 1)) :=
    ((Modules.affine_morphism_cohomology_edge j G).2 (q + 1)).1
  have : Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace (q + 1)).obj
      ((Modules.pushforward j).obj G)) :=
    (ConcreteCategory.bijective_of_isIso
      (Modules.moduleCohomologyEdgeMap j G (q + 1))).1.subsingleton
  exact ModuleCat.isZero_of_subsingleton _


end AlgebraicGeometry.Scheme
