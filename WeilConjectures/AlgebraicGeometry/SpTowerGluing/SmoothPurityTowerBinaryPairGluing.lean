/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerPairOpenRestriction2
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerBound
import Mathlib.CategoryTheory.Triangulated.Basic
import WeilConjectures.AlgebraicGeometry.TowerOpenCover.TowerOpenCoverTriangleData
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerLocalHomCriterion

/-! # Binary representability from local counit gluing

Source: latest smooth-purity blueprint, Local pairs, Gluing and Uniformity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- Binary gluing principle for actual compact-support representing pairs.
Source: latest blueprint `sk-prop-sp-tower-geometric-gluing.proof.md`, Gluing
(blueprint: def-sp-tower-binary-pair-gluing).

The property quantifies over finite-type sources and targets over the fixed field.
It asks only for two local representing pairs and constructs an ambient global counit.
It does not choose cones or objects in the definition. -/
def BinaryPairGluing (k : Type u) [Field k] : Prop :=
  ∀ (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left)
    (K : SpTowerCalculus.C l E b q Y.left)
    (U V : X.left.Opens) (_cover : U ⊔ V = ⊤)
    (HU : SpTowerCalculus.C l E b q U.toScheme)
    (HV : SpTowerCalculus.C l E b q V.toScheme)
    (epsU : (SpTowerCalculus.F l E b o q (c.precomp U.ι)).obj HU.obj ⟶ K.obj)
    (epsV : (SpTowerCalculus.F l E b o q (c.precomp V.ι)).obj HV.obj ⟶ K.obj),
    (∀ M : SpTowerCalculus.C l E b q U.toScheme,
      Function.Bijective (fun a : M.obj ⟶ HU.obj ↦
        (SpTowerCalculus.F l E b o q (c.precomp U.ι)).map a ≫ epsU)) →
    (∀ M : SpTowerCalculus.C l E b q V.toScheme,
      Function.Bijective (fun a : M.obj ⟶ HV.obj ↦
        (SpTowerCalculus.F l E b o q (c.precomp V.ι)).map a ≫ epsV)) →
    ∃ (H : SpTowerCalculus.C l E b q X.left)
      (eps : (SpTowerCalculus.F l E b o q c).obj H.obj ⟶ K.obj),
      ∀ M : SpTowerCalculus.C l E b q X.left,
        Function.Bijective (fun a : M.obj ⟶ H.obj ↦
          (SpTowerCalculus.F l E b o q c).map a ≫ eps)

/-- The binary gluing principle follows from restriction of representing pairs,
ringed-tower binary object descent, and the compact-support open-cover triangle.
Source: latest blueprint `sk-prop-sp-tower-geometric-gluing.proof.md`, Gluing and
Uniformity (blueprint: lem-sp-tower-binary-pair-gluing).

Proof. Restrict HU and HV to U intersect V by the open adjunction and the normalized
open compositor. Transpose the two restricted counits under their representing
bijections. Injectivity proves that the transposes are inverse and counit preserving.
Apply ringed-tower binary descent along this isomorphism; its constructibility clause
puts H in C_X, with finite intervals obtained from the two local intervals. Transport
epsU and epsV through the descent isomorphisms. Their signed difference annihilates
the first arrow of the compact-support open-cover triangle of H, by the overlap
counit equation. Hom-out exactness lifts their sum to eps. Its two restrictions are
the prescribed counits. For each test M, compare Hom(-,H) of its open-cover triangle
with Hom(F(-),K). The open adjunction identifies the local columns with the local
representing bijections, also for shifted tests. The abelian five lemma gives the
middle bijection. Empty or repeated opens are covered by the same triangle and zero
object argument; no coefficient evaluation is used to infer equality of tower maps. -/
theorem tower_binary_pair_gluing
    (k : Type u) [Field k]
    (z : SpTowerCalculus.FiniteCoordinates l E)
    (h : SpTowerCalculus.Preservation l E k b o q)
    (cal : SpTowerCalculus.Calculus l E k b o q z h) :
    BinaryPairGluing l E b o q k := by
  classical
  intro X Y _ _ _ _ _ _ f c K U V hcover HU HV epsU epsV hU hV
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  let : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  have : IsSeparated (X.left ↘ Spec (.of k)) := by
    change IsSeparated X.hom
    infer_instance
  have : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := by
    change LocallyOfFiniteType X.hom
    infer_instance
  have : QuasiCompact (X.left ↘ Spec (.of k)) := by
    change QuasiCompact X.hom
    infer_instance
  have : IsSeparated (Y.left ↘ Spec (.of k)) := by
    change IsSeparated Y.hom
    infer_instance
  have : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) := by
    change LocallyOfFiniteType Y.hom
    infer_instance
  have : QuasiCompact (Y.left ↘ Spec (.of k)) := by
    change QuasiCompact Y.hom
    infer_instance
  have : f.left.IsOver (Spec (.of k)) := ⟨Over.w f⟩
  have : IsSeparated (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  have : IsSeparated f.left := IsSeparated.of_comp f.left Y.hom
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  have : QuasiCompact (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  have : QuasiCompact f.left := QuasiCompact.of_comp f.left Y.hom
  let hF : ∀ M : SpTowerCalculus.C l E b q X.left,
      spConstructibleTorTowers l E Y.left (q.abelian Y.left)
        ((SpTowerCalculus.F l E b o q c).obj M.obj) :=
    fun M ↦ h f.left c M.obj M.property
  obtain ⟨H, eps, hlocal⟩ := tower_binary_local_counit l E b o q k z h cal
    X Y f c K U V hcover HU HV epsU epsV hU hV
  let cover : Fin 2 → X.left.Opens := fun i ↦ if i = 0 then U else V
  have hcover' : iSup cover = ⊤ := by
    apply top_unique
    rw [← hcover]
    exact sup_le (le_iSup_of_le 0 (by simp [cover]))
      (le_iSup_of_le 1 (by simp [cover]))
  have hlocal' : ∀ (s : Finset (Fin 2)), s.Nonempty →
      ∀ M : SpTowerCalculus.C l E b q (s.inf cover).toScheme,
        Function.Bijective (fun a : M.obj ⟶
            (SpTowerCalculus.etalePullback l E b o q (s.inf cover).ι).obj H.obj ↦
          (SpTowerCalculus.F l E b o q (c.precomp (s.inf cover).ι)).map a ≫
            (SpTowerCalculus.openComposition l E b o q (s.inf cover).ι c).inv.app
              ((SpTowerCalculus.etalePullback l E b o q (s.inf cover).ι).obj H.obj) ≫
            (SpTowerCalculus.F l E b o q c).map
              ((openAdjunction l E b o q (s.inf cover).ι).counit.app H.obj) ≫ eps) := by
    intro s hs M
    obtain ⟨i, hi⟩ := hs
    apply hlocal (s.inf cover) _ M
    by_cases hzero : i = 0
    · exact Or.inl (by simpa [cover, hzero] using (Finset.inf_le hi : s.inf cover ≤ cover i))
    · exact Or.inr (by simpa [cover, hzero] using (Finset.inf_le hi : s.inf cover ≤ cover i))
  have hglobal := tower_local_hom_criterion l E b o q k X Y f c hF
    K H (ObjectProperty.homMk eps) 2 cover hcover' hlocal'
  refine ⟨H, eps, ?_⟩
  intro M
  constructor
  · intro a₁ a₂ hab
    have hab' : (support l E b o q c hF).map (ObjectProperty.homMk a₁) ≫
        ObjectProperty.homMk eps =
        (support l E b o q c hF).map (ObjectProperty.homMk a₂) ≫
          ObjectProperty.homMk eps := by
      ext
      exact hab
    exact congrArg (fun a ↦ a.hom) ((hglobal M).1 hab')
  · intro g
    obtain ⟨a, ha⟩ := (hglobal M).2 (ObjectProperty.homMk g)
    exact ⟨a.hom, congrArg (fun a ↦ a.hom) ha⟩

end AlgebraicGeometry.ProEtale.SpTowerGluing
