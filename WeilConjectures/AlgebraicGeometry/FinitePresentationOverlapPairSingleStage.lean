/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OverlapPairCanonicalComparisons
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.AlgebraicGeometry.FinitePresentationLocalMapDatum
import WeilConjectures.AlgebraicGeometry.OverlapPairModelTransport
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import WeilConjectures.AlgebraicGeometry.Modules.ZariskiDescent

/-! # A step of persistent pairwise overlap lifting

## References

* Stacks Project, Tag 01ZR.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Lift the conjugated map on a fixed pair at one stage, without any assertion
about later stages.
(Stacks, Tag 01ZR, Tag 05N7) -/
theorem exists_overlap_pair_map_at_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (j : I) (hij : i ≤ j)
    (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    [Finite U.I₀] [∀ a, IsAffine (U.X a)]
    (N : (a : U.I₀) → (U.X a).Modules)
    (hN : ∀ a, (N a).IsFinitePresentation) (hNq : ∀ a, (N a).IsQuasicoherent)
    (M : (pullback f (c.π.app (op i))).Modules)
    (e : ∀ a, (Scheme.Modules.pullback (U.pullbackHom
      (baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))) a)).obj (N a) ≅
      (Scheme.Modules.pullback ((U.pullback₁ (baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)))).f a)).obj M)
    (a b : U.I₀) :
    ∃ (k : I) (hjk : j ≤ k),
      let q := overlapStageMap R f hij hjk
      let V := U.pullback₁ q
      let p := overlapLimitMap R c f (hij.trans hjk)
      let A := fun d ↦ (Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)
      let W := V.pullback₁ p
      let D := (modulesPseudofunctor.toDescentData W.f).obj M
      let ε := overlapIteratedComparison U q p (overlapLimitMap R c f hij)
        (by
          dsimp only [p, q, overlapLimitMap, overlapStageMap]
          rw [← baseChangeMap_comp]
          congr 1
          ext
          simpa using c.w (homOfLE hjk).op) N M e
      ∃ φ : (Scheme.Modules.pullback (pullback.fst (V.f a) (V.f b))).obj (A a) ⟶
          (Scheme.Modules.pullback (pullback.snd (V.f a) (V.f b))).obj (A b),
        overlapPairSquare V A p D ε a b φ := by
  classical
  let Xj := pullback f (Spec.map (R.map (homOfLE hij)))
  let gj := pullback.snd f (Spec.map (R.map (homOfLE hij)))
  let : QuasiSeparatedSpace Xj := quasiSeparatedSpace_of_quasiSeparated gj
  let : QuasiCompact (U.f b) := inferInstance
  let g := overlapModelHom R f hij U a b
  let : LocallyOfFinitePresentation g := by
    dsimp only [g, overlapModelHom]
    infer_instance
  let : QuasiCompact g := by
    dsimp only [g, overlapModelHom]
    infer_instance
  let : QuasiSeparated g := by
    dsimp only [g, overlapModelHom]
    infer_instance
  let F := (Scheme.Modules.pullback (overlapModelChart R f hij U a b a
    (pullback.fst (U.f a) (U.f b)))).obj (N a)
  let G := (Scheme.Modules.pullback (overlapModelChart R f hij U a b b
    (pullback.snd (U.f a) (U.f b)))).obj (N b)
  let : (N a).IsFinitePresentation := hN a
  let : (N b).IsFinitePresentation := hN b
  let : (N a).IsQuasicoherent := hNq a
  let : (N b).IsQuasicoherent := hNq b
  have hF : F.IsFinitePresentation := inferInstance
  have hG : G.IsFinitePresentation := inferInstance
  have hFq : F.IsQuasicoherent := Scheme.Modules.isQuasicoherent_pullback _ (N a)
  have hGq : G.IsQuasicoherent := Scheme.Modules.isQuasicoherent_pullback _ (N b)
  let θ := overlapModelConjugate R c f hij U a b N M e
  obtain ⟨k, hjk, hlocal⟩ := exists_finitePresentation_local_map_datum
    R c hc j g j (le_refl j) F G hF hFq hG hGq θ
  dsimp only at hlocal
  rcases hlocal with ⟨σ, hσ, C, _, _, ψ, hψ⟩
  obtain ⟨α, hα⟩ := (bijective_toDescentData_map_of_isOpenImmersion
    C.f C.iSup_opensRange _ _).surjective ψ
  have hrec := hψ α hα
  let p := overlapLimitMap R c g ((le_refl j).trans hjk)
  let V : (pullback g (c.π.app (op j))).OpenCover.{u} := C.pullback₁ p
  have hglobal : σ.hom.app F ≫ (Scheme.Modules.tensorPullback p).map α =
      θ ≫ σ.hom.app G := by
    apply (bijective_toDescentData_map_of_isOpenImmersion
      V.f V.iSup_opensRange _ _).injective
    exact Pseudofunctor.DescentData.hom_ext hrec
  subst σ
  refine ⟨k, hjk, overlapPairMapOfModel R f hij U a b hjk N α, ?_⟩
  exact overlap_pair_square_of_model_recovery R c i f j hij U N M e a b k hjk α hglobal


end AlgebraicGeometry
