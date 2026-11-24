/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
import WeilConjectures.AlgebraicGeometry.FinitePresentationLocalDescentDatum
import WeilConjectures.AlgebraicGeometry.FinitePresentationLocalMapDatum
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import WeilConjectures.AlgebraicGeometry.Modules.ZariskiDescent

/-!
# Descent of finitely presented quasi-coherent modules and maps

## References

* Stacks Project, Tag 01ZR
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem openCoverFullyFaithful {X : Scheme.{u}} (U : Scheme.OpenCover.{u} X) :
    Nonempty (modulesPseudofunctor.toDescentData U.f).FullyFaithful :=
  (Functor.FullyFaithful.nonempty_iff_map_bijective _).2
    (fun A B ↦ bijective_toDescentData_map_of_isOpenImmersion
      U.f U.iSup_opensRange A B)

set_option backward.isDefEq.respectTransparency false in
private theorem nonempty_tensorPullback_iso_of_local_datum
    {X Y : Scheme.{u}} (p : Y ⟶ X) (U : Scheme.OpenCover.{u} X)
    (D : modulesPseudofunctor.DescentData U.f) (N : X.Modules) (M : Y.Modules)
    (eN : (modulesPseudofunctor.toDescentData U.f).obj N ≅ D)
    (eD : (Pseudofunctor.DescentData.pullFunctor modulesPseudofunctor
      (f := U.f) (f' := (U.pullback₁ p).f) (p := p)
      (α := fun a ↦ a) (p' := fun a ↦ U.pullbackHom p a)
      (fun a ↦ U.pullbackHom_map p a)).obj D ≅
      (modulesPseudofunctor.toDescentData (U.pullback₁ p).f).obj M) :
    Nonempty ((Scheme.Modules.tensorPullback p).obj N ≅ M) := by
  classical
  let P := Pseudofunctor.DescentData.pullFunctor modulesPseudofunctor
    (f := U.f) (f' := (U.pullback₁ p).f) (p := p)
    (α := fun a ↦ a) (p' := fun a ↦ U.pullbackHom p a)
    (fun a ↦ U.pullbackHom_map p a)
  let t := Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
    modulesPseudofunctor (f := U.f) (f' := (U.pullback₁ p).f) (p := p)
    (α := fun a ↦ a) (p' := fun a ↦ U.pullbackHom p a)
    (fun a ↦ U.pullbackHom_map p a)
  let e : (Scheme.Modules.pullback p).obj N ≅ M :=
    (openCoverFullyFaithful (U.pullback₁ p)).some.preimageIso
      ((t.app N).symm ≪≫ P.mapIso eN ≪≫ eD)
  let comparison : Scheme.Modules.tensorPullback p ≅ Scheme.Modules.pullback p :=
    Adjunction.leftAdjointUniq
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction p))
      (Scheme.Modules.pullbackPushforwardAdjunction p)
  exact ⟨comparison.app N ≪≫ e⟩

/-- Finite-presentation descent for modules and for maps between fixed models, for the
inverse system of affine schemes `Spec (R k)` with limit cone `c` and `IsAffine c.pt`
(Stacks, Tag 01ZR). -/
theorem finitePresentation_module_map_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    (∀ M : (pullback f (c.π.app (op i))).Modules,
      M.IsFinitePresentation → M.IsQuasicoherent →
      ∃ (j : I) (hij : i ≤ j) (Mj : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules),
        Mj.IsFinitePresentation ∧ Mj.IsQuasicoherent ∧
        Nonempty ((Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj Mj ≅ M)) ∧
    (∀ (j : I) (hij : i ≤ j) (Fj Gj : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules),
      Fj.IsFinitePresentation → Fj.IsQuasicoherent →
      Gj.IsFinitePresentation → Gj.IsQuasicoherent →
      ∀ φ : (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj Fj ⟶
          (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj Gj,
      ∃ (j' : I) (hjj' : j ≤ j')
        (φj' : (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
            (Over.homMk (Spec.map (R.map (homOfLE hjj')))
              (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))).obj Fj ⟶
          (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
            (Over.homMk (Spec.map (R.map (homOfLE hjj')))
              (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))).obj Gj)
        (e : Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)) ≅
          Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
            (Over.homMk (Spec.map (R.map (homOfLE hjj')))
              (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)) ⋙
          Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op))),
        e = Scheme.Modules.tensorPullbackCompositionIso
          (baseChangeMap f
            (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op)))
          (baseChangeMap f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
            (Over.homMk (Spec.map (R.map (homOfLE hjj')))
              (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)))
          (baseChangeMap f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)))
          (by
            rw [← baseChangeMap_comp]
            congr 1
            ext
            simpa using c.w (homOfLE hjj').op) ∧
        e.hom.app Fj ≫
            (Scheme.Modules.moduleBaseChange f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op))).map φj' =
          φ ≫ e.hom.app Gj) := by
  classical
  constructor
  · intro M hM hMq
    obtain ⟨j, hij, U, _, _, D, hD, hDq, ⟨eD⟩⟩ :=
      exists_finitePresentation_local_descent_datum R c hc i f M hM hMq
    let p := baseChangeMap f
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (c.π.app (op i)))
      (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
    have hU := Scheme.zariskiTopology_le_fpqcTopology _ U.mem_grothendieckTopology
    obtain ⟨N, hNq, ⟨eN⟩⟩ :=
      exists_isQuasicoherent_toDescentData_iso_of_mem_fpqcTopology U.f hU D hDq
    have hN := isFinitePresentation_of_toDescentData_iso_of_isQuasicoherent
      U.f hU D N hNq ⟨eN⟩ hD
    exact ⟨j, hij, N, hN, hNq,
      nonempty_tensorPullback_iso_of_local_datum p U D N M eN eD⟩
  · intro j hij Fj Gj hF hFq hG hGq φ
    have hlocal := exists_finitePresentation_local_map_datum R c hc i f j hij Fj Gj
      hF hFq hG hGq φ
    rcases hlocal with ⟨j', hjj', hlocal⟩
    dsimp only at hlocal
    rcases hlocal with ⟨e, he, U, _, _, ψ, hψ⟩
    let V := U.pullback₁ (baseChangeMap f
      (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
      (T' := Over.mk (c.π.app (op i)))
      (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op)))
    let FF := (openCoverFullyFaithful U).some
    let α := FF.preimage ψ
    have hα := hψ α (FF.map_preimage ψ)
    refine ⟨j', hjj', α, e, he, ?_⟩
    apply (openCoverFullyFaithful V).some.map_injective
    exact Pseudofunctor.DescentData.hom_ext hα

end AlgebraicGeometry
