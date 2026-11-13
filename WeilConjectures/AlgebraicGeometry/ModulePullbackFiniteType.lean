/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Data.Fintype.EquivFin
import WeilConjectures.Mathlib.Topology.Category.TopCat.Opens

/-!
# Finite type is preserved by module pullback

## References

* [Stacks, Tag 01B6](https://stacks.math.columbia.edu/tag/01B6)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 600000 in
-- The over-site equivalences and tensor-pullback object require extra definitional reductions.
/-- For a morphism of schemes, the pullback of a finite type module is of finite type
(Stacks, Tag 01B6). The second conjunct records that the pullback of any epimorphism from
`free (ULift (Fin n))` over an open `V` is an epimorphism over `f⁻¹ V`. -/
theorem tensorPullback_isFiniteType (X Y : Scheme.{u}) (f : X ⟶ Y) (G : Y.Modules)
    [G.IsFiniteType] :
    ((tensorPullback f).obj G).IsFiniteType ∧
      ∀ (V : Y.Opens) (n : ℕ)
        (φ : SheafOfModules.free (R := Y.ringCatSheaf.over V) (ULift.{u} (Fin n)) ⟶
          G.over V),
        Epi φ →
          ∃ ψ : SheafOfModules.free
            (R := X.ringCatSheaf.over ((TopologicalSpace.Opens.map f.base).obj V))
            (ULift.{u} (Fin n)) ⟶
              ((tensorPullback f).obj G).over ((TopologicalSpace.Opens.map f.base).obj V),
            Epi ψ := by
  classical
  have hlocal : ∀ (V : Y.Opens) (n : ℕ)
      (φ : SheafOfModules.free (R := Y.ringCatSheaf.over V) (ULift.{u} (Fin n)) ⟶
        G.over V), Epi φ → ∃ ψ : SheafOfModules.free
          (R := X.ringCatSheaf.over ((TopologicalSpace.Opens.map f.base).obj V))
          (ULift.{u} (Fin n)) ⟶
            ((tensorPullback f).obj G).over ((TopologicalSpace.Opens.map f.base).obj V),
        Epi ψ := by
    intro V n φ hφ
    have := hφ
    let U : X.Opens := (TopologicalSpace.Opens.map f.base).obj V
    let f' := f ∣_ V
    let F := (overEquiv V).functor ⋙ pullback f' ⋙ (overEquiv U).inverse
    have hF : CategoryTheory.Limits.PreservesColimitsOfSize.{u, u} F := by
      dsimp [F]
      infer_instance
    let ε : (pullback f').obj (SheafOfModules.unit V.toScheme.ringCatSheaf) ≅
        SheafOfModules.unit U.toScheme.ringCatSheaf := by
      have : IsIso (SheafOfModules.pullbackObjUnitToUnit f'.toRingCatSheafHom) :=
        inferInstance
      exact asIso (SheafOfModules.pullbackObjUnitToUnit f'.toRingCatSheafHom)
    let η : SheafOfModules.unit (X.ringCatSheaf.over U) ≅
        F.obj (SheafOfModules.unit (Y.ringCatSheaf.over V)) :=
      (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm ≪≫
        (overEquiv U).inverse.mapIso
          (ε.symm ≪≫ (pullback f').mapIso
            (V.sheafOfModulesEquivOverUnit Y.ringCatSheaf).symm)
    let k : ((pullback f).obj G).restrict U.ι ≅
        (pullback f').obj (G.restrict V.ι) :=
      (restrictFunctorIsoPullback U.ι).app _ ≪≫ (pullbackComp U.ι f).app G ≪≫
        (pullbackCongr (morphismRestrict_ι f V).symm).app G ≪≫
        ((pullbackComp f' V.ι).symm).app G ≪≫
        (pullback f').mapIso ((restrictFunctorIsoPullback V.ι).app G).symm
    obtain ⟨adj⟩ := nonempty_tensorPullbackAdjunction f
    let c := adj.leftAdjointUniq (pullbackPushforwardAdjunction f)
    let e : F.obj (G.over V) ≅ ((tensorPullback f).obj G).over U :=
      (overEquiv U).inverse.mapIso
        ((pullback f').mapIso ((overFunctorEquiv V).app G) ≪≫ k.symm ≪≫
          (restrictFunctor U.ι).mapIso (c.app G).symm ≪≫
          ((overFunctorEquiv U).app ((tensorPullback f).obj G)).symm) ≪≫
        ((overEquiv U).unitIso.app _).symm
    refine ⟨(SheafOfModules.mapFreeIso F (ULift.{u} (Fin n)) η).hom ≫ F.map φ ≫ e.hom, ?_⟩
    infer_instance
  refine ⟨?_, hlocal⟩
  -- Assemble finite local generators over the inverse-image cover.
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData G
  have := hq
  have hgen (i : q.I) : (q.generators i).IsFiniteType := hq.isFiniteType i
  have hex (i : q.I) : ∃ (n : ℕ)
      (ψ : SheafOfModules.free
        (R := X.ringCatSheaf.over ((TopologicalSpace.Opens.map f.base).obj (q.X i)))
        (ULift.{u} (Fin n)) ⟶
          ((tensorPullback f).obj G).over ((TopologicalSpace.Opens.map f.base).obj (q.X i))),
        Epi ψ := by
    let inst : Fintype (q.generators i).I := Fintype.ofFinite _
    let n := Fintype.card (q.generators i).I
    let φ : SheafOfModules.free
        (R := Y.ringCatSheaf.over (q.X i)) (ULift.{u} (Fin n)) ⟶ G.over (q.X i) :=
      (SheafOfModules.freeFunctor.mapIso
        (Equiv.toIso (Equiv.ulift.trans (Fintype.equivFin (q.generators i).I).symm))).hom ≫
          (q.generators i).π
    have hφ : Epi φ := by
      dsimp [φ]
      infer_instance
    exact ⟨n, hlocal (q.X i) n φ hφ⟩
  choose n ψ hψ using hex
  let p : ((tensorPullback f).obj G).LocalGeneratorsData :=
    { I := q.I
      X := fun i ↦ (TopologicalSpace.Opens.map f.base).obj (q.X i)
      coversTop := fun W x hx ↦ by
        obtain ⟨V, a, ⟨i, ⟨b⟩⟩, hv⟩ := q.coversTop ⊤ (f.base x) (by trivial)
        let T := W ⊓ (TopologicalSpace.Opens.map f.base).obj V
        refine ⟨T, homOfLE inf_le_left, ⟨i, ⟨homOfLE ?_⟩⟩, ?_⟩
        · exact le_trans inf_le_right ((TopologicalSpace.Opens.map f.base).map b).le
        · exact ⟨hx, hv⟩
      generators := fun i ↦
        { I := ULift.{u} (Fin (n i))
          s := SheafOfModules.freeHomEquiv _ (ψ i)
          epi := by
            rw [Equiv.symm_apply_apply]
            exact hψ i } }
  have hp : p.IsFiniteType := by
    constructor
    intro i
    constructor
    exact inferInstanceAs (Finite (ULift.{u} (Fin (n i))))
  exact SheafOfModules.IsFiniteType.mk (M := (tensorPullback f).obj G) ⟨p, hp⟩


end AlgebraicGeometry.Scheme.Modules
