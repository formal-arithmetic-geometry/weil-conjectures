module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Sheaf.AlgebraicGeometry.AssociatedModule
public import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.AssociatedModuleHom

/-!
# Pullback of an associated module sheaf

Source: Stacks Project, Modules, Lemma 01BJ (lemma-restrict-quasi-coherent)
(blueprint: lem-weil-pbc-associated-module-pullback).
-/

@[expose] public section

universe w

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry

namespace AlgebraicGeometry

noncomputable section

/-- Pullback of an associated module is associated to extension of scalars.
This is Stacks, Modules, Lemma 01BJ.  For each `R`-module `M` the morphism `θ M` is the
unique morphism `g^* F_M ⟶ F_{S ⊗_R M}` sending `g^* c_M(m)` to `c_{S ⊗_R M}(1 ⊗ m)`
(the first conjunct: a morphism equals `θ M` iff it satisfies this equation); each `θ M`
is an isomorphism, and the family is natural in `M`.
Proof: through the chain of natural bijections
`Hom(g^* F_M, H) ≃ Hom(F_M, g_* H) ≃ Hom_R(M, Γ(Y,H))`
`≃ Hom_S(S ⊗_R M, Γ(Y,H)) ≃ Hom(F_{S ⊗_R M}, H)`
(adjunction, universal property of the associated module, scalar extension, universal
property again), the map `θ M` corresponds to `id`, and co-Yoneda gives that it is an
isomorphism; uniqueness and naturality follow from the same universal properties
(blueprint: lem-weil-pbc-associated-module-pullback). -/
theorem associatedModule_pullback
    {X Y : Scheme.{w}} (g : Y ⟶ X) :
    let adj := Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction g)
    ∃ θ : (∀ M' : ModuleCat (X.presheaf.obj (op (⊤ : Opens (X : Type w)))),
      (Scheme.Modules.tensorPullback g).obj (associatedModule
        X.toLocallyRingedSpace.toSheafedSpace M') ⟶
        associatedModule Y.toLocallyRingedSpace.toSheafedSpace
          ((ModuleCat.extendScalars g.appTop.hom).obj M')),
    (∀ (M' : ModuleCat (X.presheaf.obj (op (⊤ : Opens (X : Type w)))))
        (θ' : (Scheme.Modules.tensorPullback g).obj (associatedModule
          X.toLocallyRingedSpace.toSheafedSpace M') ⟶
          associatedModule Y.toLocallyRingedSpace.toSheafedSpace
            ((ModuleCat.extendScalars g.appTop.hom).obj M')),
        θ' = θ M' ↔
          ∀ m : M',
            θ'.val.app (op (⊤ : Opens (Y : Type w)))
                ((adj.unit.app (associatedModule
                  X.toLocallyRingedSpace.toSheafedSpace M')).app
                  ((⊤ : Opens (X : Type w)))
                  (associatedModuleCanonicalSection
                    X.toLocallyRingedSpace.toSheafedSpace M' m)) =
              associatedModuleCanonicalSection
                Y.toLocallyRingedSpace.toSheafedSpace
                ((ModuleCat.extendScalars g.appTop.hom).obj M')
                ((ModuleCat.ExtendRestrictScalarsAdj.Unit.map g.appTop.hom) m)) ∧
      (∀ M', IsIso (θ M')) ∧
      (∀ {M' N' : ModuleCat (X.presheaf.obj (op (⊤ : Opens (X : Type w))))}
        (u : M' ⟶ N'),
        (Scheme.Modules.tensorPullback g).map
            ((associatedModuleFunctor X.toLocallyRingedSpace.toSheafedSpace).map u) ≫
          θ N' =
        θ M' ≫
          (associatedModuleFunctor Y.toLocallyRingedSpace.toSheafedSpace).map
            ((ModuleCat.extendScalars g.appTop.hom).map u)) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    classical
    let adj := Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction g)
    let FX := associatedModuleFunctor X.toLocallyRingedSpace.toSheafedSpace
    let FY := associatedModuleFunctor Y.toLocallyRingedSpace.toSheafedSpace
    let L := Scheme.Modules.tensorPullback g
    let T := ModuleCat.extendScalars g.appTop.hom
    let A := FX ⋙ L
    let B := T ⋙ FY
    -- Both Hom sets map bijectively to the same R-linear maps on global sections.
    let p := fun (M : ModuleCat (X.presheaf.obj (op (⊤ : Opens X)))) (H : Y.Modules) =>
      (adj.homEquiv (FX.obj M) H).trans
        (Equiv.ofBijective _ (associatedModuleHom_bijective
          X.toLocallyRingedSpace.toSheafedSpace M ((Scheme.Modules.pushforward g).obj H)))
    let q := fun (M : ModuleCat (X.presheaf.obj (op (⊤ : Opens X)))) (H : Y.Modules) =>
      (Equiv.ofBijective _ (associatedModuleHom_bijective
        Y.toLocallyRingedSpace.toSheafedSpace (T.obj M) H)).trans
        ((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).homEquiv
          M (H.val.obj (op (⊤ : Opens Y))))
    let e := fun M H => (q M H).trans (p M H).symm
    have hp (M) (H : Y.Modules) (f : A.obj M ⟶ H) (m : M) :
        p M H f m = f.val.app (op (⊤ : Opens Y))
          ((adj.unit.app (FX.obj M)).app (⊤ : Opens X)
            (associatedModuleCanonicalSection X.toLocallyRingedSpace.toSheafedSpace M m)) := by
      simp only [p, Equiv.trans_apply, Equiv.ofBijective_apply, Adjunction.homEquiv_unit]
      rfl
    have hq (M) (H : Y.Modules) (f : B.obj M ⟶ H) (m : M) :
        q M H f m = f.val.app (op (⊤ : Opens Y))
          (associatedModuleCanonicalSection Y.toLocallyRingedSpace.toSheafedSpace (T.obj M)
            ((ModuleCat.ExtendRestrictScalarsAdj.Unit.map g.appTop.hom) m)) := by
      simp only [q, Equiv.trans_apply, Equiv.ofBijective_apply]
      rfl
    have he (M) (H : Y.Modules) (f : B.obj M ⟶ H) :
        p M H (e M H f) = q M H f := by
      exact (p M H).apply_symm_apply _
    have hn (M) (H H' : Y.Modules) (f : B.obj M ⟶ H) (h : H ⟶ H') :
        e M H' (f ≫ h) = e M H f ≫ h := by
      apply (p M H').injective
      rw [he]
      ext m
      change q M H' (f ≫ h) m = p M H' (e M H f ≫ h) m
      rw [hp, hq]
      change h.val.app _ (f.val.app _ _) = h.val.app _ ((e M H f).val.app _ _)
      exact congrArg (fun x => h.val.app (op (⊤ : Opens Y)) x)
        ((hq M H f m).symm.trans ((congrArg (fun t => t m) (he M H f)).symm.trans
          (hp M H (e M H f) m)))
    -- Transport the identity and recover its inverse by target naturality.
    let θ := fun M => e M (B.obj M) (𝟙 _)
    refine ⟨θ, ?_, ?_, ?_⟩
    · intro M f
      constructor
      · intro hf
        subst f
        intro m
        exact (hp M (B.obj M) (θ M) m).symm.trans
          ((congrArg (fun t => t m) (he M (B.obj M) (𝟙 _))).trans
            (hq M (B.obj M) (𝟙 _) m))
      · intro hf
        apply (p M (B.obj M)).injective
        rw [he]
        ext m
        exact (hp M (B.obj M) f m).trans ((hf m).trans (hq M (B.obj M) (𝟙 _) m).symm)
    · intro M
      let κ := (e M (A.obj M)).symm (𝟙 _)
      have hk : e M (A.obj M) κ = 𝟙 _ := (e M (A.obj M)).apply_symm_apply _
      have ht : θ M ≫ κ = 𝟙 _ := by
        exact (hn M (B.obj M) (A.obj M) (𝟙 _) κ).symm.trans
          ((congrArg (e M (A.obj M)) (Category.id_comp κ)).trans hk)
      have kt : κ ≫ θ M = 𝟙 _ := by
        apply (e M (B.obj M)).injective
        exact (hn M (A.obj M) (B.obj M) κ (θ M)).trans
          (by rw [hk, Category.id_comp])
      exact (show A.obj M ≅ B.obj M from ⟨θ M, κ, ht, kt⟩).isIso_hom
    · intro M N u
      -- Compare the two composites on the canonical generators.
      have hx (m : M) :
          (A.map u).val.app (op (⊤ : Opens Y))
              ((adj.unit.app (FX.obj M)).app (⊤ : Opens X)
                (associatedModuleCanonicalSection X.toLocallyRingedSpace.toSheafedSpace M m)) =
            (adj.unit.app (FX.obj N)).app (⊤ : Opens X)
              (associatedModuleCanonicalSection X.toLocallyRingedSpace.toSheafedSpace N (u m)) := by
        have h := congrArg (fun t => t.val.app (op (⊤ : Opens X))
            (associatedModuleCanonicalSection X.toLocallyRingedSpace.toSheafedSpace M m))
          (adj.unit_naturality (FX.map u))
        have hc := congrArg (fun t => t m)
          (associatedModuleCanonicalSection_natural X.toLocallyRingedSpace.toSheafedSpace u)
        change (FX.map u).val.app _
          (associatedModuleCanonicalSection X.toLocallyRingedSpace.toSheafedSpace M m) =
            associatedModuleCanonicalSection X.toLocallyRingedSpace.toSheafedSpace N (u m) at hc
        exact h.trans (congrArg (fun x => (adj.unit.app (FX.obj N)).app (⊤ : Opens X) x) hc)
      have hy (m : M) :
          (B.map u).val.app (op (⊤ : Opens Y))
              (associatedModuleCanonicalSection Y.toLocallyRingedSpace.toSheafedSpace (T.obj M)
                ((ModuleCat.ExtendRestrictScalarsAdj.Unit.map g.appTop.hom) m)) =
            associatedModuleCanonicalSection Y.toLocallyRingedSpace.toSheafedSpace (T.obj N)
              ((ModuleCat.ExtendRestrictScalarsAdj.Unit.map g.appTop.hom) (u m)) := by
        have hc := congrArg (fun t => t ((ModuleCat.ExtendRestrictScalarsAdj.Unit.map
            g.appTop.hom) m))
          (associatedModuleCanonicalSection_natural Y.toLocallyRingedSpace.toSheafedSpace
            (T.map u))
        have hu := congrArg (fun t => t m)
          ((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).unit_naturality u)
        exact hc.trans (congrArg
          (associatedModuleCanonicalSection Y.toLocallyRingedSpace.toSheafedSpace (T.obj N))
          hu.symm)
      change A.map u ≫ θ N = θ M ≫ B.map u
      apply (p M (B.obj N)).injective
      ext m
      change p M (B.obj N) (A.map u ≫ θ N) m =
        p M (B.obj N) (θ M ≫ B.map u) m
      rw [hp, hp]
      change (θ N).val.app _ ((A.map u).val.app _ _) =
        (B.map u).val.app _ ((θ M).val.app _ _)
      rw [hx]
      have ht (P : ModuleCat (X.presheaf.obj (op (⊤ : Opens X)))) (x : P) :
          (θ P).val.app (op (⊤ : Opens Y))
              ((adj.unit.app (FX.obj P)).app (⊤ : Opens X)
                (associatedModuleCanonicalSection X.toLocallyRingedSpace.toSheafedSpace P x)) =
            associatedModuleCanonicalSection Y.toLocallyRingedSpace.toSheafedSpace (T.obj P)
              ((ModuleCat.ExtendRestrictScalarsAdj.Unit.map g.appTop.hom) x) :=
        (hp P (B.obj P) (θ P) x).symm.trans
          ((congrArg (fun t => t x) (he P (B.obj P) (𝟙 _))).trans
            (hq P (B.obj P) (𝟙 _) x))
      rw [ht, ht]
      exact (hy m).symm

end
end AlgebraicGeometry
