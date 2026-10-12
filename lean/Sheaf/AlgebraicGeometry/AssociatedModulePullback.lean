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
            ((ModuleCat.extendScalars g.appTop.hom).map u)) := by sorry

end
end AlgebraicGeometry
