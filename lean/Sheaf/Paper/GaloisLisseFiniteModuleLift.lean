/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.Paper.GaloisLisseRepresentationData
import Sheaf.CategoryTheory.EquivalenceInternalModule
import WeilConjectures.AlgebraicGeometry.LisseModuleSheaves

/-! # GaloisLisseFiniteModuleLift

Source: the proof of `cor-galois-lisse-representations`. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open scoped TensorProduct FintypeCatDiscrete
namespace AlgebraicGeometry.Scheme

/-- Lift a specified finite-set fibre equivalence to finite left modules.
Source: Stacks Project, Tag 0DV5 (3), proof; the proof of
`cor-galois-lisse-representations`, step 1.
Proof: identify lisse module sheaves with module objects using
`lisseToModuleObject_isIso_of_categories`. Rewrite the diagram axioms of
`ModuleObjectStruct` as the generalized-element axioms of `InternalModule` and
lift the set equivalence with `equivalence_induces_internalModules`.
Use `internalModules_finiteContAction` to obtain continuous finite modules,
flatten the two full subcategories, and lift the finite carrier to universe u+1.
The fibre comparison is linear because the transported addition and scalar maps
are their maps on stalks. The set and module stalks agree by the filtered-colimit
forgetful comparison, whose germ formula gives the stated kappa. Naturality of
the specified set comparison gives the evaluation-action formula.
(blueprint: lem-pod-galois-lisse-finite-module-lift). -/
theorem galois_lisse_finite_module_lift
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)] [IsTopologicalGroup G]
    (Φ : Y.FiniteEtale ≌ Y.FLC) (E : Y.FLC ≌ ContAction FintypeCat.{u} G)
    (γ : G ≃ₜ* Aut (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)) ⋙
      (pointSmallEtale y).sheafFiber (A := Type (u + 1))))
    (η : Φ.functor ⋙ ObjectProperty.ι _ ⋙
      (pointSmallEtale y).sheafFiber (A := Type (u + 1)) ≅
      FiniteEtale.fiber y ⋙ CategoryTheory.forget FintypeCat.{u} ⋙
        uliftFunctor.{u + 1, u})
    (τ : E.functor ⋙ forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u} ⋙
      CategoryTheory.forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1, u} ≅
      ObjectProperty.ι _ ⋙ (pointSmallEtale y).sheafFiber (A := Type (u + 1)))
    (hτ : ∀ (F : Y.FLC) (g : G) (z : ULift.{u + 1} (E.functor.obj F).obj.V),
      τ.hom.app F ⟨((E.functor.obj F).obj.ρ g).hom z.down⟩ =
        (γ g).hom.app F (τ.hom.app F z)) :
    ∃ (e : ∀ (Λ : Type (u + 1)) [Ring Λ] [Finite Λ],
        LisseModuleSheafCategory Y Λ ≌ galoisFiniteRepresentations Λ G)
      (τM : ∀ (Λ : Type (u + 1)) [Ring Λ] [Finite Λ],
        (e Λ).functor ⋙ ObjectProperty.ι _ ⋙
          forget₂ (Rep.{u + 1} Λ G) (ModuleCat.{u + 1} Λ) ≅
        ObjectProperty.ι _ ⋙ (pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} Λ)),
      galoisFiniteEvaluationAction y G ⟨γ, Φ, η, e, τM⟩ := by sorry

end AlgebraicGeometry.Scheme
