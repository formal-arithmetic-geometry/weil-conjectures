/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseCorrespondenceData
public import WeilConjectures.CategoryTheory.InternalModule.InternalModule
public import WeilConjectures.CategoryTheory.Finite.FiniteContinuousModule
public import Mathlib.Algebra.Category.ModuleCat.Ulift
import WeilConjectures.AlgebraicGeometry.GaloisFiniteModuleLiftEquivalence
import WeilConjectures.AlgebraicGeometry.GaloisFiniteModuleLiftAction

/-! # Finite module lifting of the Galois fibre equivalence -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.Scheme

/-- Lift the finite-set fibre equivalence to finite modules, with its evaluation action.
Source: Stacks Project, Tag 0DV5 (3); proof steps 1 and 3 of
`cor-galois-lisse-representations`.
(blueprint: new-e4-galois-finite-module-lift).

Proof: identify a lisse finite-module sheaf with its finite locally constant underlying
sheaf of sets and its addition, zero, negation and scalar maps, using
`lisseToModuleObject_isIso_of_categories`. The supplied equivalence `L`, whose operations
and maps are normalized by `Lops` and `Lmaps`, replaces the ambient product diagrams by
internal modules in FLC. Transport this internal
module through `E` using `equivalence_induces_internalModules`; the inverse transport
recovers it. Apply `internalModules_finiteContAction` to obtain a finite module with
continuous linear action. The given equivalence `ε`, with its action comparison `εaction`,
raises this finite module to the required carrier universe without changing its operations
or action. Composing these equivalences gives the explicit `e`. The remaining stalk transport
component supplies the module-valued comparison for this fixed equivalence. The
underlying-fibre comparisons of the internal-module equivalences, `εaction`, and `τ`
give an underlying-set fibre
isomorphism. Naturality on the two product projections identifies its product comparison
with the pair of its components. Naturality on addition therefore gives preservation of
addition; the terminal comparison gives zero, while naturality on negation and each
scalar operation gives their preservation. The supplied module-stalk comparison is the
filtered-colimit comparison on germs, so it respects these same operations. Composing its
inverse gives the R-linear isomorphism `τM`; all component comparisons are natural.
Its action formula follows from `hτ` and the equivariant comparisons of the transported
finite actions: the representation action, after every underlying comparison, is exactly
the action used in `hτ`.
The supplied comparison `κ` is normalized on every germ by `κgerm`. Filtered-colimit
comparison and this normalization identify the induced underlying-fibre comparison with
`κ` composed with `τM`. Thus the resulting action agrees with evaluation through this
same canonical `κ`. -/
theorem galois_finite_module_lift
    {Y : Scheme.{u}} [ConnectedSpace Y] [HasFiniteProducts Y.FLC]
    [PreservesFiniteProducts (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)))]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (Φ : Y.FiniteEtale ≌ Y.FLC) (E : Y.FLC ≌ ContAction FintypeCat.{u} G)
    (γ : G ≃ₜ* Aut (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)) ⋙
      (pointSmallEtale y).sheafFiber (A := Type (u + 1))))
    (η : Φ.functor ⋙ ObjectProperty.ι _ ⋙
      (pointSmallEtale y).sheafFiber (A := Type (u + 1)) ≅
      FiniteEtale.fiber y ⋙ CategoryTheory.forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1, u})
    (τ : E.functor ⋙ forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u} ⋙
      CategoryTheory.forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1, u} ≅
      ObjectProperty.ι _ ⋙ (pointSmallEtale y).sheafFiber (A := Type (u + 1)))
    (hτ : ∀ (F : Y.FLC) (g : G) (z : ULift.{u + 1} (E.functor.obj F).obj.V),
      τ.hom.app F ⟨((E.functor.obj F).obj.ρ g).hom z.down⟩ =
        (γ g).hom.app F (τ.hom.app F z))
    (κ : ∀ (R : Type (u + 1)) [Ring R] [Finite R] (F : LisseModuleSheafCategory Y R),
      (((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} R)).obj F.obj) ≃
        (((pointSmallEtale y).sheafFiber (A := Type (u + 1))).obj
          (galoisUnderlyingSetSheaf R F.obj)))
    (κgerm : ∀ (R : Type (u + 1)) [Ring R] [Finite R] (F : LisseModuleSheafCategory Y R)
      (U : Y.Etale) (x : (pointSmallEtale y).fiber.obj U) (s : F.obj.obj.obj (op U)),
      κ R F ((pointSmallEtale y).toPresheafFiber U x F.obj.obj s) =
        (pointSmallEtale y).toPresheafFiber U x (galoisUnderlyingSetSheaf R F.obj).obj s)
    (L : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
      LambdaModuleObject Y R ≌ InternalModule R Y.FLC)
    (Lops : ∀ (R : Type (u + 1)) [Ring R] [Finite R] (A : LambdaModuleObject Y R),
      let I := ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y))
      let X : Y.FLC := ⟨A.sheaf, A.isFLC⟩
      ((L R).functor.obj A).X = X ∧
      HEq ((L R).functor.obj A).add
        (I.preimage (X := X ⨯ X) (Y := X) (prodComparison I X X ≫ A.str.add)) ∧
      HEq ((L R).functor.obj A).zero
        (I.preimage (X := ⊤_ Y.FLC) (Y := X) (terminalComparison I ≫ A.str.zero)) ∧
      HEq ((L R).functor.obj A).neg (I.preimage (X := X) (Y := X) A.str.neg) ∧
      ∀ r, HEq (((L R).functor.obj A).smul r)
        (I.preimage (X := X) (Y := X) (A.str.smul r)))
    (Lmaps : ∀ (R : Type (u + 1)) [Ring R] [Finite R]
      (A B : LambdaModuleObject Y R) (f : A ⟶ B),
      HEq (((L R).functor.map f).val).hom f.hom)
    (ε : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
      FiniteContinuousModule.{u + 1, u, u} R G ≌ galoisFiniteRepresentations R G)
    (εaction : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
      Nonempty ((ε R).functor ⋙ ObjectProperty.ι _ ⋙ (Rep.repIsoAction R G).functor ≅
        ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ (Rep.repIsoAction R G).functor ⋙
          (ModuleCat.uliftFunctor.{u + 1, u} R).mapAction G)) :
    ∃ (e : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
        LisseModuleSheafCategory Y R ≌ galoisFiniteRepresentations R G)
      (τM : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
        (e R).functor ⋙ ObjectProperty.ι _ ⋙
          forget₂ (Rep.{u + 1} R G) (ModuleCat.{u + 1} R) ≅
        ObjectProperty.ι _ ⋙ (pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} R)),
      let d : GaloisLisseFiniteData y G := ⟨γ, Φ, η, e, τM⟩
      ∀ (R : Type (u + 1)) [Ring R] [Finite R] (F : LisseModuleSheafCategory Y R),
        ∃ h : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R F.obj),
          ∀ (g : G) (z : ((d.e R).functor.obj F).obj.V),
            κ R F ((d.τ R).hom.app F (((d.e R).functor.obj F).obj.ρ g z)) =
              (d.γ g).hom.app (galoisUnderlyingFLC R F.obj h)
                (κ R F ((d.τ R).hom.app F z))   := by
  let e : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
      LisseModuleSheafCategory Y R ≌ galoisFiniteRepresentations R G :=
    fun R _ _ ↦ galoisFiniteModuleLiftEquivalence G E L ε R
  have h := galois_finite_module_lift_equivalence y G Φ E γ η τ hτ κ κgerm L Lops Lmaps ε
    εaction
  dsimp only at h
  obtain ⟨τM, hF, q, hκ, hq, _⟩ := h
  refine ⟨e, τM, ?_⟩
  exact galois_finite_module_lift_action y G E γ τ hτ κ e τM hF q hκ hq

end AlgebraicGeometry.Scheme
