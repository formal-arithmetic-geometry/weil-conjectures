/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GaloisFiniteModuleLiftEquivalence

/-! # Normalized action of the finite module lift -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open scoped FintypeCatDiscrete
namespace AlgebraicGeometry.Scheme

/-- The action identity for an equivalence and stalk comparison carrying the compatibility
data exported by `galois_finite_module_lift_equivalence`; arbitrary equivalences are not
admitted.

Proof: introduce the fixed carrier witness `h` and rewrite the left side with `hκ`,
then use `hq` to move the representation action to the `E`-action. Apply `hτ` and
rewrite the right side with `hκ`. This closes the action identity directly.
Source: Stacks Project, Tag 0DV5 (3), proof step 3.
(blueprint: new-c7-galois-finite-module-lift-action). -/
theorem galois_finite_module_lift_action
    {Y : Scheme.{u}} [ConnectedSpace Y] [HasFiniteProducts Y.FLC]
    [PreservesFiniteProducts (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)))]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (E : Y.FLC ≌ ContAction FintypeCat.{u} G)
    (γ : G ≃ₜ* Aut (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)) ⋙
      (pointSmallEtale y).sheafFiber (A := Type (u + 1))))
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
    (e : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
      LisseModuleSheafCategory Y R ≌ galoisFiniteRepresentations R G)
    (τM : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
      (e R).functor ⋙ ObjectProperty.ι _ ⋙
        forget₂ (Rep.{u + 1} R G) (ModuleCat.{u + 1} R) ≅
      ObjectProperty.ι _ ⋙ (pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} R))
    (h : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
      ∀ (F : LisseModuleSheafCategory Y R),
        IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R F.obj))
    (q : ∀ (R : Type (u + 1)) [Ring R] [Finite R]
      (F : LisseModuleSheafCategory Y R),
      ((e R).functor.obj F).obj.V →
        ULift.{u + 1} (E.functor.obj
          (galoisUnderlyingFLC R F.obj (h R F))).obj.V)
    (hκ : ∀ (R : Type (u + 1)) [Ring R] [Finite R]
      (F : LisseModuleSheafCategory Y R)
      (z : ((e R).functor.obj F).obj.V),
      κ R F ((τM R).hom.app F z) =
        τ.hom.app (galoisUnderlyingFLC R F.obj (h R F)) (q R F z))
    (hq : ∀ (R : Type (u + 1)) [Ring R] [Finite R]
      (F : LisseModuleSheafCategory Y R) (g : G)
      (z : ((e R).functor.obj F).obj.V),
      q R F (((e R).functor.obj F).obj.ρ g z) =
        ⟨((E.functor.obj (galoisUnderlyingFLC R F.obj (h R F))).obj.ρ g).hom
          (q R F z).down⟩)
    : ∀ (R : Type (u + 1)) [Ring R] [Finite R] (F : LisseModuleSheafCategory Y R),
        ∃ h : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R F.obj),
          ∀ (g : G) (z : ((e R).functor.obj F).obj.V),
            κ R F ((τM R).hom.app F (((e R).functor.obj F).obj.ρ g z)) =
              (γ g).hom.app (galoisUnderlyingFLC R F.obj h)
                (κ R F ((τM R).hom.app F z))  := by
  intro R _ _ F
  refine ⟨h R F, ?_⟩
  intro g z
  rw [hκ, hq, hτ, hκ]

end AlgebraicGeometry.Scheme
