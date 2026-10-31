/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Galois.GaloisFiniteScalarUnderlying
import WeilConjectures.AlgebraicGeometry.Galois.GaloisFiniteScalarAction

/-! # Lifting the normalized scalar comparison to representations -/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.Scheme

private noncomputable def liftScalarRepNatIso
    {C : Type v} [Category.{w} C] {R : Type (u + 1)} [Ring R]
    {G : Type u} [Group G] (P Q : C ⥤ Rep.{u + 1} R G)
    (θ : P ⋙ forget₂ (Rep.{u + 1} R G) (ModuleCat R) ≅
      Q ⋙ forget₂ (Rep.{u + 1} R G) (ModuleCat R))
    (hθ : ∀ (F : C) (g : G) (z : (P.obj F).V),
      (θ.hom.app F) ((P.obj F).ρ g z) = (Q.obj F).ρ g ((θ.hom.app F) z)) :
    P ≅ Q :=
  NatIso.ofComponents
    (fun F ↦ Rep.mkIso
      { (θ.app F).toLinearEquiv with
        isIntertwining' g := by ext z; exact hθ F g z })
    (fun {F H} φ ↦ by
      apply (forget₂ (Rep.{u + 1} R G) (ModuleCat R)).map_injective
      exact θ.hom.naturality φ)

/-- The scalar comparison lifts to a natural representation isomorphism with the exact
underlying normalization used below. Source: Stacks 0DV5 (3), blueprint
`cor-galois-lisse-representations`, base change of coefficients.
(blueprint: new-w8-galois-scalar-beta-exists).

Proof: the four-factor underlying comparison is a natural linear isomorphism.
The scalar-action lemma makes each component an intertwiner. Its inverse is also
an intertwiner by conjugation. These component representation isomorphisms are natural,
since the representation forgetful functor is faithful. Their underlying linear maps
are the original normalized comparison by construction. -/
theorem galois_finite_scalar_beta_exists
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (d : GaloisLisseFiniteData y G)
    (heval : galoisFiniteEvaluationAction y G d)
    (scalarStalk : ∀ (R S : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S]
      (f : R →+* S),
      letI : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
        ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
      letI : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} S) :=
        ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
      (pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} R) ⋙
        ModuleCat.ringExtendScalars.{u + 1, u + 1} f ≅
      (Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f :
        Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤
          Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} S)) ⋙
        (pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} S))
    (scalarStalkGerm : ∀ (R S : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S]
      (f : R →+* S),
      letI : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
        ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
      letI : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} S) :=
        ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
      ∀ (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
        (U : Y.Etale) (x : (pointSmallEtale y).fiber.obj U) (a : S)
        (s : F.obj.obj (op U)),
      ((scalarStalk R S f).hom.app F)
        (ModuleCat.ringExtensionTmul.{u + 1, u + 1} f _ a
          ((pointSmallEtale y).toPresheafFiber U x F.obj s)) =
        (pointSmallEtale y).toPresheafFiber U x
          ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f).obj F).obj
          ((toSheafify Y.smallEtaleTopology
            (F.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} f)).app (op U)
            (ModuleCat.ringExtensionTmul.{u + 1, u + 1} f _ a s)))
    (B : ∀ (R S : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S], (R →+* S) →
      (LisseModuleSheafCategory Y R ⥤ LisseModuleSheafCategory Y S))
    (α : ∀ (R S : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S] (f : R →+* S),
      B R S f ⋙ ObjectProperty.ι _ ≅ ObjectProperty.ι _ ⋙
        Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f)
    : ∃ (β : ∀ (R S : Type (u + 1))
      [Ring R] [Finite R] [Ring S] [Finite S] (f : R →+* S),
      B R S f ⋙ (d.e S).functor ⋙ ObjectProperty.ι _ ≅
        (d.e R).functor ⋙ ObjectProperty.ι _ ⋙ (Rep.repIsoAction R G).functor ⋙
          (ModuleCat.ringExtendScalars.{u + 1, u + 1} f).mapAction G ⋙
          (Rep.repIsoAction S G).inverse),
      ∀ (R S : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S]
        (f : R →+* S) (F : LisseModuleSheafCategory Y R),
        (forget₂ (Rep.{u + 1} S G) (ModuleCat S)).map ((β R S f).hom.app F) =
          (galoisFiniteScalarUnderlying d R S f (B R S f) (α R S f)
            (scalarStalk R S f)).hom.app F := by
  classical
  let β (R S : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S]
      (f : R →+* S) :=
    liftScalarRepNatIso
      (B R S f ⋙ (d.e S).functor ⋙ ObjectProperty.ι _)
      ((d.e R).functor ⋙ ObjectProperty.ι _ ⋙ (Rep.repIsoAction R G).functor ⋙
        (ModuleCat.ringExtendScalars.{u + 1, u + 1} f).mapAction G ⋙
        (Rep.repIsoAction S G).inverse)
      (galoisFiniteScalarUnderlying d R S f (B R S f) (α R S f) (scalarStalk R S f))
      (galois_finite_scalar_action y G d heval scalarStalk scalarStalkGerm B α R S f)
  exact ⟨β, fun R S _ _ _ _ f F ↦ rfl⟩

end AlgebraicGeometry.Scheme
