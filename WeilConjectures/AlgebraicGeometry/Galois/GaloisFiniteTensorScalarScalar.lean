/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseCorrespondenceData
import WeilConjectures.AlgebraicGeometry.Galois.GaloisFiniteScalarBetaExists
import WeilConjectures.AlgebraicGeometry.Galois.GaloisFiniteScalarBetaComposite

/-! # Scalar-extension component of the finite Galois comparison -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.Scheme

/-- Scalar extension part of the finite Galois comparison: given the sheafified lisse
scalar-extension functors `B`, their underlying-sheaf comparisons `α`, the stalk comparison
`scalarStalk` with its germ formula, and composite comparisons `c` satisfying the section
identity `hc`, there are natural representation comparisons `β` satisfying the
representation composite identity for these same `c`.
Source: Stacks Project, Tag 0DV5 (3); the blueprint, `cor-galois-lisse-representations`,
proof paragraph "Base change of coefficients".
(blueprint: new-d9-galois-finite-tensor-scalar-scalar).

Proof: for `a ∈ S` the map `s ↦ a ⊗ s` from `F` to the sheafified scalar extension is a map
of finite locally constant sheaves of sets, so its stalk commutes with every `σ ∈ G`
(`heval`). By `scalarStalkGerm` the stalk comparison `scalarStalk` sends `a ⊗ germ(s)` to the
germ of `a ⊗ s`; the elements `a ⊗ m` generate `S ⊗_R F_ȳ`, so the comparison is equivariant
for the induced action `a ⊗ m ↦ a ⊗ σ m`. Compose it with `α` and transport through the
normalized fibre comparisons `d.τ` to obtain `β`, natural in `F`. For `R → S → T`, the
section formula `hc` says that the stalk of `c` sends `b ⊗ (a ⊗ s)` to `b g(a) ⊗ s`, which is
also the value of `ModuleCat.ringExtensionComp` after the two comparisons `β`; the pure
tensors generate, so the representation composite identity holds. -/
theorem galois_finite_tensor_scalar_scalar
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (d : GaloisLisseFiniteData y G)
    (heval : galoisFiniteEvaluationAction y G d) (hunit : galoisFiniteUnit y G d)
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
    (c : ∀ (R S T : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S] [Ring T] [Finite T] (f :
      R →+* S)
    (g : S →+* T), B R S f ⋙ B S T g ≅ B R T (g.comp f))
    (hc : ∀
    (R S T : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S] [Ring T] [Finite T] (f : R →+* S)
    (g : S →+* T), ∀ (F :
    LisseModuleSheafCategory Y R) (U : Y.Etale) (a : S) (b : T) (z : F.obj.obj.obj (op U)), ((α R T
    (g.comp f)).hom.app F).hom.app (op U) (((c R S T f g).hom.app F).hom.hom.app (op U) (((α S T
      g).inv.app ((B
    R S f).obj F)).hom.app (op U) (((toSheafification Y.smallEtaleTopology (ModuleCat.{u + 1}
    T)).app (((B R S f).obj F).obj.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} g)).app (op U)
    (ModuleCat.ringExtensionTmul.{u + 1, u + 1} g _ b (((α R S f).inv.app F).hom.app (op U)
    (((toSheafification Y.smallEtaleTopology (ModuleCat.{u + 1} S)).app (F.obj.obj ⋙
    ModuleCat.ringExtendScalars.{u + 1, u + 1} f)).app (op U) (ModuleCat.ringExtensionTmul.{u + 1, u
    + 1} f _ a z))))))) = ((toSheafification Y.smallEtaleTopology (ModuleCat.{u + 1} T)).app
    (F.obj.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} (g.comp f))).app (op U)
    (ModuleCat.ringExtensionTmul.{u + 1, u + 1} (g.comp f) _ (b * g a) z))
    : (∃ (β : ∀ (R S : Type (u + 1))
    [Ring R] [Finite R] [Ring S] [Finite S] (f : R →+* S), B R S f ⋙ (d.e S).functor ⋙
    ObjectProperty.ι _ ≅ (d.e R).functor ⋙ ObjectProperty.ι _ ⋙ (Rep.repIsoAction R G).functor ⋙
    (ModuleCat.ringExtendScalars.{u + 1, u + 1} f).mapAction G ⋙ (Rep.repIsoAction S G).inverse), ∀
    (R S T : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S] [Ring T] [Finite T] (f : R →+* S)
    (g : S →+* T), (∀ (F : LisseModuleSheafCategory Y R)
    (z : ((d.e T).functor.obj ((B S T g).obj ((B R S f).obj F))).obj.V), ((β R T (g.comp f)).hom.app
    F).hom (((d.e T).functor.map ((c R S T f g).hom.app F)).hom.hom z) =
      (ModuleCat.ringExtensionComp.{u + 1, u
    + 1} f g).hom.app (ModuleCat.of R ((d.e R).functor.obj F).obj.V)
    ((ModuleCat.ringExtendScalars.{u + 1, u + 1} g).map ((forget₂ (Rep.{u + 1} S G) (ModuleCat.{u +
    1} S)).map ((β R S f).hom.app F)) (((β S T g).hom.app ((B R S f).obj F)).hom z)))) := by
  classical
  have _ := hunit
  obtain ⟨β, hβ⟩ := galois_finite_scalar_beta_exists y G d heval scalarStalk
    scalarStalkGerm B α
  exact ⟨β, galois_finite_scalar_beta_composite y G d scalarStalk
    scalarStalkGerm B α c hc β hβ⟩

end AlgebraicGeometry.Scheme
