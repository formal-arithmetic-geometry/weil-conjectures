/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseCorrespondenceData
import WeilConjectures.AlgebraicGeometry.Galois.GaloisFiniteTensorScalarBraided
import WeilConjectures.AlgebraicGeometry.Galois.GaloisFiniteTensorScalarScalar

/-! # Tensor and scalar comparisons for finite Galois modules -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.Scheme

/-- Tensor and scalar compatibility of a normalized finite module correspondence.
Source: Stacks Project, Tag 0DV5 (3); proof steps 4 and 5 of
`cor-galois-lisse-representations`.
(blueprint: new-e4-galois-finite-tensor-scalar).

Proof: the monoidal structure on the lisse category and its braided sheaf inclusion are
supplied as hypotheses. The source lisse tensor/scalar theorem gives the canonical stalk
comparisons with their germ formulas. Transport the tensor stalk comparison
through `d.τ`; the evaluation-action formula makes it equivariant, since both actions on
a pure tensor send `s ⊗ t` to `g(s) ⊗ g(t)`. The unit is the constant coefficient sheaf,
identified with the trivial representation by `hunit`. The associativity, symmetry and
unit identities follow on pure germs from the module identities, so the two inclusions
are braided. The actual lisse scalar-extension functor `B` and its underlying-sheaf
comparison `α` are supplied as hypotheses. On stalks the scalar-extension
comparison supplied by `scalarStalk`, normalized by `scalarStalkGerm` at this exact
geometric point, is equivariant because it sends `a ⊗ s` to `a ⊗ g(s)`; transport this map through
`d.τ` to obtain `β`. The supplied natural composite comparison `c` satisfies the
section formula `hc`. Its stalk comparison therefore sends `b ⊗ (a ⊗ s)` to
`b g(a) ⊗ s`. This is also the result of the two scalar fibre comparisons, giving the
remaining representation composite identity. Pure tensors generate the presheaf tensor
modules; sheafification extends these equalities. The two halves are
`galois_finite_tensor_scalar_braided` and `galois_finite_tensor_scalar_scalar`. -/
theorem galois_finite_tensor_scalar
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
    (ModuleCat.ringExtensionTmul.{u + 1, u + 1} (g.comp f) _ (b * g a) z)) :
    (∀ (R : Type (u + 1)) [CommRing R] [Finite R]
      (m : MonoidalCategory (LisseModuleSheafCategory Y R))
      (b : @BraidedCategory (LisseModuleSheafCategory Y R) _ m),
      Nonempty (@Functor.Braided (LisseModuleSheafCategory Y R) _ m b
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) _
        (Sheaf.monoidalCategory Y.smallEtaleTopology (ModuleCat.{u + 1} R))
        (Sheaf.braidedCategory Y.smallEtaleTopology (ModuleCat.{u + 1} R))
        (ObjectProperty.ι _)) →
      Nonempty (@Functor.Braided (LisseModuleSheafCategory Y R) _ m b
        (Rep.{u + 1} R G) _ _ _ ((d.e R).functor ⋙ ObjectProperty.ι _))) ∧
      (∃ (β : ∀ (R S : Type (u + 1))
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
  exact ⟨galois_finite_tensor_scalar_braided y G d heval hunit,
    galois_finite_tensor_scalar_scalar y G d heval hunit scalarStalk scalarStalkGerm B α c hc⟩

end AlgebraicGeometry.Scheme
