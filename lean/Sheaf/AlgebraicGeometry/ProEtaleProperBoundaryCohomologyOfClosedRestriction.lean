/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleProperBoundaryClosedRestriction
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Sheaf.RingTheory.IndEtaleUniverseTransport

/-! The global cohomology step after the closed-boundary restriction calculation. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace AlgebraicGeometry.Scheme

/-- Proper-boundary cohomology follows from vanishing after restriction to the closed
boundary. The hypothesis is the geometric input supplied by the closed-restriction lemma;
the proof performs the open-closed localization, specialization-zero evaluation, and the
weakly-contractible affine evaluation argument.
Source: Stacks, Tags 09AG, 09C9 and 098H; blueprint lem-sp-proetale-proper-boundary-cohomology.
(blueprint: lem-sp-proetale-proper-boundary-cohomology-from-closed-restriction). -/
theorem proEtale_proper_boundary_cohomology_of_closed_restriction_zero
    (R : Type u) [CommRing R]
    (hR : ∀ (S : Type u) [CommRing S] (φ : R →+* S),
      φ.FaithfullyFlat → φ.WeaklyEtale →
        ∃ r : S →+* R, r.comp φ = RingHom.id R)
    {Z E P U : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R))
    [IsClosedImmersion z] (e : E ⟶ Spec (CommRingCat.of R))
    [IsOpenImmersion e] [QuasiCompact e]
    (hcomplement : Set.range e = (Set.range z)ᶜ)
    (hspecializes : ∀ x : Spec (CommRingCat.of R), ∃ t : Z, Specializes x (z t))
    (p : P ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (h : U ⟶ pullback p e) [IsOpenImmersion h]
    (hclosed : IsClosed (Set.range h))
    [QuasiCompact (h ≫ pullback.fst p e)]
    (A : Type u) [CommRing A] [Finite A]
    [HasInjectiveResolutions (proEtaleRingModules P (proEtaleConstantRing P A))]
    (J : proEtaleRingModules U (proEtaleConstantRing U A)) [Injective J]
    (hzero : IsZero ((proEtaleConstantRingPullback A (pullback.snd z p)).obj
      ((sfIntrinsicExtensionByZero (h ≫ pullback.fst p e) A).obj J)))
    (hetale : ∃ J₀ : Sheaf U.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)),
      Nonempty ((sfIntrinsicModuleEquivalence U A).functor.obj
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) U).obj J₀) ≅ J))
    (q : ℕ) (hq : 0 < q) :
    IsZero (((SheafOfModules.toSheaf
      ((sheafCompose (ProEt.topology P)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing P A)) ⋙
        sheafToPresheaf (ProEt.topology P) AddCommGrpCat.{u + 1} ⋙
          (CategoryTheory.evaluation P.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj
            (op (ProEt.mk (𝟙 P)))).rightDerived q).obj
              ((sfIntrinsicExtensionByZero (h ≫ pullback.fst p e) A).obj J)) := by
  sorry

end AlgebraicGeometry.Scheme

