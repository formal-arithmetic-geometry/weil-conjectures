/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalization
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality
public import WeilConjectures.SixFunctors.Etale.Derived.DoubleDualCompat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry
open Scheme
namespace Etale

set_option linter.unusedVariables false in
/-- Faithfulness of algebraic-closure pullback on the ordinary finite-coefficient derived category.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-
duality/sec-verdier-biduality/sk-thm-pd-verdier-duality/det-pd-biduality-coefficients.proof.md`,
Proof (i), finite-base-field paragraph (blueprint:
`lem-sf-finite-ring-geometric-duality-finite-field`).

The morphism `g` is a base change of the surjective morphism `Spec k̄ ⟶ Spec k`, so it is
surjective and `g^*` is exact and reflects isomorphisms. Hence `D(g^*)` reflects isomorphisms,
as it commutes with homology, and so does `Lg^* ≅ D(g^*)`. The hypotheses on `p`, `ell` and `A`
are not needed. -/
theorem finiteField_biduality_algebraicClosure_pullback_reflects
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpell : p ≠ ell)
    (k : Type u) [Field k] [Finite k] [CharP k p]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, 1 ≤ r ∧ ∀ x : A, (ell ^ r) • x = 0)
    {T : Scheme.{u}} (a : T ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    let kbar := AlgebraicClosure k
    let b := Spec.map (CommRingCat.ofHom (algebraMap k kbar))
    let X := pullback a b
    let g : X ⟶ T := pullback.fst a b
    (L((g)^*[ModuleCat.{u + 1} A])).ReflectsIsomorphisms := by
  intro kbar b X g
  have hg : Surjective g := MorphismProperty.pullback_fst (P := @Surjective) _ _ inferInstance
  have := Etale.reflectsIsomorphisms_upperStar_of_surjective A g hg.surj
  have : (D((g)^*[ModuleCat.{u + 1} A])).ReflectsIsomorphisms :=
    ⟨fun f _ ↦ (Functor.jointlyReflectIsomorphisms_mapDerivedCategory
      (F := fun _ : Unit ↦ (g)^*[ModuleCat.{u + 1} A])
      ⟨fun f h ↦ have := h (); isIso_of_reflects_iso f ((g)^*[ModuleCat.{u + 1} A])⟩).isIso
      f⟩
  exact reflectsIsomorphisms_of_iso (leftDerivedUpperStarIsoMapDerivedCategory _ g).symm

end Etale
end AlgebraicGeometry
