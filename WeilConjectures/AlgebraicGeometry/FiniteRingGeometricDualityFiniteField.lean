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
public import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.FiniteFieldBidualityBaseChange
import WeilConjectures.AlgebraicGeometry.FiniteFieldBidualityReflects

/-!
# Finite-field geometric Verdier biduality for finite coefficients

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/
sec-verdier-biduality/sk-thm-pd-verdier-duality/det-pd-biduality-coefficients.proof.md`,
Proof (i), finite-base-field paragraph (blueprint:
`lem-sf-finite-ring-geometric-duality-finite-field`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

/--
Finite-field geometric Verdier biduality for an arbitrary finite coefficient ring.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/
sec-verdier-biduality/sk-thm-pd-verdier-duality/det-pd-biduality-coefficients.proof.md`,
Proof (i), finite-base-field paragraph (blueprint:
`lem-sf-finite-ring-geometric-duality-finite-field`).

Proof (statement node, postponed here):
1. If the coefficient ring is zero, every unital module is zero; if the scheme is empty,
   the empty covering forces every module sheaf to have only its zero section. In either
   case the derived category is zero and the evaluation transpose is the unique identity.
2. Choose an algebraic closure of the finite field. Every element lies in a finite field,
   so the finite-field power-cardinality lemma makes its minimal polynomial divide
   `X^Q - X`, whose derivative is `-1`; hence the extension is separable algebraic.
   The additive exponent of the nonzero coefficient ring divides `ell ^ r`, so it is
   prime to the characteristic and invertible over the base and its algebraic closure.
3. For the base change `g : T ×_k kbar ⟶ T`, separated finite type is preserved by
   base change, and finite type over a field is Noetherian. The pullback of `L` is
   therefore bounded constructible with finite Tor amplitude by the stratified-perfect
   calculus, with the same arbitrary finite coefficient ring.
4. The evaluation-compatible field-extension comparison supplies the canonical isomorphism
   `theta_L : g^* D_T D_T L ≅ D_Tbar D_Tbar (g^* L)` and the actual identity
   `theta_L ≫ delta_(g^*L) = g^*(delta_L)`, using the Verdier duality and evaluation
   constructions recorded in `verdierDual` and `verdierDualDoubleDual`.
5. Algebraically closed geometric duality makes `delta_(g^*L)` an isomorphism. Thus
   `g^*(delta_L)` is an isomorphism by the identity in step 4.
6. The algebraic-closure map is fpqc, and its base change `g` is fpqc and surjective.
   Pullback of ordinary constant-coefficient module sheaves is faithful and exact, and
   its derived functor is the termwise triangulated functor.
7. Applying this functor to a cone of `delta_L` gives an acyclic cone. Exactness commutes
   with cohomology, and faithfulness shows every cohomology object of the original cone
   is zero. The acyclic-cone criterion in the derived localization then makes `delta_L`
   an isomorphism. No constructibility or boundedness assumption on the cone is used.
-/
theorem isIso_verdierDualDoubleDual_app_finiteField
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpell : p ≠ ell)
    (k : Type u) [Field k] [Finite k] [CharP k p]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, 1 ≤ r ∧ ∀ x : A, (ell ^ r) • x = 0)
    {T : Scheme.{u}} (a : T ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    {L : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (hL : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T L) :
    letI : HasCompactification a := (NagataCompactification a).hasCompactification
    IsIso ((verdierDualDoubleDual A a).app L) := by
  dsimp
  let kbar := AlgebraicClosure k
  let b := Spec.map (CommRingCat.ofHom (algebraMap k kbar))
  let X := pullback a b
  let g : X ⟶ T := pullback.fst a b
  letI : HasCompactification a := (NagataCompactification a).hasCompactification
  letI : (L((g)^*[ModuleCat.{u + 1} A])).ReflectsIsomorphisms :=
    finiteField_biduality_algebraicClosure_pullback_reflects p ell hpell k A hA a
  have hmap := finiteField_biduality_baseChange p ell hpell k A hA a hL
  letI : IsIso ((L((g)^*[ModuleCat.{u + 1} A])).map
      ((verdierDualDoubleDual A a).app L)) := hmap
  exact isIso_of_reflects_iso ((verdierDualDoubleDual A a).app L)
    (L((g)^*[ModuleCat.{u + 1} A]))

end Etale

end AlgebraicGeometry
