/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
import Sheaf.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.SixFunctors.BaseChange.Derived
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Smooth base change for limits of smooth schemes

Source: Stacks Project, Tag 0F09, lemma-smooth-base-change-general
(blueprint: lem-kun-0f09).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Smooth base change along an inverse limit with affine transitions.
Source: Stacks Project, Tag 0F09, lemma-smooth-base-change-general
(blueprint: lem-kun-0f09).

Proof (following Tag 0F09):
1. For each stage form the cartesian base-change square of `f` along `η.app i`.
   The affine-transition permanence statement `lem-weil-pbc-affine-morphism-
   permanence` and the cone universal property identify its inverse limit with
   `sq`'s square, without an absolute quasi-compactness assumption on `S`.
2. Apply `sbc-thm-smooth-base-change` to each stage.  The smooth leg is
   `η.app i`, the quasi-compact and quasi-separated leg is `f`, and the
   coefficient sheaf is on the constant `X` corner.  This gives the degreewise
   finite-stage exchange isomorphisms.
3. Apply `lem-kun-0ezt` to the transposed system.  Its coefficient system on
   the constant corner is `H^q(E)` with identity transitions, so its colimit is
   `H^q(E)`; Step 1 supplies the limits and Step 2 supplies the stage maps.
4. Use `def-weil-pbc-hypercohomology-filtrations` and
   `lem-weil-pbc-truncation-couple-morphism` to obtain the two truncation exact
   couples.  `lem-kun-bc-map-on-cohomology` identifies their first-page map,
   and `lem-sp-couple-morphism` propagates it to every page.  The hypothesis
   `hE` supplies the torsion condition for every cohomology sheaf.
5. By `lemma-weil-pbc-hypercohomology-convergence` and
   `lemma-weil-pbc-exact-couple-abutment`, the page maps stabilize and induce
   maps on finite abutment filtrations.  Page induction and
   `lem-sp-finite-filtration-induction` make every cohomology map invertible,
   including the degrees below the lower bound.
6. Finally `lem-weil-pbc-derived-plus-iso-on-cohomology` turns the
   cohomology isomorphisms into the asserted isomorphism in `D⁺`.

The stalkwise torsion hypothesis is elementwise; no common annihilator is
assumed.  The empty scheme and zero complex satisfy it vacuously, and the
nonempty directed index is retained explicitly. -/
theorem smoothBaseChange_of_inverseLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (S : Scheme.{u})
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (η : D ⟶ (Functor.const Iᵒᵖ).obj S)
    (htrans : ∀ (i j : Iᵒᵖ) (a : i ⟶ j), IsAffineHom (D.map a))
    (c : Cone D) (hc : IsLimit c)
    (g : c.pt ⟶ S)
    (hη : ∀ (i : Iᵒᵖ), c.π.app i ≫ η.app i = g)
    (hsm : ∀ (i : Iᵒᵖ), Smooth (η.app i))
    (hqc : ∀ (i : Iᵒᵖ), QuasiCompact (η.app i))
    (hqs : ∀ (i : Iᵒᵖ), QuasiSeparated (η.app i))
    {X : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {X' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ c.pt}
    (sq : ChosenCartesianSquare g' f' f g)
    (E : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hE : ∀ (q : ℤ) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ X)
      (x : ((Scheme.pointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj
        ((DerivedCategory.Plus.homologyFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj E)),
      ∃ n : ℕ, 0 < n ∧ n • x = 0 ∧ IsUnit (n : Γ(S, ⊤))) :
    IsIso ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
      sq.toCommSq).app E) := by
  sorry

end AlgebraicGeometry
