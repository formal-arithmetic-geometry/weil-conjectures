/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.ConstructibleSheaf.Pullback
import Sheaf.AlgebraicGeometry.OpenClosedRecollement
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare

/-!
# Devissage of a constructible etale module sheaf

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-fin-constructible-devissage.md`
(blueprint: lem-fin-constructible-devissage).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- A constructible sheaf has a finite filtration with factors extended from lisse sheaves
on locally closed constructible subschemes. The locally closed extension uses the canonical
scheme-theoretic closure `j.image`, cut out by `j.ker`, its closed immersion `j.imageι`,
and the open immersion `j.toImage`.

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-fin-constructible-devissage.md`
(blueprint: lem-fin-constructible-devissage).

Proof:
1. Induct simultaneously over finite-type schemes on their finite dimension
   (`lem-kun-dimension-finite-type`), starting with the empty scheme and length zero.
   Choose the lisse open by `fin2-lem-lisse-dense-open`; its closed complement is again
   finite type and has smaller dimension.
2. Use `lem-weil-pbc-open-closed-short-exact` to express the sheaf as an extension of
   the open extension by zero by the closed pushforward of the closed restriction.
3. The restriction is constructible (`prop-constructible-pullback`). Apply induction
   and push its filtration forward, using exact closed pushforward from
   `lem-cbc-open-closed-recollement`.
4. Closed immersions compose, and their direct images compose by the section formula
   of `def-weil-pbc-direct-image`. The closure of a stratum in the closed complement
   is its closure in the ambient scheme. For the initial open term, apply extension
   by zero base change (`lem-cbc-extension-zero-base-change`) to its closure and its
   complementary open, then the open-closed exact sequence. This identifies the open
   extension with closed pushforward of extension into its scheme-theoretic closure.
   The strata are locally closed and constructible since the ambient scheme is Noetherian.
5. Pull the pushed filtration back under the quotient epimorphism and prepend zero.
   The first quotient is the open extension; all subsequent quotients agree with those
   of the pushed filtration by the cokernel universal property. This also covers a
   zero-length closed filtration. No splitting is asserted. -/
theorem exists_constructible_sheaf_devissage
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (hΛ : IsSmoothBaseChangeCoefficients N Λ X)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    ∃ (m : ℕ) (S : Fin (m + 1) → Subobject F),
      IsZero (S 0 : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ∧
      S (Fin.last m) = ⊤ ∧
      ∃ hS : ∀ r : Fin m, S r.castSucc ≤ S r.succ,
        ∀ r : Fin m, ∃ (T : Scheme.{u}) (j : T ⟶ X),
          IsImmersion j ∧ Topology.IsConstructible (Set.range j) ∧
          ∃ (_ : IsOpenImmersion j.toImage)
            (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
            Scheme.IsFiniteLocallyConstantSheaf L ∧
            Nonempty (cokernel (Subobject.ofLE (S r.castSucc) (S r.succ) (hS r)) ≅
              (lowerStar (ModuleCat.{u + 1} Λ) j.imageι).obj
                ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j.toImage).obj L)) := by
  sorry

end AlgebraicGeometry.Etale
