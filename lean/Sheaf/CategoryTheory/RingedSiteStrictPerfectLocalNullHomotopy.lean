/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RingedToposBinaryDescentDefs
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.EpiMono
import Sheaf.CategoryTheory.SiteCoveringAxioms

/-! # Local null-homotopy from a strictly perfect complex on a ringed site

Source: Stacks Project, Cohomology on Sites, Tag 08FP, lemma-local-homotopy (2)
(blueprint: lem-sfb-ringed-site-strict-perfect-local-null-homotopy).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A map from a bounded complex of finite-free retracts, zero below `a`, to a complex
with zero cohomology in degrees at least `a` has a null-homotopy on a covering sieve.

Source: Stacks Project, Cohomology on Sites, Tag 08FP, lemma-local-homotopy (2),
using Tag 08FN, lemma-local-lift-map
(blueprint: lem-sfb-ringed-site-strict-perfect-local-null-homotopy).

The family `h j` is the component customarily denoted `h^{j+1}`. Thus the displayed
identity is the usual null-homotopy identity in degree `j+1`, and ranges over all degrees.
A covering sieve is the covering family consisting of all its arrows.

Proof:
1. Restriction to a slice is exact by `lem-pur-site-restriction-module-adjunction-exact`,
so preserves cohomology vanishing. Sectionwise restriction also preserves the finite-free
retractions and all map identities (`def-pur-localized-ringed-site`).
2. Choose an upper support bound `b` and construct the homotopy in descending degrees
`b, b-1, ..., a`, initially zero above `b`. In degree `n`, subtract the already chosen
term `h^{n+1} d_P^n` from `w^n`. The chain-map equation and the identity in degree `n+1`
show that this residual map lands in the cycles of `K` in degree `n`.
3. Vanishing of `H^n(K)` makes `K^{n-1}` onto those cycles. Forgetting to abelian sheaves
preserves cokernels (`lem-weil-pbc-module-sheaves-colimits-forgetful`), so this epimorphism
is locally surjective by `lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective`, with
abelian sheafification supplied by `def-weil-pbc-sheafification`.
4. Split `P^n` off a finite free module. Locally lift the residual map on each of its
finitely many basis elements, refine the finitely many coverings, and extend the lifts
linearly. Compose with the inclusion of the retract to obtain `h^n`. The retraction
identity gives the required degree-`n` equation; restriction preserves all higher ones.
For rank zero the zero lift on the identity covering suffices.
5. Compose the finitely many coverings by `def-weil-pbc-sites-and-cohomology` and use
relocalization to identify the restrictions. Set the remaining components below `a`
to zero. Outside the support of `P` both sides vanish; at the lower boundary the
outgoing differential of the zero source is zero. The zero complex uses the identity
cover and zero homotopy. No step imposes a bound on `K`. -/
theorem ringedSite_strictPerfect_local_nullHomotopy
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{max c v r}) (U : C)
    (a : ℤ)
    (P K : CochainComplex
      (ringedSiteModules.{max c v r}
        (((sheafCompose J
          (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)) ℤ)
    (hbounded : ∃ l b : ℤ, ∀ j : ℤ, j < l ∨ b < j → IsZero (P.X j))
    (hfinite : ∀ j : ℤ, ∃ n : ℕ,
      ∃ i : P.X j ⟶ SheafOfModules.free
          (R := (((sheafCompose J
          (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U))
          (ULift.{max c v r} (Fin n)),
      ∃ p : SheafOfModules.free
          (R := (((sheafCompose J
          (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U))
          (ULift.{max c v r} (Fin n)) ⟶ P.X j,
        i ≫ p = 𝟙 (P.X j))
    (hbelow : ∀ j : ℤ, j < a → IsZero (P.X j))
    (hacyclic : ∀ j : ℤ, a ≤ j → IsZero (K.homology j)) (w : P ⟶ K) :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (f : V ⟶ U), S f →
      ∃ h : ∀ j : ℤ,
        (SheafOfModules.overMap
          ((sheafCompose J
            (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) f).obj (P.X (j + 1)) ⟶
        (SheafOfModules.overMap
          ((sheafCompose J
            (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) f).obj (K.X j),
      ∀ j : ℤ,
        (SheafOfModules.overMap
          ((sheafCompose J
            (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) f).map (w.f (j + 1)) =
          h j ≫ (SheafOfModules.overMap
            ((sheafCompose J
            (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) f).map (K.d j (j + 1)) +
          (SheafOfModules.overMap
            ((sheafCompose J
            (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) f).map
              (P.d (j + 1) ((j + 1) + 1)) ≫ h (j + 1) := by
  sorry

end CategoryTheory
