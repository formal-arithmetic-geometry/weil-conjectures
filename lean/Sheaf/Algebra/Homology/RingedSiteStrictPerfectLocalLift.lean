/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q113
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Local homotopy lifting from a strictly perfect complex on a ringed site

Source: Stacks Project, sites-cohomology.tex, Tag 08FQ,
lemma-lift-through-quasi-isomorphism.
(blueprint: lem-sfb-ringed-site-strict-perfect-local-lift).

Restriction over an arrow `f : V ⟶ U` is taken on `(C/U)/(V/U)`, the canonical
relocalization of `C/V`. Its section at `W → V → U` is the original section at `W`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [instance] CategoryTheory.module_overFunctor_preservesZero

universe c v r

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- A chain map from a bounded finite-free-retract complex lifts locally up to homotopy
through a partial cohomology approximation. There is no bound on either target complex.

Source: Stacks Project, sites-cohomology.tex, Tag 08FQ.
(blueprint: lem-sfb-ringed-site-strict-perfect-local-lift).

Proof plan: form the cone C(v), whose degree j term is F^j ⊕ G^(j+1).
The cone long exact cohomology sequence (lem-sf-derived-homology-long-exact) and
surjectivity of H^j(v), together with injectivity of H^(j+1)(v), imply that
H^j(C(v)) = 0 for j ≥ a. Apply
lem-sfb-ringed-site-strict-perfect-local-null-homotopy to the composite E → F → C(v).
It applies because E has finite support, its terms are finite-free retracts, and
it vanishes below a. This gives a covering sieve of U and a null homotopy on each
member. Write the degree j null homotopy as (s^j,t^j) with values in
F^(j-1) ⊕ G^j. The G-component of the homotopy equation states that t is a chain map.
The F-component states u^j - v^j t^j = d_F s^j + s^(j+1) d_E, the desired homotopy.
All restrictions are sectionwise (def-pur-localized-ringed-site), including the
identification of the iterated slice with C/V. In Lean the homotopy components
are `h.hom j (j - 1)`; `h.comm` is precisely this equation after rearrangement. -/
theorem exists_strictPerfect_local_lift
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max c v r}) (U : C) (a : ℤ)
    [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (E F G : CochainComplex (ringedSiteModules.{max c v r}
      (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)) ℤ)
    (u : E ⟶ F) (v : G ⟶ F)
    (hbounded : ∃ b d : ℤ, ∀ j : ℤ, j < b ∨ d < j → IsZero (E.X j))
    (hfinite : ∀ j : ℤ, ∃ n : ℕ,
      ∃ i : E.X j ⟶ ∏ᶜ fun _ : Fin n ↦ unit
        (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U),
      ∃ p : (∏ᶜ fun _ : Fin n ↦ unit
        (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)) ⟶
          E.X j,
        i ≫ p = 𝟙 (E.X j))
    (hbelow : ∀ j : ℤ, j < a → IsZero (E.X j))
    (hiso : ∀ j : ℤ, a < j → IsIso (HomologicalComplex.homologyMap v j))
    (hepi : Epi (HomologicalComplex.homologyMap v a)) :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (f : V ⟶ U), S f →
      ∃ t : ((overFunctor
            (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)
            (Over.mk f)).mapHomologicalComplex (.up ℤ)).obj E ⟶
          ((overFunctor
            (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)
            (Over.mk f)).mapHomologicalComplex (.up ℤ)).obj G,
        Nonempty (Homotopy
          (((overFunctor
            (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)
            (Over.mk f)).mapHomologicalComplex (.up ℤ)).map u)
          (t ≫ ((overFunctor
            (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)
            (Over.mk f)).mapHomologicalComplex (.up ℤ)).map v)) := by
  sorry

end SheafOfModules
