module

public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Pseudo-coherence on an arbitrary ringed site

Source: Stacks Project, sites-cohomology.tex, Tags 08FT and 08FU
(blueprint: def-sfb-ringed-site-pseudocoherent-complex).
-/

@[expose] public section
set_option autoImplicit false

universe u v r w w'
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max u v r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
  (R : Sheaf J CommRingCat.{max u v r})
  [HasDerivedCategory.{w} (ringedSiteModules.{max u v r}
    ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R))]
  [∀ U : C, HasDerivedCategory.{w'} (ringedSiteModules.{max u v r}
    (((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R).over U))]

/-- Local strictly perfect approximations, invertible on cohomology above `m` and
surjective in degree `m`. Both the cover and approximation may depend on `m`.
Source: Stacks Project, Tags 08FT and 08FU (derived formulation)
(blueprint: def-sfb-ringed-site-pseudocoherent-complex). -/
def IsMPseudoCoherentOnRingedSite
    (m : ℤ) (K : DerivedCategory (ringedSiteModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R))) :
    Prop :=
  ∀ U : C, ∃ S : Sieve U, S ∈ J U ∧
    ∀ (V : C) (f : V ⟶ U), S f →
      ∃ P : CochainComplex (ringedSiteModules.{max u v r}
          (((sheafCompose J
            (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R).over V)) ℤ,
        (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
        Nonempty (StrictPerfectCoefficientPackageOnSite _ P) ∧
        ∃ α : DerivedCategory.Q.obj P ⟶ ringedSiteDerivedRestrictionOfUniverses
            ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)
            V K,
          (∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map α)) ∧
          Epi ((DerivedCategory.homologyFunctor _ m).map α)

/-- Pseudo-coherence means `m`-pseudo-coherence for every integer, without a common cover.
Source: Stacks Project, Tag 08FT
(blueprint: def-sfb-ringed-site-pseudocoherent-complex). -/
def IsPseudoCoherentOnRingedSite
    (K : DerivedCategory (ringedSiteModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R))) :
    Prop :=
  ∀ m : ℤ, IsMPseudoCoherentOnRingedSite.{u, v, r, w, w'} R m K

end SheafOfModules
