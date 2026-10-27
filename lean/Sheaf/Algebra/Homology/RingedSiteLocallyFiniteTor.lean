module

public import Sheaf.AlgebraicGeometry.RingedProEtaleTorAmplitudeOfUniverses
public import Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses

/-! # Locally finite Tor dimension on an arbitrary ringed site

Source: Stacks Project, sites-cohomology.tex, Tag 08FZ (3)
(blueprint: def-sfb-ringed-site-locally-finite-tor-dimension).
-/

@[expose] public section
set_option autoImplicit false

universe u v r w w'
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Every site object admits a cover with a finite universal Tor interval on each member.
The interval is chosen after the member, and tests every module sheaf on that slice.
Source: Stacks Project, Tag 08FZ (3)
(blueprint: def-sfb-ringed-site-locally-finite-tor-dimension). -/
def HasLocallyFiniteTorDimensionOnRingedSite
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max u v r}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J CommRingCat.{max u v r})
    [HasDerivedCategory.{w} (ringedSiteModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R))]
    [hDU : ∀ U : C, HasDerivedCategory.{w'} (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R).over U))]
    (K : DerivedCategory (ringedSiteModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R))) :
    Prop :=
  ∀ U : C, ∃ S : Sieve U, S ∈ J U ∧
    ∀ (V : C) (f : V ⟶ U), S f →
      @HasFiniteRingedSiteTorAmplitudeOfUniverses.{max u v, v, max u v r, w'}
        (Over V) _ _ (J.over V) (R.over V) _ _ (hDU V)
        (ringedSiteDerivedRestrictionOfUniverses
          ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R) V K)

end SheafOfModules
