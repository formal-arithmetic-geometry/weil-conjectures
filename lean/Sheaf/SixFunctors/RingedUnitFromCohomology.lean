module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Sheaf.CategoryTheory.ExactDerivedAdjunctionBounds
import Sheaf.CategoryTheory.HeartTestBoundedBelow

/-! # Bounded-below derived unit detected on cohomology sheaves

Source: Stacks Project, `literature/stacks-project/sites-cohomology.tex`, Tag 0D7T,
lemma-bounded-in-image-downstairs (blueprint: lem-sfb-ringed-unit-from-cohomology).
-/

@[expose] public section

set_option autoImplicit false

universe u wA wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The canonical exact-pullback/right-derived-direct-image adjunction, with its
K-injective resolution structure supplied by the existing Grothendieck category theorem.
Source: Stacks Project, Tag 0D7T, lemma-bounded-in-image-downstairs, canonical derived
adjunction (blueprint: lem-sfb-ringed-unit-from-cohomology).
This specializes the upstream derived adjunction without choosing any functor or map. -/
noncomputable def exactRingedDerivedAdjunction
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (O : Sheaf J CommRingCat.{u}) (R : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))
    [HasDerivedCategory.{wA} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [HasDerivedCategory.{wB} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))]
    (F : ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u, u, u, u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (adj : F ⊣ f.modules) :=
  letI : IsGrothendieckAbelian.{u}
      (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    SheafOfModules.isGrothendieckAbelian
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  adj.mapDerivedCategoryRightDerivedAdjunction

/-- The canonical derived unit is an isomorphism on a bounded-below complex when it is so on
all cohomology sheaves.

Source: Stacks Project, `literature/stacks-project/sites-cohomology.tex`, Tag 0D7T,
lemma-bounded-in-image-downstairs (blueprint: lem-sfb-ringed-unit-from-cohomology).

Proof: exactness of the module pullback identifies its derived functor with the termwise
functor and transports lower cohomological bounds using the exact-functor factorization and
cohomology comparison (lem-weil-pbc-exact-functor-derived-factorization and
lem-weil-pbc-exact-functor-complex-cohomology). The adjunction bound lemma
(lem-pur-exact-derived-adjunction-bounds) gives preservation of every lower bound by the
right derived direct image. The canonical adjunction-shift compatibility and the theorem
that a triangulated left adjoint has triangulated right adjoint
(lem-weil-pbc-adjunction-shift-compatibility-unique and lem-sf-triangulated-right-adjoint)
make the derived unit shift-compatible. Restricting to bounded-below derived categories,
the bounded-below heart test (lem-weil-pbc-heart-test-bounded-below) applies to the unit,
using its invertibility on every degree-zero cohomology sheaf, and proves invertibility at K.
No finite cohomological dimension or upper bound is assumed.
-/
theorem ringedUnitFromCohomology
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (O : Sheaf J CommRingCat.{u}) (R : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))
    [HasDerivedCategory.{wA} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [HasDerivedCategory.{wB} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))]
    (F : ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u, u, u, u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (adj : F ⊣ f.modules)
    (a : ℤ) (K₀ : DerivedCategory (ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)))
    (hbelow : ∀ q : ℤ, q < a →
      IsZero ((DerivedCategory.homologyFunctor
        (ringedSiteModules.{u, u, u, u}
          ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) q).obj K₀))
    (hcoh : ∀ q : ℤ,
      IsIso ((exactRingedDerivedAdjunction O R f F adj).unit.app
        ((DerivedCategory.singleFunctor
          (ringedSiteModules.{u, u, u, u}
          ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) 0).obj
          ((DerivedCategory.homologyFunctor
            (ringedSiteModules.{u, u, u, u}
          ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) q).obj K₀)))) :
    IsIso ((exactRingedDerivedAdjunction O R f F adj).unit.app K₀) := by
  sorry

end CategoryTheory
