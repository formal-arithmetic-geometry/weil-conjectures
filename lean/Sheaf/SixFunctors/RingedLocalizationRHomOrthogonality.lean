/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.RingedSectionLocalizationRing
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.Algebra.Homology.HomComplex
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Localization orthogonality for derived internal Hom

Source: Stacks Project, `algebraization.tex`, Tags 0996 and 0997
(blueprint: lem-sf-ringed-localization-rhom-orthogonality).

The sectionwise coinduction below is the actual module-theoretic construction
`S(U) →ₗ[R(U)] M(U)`, with the `S(U)`-action supplied by Mathlib's
`ModuleCat.coextendScalars`.  The derived statement records the induced sheaf
coinduction together with its adjunction; its existence and the comparison are
the postponed theorem content of this stage.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

/-- The concrete coinduced module on one object of a ringed site.

Source: Stacks Project, `algebraization.tex`, Tag 0932 and Tag 0996
(blueprint: lem-sf-ringed-localization-rhom-orthogonality).
For a ring-map component `R(U) → S(U)` and an `R(U)`-module `M`, this is the
module of `R(U)`-linear maps `S(U) → M`, with `S(U)` acting by precomposition
with multiplication.  It is the sectionwise formula used to assemble the
coinduced sheaf module in the theorem below.
-/
def ringedLocalizationCoinductionSection
    {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S) (U : Cᵒᵖ)
    (M : ModuleCat (R.obj.obj U)) : ModuleCat (S.obj.obj U) :=
  (ModuleCat.coextendScalars ((α.hom.app U).hom)).obj M

/-- Restriction of scalars for sheaves of modules preserves finite limits.

Source: Stacks Project, `sites-modules.tex`, Tags 03D9 and 03DA
(blueprint: lem-sf-ringed-localization-rhom-orthogonality).
The underlying sheaf of abelian groups is unchanged, so the comparison with
the forgetful functor is an isomorphism; finite limits are reflected there.
-/
theorem ringedLocalizationRestrictionFiniteLimits
    {R S : Sheaf J RingCat.{u}} (α : R ⟶ S) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{u} α) := sorry

/-- Restriction of scalars for sheaves of modules preserves finite colimits.

Source: Stacks Project, `sites-modules.tex`, Tags 03D9 and 03DA
(blueprint: lem-sf-ringed-localization-rhom-orthogonality).
The underlying sheaf of abelian groups is unchanged, so the comparison with
the forgetful functor is an isomorphism; finite colimits are reflected there.
-/
theorem ringedLocalizationRestrictionFiniteColimits
    {R S : Sheaf J RingCat.{u}} (α : R ⟶ S) :
    PreservesFiniteColimits (SheafOfModules.restrictScalars.{u} α) := sorry

noncomputable def ringedLocalizationDerivedRestriction
    (R : Sheaf J CommRingCat.{u})
    (s : (R.obj ⋙ forget CommRingCat).sections)
    [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat RingCat)).obj (ringedLocalizationRing R s)))] :
    DerivedCategory
        (SheafOfModules.{u} ((sheafCompose J
          (forget₂ CommRingCat RingCat)).obj (ringedLocalizationRing R s))) ⥤
      DerivedCategory
        (SheafOfModules.{u} ((sheafCompose J
          (forget₂ CommRingCat RingCat)).obj R)) := by
  letI : PreservesFiniteLimits (SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map
        (ringedLocalizationRingUnit R s))) :=
    ringedLocalizationRestrictionFiniteLimits _
  letI : PreservesFiniteColimits (SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map
        (ringedLocalizationRingUnit R s))) :=
    ringedLocalizationRestrictionFiniteColimits _
  exact (SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map
      (ringedLocalizationRingUnit R s))).mapDerivedCategory

noncomputable def ringedLocalizationDerivedUnit
    (R : Sheaf J CommRingCat.{u})
    (s : (R.obj ⋙ forget CommRingCat).sections)
    [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat RingCat)).obj (ringedLocalizationRing R s)))] :
    DerivedCategory
      (SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat RingCat)).obj R)) := by
  let T := ringedLocalizationDerivedRestriction R s
  exact T.obj ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj (ringedLocalizationRing R s))) 0).obj
      (SheafOfModules.unit _))

noncomputable def ringedLocalizationDerivedInner
    (R : Sheaf J CommRingCat.{u})
    (s : (R.obj ⋙ forget CommRingCat).sections)
    [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat RingCat)).obj (ringedLocalizationRing R s)))] :
    DerivedCategory
      (SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat RingCat)).obj R)) ⥤
      DerivedCategory
        (SheafOfModules.{u} ((sheafCompose J
          (forget₂ CommRingCat RingCat)).obj R)) :=
  (Functor.curry.obj (derivedInternalHomOfUniverses J R)).obj
    (op (ringedLocalizationDerivedUnit R s))

/-- Localization orthogonality for derived internal Hom.

Source: Stacks Project, `algebraization.tex`, Tag 0996, lemma
`map-twice-localize`, clause (2), and Tag 0997, lemma `hom-from-Af`,
implication (1) ⇒ (2) (blueprint: lem-sf-ringed-localization-rhom-orthogonality).

Proof, postponed at stage 2, follows six steps.  (1) Restriction of scalars
is additive, exact, and detects zero complexes because it leaves the underlying
abelian sheaf unchanged.  (2) The sectionwise formula in
`ringedLocalizationCoinductionSection`, evaluated on every slice, gives the
coinduction adjunction by evaluation at one and its inverse
`m ↦ (c ↦ a(c m))`.  (3) A K-injective resolution over `R`, together with
right-adjoint preservation of K-injectives, equips the inner derived Hom with
the `S`-module structure.  (4) The degreewise evaluation and coinduction
formulas give mutually inverse Hom-complex maps, including all products and
the differential signs.  (5) The K-injective models compute both derived
internal Homs and descend to a natural isomorphism, independent of
representatives.  (6) If the inner object vanishes, exact restriction detects
that its coinduced complex is acyclic, so the outer derived Hom vanishes.
No boundedness, finite-generation, or flatness hypothesis is used.
-/
theorem ringedLocalizationRHomOrthogonality
    (R : Sheaf J CommRingCat.{u})
    (s : (R.obj ⋙ forget CommRingCat).sections)
    [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat RingCat)).obj (ringedLocalizationRing R s)))] :
    ∃ (H : DerivedCategory
        (SheafOfModules.{u} ((sheafCompose J
          (forget₂ CommRingCat RingCat)).obj R)) ⥤
        DerivedCategory
          (SheafOfModules.{u} ((sheafCompose J
            (forget₂ CommRingCat RingCat)).obj (ringedLocalizationRing R s)))),
      Nonempty (ringedLocalizationDerivedRestriction R s ⊣ H) ∧
      Nonempty (let T := ringedLocalizationDerivedRestriction R s
        let DR := DerivedCategory
          (SheafOfModules.{u} ((sheafCompose J
            (forget₂ CommRingCat RingCat)).obj R))
        let DS := DerivedCategory
          (SheafOfModules.{u} ((sheafCompose J
            (forget₂ CommRingCat RingCat)).obj (ringedLocalizationRing R s)))
        let HR := derivedInternalHomOfUniverses J R
        let HS := derivedInternalHomOfUniverses J (ringedLocalizationRing R s)
        let I := ringedLocalizationDerivedInner R s ⋙ H
        let LHS := T.op.prod (𝟭 DR) ⋙ HR
        let RHS := (𝟭 DSᵒᵖ).prod I ⋙ HS ⋙ T
        LHS ≅ RHS) ∧
      ∀ (L : DerivedCategory
          (SheafOfModules.{u} ((sheafCompose J
            (forget₂ CommRingCat RingCat)).obj (ringedLocalizationRing R s))))
        (K : DerivedCategory
          (SheafOfModules.{u} ((sheafCompose J
            (forget₂ CommRingCat RingCat)).obj R))),
        IsZero ((ringedLocalizationDerivedInner R s ⋙ H).obj K) →
        IsZero ((derivedInternalHomOfUniverses J R).obj
          (op ((ringedLocalizationDerivedRestriction R s).obj L), K)) := by
  sorry

end CategoryTheory
