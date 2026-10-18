/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q94
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.AlgebraicGeometry.AllowableTorsionDerivedCategories
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses

/-!
# Ambient categories and small full subcategories

Source: blueprint main-20261015, sec-six-functors/sk-def-sf-categories,
order 2385 (blueprint: def-sf-categories).

The ambient categories use Mathlib's ringed-site modules and ordinary derived categories.
The finite categories use the intrinsic constructibility predicates. Higher stages reuse
exactly the completed integral, scalar-localization and common-stage categories; they
are never placed in an ordinary constant-coefficient derived category.

The existing coefficient-stage names are reexported unchanged:
`sfIntegralConstructibleCategory`, `finiteTorConstructibleIntegralCategory`,
`sfRationalConstructibleCategory`, `generalAlgebraicallyClosedConstructibleCategory`,
and `finiteTorFieldCoefficientCategory`. The definitions below add only the full
subcategories and interval intersections needed to assemble this notation.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe c h r m w u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures

section RingedSite

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{r}) [HasSheafify J AddCommGrpCat.{m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasDerivedCategory.{w} (ringedSiteModules.{m} R)]

/-- The ambient ordinary derived category of module sheaves on a ringed site.
For a commutative ring sheaf use its image under `sheafCompose J (forget₂ _ RingCat)`.
Site objects, arrows, scalars, module values and localization have independent universes.
Source: blueprint order 2385 (blueprint: def-sf-categories). -/
abbrev sfAmbientDerivedCategory := DerivedCategory (ringedSiteModules.{m} R)

/-- The bounded-below full subcategory, defined by cohomology vanishing sufficiently
far in negative degrees. Source: blueprint order 2385 (blueprint: def-sf-categories). -/
abbrev sfAmbientDerivedCategoryPlus := DerivedCategory.Plus (ringedSiteModules.{m} R)

/-- The bounded-above full subcategory, defined by cohomology vanishing sufficiently
far in positive degrees. Source: blueprint order 2385 (blueprint: def-sf-categories). -/
abbrev sfAmbientDerivedCategoryMinus := DerivedCategory.Minus (ringedSiteModules.{m} R)

/-- The bounded full subcategory, with cohomology supported in a finite interval.
Source: blueprint order 2385 (blueprint: def-sf-categories). -/
abbrev sfAmbientDerivedCategoryBounded := DerivedCategory.Bounded (ringedSiteModules.{m} R)

end RingedSite

/-- Constant-coefficient ambient notation on either small site: sheafify the actual
constant ring presheaf and then take its module derived category. The coefficient is
commutative; `RingCat` merely forgets that property when forming module sheaves.
Supplying the small etale or pro-etale topology gives the two sites.
Source: blueprint order 2385 (blueprint: def-sf-categories). -/
abbrev sfConstantDerivedCategory {C : Type c} [Category.{h} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J RingCat.{r}]
    (A : Type r) [CommRing A] [HasSheafify J AddCommGrpCat.{m}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasDerivedCategory.{w} (ringedSiteModules.{m}
      ((constantSheaf J RingCat.{r}).obj (RingCat.of A)))] :=
  DerivedCategory (ringedSiteModules.{m}
    ((constantSheaf J RingCat.{r}).obj (RingCat.of A)))

/-- The allowable-prime-torsion full subcategory of the bounded-below derived category
for an arbitrary ring sheaf on the small etale site. Every integer cohomology stalk
is tested on every geometric point and every element. The recorded abelian etale
predicate is applied to the underlying abelian sheaf of the module cohomology.
`P` is used under the convention that its primes are invertible on `T`.
Source: blueprint order 2385 (blueprint: def-sf-categories). -/
abbrev sfEtaleAllowableTorsionCategory (T : Scheme.{u})
    (R : Sheaf T.smallEtaleTopology RingCat.{u + 1}) (P : Set ℕ)
    [HasDerivedCategory.{w} (SheafOfModules.{u + 1} R)] :=
  ObjectProperty.FullSubcategory (fun K : DerivedCategory.Plus (SheafOfModules.{u + 1} R) ↦ ∀ i : ℤ,
    Etale.allowableTorsionSheafProperty T P
      ((SheafOfModules.toSheaf R).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u + 1} R) i).obj
          K.obj)))

/-- The allowable-prime-torsion full subcategory on the small pro-etale site, with
arbitrary commutative ring sheaf. The stalk functor is the recorded pointed-neighbourhood
module colimit with its actual scalar action. Each stalk element must have a positive
annihilator whose prime divisors belong to `P`; `P` is used under the invertibility
convention on `T`. Source: blueprint order 2385 (blueprint: def-sf-categories). -/
abbrev sfProEtaleAllowableTorsionCategory (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) (P : Set ℕ)
    [HasDerivedCategory.{w} (SheafOfModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))] :=
  ObjectProperty.FullSubcategory (fun K : DerivedCategory.Plus (SheafOfModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ↦
    ∀ (i : ℤ) (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ T)
      (x : (Scheme.geometricRingModuleStalkFunctor s R).obj
        ((DerivedCategory.homologyFunctor _ i).obj K.obj)),
      ∃ n : ℕ, 0 < n ∧ (∀ p : ℕ, p.Prime → p ∣ n → p ∈ P) ∧ n • x = 0)

/-- The finite-etale bounded constructible category. Its objects satisfy the recorded
finite-constant-value constructibility condition and boundedness, and all morphisms
are inherited from the ordinary derived category.
Source: blueprint order 2385 (blueprint: def-sf-categories). -/
abbrev sfEtaleConstructibleCategory (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (T : Scheme.{u}) :=
  (Etale.DerivedCategory.isBoundedConstructible Λ T).FullSubcategory

/-- The full finite-Tor subcategory of the finite-etale constructible category: one
ordered interval works after tensoring with every module sheaf in degree zero.
Source: blueprint order 2385 (blueprint: def-sf-categories). -/
abbrev sfEtaleConstructibleFiniteTorCategory (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (T : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (fun K : sfEtaleConstructibleCategory Λ T ↦ ∃ a b : ℤ, a ≤ b ∧
    Etale.DerivedCategory.hasTorAmplitudeIn Λ T a b K.obj)

/-- The finite-etale cohomological interval full subcategory. No Tor condition is imposed.
The intended notation has `a ≤ b`; the formula also makes sense for every pair of bounds.
Source: blueprint order 2385 (blueprint: def-sf-categories). -/
abbrev sfEtaleConstructibleIntervalCategory (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (T : Scheme.{u}) (a b : ℤ) :=
  ObjectProperty.FullSubcategory (fun K : sfEtaleConstructibleCategory Λ T ↦
    ∀ i : ℤ, (i < a ∨ b < i) → IsZero ((DerivedCategory.homologyFunctor _ i).obj K.obj))

section FiniteCoefficients

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u})

/-- The intrinsic bounded constructible category at `A_{E,n}` on the pro-etale site.
No etale-origin hypothesis is added. Source: blueprint order 2385
(blueprint: def-sf-categories). -/
abbrev sfFiniteConstructibleCategory :=
  (Scheme.intrinsicFiniteTorsionConstructible l E n hn T).FullSubcategory

/-- The finite coefficient finite-Tor category uses the exact recorded predicate, which
already conjoins constructibility and an ordered finite Tor interval.
Source: blueprint order 2385 (blueprint: def-sf-categories). -/
abbrev sfFiniteConstructibleFiniteTorCategory :=
  finiteTorConstructibleCategory l E n hn T

/-- The finite pro-etale cohomological interval category, using the recorded intrinsic
constructible interval full subcategory. Cohomology vanishes outside the inclusive
interval `[a,b]`; no finite-Tor condition is imposed. The intended bounds satisfy `a ≤ b`.
Source: blueprint order 2385 (blueprint: def-sf-categories). -/
abbrev sfFiniteConstructibleIntervalCategory (a b : ℤ) :=
  intrinsicConstructibleIntervalCategory l E n hn T a b

end FiniteCoefficients

section HigherCoefficients

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The integral ambient derived category uses the completed ring sheaf through the
recorded `scalarReductionSource`; it is not the constant integral ring sheaf.
Source: blueprint order 2385 (blueprint: def-sf-categories). -/
abbrev sfIntegralAmbientDerivedCategory := DerivedCategory (scalarReductionSource.{u, u} l E T)

/-- The integral interval category is the intersection of the recorded shifted standard
classes within the derived-complete bounded constructible category. Completeness and
one common cohomological interval for all reductions are retained by the ambient category.
Source: blueprint order 2385 (blueprint: def-sf-categories). -/
abbrev sfIntegralConstructibleIntervalCategory (a b : ℤ) :=
  (sfIntegralStandardClass l E T false a ⊓ sfIntegralStandardClass l E T true b).FullSubcategory

/-- The rational interval category uses the standard classes on the actual scalar
localization, rather than any ordinary constant-coefficient ambient category.
Source: blueprint order 2385 (blueprint: def-sf-categories). -/
abbrev sfRationalConstructibleIntervalCategory (a b : ℤ) :=
  (sfRationalStandardClass l E T false a ⊓ sfRationalStandardClass l E T true b).FullSubcategory

/-- At the rational field stage finite-Tor constructible means bounded constructible,
by the recorded field-category alias. Source: blueprint order 2385
(blueprint: def-sf-categories). -/
abbrev sfRationalConstructibleFiniteTorCategory :=
  finiteTorFieldCoefficientCategory (sfRationalConstructibleCategory l E T)

end HigherCoefficients

/-- At algebraically closed coefficients finite-Tor constructible means the actual
common-stage bounded constructible category, by definition.
Source: blueprint order 2385 (blueprint: def-sf-categories). -/
abbrev sfCommonStageConstructibleFiniteTorCategory (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (T : Scheme.{u}) :=
  finiteTorFieldCoefficientCategory (generalAlgebraicallyClosedConstructibleCategory l Ω T)

/-- The algebraically closed interval category is the full subcategory on the two
common-stage standard classes, with their actual isomorphism-closure meanings.
Source: blueprint order 2385 (blueprint: def-sf-categories). -/
abbrev sfCommonStageConstructibleIntervalCategory (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (T : Scheme.{u}) (a b : ℤ) :=
  (sfCommonStageStandardClass l T Ω false a ⊓
    sfCommonStageStandardClass l T Ω true b).FullSubcategory

end WeilConjectures
