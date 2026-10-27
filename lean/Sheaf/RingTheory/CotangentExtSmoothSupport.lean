/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.RingTheory.CotangentResolutionCoherence
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.Field.IsField
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs
import Sheaf.RingTheory.FinitePolynomialSimplicialResolution
import WeilConjectures.RingTheory.KaehlerDifferentialsPolynomialExtension
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.AlgebraicGeometry.LciCotangentPresentation
import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
import WeilConjectures.AlgebraicGeometry.SmoothRelativeDifferentialsFiniteLocallyFree
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Positive cotangent Ext on the smooth locus

Source: Stacks Project, Cotangent Complex, Tags 08PX, 08QI, 08SF and 08R5;
More on Algebra, Tag 0A6A(3)
(blueprint: lem-sfb-cotangent-ext-smooth-support).

The Ext groups use the full standard polynomial cotangent complex. The localization
isomorphism is normalized by the canonical cotangent square and the coefficient map
`n ↦ n/1`, using exact restriction of scalars and its canonical shift comparisons.

## Main definitions and statement

- `cotangentExt`: morphisms from the full cotangent complex to a shifted module.
- `IsCotangentExtLocalization`: the canonical localization comparison square.
- `cotangentExt_finite_localization_smooth_support`: finiteness and localization,
  with positive-degree vanishing at smooth primes and the support inclusion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry

namespace Algebra.CotangentResolution

variable [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]

/-- The ordinary module cotangent Ext group `Hom(L_{B/A}, N[j])`, with its canonical
`B`-module structure from the linear derived category. Source: Stacks 08PN and 0A6A
(blueprint: lem-sfb-cotangent-ext-smooth-support). -/
abbrev cotangentExt (C : Coherence.{u}) (f : Arrow CommRingCat.{u})
    (N : ModuleCat.{u} f.right) (j : ℤ) :=
  @Quiver.Hom (DerivedCategory (ModuleCat.{u} f.right)) _ (cotangentComplex C f)
    (((DerivedCategory.singleFunctor (ModuleCat.{u} f.right) 0).obj N)⟦j⟧)

/-- The cotangent Ext group bundled with its canonical scalar action. Source: Stacks 0A6A
(blueprint: lem-sfb-cotangent-ext-smooth-support). -/
abbrev cotangentExtModule (C : Coherence.{u}) (f : Arrow CommRingCat.{u})
    (N : ModuleCat.{u} f.right) (j : ℤ) : ModuleCat.{u + 1} f.right :=
  ModuleCat.of f.right (cotangentExt C f N j)

/-- The localized algebra arrow `A → S⁻¹B`. Source: Stacks 08SF
(blueprint: lem-sfb-cotangent-ext-smooth-support). -/
abbrev localizedArrow (f : Arrow CommRingCat.{u}) (S : Submonoid f.right) :
    Arrow CommRingCat.{u} :=
  Arrow.mk (f.hom ≫ CommRingCat.ofHom (algebraMap f.right (Localization S)))

/-- The canonical square from `A → B` to `A → S⁻¹B`. Source: Stacks 08SF
(blueprint: lem-sfb-cotangent-ext-smooth-support). -/
def localizationSquare (f : Arrow CommRingCat.{u}) (S : Submonoid f.right) :
    f ⟶ localizedArrow f S :=
  Arrow.homMk (𝟙 f.left) (CommRingCat.ofHom (algebraMap f.right (Localization S))) rfl

/-- The actual localized coefficient module. Source: Stacks 08SF
(blueprint: lem-sfb-cotangent-ext-smooth-support). -/
abbrev localizedCoefficient {f : Arrow CommRingCat.{u}} (S : Submonoid f.right)
    (N : ModuleCat.{u} f.right) : ModuleCat.{u} (localizedArrow f S).right :=
  ModuleCat.of (Localization S) (LocalizedModule S N)

/-- The localized Ext group bundled over the localized ring. Source: Stacks 08SF and 0A6A
(blueprint: lem-sfb-cotangent-ext-smooth-support). -/
abbrev localizedCotangentExtModule (C : Coherence.{u}) (f : Arrow CommRingCat.{u})
    (N : ModuleCat.{u} f.right) (S : Submonoid f.right) (j : ℤ) :
    ModuleCat.{u + 1} (localizedArrow f S).right :=
  ModuleCat.of (Localization S) (LocalizedModule S (cotangentExt C f N j))

/-- The canonical Ext restriction square, retaining the cotangent ring-square map
and the canonical degree-zero and shift comparisons. The theorem below pins the
coefficient arrow to `n ↦ n/1`. Source: Stacks 08SF and the unit description before 0A6A
(blueprint: lem-sfb-cotangent-ext-smooth-support). -/
def IsCotangentExtLocalization (C : Coherence.{u}) (f : Arrow CommRingCat.{u})
    (N : ModuleCat.{u} f.right) (S : Submonoid f.right) (j : ℤ)
    (ι : N ⟶ (ModuleCat.restrictScalars (localizationSquare f S).right.hom).obj
      (localizedCoefficient S N))
    (ξ : cotangentExt C f N j)
    (η : cotangentExt C (localizedArrow f S) (localizedCoefficient S N) j) : Prop :=
  ξ ≫ ((DerivedCategory.singleFunctor (ModuleCat.{u} f.right) 0).map ι)⟦j⟧' =
    cotangentMap C (localizationSquare f S) ≫
      (ModuleCat.restrictScalars (localizationSquare f S).right.hom).mapDerivedCategory.map η ≫
      ((ModuleCat.restrictScalars
        (localizationSquare f S).right.hom).mapDerivedCategory.commShiftIso j).hom.app _ ≫
      ((ModuleCat.restrictScalars
        (localizationSquare f S).right.hom).mapDerivedCategorySingleFunctor 0).hom.app _⟦j⟧'

/-- Positive cotangent Ext is finite, its canonical localization is an isomorphism,
and its support lies in the nonsmooth locus. Source: Stacks 08PX, 08QI, 08SF, 08R5
and 0A6A(3) (blueprint: lem-sfb-cotangent-ext-smooth-support).

Proof:
1. A field is Noetherian. Use lem-sfb-finite-polynomial-simplicial-resolution and
lem-trf-cotangent-resolution-coherence to represent the full cotangent complex by
`E` in nonpositive degrees. The polynomial differential basis of
lem-weil-pbc-kahler-differentials-polynomial-extension makes every term finite free.
2. By lem-sc-bounded-above-projective-kprojective, `E` is K-projective.
lem-coef-kprojective-derived-hom-bijection identifies the Ext group with the
cohomology of `Hom(E,N[0])`; degree `j` is a finite power of `N`, since the target
is concentrated in degree zero. These identifications are linear and natural.
3. The algebra is Noetherian by lem-weil-pbc-finite-type-algebra-noetherian.
lem-weil-pbc-noetherian-submodule-finite makes the cycles finite, and their
quotient by the boundaries is finite.
4. By lem-trf-cotangent-augmentation-localization, localized `E` represents the
localized cotangent complex. Localization of Hom from each finite free term is
Hom of the localized terms: in a basis both are the same finite power of `S⁻¹N`.
This identification commutes with differentials. Exact localization commutes
with cohomology. Step 2 over `S⁻¹B` gives the claimed linear equivalence. Its
restriction square is precisely IsCotangentExtLocalization, by the canonical
cotangent map and coefficient unit. This includes multiplicative sets containing zero.
5. At a smooth prime choose a smooth affine principal neighborhood.
lem-trf-lci-cotangent-presentation and
lem-cbc-normalized-alternating-homotopy-equivalence identify the full affine
complex with the sheaf cotangent complex. The smooth clause and
lem-ag-smooth-relative-differentials-finite-locally-free identify this locally
with a finite free module in degree zero. Taking stalks preserves the comparison
by lem-weil-pbc-module-stalk-exact and
lem-weil-pbc-spec-tilde-stalk-localization. Thus `E` localized at the prime is
isomorphic in the derived category to a finite free module in degree zero.
6. Apply step 4 at the prime. By step 2, morphisms from that finite free
single complex to `N[j]` are represented by chain maps. If `j ≥ 1`, source and
target occupy distinct degrees, so every such map is zero. This gives
subsingleton localizations. The support inclusion is exactly their vanishing
at every smooth prime. -/
theorem cotangentExt_finite_localization_smooth_support
    (C : Coherence.{u}) (f : Arrow CommRingCat.{u}) (_hk : IsField f.left)
    (_hfinite : RingHom.FiniteType f.hom.hom)
    (N : ModuleCat.{u} f.right) [Module.Finite f.right N] (j : ℤ) (_hj : 1 ≤ j) :
    Module.Finite f.right (cotangentExt C f N j) ∧
    (∀ S : Submonoid f.right,
      ∃ (ι : N ⟶ (ModuleCat.restrictScalars (localizationSquare f S).right.hom).obj
          (localizedCoefficient S N)),
        (∀ n : N, ι n = LocalizedModule.mk n 1) ∧
        ∃ e : localizedCotangentExtModule C f N S j ≅
            cotangentExtModule C (localizedArrow f S) (localizedCoefficient S N) j,
          ∀ ξ : cotangentExt C f N j,
            IsCotangentExtLocalization C f N S j ι ξ (e.hom (LocalizedModule.mk ξ 1))) ∧
    (∀ q : PrimeSpectrum f.right,
      (∃ U : (Spec f.right).Opens, q ∈ U ∧ AlgebraicGeometry.Smooth (U.ι ≫ Spec.map f.hom)) →
        Subsingleton (LocalizedModule q.asIdeal.primeCompl (cotangentExt C f N j))) ∧
    {q : PrimeSpectrum f.right |
      ¬ Subsingleton (LocalizedModule q.asIdeal.primeCompl (cotangentExt C f N j))} ⊆
      {q : PrimeSpectrum f.right |
        ¬ ∃ U : (Spec f.right).Opens, q ∈ U ∧ AlgebraicGeometry.Smooth (U.ι ≫ Spec.map f.hom)} := by
  sorry

end Algebra.CotangentResolution
