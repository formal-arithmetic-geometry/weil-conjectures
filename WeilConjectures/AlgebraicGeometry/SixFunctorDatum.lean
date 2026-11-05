/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons
public import WeilConjectures.SixFunctors.Etale.Derived.Orientation

/-! # Finite-coefficient six-functor datum

Source: current blueprint, `def-sf-datum`, coefficients, morphisms, operations and
clauses A1--A4 and A6--A10 (blueprint: def-sf-datum).

This records properties of the existing ordinary unbounded small-etale operations.
In particular its smooth base-change clause is on the entire unbounded categories.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

open scoped CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

/--
A six-functor datum for a finite coefficient ring on the small étale sites.

Source: `literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-ctf-finite-geometric-restriction/
sk-prop-sf-rf-shriek-preservation/def-sf-datum.md`, node `def-sf-datum`, order 2713
(blueprint: def-sf-datum).

The fields state the coefficient twist data, the ordinary unbounded small-etale operations,
and clauses (A1), (A2), (A3), (A4), (A6), (A7), (A8), (A9), and (A10) of the source node.
The smooth direct-image base-change field is deliberately on the full unbounded derived
categories, exactly as in clause (A2); the other fields use the canonical operations and
constructible finite-Tor predicate supplied by the recorded dependency declarations.
-/
structure SixFunctorDatum (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (k : Type u) [Field k] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (aY : Y ⟶ Spec (.of k)) [HasTateTwist Λ]
    [HasInvertibleExponent Λ (Spec (.of k))] [HasCompactification f]
    [QuasiCompact f] [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasCompactification aY] [HasCompactification (f ≫ aY)] : Prop where
  /-- A1: ordinary derived inverse image and direct image are adjoint.
  Source: def-sf-datum, A1 (blueprint: def-sf-datum). -/
  upperStarLowerStarAdjunction :
    Nonempty (L((f)^*[ModuleCat.{u + 1} Λ]) ⊣ R((f)_*[ModuleCat.{u + 1} Λ]))
  /-- A1: compact support and exceptional inverse image are adjoint.
  Source: def-sf-datum, A1 (blueprint: def-sf-datum). -/
  lowerShriekUpperShriekAdjunction :
    Nonempty (R(f)_![ModuleCat.{u + 1} Λ] ⊣ R(f)^![Λ])
  /-- A2: compact-support base change for every Cartesian square.
  Source: def-sf-datum, A2 (blueprint: def-sf-datum). -/
  baseChangeLowerShriek : ∀ {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (g' : X' ⟶ X)
      (f' : X' ⟶ Y'), IsPullback g' f' f g → ∀ [HasCompactification f'],
      Nonempty (R(f)_![ModuleCat.{u + 1} Λ] ⋙ L((g)^*[ModuleCat.{u + 1} Λ]) ≅
        L((g')^*[ModuleCat.{u + 1} Λ]) ⋙ R(f')_![ModuleCat.{u + 1} Λ])
  /-- A2: unbounded direct-image base change for proper f.
  Source: def-sf-datum, A2 (blueprint: def-sf-datum). -/
  baseChangeLowerStarOfProper :
    ∀ {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y'),
      IsPullback g' f' f g → IsProper f →
      Nonempty (R((f)_*[ModuleCat.{u + 1} Λ]) ⋙ L((g)^*[ModuleCat.{u + 1} Λ]) ≅
        L((g')^*[ModuleCat.{u + 1} Λ]) ⋙ R((f')_*[ModuleCat.{u + 1} Λ]))
  /-- A2: unbounded direct-image base change for smooth g.
  Source: def-sf-datum, A2 (blueprint: def-sf-datum). -/
  baseChangeLowerStarOfSmooth :
    ∀ {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y'),
      IsPullback g' f' f g → Smooth g →
      Nonempty (R((f)_*[ModuleCat.{u + 1} Λ]) ⋙ L((g)^*[ModuleCat.{u + 1} Λ]) ≅
        L((g')^*[ModuleCat.{u + 1} Λ]) ⋙ R((f')_*[ModuleCat.{u + 1} Λ]))
  /-- A3: the canonical right-coefficient projection map is invertible on all inputs.
  Source: def-sf-datum, A3 (blueprint: def-sf-datum). -/
  projectionFormula : ∀ K L, HasProjectionFormula (ModuleCat.{u + 1} Λ) f K L
  /-- A4: independence of the chosen compactification.
  Source: def-sf-datum, A4 (blueprint: def-sf-datum). -/
  lowerShriekCompactificationIndependent : ∀ c c' : Compactification f,
    Nonempty (Rf_!(c)[ModuleCat.{u + 1} Λ] ≅ Rf_!(c')[ModuleCat.{u + 1} Λ])
  /-- A4: composition of compact-support direct images.
  Source: def-sf-datum, A4 (blueprint: def-sf-datum). -/
  lowerShriekComp : ∀ {Z : Scheme.{u}} (h : Y ⟶ Z) [HasCompactification h]
    [HasCompactification (f ≫ h)] [QuasiCompact (f ≫ h)],
    Nonempty (R(f ≫ h)_![ModuleCat.{u + 1} Λ] ≅
      R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(h)_![ModuleCat.{u + 1} Λ])
  /-- A4: proper coincidence.
  Source: def-sf-datum, A4 (blueprint: def-sf-datum). -/
  lowerShriekIsoLowerStarOfProper :
    IsProper f → Nonempty (R(f)_![ModuleCat.{u + 1} Λ] ≅ R((f)_*[ModuleCat.{u + 1} Λ]))
  /-- A7: smooth purity with the given Tate twist, including relative dimension zero.
  Source: def-sf-datum, A7 (blueprint: def-sf-datum). -/
  orientation : ∀ d : ℕ, SmoothOfRelativeDimension d f → Nonempty (Orientation Λ f d)
  /-- A6: Verdier biduality on bounded constructible finite-Tor objects.
  Source: def-sf-datum, A6 (blueprint: def-sf-datum). -/
  biduality : ∀ K, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
    Nonempty (K ≅ (verdierDual Λ (f ≫ aY)).obj
      (op ((verdierDual Λ (f ≫ aY)).obj (op K))))
  /-- A8: Verdier exchange on every unbounded object.
  Source: def-sf-datum, A8 (blueprint: def-sf-datum). -/
  verdierExchange : ∀ M,
    Nonempty ((verdierDual Λ aY).obj
        (op ((R(f)_![ModuleCat.{u + 1} Λ]).obj M)) ≅
      (R((f)_*[ModuleCat.{u + 1} Λ])).obj
        ((verdierDual Λ (f ≫ aY)).obj (op M)))
  /-- A9: the four external-product comparisons on exactly their stated finite-Tor domains.
  Source: def-sf-datum, A9 (blueprint: def-sf-datum). -/
  kunneth : HasKunnethComparisons Λ (Spec (.of k))
  /-- A10: inverse image preserves the constructible finite-Tor subcategory.
  Source: def-sf-datum, A10 (blueprint: def-sf-datum). -/
  ctfLeftDerivedUpperStar : ∀ K,
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)
  /-- A10: derived tensor preserves the constructible finite-Tor subcategory.
  Source: def-sf-datum, A10 (blueprint: def-sf-datum). -/
  ctfTensor : ∀ K M, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M →
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj M)
  /-- A10: direct image preserves the constructible finite-Tor subcategory.
  Source: def-sf-datum, A10 (blueprint: def-sf-datum). -/
  ctfRightDerivedLowerStar : ∀ K,
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
        ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)
  /-- A10: compact support preserves the constructible finite-Tor subcategory.
  Source: def-sf-datum, A10 (blueprint: def-sf-datum). -/
  ctfRightDerivedLowerShriek : ∀ K,
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
        ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)
  /-- A10: exceptional inverse image preserves the constructible finite-Tor subcategory.
  Source: def-sf-datum, A10 (blueprint: def-sf-datum). -/
  ctfRightDerivedUpperShriek : ∀ K,
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
        ((R(f)^![Λ]).obj K)
  /-- A10: Verdier duality preserves the constructible finite-Tor subcategory.
  Source: def-sf-datum, A10 (blueprint: def-sf-datum). -/
  ctfVerdierDual : ∀ K,
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
        ((verdierDual Λ (f ≫ aY)).obj (op K))

end AlgebraicGeometry.Etale
