/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.TensorProduct.Maps
public import Sheaf.RingTheory.CotangentResolutionCoherence
import Sheaf.Algebra.Homology.BoundedFlatKFlat
import Sheaf.Algebra.Homology.KFlatScalarExtensionCounit
import Sheaf.RingTheory.LocalizationCotangentVanishing
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.RingTheory.Kaehler.Polynomial
import Sheaf.RingTheory.CotangentFlatBaseChange
import Sheaf.RingTheory.CotangentTransitivityTriangle

/-!
# Cotangent bootstrap from the diagonal

Source: Stacks Project, Cotangent Complex, Tag 08R1
(blueprint: lem-trf-cotangent-bootstrap).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Algebra.CotangentResolution

/-- `B` as an `A`-module along an arrow `A ⟶ B`, by restriction of scalars.
Source: Stacks Project, Cotangent Complex, Tag 08R1
(blueprint: lem-trf-cotangent-bootstrap). -/
def arrowModule (f : Arrow CommRingCat.{u}) : ModuleCat.{u} (f.left : Type u) :=
  (ModuleCat.restrictScalars f.hom.hom).obj
    (ModuleCat.of (f.right : Type u) (f.right : Type u))

/-- The multiplication arrow `B ⊗[A] B → B` defining the diagonal cotangent
complex `L_{B/(B ⊗_A B)}`. The tensor and its multiplication are Mathlib's
canonical constructions, with the algebra structure induced by the given arrow.
Source: Stacks Project, Cotangent Complex, Tag 08R1
(blueprint: lem-trf-cotangent-bootstrap). -/
def diagonalCotangentArrow (f : Arrow CommRingCat.{u}) : Arrow CommRingCat.{u} := by
  letI : Algebra (f.left : Type u) (f.right : Type u) := f.hom.hom.toAlgebra
  exact Arrow.mk (CommRingCat.ofHom
    (Algebra.TensorProduct.lmul' (f.left : Type u) (S := (f.right : Type u))).toRingHom)

/-- If the positive Tor groups of `B` over `A` vanish and the diagonal
cotangent complex vanishes, then the cotangent complex of `B` over `A`
vanishes. Source: Stacks Project, Cotangent Complex, Tag 08R1
(blueprint: lem-trf-cotangent-bootstrap).

Proof:
1. Put `D = B ⊗[A] B`, let `ι₁`, `ι₂` denote its two inclusions, and let
   `μ : D → B` be multiplication. Choose a free resolution `F` of `B` over `A`.
   By `lem-pc-module-bounded-flat-kflat` it is K-flat, and
   `lem-pc-kflat-scalar-extension-counit` computes the derived self-tensor by
   `F ⊗[A] B`. Its degree `-i` cohomology is `Torᵢ` by
   `def-weil-pbc-tor-modules`, and its degree zero is `D`. The Tor hypothesis
   therefore makes the canonical map `B ⊗ᴸ[A] B → D[0]` a quasi-isomorphism.
   Apply `lem-trf-cotangent-flat-base-change` to the square with factor maps
   `ι₁`, `ι₂`: this gives `L_{B/A} ⊗ᴸ[B] D ≅ L_{D/B}`, with scalar extension
   along `ι₁` and the right cotangent complex taken along `ι₂`.
2. Apply `lem-trf-cotangent-transitivity-triangle` to `B → D → B` using `ι₂`
   and `μ`. Its middle term is `L_{B/B} = 0`: identify the identity with
   localization at `{1}` by `lem-trf-localization-cotangent-vanishing` and the
   strictly functorial standard comparisons of
   `lem-trf-cotangent-resolution-coherence`. Its third term is `L_{B/D} = 0`
   by the diagonal hypothesis. The long exact sequence of
   `lem-sf-derived-homology-long-exact` shows `L_{D/B} ⊗ᴸ[D] B = 0`.
3. The standard complex `K` representing `L_{B/A}` has free terms by
   `lem-weil-pbc-polynomial-ring-kahler-basis-any-variables` and is zero in
   positive degrees by `lem-trf-cotangent-resolution-coherence`. It is K-flat
   by `lem-pc-module-bounded-flat-kflat`. Twice applying
   `lem-pc-kflat-scalar-extension-counit` computes the iterated scalar
   extension by `(K ⊗[B] D) ⊗[D] B`. The chain maps
   `(k ⊗ d) ⊗ b ↦ μ(d) b k` and `k ↦ (k ⊗ 1) ⊗ 1` are inverse because
   `μ ∘ ι₁ = id`. Thus it is isomorphic to `K`. Apply scalar extension along
   `μ` to Step 1 and use Step 2 to conclude that `L_{B/A}` is zero. -/
theorem cotangentComplex_isZero_of_tor_and_diagonal
    [∀ R : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    (C : Coherence.{u}) (f : Arrow CommRingCat.{u})
    (hTor : ∀ i : ℕ, 0 < i →
      IsZero (((CategoryTheory.Tor' (ModuleCat.{u} (f.left : Type u)) i).obj
        (arrowModule f)).obj (arrowModule f)))
    (hDiagonal : IsZero (cotangentComplex C (diagonalCotangentArrow f))) :
    IsZero (cotangentComplex C f) := by
  sorry

end Algebra.CotangentResolution
