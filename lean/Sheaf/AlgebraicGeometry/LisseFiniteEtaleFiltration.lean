/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.CategoryTheory.Subobject.Limits

import Sheaf.Paper.GaloisLisseRepresentations
import Sheaf.AlgebraicGeometry.FundamentalGroup.OpenSubgroups
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import Sheaf.RepresentationTheory.PrimaryPGroupFiltration
import Sheaf.AlgebraicGeometry.FiniteEtaleTraceDegree
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.GroupTheory.Sylow
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Prime-to-primary finite étale filtration covers

Source: Stacks Project, Tags 0GJ0 and 0DV5 (3), with componentwise assembly on an
affine Noetherian base (blueprint: lem-weil-pbc-etale-lisse-finite-etale-filtration).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- A finite local system of modules over a finite ring, killed by a positive prime power,
admits a finite étale surjection of constant prime-to-primary degree, and on a finite affine
clopen decomposition of its source the pullback has constant finite-module graded pieces.
Source: Stacks Project, Tags 0GJ0, 0DV5 (3), 0DV6 and 0GIZ
(blueprint: lem-weil-pbc-etale-lisse-finite-etale-filtration).

Proof plan:
1. For the empty base use its identity, degree one, and no clopen summands. Otherwise an
   affine Noetherian scheme is Noetherian and has finitely many irreducible components
   (`pqf-def-locnoeth`, `lem-weil-pbc-affine-scheme-qcqs`,
   `lem-weil-pbc-noetherian-finitely-many-components`).
2. The intersection graph of the irreducible components partitions them into connected
   clopen unions. The clopen-idempotent theorem and principal localization identify these
   unions with affine schemes (`def-weil-irreducible-components`,
   `lem-weil-pbc-spec-clopen-idempotent`, `lem-weil-pbc-principal-localization-open-immersion`).
3. On each component the finite-coefficient part of `cor-galois-lisse-representations`
   identifies the sheaf with a finite module with continuous fundamental-group action.
4. Its monodromy image is finite and its kernel is open, since it is the intersection of
   finitely many open stabilizers. Take an ell-Sylow subgroup, of positive prime-to-ell index
   (`lem-weil-pbc-sylow-subgroup-prime-index`), and its open inverse image.
5. The open-subgroup correspondence supplies a connected finite étale cover of that index.
   Pullback restricts the module action to the Sylow subgroup, with the same fibre module
   (`cor-galois-open-subgroups`, `thm-galois-fundamental`,
   `lem-weil-pbc-finite-etale-trace-degree`). Positive degree gives surjectivity.
6. Apply `lem-sc-primary-pgroup-filtration` to the primary additive group of the fibre.
   This permits the zero group and a length-zero chain.
7. Take the coefficient-ring spans of that additive filtration. Linearity implies that
   h*z-z lies in the preceding span, so the quotient module has trivial action. The
   quotients are finite sets because the fibre is finite.
8. The exact finite-coefficient equivalence turns these invariant submodules into sheaf
   subobjects and their quotients into constant finite-module sheaves
   (`cor-galois-lisse-representations`, `def-weil-pbc-constant-sheaf`).
9. Finite covers of the affine components are affine. Repeat the cover over component j
   by the product of all other component degrees. Their finite coproduct is affine and
   finite over the base, by the finite-product spectrum and affine fibre-product formulas
   (`lem-weil-pbc-affine-morphism-permanence`, `def-weil-finite-integral-morphism`,
   `lem-weil-pbc-finite-affine-coproduct-spectrum`, `lem-weil-pbc-fibre-product-affine-spectra`).
10. The coproduct map is étale and has the common positive prime-to-ell degree. Its
    summands are affine and clopen. Inverse-image composition carries their filtrations
    to the restrictions of the global pullback, respecting all scalar operations
    (`lem-weil-pbc-etale-composition-cancellation`, `lem-sc-etale-coproduct-etale`,
    `lem-weil-pbc-scheme-coproduct-family`, `def-weil-pbc-inverse-image`,
    `lem-weil-pbc-inverse-image-composition`). -/
theorem exists_lisse_finiteEtale_filtration
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteLocallyConstantSheaf F]
    (ℓ n : ℕ) (hℓ : ℓ.Prime) (hn : 1 ≤ n) (hF : (ℓ ^ n) • 𝟙 F = 0) :
    ∃ (T : Scheme.{u}) (g : T ⟶ Spec (.of A)),
      IsFinite g ∧ Etale g ∧ Surjective g ∧
      ∃ d : ℕ, 1 ≤ d ∧ ¬ ℓ ∣ d ∧
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of A)),
          Nat.card (g.GeometricFiber s) = d) ∧
        ∃ (k : ℕ) (U : Fin k → T.Opens),
          (∀ a, IsAffineOpen (U a) ∧ IsClosed (U a : Set T)) ∧
          Pairwise (fun a b => Disjoint (U a) (U b)) ∧
          (⋃ a, (U a : Set T)) = Set.univ ∧
          ∀ a : Fin k, ∃ (r : ℕ)
            (c : Fin (r + 1) → Subobject
              ((upperStar (ModuleCat.{u + 1} Λ) (U a).ι).obj
                ((upperStar (ModuleCat.{u + 1} Λ) g).obj F)))
            (hc : Monotone c),
            IsZero (c 0 : Sheaf (U a).toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ∧
            c (Fin.last r) = ⊤ ∧
            ∀ i : Fin r, ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
              Nonempty (cokernel (Subobject.ofLE (c i.castSucc) (c i.succ)
                (hc (Fin.castSucc_le_succ i))) ≅
                  (constantSheaf (U a).toScheme.smallEtaleTopology
                    (ModuleCat.{u + 1} Λ)).obj M) := by
  sorry

end AlgebraicGeometry.Etale
