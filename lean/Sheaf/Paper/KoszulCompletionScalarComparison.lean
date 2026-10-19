/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.Paper.AdicReductionAdjunction
public import Sheaf.Paper.IntrinsicKoszulCompletion
import all WeilConjectures.RingTheory.KoszulBaseChangeIso
import Sheaf.Paper.StrictPerfectCoefficientPackage
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses

/-! # Perfect scalar extension commutes with the Koszul product cone

Source: literature/blueprint/main-20261015/blueprint/sec-proper-base-change/
sk-thm-properbasechange/lemma-weil-pbc-adic-completion-reduction.proof.md,
first three proof sentences (order 1328).
(blueprint: lem-weil-pbc-koszul-completion-scalar-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The canonical scalar comparison for the Koszul cone, with its unit square.
No relation between `f` and `d.ideal` is required for this tensor comparison.

Source: literature/blueprint/main-20261015/blueprint/sec-proper-base-change/
sk-thm-properbasechange/lemma-weil-pbc-adic-completion-reduction.proof.md,
first three proof sentences (order 1328).
(blueprint: lem-weil-pbc-koszul-completion-scalar-comparison).

Proof: represent the perfect quotient by a bounded finite-projective complex over Λ.
Sheafify the complex and its finite-free retract splittings. Tensoring a finite-free
term with a countable product commutes with that product by its coordinates; restricting
to the retract proves the assertion for each finite-projective term. In each total degree
only finitely many coefficient degrees contribute, so finite biproducts commute with the
countable products. Exact countable products on the pro-etale site compute the derived
products. Thus derived scalar extension commutes with both products in the Koszul cone.
The tensor-cone comparison, with the shifted-coordinate sign, identifies this cone with
the Koszul cone formed over the quotient ring. Use the exterior-basis construction
proving nonempty_koszulBaseChangeIso for coefficient base change. It sends generators
to their quotient images; checking the diagonal maps proves transition compatibility.
On the
unit summand every comparison sends c tensor 1 to c tensor 1. This gives the displayed
unit square. K-flat computation and the canonical Hom equivalence transport the result
to the arbitrary model P. Bounds and ranks are finite even for the empty generator list;
the zero-ring case consists entirely of zero objects. -/
theorem koszulCompletionScalarComparison (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) (r : ℕ) (f : Fin r → Λ)
    {K : proEtaleDerivedCategory X Λ} (M : AdicKFlatModel X Λ K)
    (P : AdicKFlatModel X Λ
      ((adicLocalization X Λ).obj (koszulCompletionComplex X Λ r f M.complex))) (n : ℕ) :
    ∃ e : adicReduction X d P ⟨n + 1, Nat.succ_pos n⟩ ≅
        (adicLocalization X (Λ ⧸ d.ideal ^ (n + 1))).obj
          (koszulCompletionComplex X (Λ ⧸ d.ideal ^ (n + 1)) r
            (fun j ↦ Ideal.Quotient.mk (d.ideal ^ (n + 1)) (f j))
            (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) M.complex)),
      adicReductionMap X d M P n
          (M.realization.inv ≫ (adicLocalization X Λ).map
            (koszulCompletionUnitComplex X Λ r f M.complex)) ≫ e.hom =
        (adicLocalization X (Λ ⧸ d.ideal ^ (n + 1))).map
          (koszulCompletionUnitComplex X (Λ ⧸ d.ideal ^ (n + 1)) r
            (fun j ↦ Ideal.Quotient.mk (d.ideal ^ (n + 1)) (f j))
            (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) M.complex)) := by
  sorry

end AlgebraicGeometry.Scheme
