/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism
import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.FiniteBirationalNormalIso
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import Sheaf.TraceFormula.NodalSubcurveBoundary
import Sheaf.AlgebraicGeometry.NodalCurveNormalizationEuler

/-! # Euler defect of a nodal subcurve contracted to a smooth point

Source: Temkin, Stable modification of relative curves, Appendix B, Lemma B.1 and
Corollary B.2, pp. 57--58; the explicit closed-union calculation of the DAG node
uses Stacks Project, Tags 0E38, 02OG, 0AB1, 0C4J, 08AA, 0C1R and 0CBW
(blueprint: lem-trf-nodal-contraction-euler-defect).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory
open scoped BigOperators

namespace AlgebraicGeometry

/-- Contracting a connected nodal subcurve to a smooth point has Euler defect equal
to its number of components minus its internal nodes, boundary points and component genera.

The closed point `y` is equivalently a `k`-point by `pointEquivClosedPoint`. The reduced
closed immersion `i` with image `f ⁻¹' {y}` specifies the reduced fibre, without requiring
the scheme-theoretic fibre to be reduced. The equivalence `components` enumerates all
irreducible components exactly once. The integral closed immersions `j a` give these
components their reduced structure. Their normalizations use the recorded canonical
`Scheme.normalization` and `Scheme.fromNormalization` constructions. On these smooth proper
connected curves, `Scheme.Hom.genus` is `dim_k H¹(𝒪)`, by Serre duality. The nonsmooth points
of `B` count internal nodes once, including self-nodes. Boundary nodes are smooth on `B`.
All subtractions take place in `ℤ`. No equality of Euler characteristics, zero-genus condition
or tree condition is assumed.

Source: Temkin, Appendix B, Lemma B.1 and the calculation in Corollary B.2, pp. 57--58;
Stacks Project, Tags 0E38, 02OG, 0AB1, 0C4J, 08AA, 0C1R and 0CBW
(blueprint: lem-trf-nodal-contraction-euler-defect).

Proof (the seven steps of the DAG node):
1. Proper finite-type schemes over `k` are Noetherian. Let `A` be the reduced closure of
   `D` minus `B`. Pure dimension one makes `B` a union of whole irreducible components,
   with `A` the union of the remaining components. Their radical ideals intersect in zero.
   The nodal-subcurve-boundary lemma applied on `N` makes `B` nodal and identifies the
   scheme-theoretic intersection `T = A ∩ B` with `r` reduced copies of `Spec k`.
2. The restriction `h : A → C` is proper and an isomorphism off `y`. Its fibre over `y`
   has the finite underlying set `T`. Every other fibre is a singleton or empty, so the
   proper-finite-fibres criterion makes `h` finite. Closed subcurves `A`, `B`, `T` are proper.
3. Take a smooth open neighbourhood of `y` in `C`. It is normal; its components are
   disjoint. Retain the integral component containing `y`. Every component of `A` meets
   the complement of `B`, so its inverse image is reduced and has the single generic point
   supplied by the off-`y` isomorphism. It is integral. The function fields agree on that
   dense open. Finite-birational-normal-iso makes `h` an isomorphism there. Together with
   the given off-`y` isomorphism this gives `A ≅ C`.
4. For the closed inclusions of `A`, `B`, `T` into `D`, restriction and difference of
   restrictions give `0 → 𝒪_D → 𝒪_A ⊕ 𝒪_B → 𝒪_T → 0`, with direct images understood.
   Affine-locally it is `0 → R → R/I ⊕ R/J → R/(I+J) → 0`, since `I ∩ J = 0`.
   Pairs with the same residue lift to `R`; lifting into the first summand gives surjectivity.
5. Closed-immersion coherent cohomology and Euler additivity give
   `χ(D) = χ(A) + χ(B) - χ(T)`. The finite discrete reduced scheme `T` has global
   sections of dimension `r` over `k` and no higher cohomology. Hence `χ(D) - χ(C) = χ(B) - r`.
   This step allows disconnected `C`, `D` and an empty boundary.
6. Nodal-curve-normalization-euler applies to the proper reduced connected nodal curve
   `B`, giving `χ(B) = v - e - sum_i g_i`. Self-nodes contribute once. Boundary nodes
   are smooth on `B` and have already contributed to `r`.
7. Substitute the normalization identity into the closed-union identity and rearrange
   in `ℤ` to obtain the displayed formula.
-/
theorem nodal_contraction_euler_defect
    (k : Type u) [Field k] [IsAlgClosed k]
    {C D : Scheme.{u}} [C.Over (Spec (.of k))] [D.Over (Spec (.of k))]
    [IsProper (C ↘ Spec (.of k))] [IsProper (D ↘ Spec (.of k))]
    [IsReduced C] [IsReduced D]
    (hC : C.IsPureDimension 1) (hD : D.IsPureDimension 1)
    (f : D ⟶ C) [f.IsOver (Spec (.of k))] [IsProper f]
    (y : C) (hy : IsClosed ({y} : Set C)) (hysmooth : y ∈ (C ↘ Spec (.of k)).smoothLocus)
    (B : Scheme.{u}) [IsReduced B] [ConnectedSpace B]
    (i : B ⟶ D) [IsClosedImmersion i]
    (hB : Set.range i = f ⁻¹' {y}) (hBpure : B.IsPureDimension 1)
    (hoff : IsIso (f ∣_ (⟨{y}ᶜ, hy.isOpen_compl⟩ : C.Opens)))
    (N : D.Opens) (hN : Set.range i ⊆ N)
    (hnodal : ∀ x : D, x ∈ N → x ∉ (D ↘ Spec (.of k)).smoothLocus →
      Nonempty (AdicCompletion (IsLocalRing.maximalIdeal (D.presheaf.stalk x))
        (D.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) k ⧸ Ideal.span
            {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1})))
    (v : ℕ) (components : Fin v ≃ irreducibleComponents B)
    (Z : Fin v → Scheme.{u}) [∀ a : Fin v, IsIntegral (Z a)]
    (j : ∀ a : Fin v, Z a ⟶ B) [∀ a : Fin v, IsClosedImmersion (j a)]
    (hcomponents : ∀ a : Fin v, Set.range (j a) = (components a).1)
    (hnormalizations : ∀ a : Fin v,
      IsProper ((Z a).fromNormalization ≫ j a ≫ i ≫ D ↘ Spec (.of k)) ∧
      Smooth ((Z a).fromNormalization ≫ j a ≫ i ≫ D ↘ Spec (.of k)) ∧
      ConnectedSpace (Z a).normalization) :
    Scheme.Modules.eulerChar k (SheafOfModules.unit D.ringCatSheaf) -
        Scheme.Modules.eulerChar k (SheafOfModules.unit C.ringCatSheaf) =
      (v : ℤ) - (Nat.card {b : B // b ∉ (i ≫ D ↘ Spec (.of k)).smoothLocus} : ℤ) -
        (Nat.card {x : D // x ∈ Set.range i ∩ closure (Set.range i)ᶜ} : ℤ) -
        ∑ a : Fin v, (((Z a).fromNormalization ≫ j a ≫ i ≫ D ↘ Spec (.of k)).genus : ℤ) := by
  sorry

end AlgebraicGeometry
