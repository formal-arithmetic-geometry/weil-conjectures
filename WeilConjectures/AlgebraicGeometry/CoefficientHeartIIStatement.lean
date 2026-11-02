/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartFiltration
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSmall
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Triangulation and finite cone generation for field coefficients

Source: blueprint latest,
`part-six-operations/sec-reduction-finite-coefficients/`
`sec-constructible-sheaves-with-field-coefficients/sk-cor-coefficient-heart-ii/_section.md`
and `sk-cor-coefficient-heart-ii.proof.md` (blueprint: sk-cor-coefficient-heart-ii).

The standing setting is a separated finite-type scheme over a field of positive
characteristic, with characteristic different from the coefficient prime.  The
constructible property is the existing bounded constructible property for the
pulled-back condensed coefficient ring.  The proof follows the blueprint: the long
exact cohomology sequence with the closure clause of `sk-lem-coefficient-heart`,
then truncation induction and the finite filtration clause of that lemma.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- In the standing coefficient setting, bounded constructible complexes form a
triangulated subcategory and admit finite cone presentations by shifted locally
closed extensions of lisse modules.

Source: blueprint latest,
`part-six-operations/sec-reduction-finite-coefficients/`
`sec-constructible-sheaves-with-field-coefficients/sk-cor-coefficient-heart-ii/_section.md`
and `sk-cor-coefficient-heart-ii.proof.md`, both paragraphs
(blueprint: sk-cor-coefficient-heart-ii).

The first conjunct is the triangulated-subcategory assertion.  The second
conjunct gives a finite sequence ending at the chosen complex; each term is
an integer shift of a canonical locally closed extension of a lisse module,
or is a shifted cone whose two inputs occur earlier in the sequence.  The
Noetherian structure used by the canonical extension is constructed from the
standing finite-type and quasi-compact hypotheses.

Proof plan, following the node's three steps:
1. For a distinguished triangle `K → K' → K'' → K[1]` with `K, K'` bounded
   constructible, the long exact homology sequence
   (lem-sf-derived-homology-long-exact) makes each `H^i K''` an extension of
   `ker(H^{i+1} K → H^{i+1} K')` by `coker(H^i K → H^i K')`; both are constructible by
   clause (1) of sk-lem-coefficient-heart, hence so is `H^i K''`, and `K''` vanishes
   outside `[a-1, b]` when `K, K'` live in `[a, b]`.  Zero and isomorphic objects stay
   inside, `H^i(K[n]) = H^{i+n}(K)` gives shift stability, and rotation gives
   two-out-of-three: the property is triangulated.
2. Generation: induct on the number of nonzero `H^i K`.  If none, `K ≅ 0`, the cone of
   the identity of `Λ_X[0]` (`a = id_X`, free rank-one lisse module).  Otherwise let
   `i` be the top degree; the truncation triangle
   (def-sbc-standard-tstructure-derived-category, lem-weil-pbc-truncation-triangle)
   `τ_{<i} K → K → H^i(K)[-i] →` rotated backwards exhibits `K` as a cone of
   `H^i(K)[-i-1] → τ_{<i} K`, and `τ_{<i} K` has one fewer nonzero cohomology sheaf.
3. For a constructible sheaf `F`, the filtration of clause (3) of
   sk-lem-coefficient-heart has quotients `a_{k!} L_k`; each short exact sequence
   `0 → F_{k-1} → F_k → a_{k!} L_k → 0` is a distinguished triangle
   (lem-sf-derived-ses-triangle), so backward rotation builds `F` (and all its shifts)
   by finitely many cones from shifted generators.  Concatenating these finite
   sequences with the cones of step 2 gives the finite sequence of the conclusion.
-/
theorem coefficientHeartIIStatement (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    (constantModelBoundedConstructible (coefficientHeartRingObj Λ) X).IsTriangulated ∧
      ∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (coefficientHeartRingObj Λ) X)),
        constantModelBoundedConstructible (coefficientHeartRingObj Λ) X K →
          ∃ (N : ℕ) (F : Fin (N + 1) → DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
              (condensedRingObj (coefficientHeartRingObj Λ) X))),
            F (Fin.last N) = K ∧ ∀ r : Fin (N + 1),
              (∃ (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a)
                (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
                  (condensedRingObj (coefficientHeartRingObj Λ) S)) (n : ℤ),
                IsLisseCoefficientModule (coefficientHeartRingObj Λ) L ∧
                  Nonempty (F r ≅ ((DerivedCategory.singleFunctor _ 0).obj
                    ((@coefficientHeartLocallyClosedExtension
                      (coefficientHeartRingObj Λ) _ S X
                      (@AlgebraicGeometry.IsNoetherian.noetherianSpace X
                        { toIsLocallyNoetherian :=
                            LocallyOfFiniteType.isLocallyNoetherian
                              (X ↘ Spec (.of k))
                          toCompactSpace :=
                            QuasiCompact.compactSpace_of_compactSpace
                              (X ↘ Spec (.of k)) }) a ha).obj L))⟦n⟧)) ∨
              (∃ (i j : Fin (N + 1)), i < r ∧ j < r ∧
                ∃ (n : ℤ) (f : F i ⟶ F j) (g : F j ⟶ (F r)⟦n⟧)
                  (h : (F r)⟦n⟧ ⟶ (F i)⟦(1 : ℤ)⟧),
                  Pretriangulated.Triangle.mk f g h ∈ distTriang _) := by
  sorry

end AlgebraicGeometry.ProEtale
