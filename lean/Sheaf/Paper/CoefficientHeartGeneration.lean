/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.Paper.CoefficientHeart
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.Paper.CoefficientHeartCommonStratification
import Sheaf.Paper.CoefficientHeartFiltration
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import WeilConjectures.CategoryTheory.TruncationTriangle
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.CoefficientHeartTriangulated
import Sheaf.Paper.CondensedConstantConstructibility

/-!
# Finite cone generation of the bounded constructible coefficient category

Source: blueprint main-20261015, sec-six-functors-basics/sk-cor-coefficient-heart-ii/
sk-cor-coefficient-heart-ii-generation.md and its proof
(blueprint: det-cor-coefficient-heart-ii-generation).

The witness below is a nonempty finite sequence ending at the specified object. Its
entries are shifted lisse extensions or shifted cones between strictly earlier entries.
Distinguished triangles express cones intrinsically in the ordinary derived category.
No closure under arbitrary coproducts or direct summands enters the statement.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Bounded constructibility over E or Qbar_l is equivalent to the explicit finite cone
construction from shifted locally closed extensions of lisse coefficient modules.
`Fin (N + 1)` lists the objects K_1,...,K_{N+1}; its last entry equals K. A distinguished
triangle with third vertex `(F r)[n]` says that `F r` is a cone up to integer shift and
isomorphism, since distinguished triangles are closed under isomorphism.

Source: blueprint sk-cor-coefficient-heart-ii-generation and its proof
(blueprint: det-cor-coefficient-heart-ii-generation).

Proof plan (the five steps of the DAG node):
1. Let T be the class admitting such finite witnesses. Zero is a generator: take the
identity immersion and rank zero. Concatenate two witnesses and append their cone.
For an isomorphic replacement append a cone of zero into the old object. Shift every
entry to shift a witness; three rotations, or three inverse rotations, of a cone triangle
give the required signed shifted triangle. Iterate for every integer shift. These are
finite constructions and never require a direct summand or an infinite closure.
2. Factor a locally closed immersion through its scheme-theoretic closure, as in
sk-lem-coefficient-heart. Apply lem-weil-pbc-proetale-ringed-open-closed with the Cartesian
coefficient identifications of sk-prop-sfb-cartesian-coefficients. Its extension restricts
to L on S and zero on the closure minus S and outside the closure. All complementary
open immersions are quasi-compact: every open in Noetherian X is quasi-compact by
lem-weil-pbc-noetherian-open-subscheme-noetherian; an open in the closed closure is a
closed subset of an open of X, hence quasi-compact. Thus the three pieces, omitting empty
ones, give a finite lisse stratification. The criterion of sk-lem-coefficient-heart gives
constructibility. Shifts and cones preserve bounded constructibility by
det-cor-coefficient-heart-ii-triangulated, so induction on a witness proves the converse.
3. For a constructible sheaf take an adapted stratification from sk-lem-coefficient-heart.
Refine and order it by det-lem-coefficient-heart-common-stratification, preserving lisse
restrictions. Apply det-lem-coefficient-heart-filtration to get a finite filtration
0 = F_0 contained in ... contained in F_m = F with quotients A_k = a_{k!}L_k.
4. Regard each filtration sequence as a degree-zero short exact sequence of complexes.
lem-weil-pbc-complex-ses-triangle gives F_{k-1} -> F_k -> A_k -> F_{k-1}[1]. Inverse
rotation gives A_k[-1] -> F_{k-1} -> F_k -> A_k with the negative shifted connecting
map. Starting from zero, append this generator and cone at each stage. Shift this finite
witness to construct every F[n]. The zero sheaf requires only the rank-zero generator.
5. For a bounded constructible complex choose a representative C with cohomology in
[a,b]. By def-kun-truncations, the image of tau_le(a-1) C is zero in the derived category
and tau_le b C is isomorphic to K. For q from a to b, lem-weil-pbc-truncation-triangle
and inverse rotation exhibit tau_le q C as the cone of
H^q(C)[-q-1] -> tau_le(q-1) C, with the signed connecting map. Steps 3--4 give a witness
for the first term. Concatenate witnesses and append each cone, then use isomorphism
closure to end at K. Vanishing intermediate cohomology and an acyclic C use the same
zero case. Together with step 2 this proves the equivalence. -/
theorem coefficientHeart_generation (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (coefficientHeartRingObj Λ) X))) :
    constantModelBoundedConstructible (coefficientHeartRingObj Λ) X K ↔
      ∃ (N : ℕ) (F : Fin (N + 1) → DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (coefficientHeartRingObj Λ) X))),
        F (Fin.last N) = K ∧ ∀ r : Fin (N + 1),
          (∃ (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a)
            (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
              (condensedRingObj (coefficientHeartRingObj Λ) S)) (n : ℤ),
            IsLisseCoefficientModule (coefficientHeartRingObj Λ) L ∧
              Nonempty (F r ≅ ((DerivedCategory.singleFunctor _ 0).obj
                ((coefficientHeartLocallyClosedExtension
                  (coefficientHeartRingObj Λ) a ha).obj L))⟦n⟧)) ∨
          (∃ (i j : Fin (N + 1)), i < r ∧ j < r ∧
            ∃ (n : ℤ) (f : F i ⟶ F j) (g : F j ⟶ (F r)⟦n⟧)
              (h : (F r)⟦n⟧ ⟶ (F i)⟦(1 : ℤ)⟧),
              Pretriangulated.Triangle.mk f g h ∈ distTriang _) := by
  sorry

end AlgebraicGeometry.ProEtale
