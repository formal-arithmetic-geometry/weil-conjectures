/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Topology.NoetherianSpace
import Sheaf.Paper.FiniteModelStratumFiltration
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.CategoryTheory.TruncationTriangle

/-!
# Finite generation from constant-model strata

Source: Stacks Project, Tags 08J5 and 09Y5; finite-stratum and Postnikov assembly
extracted from Bhatt--Scholze, Lemma 6.3.14 and Proposition 6.8.11(3)
(blueprint: lem-sfb-bounded-finite-model-generation).

The finite witness is a list of derived objects ending at K up to isomorphism.
Each entry is zero, a specified stratum generator, an integer shift of an earlier
entry up to isomorphism, or an extension of two strictly earlier entries.
The ordinary uncompleted derived category and arbitrary condensed coefficients are used.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Every bounded constant-model constructible complex lies in any isomorphism-closed
class containing zero and the indicated stratum sheaves and closed under integer shifts
and extensions. There is an explicit finite construction using precisely these operations.
Here `C.IsTriangulated` packages ContainsZero, IsStableUnderShift and
IsTriangulatedClosed₂; with isomorphism closure its last condition is exactly extension
closure in the middle vertex, not closure under retracts or infinite coproducts.

Source: Stacks Tags 08J5, 09Y5; Bhatt--Scholze Lemma 6.3.14 and Proposition 6.8.11(3),
finite-stratum/Postnikov assembly (blueprint: lem-sfb-bounded-finite-model-generation).

Proof plan (the five steps of the node):
1. For each constructible sheaf F, `lem-sfb-finite-model-stratum-filtration` supplies a
finite filtration from zero to F whose quotients are v_! t_* L with S reduced closed
in V and L having a finite constant local model. These are exactly the assumed generators.
2. Place each filtration sequence in degree zero. By
`lem-weil-pbc-complex-ses-triangle` it gives a distinguished triangle. Induction on the
finite filtration length, starting with zero, puts F[0] in C. Concatenating the finite
witnesses for the two outer vertices and appending the middle vertex records each step.
3. For K with cohomology in [a,b], set T_q = tau_le q K on a cochain representative.
By `lem-weil-pbc-truncation-cohomology`, T_(a-1) is acyclic and T_b -> K is a
quasi-isomorphism. The localization `def-weil-abstract-derived-category` therefore
identifies them with zero and K, respectively; no infinite truncation tower is used.
4. For q = a,...,b, `lem-weil-pbc-truncation-triangle` supplies the triangle
T_(q-1) -> T_q -> H^q(K)[-q] -> T_(q-1)[1]. Steps 1--2 construct H^q(K)[0]. Append
its integer shift, then this extension. Finite induction and the final isomorphism
put K in C and produce the displayed finite list.
5. The finitely many sheaf filtration lengths and the b-a+1 Postnikov steps have finite
sum. An acyclic K needs only a zero object. The empty scheme permits length zero.
No argument uses a field, finite Tor amplitude, or torsion-freeness, so arbitrary
commutative condensed rings and integral torsion local models are included. -/
theorem bounded_finiteModel_generation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (C : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
    [C.IsClosedUnderIsomorphisms] [C.IsTriangulated]
    (hgen : ∀ (V S : Scheme.{u}) (v : V ⟶ X) [IsOpenImmersion v]
      (t : S ⟶ V) [IsClosedImmersion t] [IsReduced S]
      (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)),
      HasFiniteConstantLocalModel Λ S L →
        C ((DerivedCategory.singleFunctor _ 0).obj
          ((openImmersionLowerShriek Λ v).obj ((lowerStar Λ t).obj L))))
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hK : constantModelBoundedConstructible Λ X K) :
    C K ∧ ∃ (N : ℕ) (F : Fin (N + 1) → DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      Nonempty (F (Fin.last N) ≅ K) ∧ ∀ r : Fin (N + 1),
        IsZero (F r) ∨
        (∃ (V S : Scheme.{u}) (v : V ⟶ X), Exists fun [IsOpenImmersion v] ↦
          ∃ t : S ⟶ V, IsClosedImmersion t ∧ IsReduced S ∧
          ∃ L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S),
            HasFiniteConstantLocalModel Λ S L ∧
            Nonempty (F r ≅ (DerivedCategory.singleFunctor _ 0).obj
              ((openImmersionLowerShriek Λ v).obj
                ((lowerStar Λ t).obj L)))) ∨
        (∃ (i : Fin (N + 1)) (n : ℤ), i < r ∧ Nonempty (F r ≅ (F i) ⟦n⟧)) ∨
        (∃ (i j : Fin (N + 1)), i < r ∧ j < r ∧
          ∃ (f : F i ⟶ F r) (g : F r ⟶ F j) (h : F j ⟶ (F i) ⟦(1 : ℤ)⟧),
            Pretriangulated.Triangle.mk f g h ∈ distTriang _) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
