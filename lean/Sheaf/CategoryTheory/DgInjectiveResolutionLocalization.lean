/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.CategoryTheory.DgAlgebraHomotopyStructure
public import Sheaf.CategoryTheory.DgBimoduleModels
import Sheaf.CategoryTheory.DgGoodCharacterEmbedding
import Sheaf.Algebra.Homology.GoodCoresolutionProductTotal
import Sheaf.CategoryTheory.DgCompleteCofreeOrthogonality
import Sheaf.CategoryTheory.DgHomotopyAcyclicLocalization
import Mathlib.CategoryTheory.Triangulated.Orthogonal

/-!
# Homotopically injective DG resolutions and localization

Source: Stacks Project, dga.tex, Tags 09KU, 09KS and 09KY(2)
(blueprint: lem-sfb-dg-injective-resolution-localization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace CategoryTheory.DgAlgebra

/-- Every unbounded right DG module has a homotopically injective resolution.
The localization factors through the actual DG homotopy quotient, and its maps
into every homotopically injective target are bijective. These bijections are
natural in both variables: they are the maps of the single functor `L`, whose
composition law gives L(bfa)=L(b)L(f)L(a). Their inverses are consequently natural
by uniqueness. The equation `homotopyQuotient A ⋙ L = Q A` fixes this functor on
objects and on every representative, so the comparison is the canonical one.
Every integer shift, with its actual differential and unchanged right action,
preserves homotopical injectivity. No boundedness, flatness or commutativity is
assumed, and no triangulation structure is assumed to exist as an extra hypothesis.

Source: Stacks Project, dga.tex, Tag 09KU, lemma-right-resolution;
Tag 09KS, lemma-property-I-K-injective, applied in all shifts;
Tag 09KY, lemma-hom-derived, part (2) and its proof
(blueprint: lem-sfb-dg-injective-resolution-localization).

Proof plan (the five steps of the node):
1. Starting with M_0=Y, apply lem-sfb-dg-good-character-embedding to obtain
M_i into E_i and set M_{i+1}=E_i/M_i. Define E_i to E_{i+1} by quotient then
inclusion. The augmented coresolution is degreewise exact; each E_i has a
specified graded-split two-step filtration with character-dual shift products.
2. The differential-cokernel rows are right exact by lifting an element and
then a boundary preimage in the preceding degree. Their first maps are injective
by the same embedding lemma. Splice these sequences and apply
lem-sfb-good-coresolution-product-total to obtain Y into I, where
I^n is the product of E_i^(n-i) and d(x)_i=f_{i-1}(x_{i-1})+(-1)^i d(x_i).
Mixed terms cancel in d squared; the remaining terms vanish. Coordinatewise right
action satisfies Leibniz because (-1)^i(-1)^(n-i)=(-1)^n. The augmentation is DG-linear.
3. Filter I by zero coordinates j<i in step 2i, imposing additionally x_i in E_i'
in step 2i+1. The layers are (E_i/E_i')[-i] and E_i'[-i]. Coordinate sections
and the graded splittings split the quotient transitions, and compatible finite
truncations give completeness. Apply lem-sfb-dg-complete-cofree-orthogonality to
this filtration and all its shifts. Thus Hom_K(C,I[r]) vanishes for every acyclic
C and every r. The identity of homogeneous maps identifies Hom(C,I[r]) with
Hom(C,I)[r], including its signed differential, proving homotopical injectivity.
4. For any homotopically injective J, its defining condition gives Hom_K(C,J)=0
for acyclic C. Lem-sfb-dg-homotopy-acyclic-localization identifies quasi-isomorphisms
with the acyclic cone class in the triangulated homotopy category. Homotopic maps
have equal localization images, giving the factorization L. Apply
lem-sfb-right-orthogonal-localization-hom to this localization and J: its bijection
is exactly L.map, with no filtration assumption on J.
5. Functoriality gives the two-variable naturality of these bijections; bijectivity
gives naturality of the inverses. The same signed Hom-shift identity as in step 3
identifies H^n Hom(C,J[r]) with H^(n+r) Hom(C,J), so all shifts remain injective.
All products and complexes use the fixed component universe; no support or
flatness restriction occurs. -/
theorem dg_injective_resolution_localization (A : Algebra.{u}) :
    (∀ Y : RightModule A, ∃ (I : RightModule A) (i : Y ⟶ I),
      quasiIsomorphisms A i ∧ IsHomotopicallyInjective A I) ∧
    (∃ L : HomotopyCategory A ⥤ Derived A,
      homotopyQuotient A ⋙ L = Q A ∧
      ∀ (X I : RightModule A), IsHomotopicallyInjective A I →
        Function.Bijective (L.map :
          ((homotopyQuotient A).obj X ⟶ (homotopyQuotient A).obj I) →
            (L.obj ((homotopyQuotient A).obj X) ⟶
              L.obj ((homotopyQuotient A).obj I)))) ∧
    (∀ I : RightModule A, IsHomotopicallyInjective A I →
      ∀ (r : ℤ) (S : RightModule A), ShiftComparison A r I S →
        IsHomotopicallyInjective A S) := by
  sorry

end CategoryTheory.DgAlgebra
