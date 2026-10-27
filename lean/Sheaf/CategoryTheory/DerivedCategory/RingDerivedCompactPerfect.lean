/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.CompactObject
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import Sheaf.Algebra.Homology.SubcategoryLeftResolution
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.CompactHomHocolim
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Algebra.Module.Projective
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingSummand

/-!
# Compact derived modules are perfect

Source: Stacks Project, More on Algebra, Tag 07LT, `proposition-perfect-is-compact`,
implication (2) to (1), and Tag 0656, `definition-perfect`
(blueprint: lem-sfb-ring-derived-compact-perfect).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- A compact object of the unbounded derived category of modules over any commutative
ring is perfect. Its bounded model can equivalently have terms given as retracts of
finite free modules; the retraction ranks may be zero.

Source: Stacks Project, More on Algebra, Tag 07LT, `proposition-perfect-is-compact`,
implication (2) to (1), Tag 0656, `definition-perfect`, and Algebra, Tag 00NX
(blueprint: lem-sfb-ring-derived-compact-perfect).

Proof:
1. Represent E by K. The canonical maps to the good lower truncations T_n for n >= 0
   give K -> directSum T_n, since only finitely many summands occur in each degree.
   By lem-pc-derived-module-direct-sums this is a derived coproduct. Compactness
   (def-pc-compact-object) makes the map a finite sum of maps through summands.
   For n outside that finite support, E -> Q(T_n) is zero and induces the identity
   in cohomology in degrees r >= n. Thus E has an upper cohomological bound b.
2. Good upper truncation gives a complex C zero above b and quasi-isomorphic to K.
   Apply lem-sfb-subcategory-left-resolution to the class of all free modules.
   This class contains zero and covers every module by the free module on its
   underlying set. Obtain a bounded-above free complex P with Q(P) isomorphic to E.
3. The stupid lower truncations L_m of P have union P. If B is their direct sum and
   s is the successor map, 0 -> B --(1-s)--> B -> P -> 0 is degreewise exact:
   the first nonzero coordinate gives injectivity, finite support lets one move
   a class to a single late coordinate, and the union gives surjectivity.
   Use lem-weil-pbc-complex-ses-triangle and lem-pc-derived-module-direct-sums
   to form the telescope triangle. By lem-pc-compact-hom-hocolim, the identity
   of E factors through a bounded free L_m, giving a retraction E -> Q(L_m) -> E.
4. Induct upwards through the finitely many degrees [a,b] of this free complex L.
   Suppose all terms below c are finite free. The incoming differential has
   support in a finite subset S_0 of a basis of L^c. Projection gives a chain map
   L -> directSum of A[-c] over the remaining basis elements. Compactness and
   lem-pc-derived-module-direct-sums enlarge S_0 to a finite S such that the
   composite from E to the complementary sum is zero in D(A).
5. The degreewise kernel L' of this surjective projection has (L')^c = A^S and
   all other terms unchanged. Its short exact sequence yields a triangle by
   lem-weil-pbc-complex-ses-triangle. Clause (ii) of
   lem-weil-pbc-hom-into-triangle-exact lifts E -> Q(L) to E -> Q(L'). Composing
   the original projection to E retains the retraction. Induction makes every
   term finite free while retaining the fixed bounds.
6. Write the resulting retraction as i : E -> Q(F), p : Q(F) -> E. Complete i to
   a triangle. Its connecting map is zero: the rotated zero-composite clause of
   lem-weil-pbc-hom-into-triangle-exact gives i[1] composed with it equal to zero;
   composition with p[1] cancels i[1]. By lem-pc-derived-zero-third-split,
   Q(F) is a binary direct sum E + C. Finite free modules are finite projective
   by def-weil-pbc-projective-module, so lem-sf-perfect-ring-summand proves
   IsPerfectRingComplex E and supplies a bounded finite-projective model.
7. For each finite projective term M choose generators and the resulting
   surjection A^n -> M. Projectivity lifts id_M to a section, giving p.comp i = id.
   Conversely, given such a retraction, the images under p of the standard basis
   generate M; lifting maps on that basis and composing with i proves projectivity.
   This proves the equivalent termwise formulation, including rank zero outside
   the bounded interval. No Noetherian assumption occurs.
-/
theorem isPerfectRingComplex_of_isCompactObject {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (E : DerivedCategory (ModuleCat.{u} A)) (hE : IsCompactObject.{u} E) :
    IsPerfectRingComplex E ∧
      ∃ (F : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ),
        F.IsStrictlyGE a ∧ F.IsStrictlyLE b ∧
        (∀ r : ℤ, ∃ (n : ℕ) (i : F.X r →ₗ[A] (Fin n → A))
          (p : (Fin n → A) →ₗ[A] F.X r), p.comp i = LinearMap.id) ∧
        Nonempty (E ≅ Q.obj F) := by
  sorry

end DerivedCategory
