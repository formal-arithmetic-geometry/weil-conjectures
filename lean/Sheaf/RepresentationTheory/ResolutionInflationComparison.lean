/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker Q39
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.RepresentationTheory.Homological.Resolution
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Sheaf.Algebra.Homology.QuotientTensorResolutionLiftHomotopy

/-!
# Projective resolution maps compute inflation

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-base-field-cd,
sk-lem-base-field-cd-inflation.proof.md, paragraph 3, "It computes inflation";
Stacks Project, Tag 00LS, comparison homotopy construction
(blueprint: lem-sfb-resolution-inflation-comparison).

The integer ring is lifted to the common ambient universe. A representation over this
ring is precisely an abelian group with a group action. The cochain map is specified on
every equivariant homomorphism, so the assertion includes the actual precomposition map.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace groupCohomology

/-- A quotient-equivariant chain map of projective resolutions lifting the identity
computes inflation in every nonnegative degree.

Source: blueprint main-20261015, sk-lem-base-field-cd-inflation.proof.md, paragraph 3;
Stacks Project, Tag 00LS, part (2)
(blueprint: lem-sfb-resolution-inflation-comparison).

Proof:
1. Apply `lem-sfb-bar-resolution-cochains` to both groups. It gives projective bar
resolutions B, B' and evaluation isomorphisms from their Hom complexes to the displayed
inhomogeneous cochain complexes.
2. Map the free basis of B' to that of B by applying π to the coefficients and every
entry of a tuple. Multiplicativity of π makes this map b commute with each differential;
it preserves augmentation. Evaluation identifies precomposition by b with cochain
pullback along π in every coordinate.
3. Use `lem-sfb-projective-resolution-homotopy-equivalence` separately over the two
group rings to choose augmentation-preserving homotopy inverse comparisons u : P → B,
v : B → P and u' : P' → B', v' : B' → P'. No restricted resolution is asserted projective.
4. If a - a' = d h + h d and z is a Hom cocycle, then z(a - a') = (z h)d is a
coboundary. In degree zero it is zero since h in degree -1 is zero. Thus u and v,
and likewise u' and v', induce inverse isomorphisms on Hom cohomology.
5. By `new-t4-augmented-resolution-lift-homotopy`, any two augmentation-preserving
comparisons are homotopic, so these identifications are canonical. The module categories
are abelian: kernels and cokernels carry induced actions and coimage maps isomorphically
to image. Epimorphisms are surjections, so the stated lifting property is categorical
projectivity. These are the canonical identifications `groupCohomologyIso`.
6. Compare A = (Res u) f and A' = b u' from P' to Res B. They have the same
augmentation. Restriction changes no underlying groups, kernels or images, so Res B
remains augmented exact. Apply `new-t4-augmented-resolution-lift-homotopy` to obtain a
homotopy between A and A'; only the source P' must have projective terms.
7. For a cocycle z : B_s → M, the homotopy gives
z u_s f_s - z b_s u'_s = (z h_{s-1})d, with zero difference for s = 0. Hence
f* u* = (u')* b* on cohomology. Step 2 identifies b* with inflation, and Steps 4–5
identify u* and (u')* with the canonical resolution isomorphisms. This is the displayed
square for every natural degree. The cochain map F itself is restriction followed by
precomposition; the chain-map equation for f verifies commutation with differentials. -/
theorem resolution_inflation_comparison
    {G G' : Type u} [Group G] [Group G']
    (π : G' →* G) (hπ : Function.Surjective π)
    (M : Rep.{u} (ULift.{u} ℤ) G)
    (P : ProjectiveResolution (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ)))
    (P' : ProjectiveResolution (Rep.trivial (ULift.{u} ℤ) G' (ULift.{u} ℤ)))
    (f : P'.complex ⟶
      ((Rep.resFunctor (k := ULift.{u} ℤ) π).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex)
    (hf : f.f 0 ≫ (Rep.resFunctor π).map (P.π.f 0) = P'.π.f 0) :
    ∃ F : P.complex.linearYonedaObj (ULift.{u} ℤ) M ⟶
        P'.complex.linearYonedaObj (ULift.{u} ℤ) (Rep.res π M),
      (∀ (n : ℕ) (h : P.complex.X n ⟶ M),
        (F.f n) h = f.f n ≫ (Rep.resFunctor π).map h) ∧
      ∀ s : ℕ,
        (groupCohomologyIso M s P).hom ≫ HomologicalComplex.homologyMap F s =
          groupCohomology.map π (𝟙 (Rep.res π M)) s ≫
            (groupCohomologyIso (Rep.res π M) s P').hom := sorry

end groupCohomology
