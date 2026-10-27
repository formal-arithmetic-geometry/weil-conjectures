module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Finite surjective morphism of Proj for a finite graded extension

Source: Stacks Project, Constructions, Tag 01MY (lemma-morphism-proj), together with
Algebra, Tags 00GK, 00GQ and 07Z2, and Morphisms, Tag 01WI
(blueprint: `lem-per-finite-graded-proj-morphism`).

The statement records the canonical morphism on Proj induced by an injective finite
extension of nonnegative graded commutative rings.  Its chart formula is expressed
through Mathlib's homogeneous localization and Proj chart maps.
-/

@[expose] public section

universe u

open CategoryTheory HomogeneousLocalization

namespace AlgebraicGeometry

variable {C A σ τ : Type u}
variable [CommRing C] [CommRing A]
variable [SetLike σ C] [AddSubgroupClass σ C]
variable [SetLike τ A] [AddSubgroupClass τ A]
variable {𝒞 : ℕ → σ} {𝒜 : ℕ → τ}
variable [GradedRing 𝒞] [GradedRing 𝒜]

/--
For an injective graded map which is finite and whose source is finite type over its
degree-zero part, the induced Proj morphism is finite and surjective and has the
usual homogeneous-localization chart maps.

Source: Stacks Project, Constructions, Tag 01MY (lemma-morphism-proj), with the
finite and surjective conclusions supplied by Algebra, Tags 07Z2, 00GK and 00GQ,
and Morphisms, Tag 01WI (blueprint: `lem-per-finite-graded-proj-morphism`).
Proof:
1. Replace finite `C`-module generators of `A` by their homogeneous components,
   include one, and bound their degrees by `N`. For a homogeneous element of
   degree greater than `N`, project a generator expansion to that degree: all
   its coefficients have positive degree in `C`. At a point of `Proj 𝒜`, take
   a positive-degree element outside the prime and raise it to degree above `N`.
   Its expansion shows that some positive-degree element of `C` also stays
   outside the contracted prime. Thus the source charts cover the whole Proj
   (`def-weil-finitely-generated-module`, `def-pc-proj`).
2. On every homogeneous chart define the map by applying `ι` to numerator and
   denominator. The localization relation makes it well defined, and
   injectivity of `ι` makes the chart map injective
   (`def-nagata-homogeneous-localization-degree-zero`, `def-weil-affine-spectrum`).
3. On two chart overlaps the intersection formula identifies the principal
   opens cut out by `g^d/f^e`. Their ring maps agree because both send each
   fraction with denominator `(fg)^m` to its image fraction
   (`lem-weil-pbc-proj-basic-open-intersection`).
4. Glue these agreeing chart maps to a morphism on the entire source. The
   fraction formulas characterize the canonical morphism of Tag 01MY
   (`lem-weil-pbc-scheme-morphism-gluing`).
5. In each source chart the inverse image of `D₊(f)` is the principal open
   of the image of `f^e/g^d`, hence is the intersection with `D₊(ι(f))`.
   The charts cover, giving the stated inverse-image equality and chart square
   (`lem-weil-pbc-proj-basic-open-intersection`, `def-pc-proj`).
6. Regard `A` as the finite graded `C`-module with action through `ι`.
   Dehomogenization identifies its finite degree-zero module with the chart
   ring `Away 𝒜 (ι f)`, with scalar action `Away.map ι f`. Finiteness is local
   on the target, so the morphism is finite
   (`lem-per-finite-graded-module-dehomogenization`,
   `lem-weil-pbc-finite-local-on-target`).
7. Each injective finite chart map is integral, so lying-over makes its Spec
   map surjective. The target standard charts cover; therefore the morphism
   is surjective, also for empty charts and empty Proj
   (`lem-weil-pbc-finite-algebra-is-integral`,
   `lem-weil-pbc-integral-injective-lying-over`, `def-weil-surjective-morphism`).
-/
theorem Proj.exists_isFinite_surjective_of_finite_graded
    (ι : 𝒞 →+*ᵍ 𝒜)
    (hι : Function.Injective ι)
    (hC : (algebraMap (𝒞 0) C).FiniteType)
    (hA : ι.toRingHom.Finite) :
    ∃ r : Proj 𝒜 ⟶ Proj 𝒞,
      IsFinite r ∧ Surjective r ∧
        (∀ (d : ℕ) (f : C) (hf : f ∈ 𝒞 d) (hd : 0 < d),
          r ⁻¹ᵁ Proj.basicOpen 𝒞 f = Proj.basicOpen 𝒜 (ι f)) ∧
        (∀ (d : ℕ) (f : C) (hf : f ∈ 𝒞 d) (hd : 0 < d),
          Proj.awayι 𝒜 (ι f) (ι.map_mem hf) hd ≫ r =
            Spec.map (CommRingCat.ofHom (Away.map ι f)) ≫
              Proj.awayι 𝒞 f hf hd) := by
  sorry

end AlgebraicGeometry
