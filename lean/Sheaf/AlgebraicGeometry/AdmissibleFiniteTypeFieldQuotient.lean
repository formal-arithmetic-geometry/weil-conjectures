/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.QuasiProjective
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import Sheaf.AlgebraicGeometry.FiniteFreeAlgebraSpectrum
import Sheaf.AlgebraicGeometry.AffineGroupoidOrbitFibres
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Adjoin.Tower
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.GroupTheory.MonoidLocalization.Away
import WeilConjectures.RingTheory.GradedPrimeAvoidance
import Sheaf.AlgebraicGeometry.ProjStandardOpenBasis

/-!
# Finite quotients of admissible actions over a field

Source: ILO, Travaux de Gabber, IX 1.4, printed pp. 132--133, and X 2.3 Step 2,
printed p. 151; Stacks Project, Tags 03JE, 00IS, and 01ZY
(blueprint: lem-sfb-admissible-finite-type-field-quotient).

## Main definitions

- `finiteQuotientInvariantSections`: the invariant subring used in the affine quotient formula.

## Main statements

- `exists_admissible_finite_type_field_quotient`: all quotient and finiteness properties.
- `orbit_in_affine_of_quasiProjective`: quasi-projective finite-type actions are admissible.
- `orbit_in_affine_subgroup`: admissibility passes to every subgroup.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The invariant subring of sections on an invariant open, expressed by equalizers of actual
pullback and restriction maps on common subopens. This is the ring appearing in the affine
quotient formula, without choosing identifications of equal opens. The definition also makes
sense on an arbitrary open, using the same overlap equations.
Source: ILO IX 1.4, pp. 132--133, invariant structure sheaf
(blueprint: lem-sfb-admissible-finite-type-field-quotient). -/
def finiteQuotientInvariantSections {H : Type v} [Group H] {V : Scheme.{u}}
    (a : H →* Aut V) (W : V.Opens) : Subring Γ(V, W) :=
  ⨅ (g : H) (T : V.Opens) (hT : T ≤ W) (hTg : T ≤ (a g).hom ⁻¹ᵁ W),
    ((a g).hom.appLE W T hTg).hom.eqLocus (V.presheaf.map (homOfLE hT).op).hom

/-- An admissible finite group action on a separated scheme locally of finite type over a
field has a finite geometric categorical quotient, compatible with invariant opens and
invariant affine spectra. Finiteness over an open of any invariant target descends to it.
The geometric fibres below are the actual scheme pullbacks; their action maps are uniquely
specified by their two projections.

Source: ILO IX 1.4, pp. 132--133, and X 2.3 Step 2, p. 151; Stacks Tags 03JE and 00IS
(blueprint: lem-sfb-admissible-finite-type-field-quotient).

Proof:
1. Intersect the finitely many translates of an affine neighbourhood of each orbit.
   Separatedness makes these intersections affine by
   lem-weil-pbc-separated-affine-open-intersection. All invariant affine opens form a cover.
2. On W = Spec R form the action groupoid with arrows the disjoint union of H copies of W.
   The source is finite free, using lem-weil-pbc-finite-affine-coproduct-spectrum and
   lem-weil-pbc-finite-free-algebra-spectrum; inversion identifies source and target.
   Apply lem-a1-affine-groupoid-orbit-fibres to the equalizer A = R^H. Integrality and orbit
   fibres follow from lem-dl-a1-finite-invariant-prime-orbits-residues. The map is closed by
   lem-weil-pbc-integral-spec-closed-map, hence a topological quotient.
3. Give |V|/H its quotient topology and the sheaf of invariant sections. The orbit map is
   open since the saturation of an open is the union of its translates. Invariant opens
   are saturated, and their quotient topology is the restricted quotient topology.
4. For f in A, identify A_f with (R_f)^H: for a fixed fraction r/f^n choose a common
   annihilating exponent for all finitely many differences g(r)-r. This works with zero
   divisors. Use def-weil-ring-localization-away,
   lem-weil-pbc-affine-open-section-vanishing-prime and
   lem-weil-pbc-spec-localization-away-basic-open. The equalities respect restrictions,
   hence identify the invariant sheaf on q(W) with the structure sheaf of Spec A.
   These affine charts give the scheme and its field structure and make q a scheme map.
5. The affine-local-target criterion pqf-lem-affine-local-target makes q affine. On any
   affine inverse image Spec R, lem-weil-pbc-lft-affine-pairs makes R finite type over e.
   The same generators generate R over A, and are integral over A. Apply
   lem-sc-finite-generated-integral-subring and def-weil-finite-integral-morphism.
   The affine orbit calculation gives surjectivity and transitivity on geometric fibres.
6. Artin--Tate (lem-sfb-artin-tate-subalgebra-finite-type) makes each A finite type over e.
   Thus Q is locally of finite type, without quasi-compactness. If V is reduced, each R,
   and therefore its subring A, is reduced (def-pc-reduced-scheme).
7. An invariant map factors continuously through the orbit space and on sections through
   the invariant sheaf. The factor is local on stalks: pull back a putative unit to a
   point of V above the chosen point of Q and use locality of the original map.
   Uniqueness follows from surjectivity and injectivity on sections. This uses
   def-weil-locally-ringed-space-morphism. The same construction restricts to every
   invariant open and proves both its categorical property and the affine formula.
8. Given v finite over U, take an affine T = Spec C in U. Its inverse image is Spec R,
   finite over C. The image C' of C in R lies in A = R^H and contains the image of e.
   R is finite over C', so Artin--Tate makes C' finite type over e, even for arbitrary C.
9. By lem-weil-pbc-finite-type-algebra-noetherian, C' is Noetherian. The C'-submodule
   A of R is finite by lem-weil-pbc-noetherian-submodule-finite. Its generators also
   generate over C. This proves Q times_B U finite over U on affine charts, using
   def-weil-finite-integral-morphism and def-pc-fibre-product.
10. The quasi-projective and subgroup admission assertions are stated separately below.
    They use graded prime avoidance and the positive-degree affine standard opens of Proj.
-/
theorem exists_admissible_finite_type_field_quotient
    (e : Type u) [Field e] (V : Scheme.{u}) (p : V ⟶ Spec (.of e))
    [IsSeparated p] [LocallyOfFiniteType p]
    (H : Type v) [Group H] [Finite H] (a : H →* Aut V)
    (ha : ∀ g : H, (a g).hom ≫ p = p)
    (horbit : ∀ x : V, ∃ W : V.affineOpens, ∀ g : H, (a g).hom x ∈ W.1) :
    ∃ (Q : Scheme.{u}) (b : Q ⟶ Spec (.of e)) (q : V ⟶ Q),
      q ≫ b = p ∧ IsAdmissibleFiniteSchemeQuotient a q ∧ Surjective q ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Q),
        Nonempty ↥(pullback (C := Scheme.{u}) q t) ∧
        ∀ x y : ↥(pullback (C := Scheme.{u}) q t), ∃ (g : H) (l : pullback q t ⟶ pullback q t),
          l ≫ pullback.fst q t = pullback.fst q t ≫ (a g).hom ∧
          l ≫ pullback.snd q t = pullback.snd q t ∧ l x = y) ∧
      (∀ (Z : Scheme.{u}) (f : V ⟶ Z), (∀ g : H, (a g).hom ≫ f = f) →
        ∃! r : Q ⟶ Z, q ≫ r = f) ∧
      LocallyOfFiniteType b ∧ (IsReduced V → IsReduced Q) ∧
      (∀ W : V.Opens, (∀ g : H, (a g).hom ⁻¹ᵁ W = W) →
        ∃ (O : Q.Opens) (aW : H →* Aut W.toScheme) (r : W.toScheme ⟶ O.toScheme),
          q ⁻¹ᵁ O = W ∧
          (∀ g : H, (aW g).hom ≫ W.ι = W.ι ≫ (a g).hom) ∧
          r ≫ O.ι = W.ι ≫ q ∧ IsAdmissibleFiniteSchemeQuotient aW r ∧
          ∀ (Z : Scheme.{u}) (f : W.toScheme ⟶ Z),
            (∀ g : H, (aW g).hom ≫ f = f) → ∃! s : O.toScheme ⟶ Z, r ≫ s = f) ∧
      (∀ (W : V.Opens) (hW : IsAffineOpen W), (∀ g : H, (a g).hom ⁻¹ᵁ W = W) →
        ∃ (O : Q.Opens) (hpre : q ⁻¹ᵁ O = W) (_ : IsAffineOpen O)
          (i : O.toScheme ≅ Spec (.of (finiteQuotientInvariantSections a W))),
          q.resLE O W (le_of_eq hpre.symm) ≫ i.hom =
            hW.isoSpec.hom ≫
              Spec.map (CommRingCat.ofHom (finiteQuotientInvariantSections a W).subtype)) ∧
      ∀ (B : Scheme.{u}) (c : B ⟶ Spec (.of e)) (v : V ⟶ B),
        v ≫ c = p → (∀ g : H, (a g).hom ≫ v = v) →
        ∃ r : Q ⟶ B, q ≫ r = v ∧ r ≫ c = b ∧
          ∀ U : B.Opens, IsFinite (v ∣_ U) → IsFinite (pullback.snd r U.ι) := by
  sorry

/-- Every finite group action on a quasi-projective finite-type scheme over a field has
its orbits in affine opens. Quasi-projectivity is the existing finite projective-space
immersion predicate, so no projectivity of a quotient is asserted.
Source: Stacks Project, Tag 01ZY, case (4); ILO IX 1.4, pp. 132--133
(blueprint: lem-sfb-admissible-finite-type-field-quotient).

Proof (step 10 of the node): factor the immersion through a closed subscheme of an open O
of projective space. For any finite nonempty set of points use the homogeneous ideal of
its complement, intersected with the irrelevant ideal. This ideal is contained in none of
the corresponding homogeneous primes. Apply lem-sc-graded-prime-avoidance to find a
positive-degree homogeneous f avoiding all these primes. By lem-sc-proj-standard-open-basis,
D_+(f) is affine and lies in O. Its inverse image is affine by def-weil-closed-immersion.
The empty finite set lies in the empty affine open. Apply this to the finite orbit. -/
theorem orbit_in_affine_of_quasiProjective
    (e : Type u) [Field e] (V : Scheme.{u}) (p : V ⟶ Spec (.of e))
    [LocallyOfFiniteType p] [QuasiCompact p] (hp : IsQuasiProjective p)
    (H : Type v) [Group H] [Finite H] (a : H →* Aut V)
    (ha : ∀ g : H, (a g).hom ≫ p = p) :
    ∀ x : V, ∃ W : V.affineOpens, ∀ g : H, (a g).hom x ∈ W.1 := by
  sorry

/-- Every subgroup action of an admissible action is admissible, with no faithfulness or
freeness requirement. Source: ILO IX 1.4, pp. 132--133, and X 2.3 Step 2, p. 151
(blueprint: lem-sfb-admissible-finite-type-field-quotient).

Proof (last part of step 10): the orbit of a point under a subgroup K is contained in its
H-orbit. The same affine open containing the H-orbit contains every point of the K-orbit.
This works for the trivial subgroup and for the empty scheme. -/
theorem orbit_in_affine_subgroup
    {V : Scheme.{u}} {H : Type v} [Group H] [Finite H] (a : H →* Aut V)
    (horbit : ∀ x : V, ∃ W : V.affineOpens, ∀ g : H, (a g).hom x ∈ W.1)
    (K : Subgroup H) :
    ∀ x : V, ∃ W : V.affineOpens, ∀ g : K, ((a.comp K.subtype) g).hom x ∈ W.1 := by
  sorry

end AlgebraicGeometry
