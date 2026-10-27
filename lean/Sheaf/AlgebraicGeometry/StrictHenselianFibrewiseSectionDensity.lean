module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Sheaf.AlgebraicGeometry.EtaleLocalNormalForm
import Sheaf.RingTheory.Etale.QuasiFiniteAtPrime
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Etale.Basic
import WeilConjectures.RingTheory.QuasiFiniteAtPrime
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian

/-! # Geometric fibre density of strict-henselian sections

Source: Agent-formulated section-density input, motivated by Stacks Project, Tag 055U,
`lemma-etale-nbhd-dominates-smooth`, together with strict-henselian étale lifting.
(blueprint: lem-sfb-strict-henselian-fibrewise-section-density).

The statement records density of values of global sections in every geometric fibre.
A map from the spectrum of an algebraically closed field represents the geometric fibre;
its image is the selected base point.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

/-- Geometric fibre density of sections over a strictly henselian local ring.

Source: Agent-formulated section-density input, motivated by Stacks Project, Tag 055U,
`lemma-etale-nbhd-dominates-smooth`, and the strict-henselian étale lifting theorem
`AlgebraicGeometry.Scheme.exists_section_of_etale_of_isStrictlyHenselianLocalRing`.
(blueprint: lem-sfb-strict-henselian-fibrewise-section-density).

Proof (the accepted agent-written split):
1. By `sbc-thm-etale-local-normal-form`, choose an affine étale chart U → A^d around
   e(s), where s is the closed point of S = Spec R. An open containing the closed point
   of a local spectrum is all of S, so the base neighbourhood is S and e factors
   through U. Write α for its coordinate vector. Geometric irreducibility makes
   V = U_Ω ∩ W a nonempty open of the irreducible affine scheme U_Ω.
2. By `lem-weil-pbc-etale-ring-base-change` and
   `lem-weil-pbc-etale-ring-map-quasi-finite`, the chart π_Ω is quasi-finite, using
   `def-weil-pbc-ring-map-quasi-finite-at-prime` and `pqf-def-quasifinite` for the
   isolated-fibre-point definition. The closed complement Z = U_Ω \ V is nowhere dense.
   By `lem-sfb-quasifinite-closed-nowhere-dense-image`, its image is nowhere dense.
   Choose a nonempty principal open D(P) disjoint from its closure. Then P is nonzero
   and every point above a coordinate vector where P is nonzero lies in V.
3. A nonzero polynomial over a field cannot vanish on a product of infinite subsets:
   induct on the number of variables, first avoiding the zero set of a nonzero
   coefficient, then the finitely many roots in the final variable. Zero variables
   means a nonzero constant. The residue field k is separably closed, hence infinite:
   if its cardinality were N, T^N - T - 1 would be separable and have no root in k.
4. If q is not the maximal ideal m, choose t in m outside q. Multiplication by its
   nonzero image in the domain R/q shows that the image of m in κ(q), hence in Ω,
   is infinite (R/q surjects onto the infinite field k). Apply step 3 to the images
   of the coordinate cosets α_i + m to choose r congruent to α modulo m with P(r) ≠ 0.
   The scheme E = U ×[A^d_S,r] S is étale over S by the affine étale base-change node,
   and its closed fibre contains the point from e(s). The theorem
   `lem-sbc-strict-henselian-etale-neighbourhood-section` gives a section of E → S.
   Its composite a has coordinates r and its Ω-value belongs to V, hence W.
5. If q = m, the image J of U_k → A^d_k is nonempty open by
   `lem-weil-pbc-etale-morphism-open-map`. Choose a nonzero h over k with D(h) ⊆ J.
   Step 3 applied to P h_Ω on k^d gives b in J with P(b) ≠ 0. Lift its coordinates
   to R, form E as before, and use the nonempty closed fibre and the same
   strict-henselian section theorem. The resulting a again has Ω-value in V.
6. Every prime of the local ring lies below m, so steps 4 and 5 cover all cases.
   Meeting every nonempty open is precisely density. The proof uses the given
   section and smooth charts, and no group structure.

The two projection equations in the conclusion uniquely specify the base change
of a: they are the universal property of `pullback`. Evaluating it at `default`,
the unique point of Spec Ω, gives the induced Ω-point. `Scheme.SpecToEquivOfField`
identifies t with a prime q and an embedding κ(q) → Ω, including transcendental
algebraically closed extensions. Finite presentation is expressed by smoothness
(which supplies local finite presentation), quasi-compactness, and separatedness
(which supplies quasi-separatedness).
-/
theorem AlgebraicGeometry.Scheme.strictHenselian_fibrewiseSection_dense
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsStrictlyHenselianLocalRing R]
    {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R))
    [Smooth f] [QuasiCompact f] [IsSeparated f]
    [GeometricallyIrreducible f]
    (e : Spec (.of R) ⟶ X) (he : e ≫ f = 𝟙 _)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ Spec (.of R))
    (W : Set ↥(pullback f t)) (hW : IsOpen W) (hWne : W.Nonempty) :
    ∃ (a : Spec (.of R) ⟶ X), a ≫ f = 𝟙 _ ∧
      ∃ b : Spec (.of Ω) ⟶ pullback f t,
        b ≫ pullback.fst f t = t ≫ a ∧
        b ≫ pullback.snd f t = 𝟙 _ ∧ b default ∈ W := by
  sorry
