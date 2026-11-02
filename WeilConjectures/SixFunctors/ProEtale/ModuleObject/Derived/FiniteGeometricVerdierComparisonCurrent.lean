/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteFieldDualizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients

/-!
# Finite-coefficient geometric Verdier comparison

Source: latest blueprint,
`part-six-operations/sec-six-functors/sec-the-remaining-operations/`
`sk-thm-sf-ctf-stability/det-prop-sf-biduality-general.proof.md`, opening locality/restriction step
(blueprint: lem-sfb-finite-geometric-verdier-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Finite-coefficient geometric pullback over an algebraic closure preserves the
constructible finite-Tor category, reflects isomorphisms, and carries the dualizing
object and its evaluation to the algebraically closed base change.

The compact-support comparison is the canonical mate composite for the chosen
compactification, and its invertibility and counit normalization are asserted.  The
internal-Hom comparison is the evaluation transpose followed by the map induced by
that dualizing-object isomorphism, and is natural contravariantly in its first argument.
No biduality or anti-equivalence assertion is included.

Proof source: latest blueprint,
`part-six-operations/sec-six-functors/sec-the-remaining-operations/`
`sk-thm-sf-ctf-stability/det-prop-sf-biduality-general.proof.md`,
opening locality/restriction paragraph and finite-coefficient tower argument.

Proof (the thirteen steps of the DAG node):
1. Identify finite-coefficient internal modules with ordinary constant-A modules,
then identify their bounded constructible finite-Tor categories with the etale ones.
The site and internal-module comparisons preserve pullbacks, support, tensor, Hom,
units, counits and evaluation, so they identify the specified canonical arrows.
2. Inverse image is exact. Pull back bounded flat constructible representatives;
constructibility and the Tor interval persist. The canonical derived tensorator is
invertible and satisfies the monoidal axioms. On homogeneous elements in degrees
 i,j both symmetry composites multiply by (-1)^(i*j), giving the Koszul symmetry.
3. Every field-extension projection is a surjective fpqc base change. Its etale
module inverse image is faithful and exact. Applied to the cohomology of a cone,
this detects isomorphisms; transfer this detection to the internal realization.
4. Compact-support base change is the open-extension comparison followed by the
proper direct-image mate. Coherent compactification comparison identifies its
base-changed compactification with any other chosen compactification.
5. Choose a separable closure inside kbar and its directed finite separable tower.
The finite-stage projections are finite etale, their limit is affine ind-etale.
Finite cohomological dimension at every stage and dimension zero at the separably
closed point provide the constructible exceptional adjoints and support stability.
6. At each finite etale stage, the sum functors are left adjoint to pullback and
agree with compact support. Support composition and these adjunctions identify
Hom(P,g_i^*W) with Hom(Ra_i!P,A_i), naturally in P. The representing objects
therefore give isomorphisms g_i^*W to W_i.
7. The etale-horizontal support mate identifies the sum counit in this bijection
with the inverse of the specified exchange. It gives the displayed counit
normalization. Exchange pasting makes these isomorphisms compatible up the tower.
8. Constructible finite-Tor object descent and Hom continuity pass these compatible
representing bijections to the separable closure. Apply continuity also on the
base point to the compact-support images, which remain constructible finite-Tor.
Descent of morphisms and equalities ensures independence and naturality.
9. The exceptional adjunction identifies the final Hom group with Hom(P,W_s).
Applying the natural representing bijection and its inverse to the identities
constructs the two inverse maps. At the original-stage presentation of W, its
identity corresponds to epsilon_a, proving the counit normalization at k_s.
10. The remaining purely inseparable extension induces universal homeomorphisms.
Topological invariance gives an etale topos equivalence. Descend locally closed
strata and their trivializing etale covers through this equivalence: it preserves
bounded constructibility both ways. Its monoidality matches all Tor tests, so it
also preserves finite Tor amplitude both ways.
11. Full faithfulness, essential surjectivity on the constructible finite-Tor
categories, compact-support exchange and the exceptional adjunction identify the
two representing Hom functors across the purely inseparable step. This yields
the normalized dualizing isomorphism there. Compose with step 9; exchange pasting
and naturality give exactly the asserted normalization over kbar.
12. Along the affine ind-etale projection to k_s, internal-Hom comparison is
invertible for constructible finite-Tor first argument and bounded second argument.
Along the universal homeomorphism it is invertible by the monoidal equivalence.
Evaluation-preserving site comparisons identify their composite with precisely
the transpose beta for G, proving its invertibility.
13. Compose beta with Hom(1,w). Both factors are invertible. Naturality of the
closed adjunction gives contravariant naturality. Its transpose identity followed
by naturality of evaluation in the second argument is the displayed evaluation
equation. The fixed braiding converts the library's K tensor Hom convention into
Hom tensor K. Zero coefficients (including exponent zero), empty X and identity
algebraic closure are included, giving the unique zero or identity comparisons.

(blueprint: lem-sfb-finite-geometric-verdier-comparison).
-/
theorem finite_geometric_verdier_comparison_current
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hple : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    (hk : Finite k ∨ IsAlgClosed k)
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, (ell : A) ^ r = 0)
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (X : Scheme.{u}) (a : X ⟶ Spec (.of k))
    [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a]
    (c : Compactification a) :
    (detSfDerivedPullback (cartesianFinitePointRing A)
        (pullback.fst a (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))).IsTriangulated ∧
    Nonempty (FiniteFieldDualizingPullbackData
      (constantModelBoundedConstructible (cartesianFinitePointRing A) X ⊓
        DerivedCategory.finiteTorAmplitude _)
      (constantModelBoundedConstructible (cartesianFinitePointRing A) X ⊓
        DerivedCategory.finiteTorAmplitude _)
      (constantModelBoundedConstructible (cartesianFinitePointRing A)
        (pullback a (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) ⊓
        DerivedCategory.finiteTorAmplitude _)
      (detSfDerivedPullback (cartesianFinitePointRing A)
        (pullback.fst a (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))))
      (detSfDerivedPullback (cartesianFinitePointRing A)
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
      (leftDerivedUpperStarUnitIso (cartesianFinitePointRing A)
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
      (finiteFieldDerivedBraiding (CommMon.mk (cartesianFinitePointRing A)) X)
      (finiteFieldDerivedBraiding (CommMon.mk (cartesianFinitePointRing A))
        (pullback a (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) )
      (detSfCompactSupport (cartesianFinitePointRing A) c)
      (detSfCompactSupport (cartesianFinitePointRing A)
        (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))))
      (detSfCompactSupportBaseChangeComposite (cartesianFinitePointRing A) a
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) c
        (compactSupportOpenBaseChangeIso (cartesianFinitePointRing A) a
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) c))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
