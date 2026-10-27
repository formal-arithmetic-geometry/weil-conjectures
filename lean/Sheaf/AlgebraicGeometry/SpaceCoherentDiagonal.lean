/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.AlgebraicGeometry.SpaceCoherentStackGeneral
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.SpaceModuleBaseChangeFlatProperSupport

/-! # The diagonal of coherent families on algebraic spaces

Source: Stacks Project, quot.tex, Situation 08KB and Tag 08W6, lemma-coherent-diagonal
(blueprint: lem-sfb-space-coherent-diagonal).

The already constructed total category retains distinct maps to B and the actual
pullback module isomorphisms. Representability is the existing two-fibre-product criterion.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- The coherent-family groupoid has diagonal representable by algebraic spaces.
Source: Stacks Project, quot.tex, Situation 08KB and Tag 08W6, lemma-coherent-diagonal;
Tag 08K9, proposition-isom; algebraic.tex, Tag 045G
(blueprint: lem-sfb-space-coherent-diagonal).

Proof:
1. For two objects (b,M), (c,N) over T, form the equality locus E of b and c by
   base-changing the scheme-representable diagonal of B. Its universal property
   makes factorization through E equivalent to equality after restriction.
2. Pull M and N to X_E. Finite presentation survives base change by
   lem-sfb-space-flat-proper-fp-locality. The chart maps are locally of finite type,
   so lem-sfb-space-module-base-change-flat-proper-support preserves the modules'
   quasi-coherence, finite presentation, relative flatness and proper support.
3. Apply lem-sfb-space-module-hom-affine to the four ordered pairs (M,N), (N,M),
   (M,M), (N,N), obtaining representing spaces H, H', A, D over E.
4. Tensor pullback preserves composition and identity. Thus composition defines
   H times_E H' to A times_E D, and the two identities define an E-section.
   Pulling back along this section gives an algebraic space J by
   lem-trf-space-fibre-products-etale-covers.
5. Its points are inverse pairs (v,w) with wv=id and vw=id. Projection to v is
   naturally bijective with module isomorphisms; the inverse assigns (v,v inverse).
   For a general T' to T the unique factorization through E is required, so both
   sets are empty when b and c remain unequal.
6. Unpack the existing two-fibre-product definition: a triple (z,alpha,beta) maps
   to beta composed with alpha inverse. Every isomorphism occurs, and two triples
   giving the same isomorphism have a unique compatible arrow. This equivalence
   is natural under pullback. Hence the isomorphism presheaves, and equivalently
   the diagonal in the recorded fibred-groupoid convention, are algebraic spaces. -/
theorem coherent_diagonal {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (hfp : ProperQuotFinitePresentation f) :
    HasAlgebraicSpaceDiagonal (CoherentModuli.category f) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
