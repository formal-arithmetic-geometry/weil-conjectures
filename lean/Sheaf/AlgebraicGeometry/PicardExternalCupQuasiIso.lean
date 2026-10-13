/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalCupCochain
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

import Sheaf.AlgebraicGeometry.AffineModuleCechComparisonNatural
import Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import Sheaf.AlgebraicGeometry.LerayDegenerateSections
import Sheaf.AlgebraicGeometry.ModuleCechComparisonIsoAffine
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.QcqsCohomologyDirectSum
import Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import Sheaf.AlgebraicGeometry.QuasicoherentAcyclicEmbedding
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteCohomologicalDimension
import Sheaf.Paper.CechComparisonMapNaturality
import Sheaf.Paper.CechCupPullbackCompat
import Sheaf.Paper.HigherDirectImagePresheaf
import Sheaf.Algebra.Homology.TensorKunnethNat

/-! # Geometric invertibility of the normalized external cup comparison

Source: Stacks Project, Varieties, Tag 0BED, proof after equation 33.29.1.1.
(blueprint: lem-sc-picard-external-cup-quasi-iso).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Every cochain realization with the specified cup normalization induces isomorphisms
on natural-degree homology. No cochain map or cohomology model is chosen here.
Source: Stacks Project, Varieties, Tag 0BED, short exact sequence argument,
the two dimension-shifting inductions and the acyclic base case
(blueprint: lem-sc-picard-external-cup-quasi-iso).

Proof: Choose finite affine covers U of X and V of Y. Affine diagonal ensures that
all nonempty finite intersections are affine; the product cover W has the same
property. Affine Cech comparisons identify the factor and product cohomologies
with those of these covers. Refinement along the two projections and signed cup
define the Cech tensor-total comparison, normalized by Tags 01FD, 07MB and 0FKV.
Sections on affine intersections are exact on quasi-coherent modules, and field
tensor is exact. The affine pullback and tensor section formulas identify product
sections with tensors of factor sections. Consequently a short exact coefficient
sequence in either variable gives a map of short exact sequences of complexes.
The long exact sequences and five lemma give the two-out-of-three principle for
this Cech comparison to be a quasi-isomorphism.
Assign each coefficient a nonnegative cohomological bound, using finite
quasi-coherent cohomological dimension. Embed it in an acyclic quasi-coherent
module; the cokernel has bound smaller by one when the original bound is positive.
First induct on the bound for G with F acyclic, then induct on the bound for F
with arbitrary G. The base has both coefficients acyclic, including the zero case.
For affine V in Y, Cech(U times V, external coefficients) is Cech(U,F) tensor G(V).
Exact field tensor gives zero positive cohomology and Gamma(X,F) tensor G(V) in
degree zero. The higher-direct-image presheaf description therefore gives zero
positive higher direct images under pr2 and identifies its ordinary direct image
with Gamma(X,F) tensor G. Expand Gamma(X,F) in a basis. On qcqs Y cohomology
commutes with that direct sum; hence it vanishes in positive degrees and is the
section tensor product in degree zero. Leray degeneration computes the product
cohomology accordingly. Split the two vector-space complexes into their degree-zero
homology representatives and contractible pairs. Contracting either tensor factor
contracts its tensor summand, with the Koszul sign for the second factor. Thus the
tensor total too is concentrated in degree zero. The Cech comparison in degree zero
sends s tensor t to the product of their projection pullbacks, exactly the affine
section tensor isomorphism. This proves the base case and both inductions.
Finally transport the Cech homology comparison to the fixed resolution models via
picardScalarModelEquiv. The field-linear tensor Kunneth cycle formula and
surjectivity of each homology projection show that tensor-cycle classes span the
source homology. IsPicardExternalCupCochain identifies homologyMap c with the
transported Cech comparison on those classes. They are therefore equal as linear
maps. The latter is an isomorphism, so homologyMap c is one too, in every n. -/
theorem picardExternalCupCochain_isIso
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (c : picardExternalTotal f g F G ⟶
      picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
    (hc : IsPicardExternalCupCochain f g F G c) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap c (n : ℤ)) := by sorry

end AlgebraicGeometry.Scheme.Modules
