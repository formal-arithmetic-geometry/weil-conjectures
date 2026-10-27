module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.GroupScheme.IdentityLocalDimension
import Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality
import Sheaf.RingTheory.SmoothOverFieldRegularLocal
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Dimension and smoothness at the identity of an affine algebraic group

Source: Milne, Algebraic Groups (2017), Proposition 1.37, printed p.18, using
Proposition 1.28, the dimension paragraph on printed p.17, and Appendix A.51-A.52
(blueprint: lem-sfb-group-tangent-dimension-smoothness).

The tangent space is the recorded dual-number tangent space, with scalars restricted
along the structural map from the base field to the residue field of the identity.
Neither connectedness nor reducedness is assumed.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.GrpObj

/-- The base-field action on the existing tangent space at the identity, obtained by
restricting its residue-field action along the structural map `F → κ(e)`.

Source: Milne, Algebraic Groups (2017), Proposition 1.37 and Appendix A.51-A.52;
Stacks Project, Tag 0B2C (blueprint: lem-sfb-group-tangent-dimension-smoothness).
This supplies only the canonical scalar restriction, without changing tangent vectors.
-/
noncomputable instance identitySchemeTangentSpaceModule
    (F : Type u) [Field F] (G : Over (Spec (.of F))) [GrpObj G] :
    Module F (schemeTangentSpace F G.left G.hom (onePoint G)) :=
  Module.compHom (schemeTangentSpace F G.left G.hom (onePoint G))
    (StructureSheaf.toStalk F (G.hom (onePoint G)) ≫
      G.hom.stalkMap (onePoint G) ≫ G.left.residue (onePoint G)).hom

/-- An affine finite-type group scheme over an algebraically closed field has finite
nonnegative Krull dimension and finite-dimensional identity tangent space. Its dimension
is at most the tangent dimension, with equality exactly when it is smooth over the field.

Source: Milne, Algebraic Groups (2017), Proposition 1.37, printed p.18, using
Proposition 1.28, the dimension paragraph on printed p.17, and Appendix A.51-A.52
(blueprint: lem-sfb-group-tangent-dimension-smoothness).

Proof for stage 3:
1. Choose a finite-type affine chart at the identity. Its augmentation to F has a
   maximal kernel with residue field F. By lem-weil-pbc-affine-open-stalk-localization,
   its localization is the identity stalk R. The finite-type and localization
   Noetherian permanence lemmas lem-weil-pbc-finite-type-algebra-noetherian and
   lem-weil-pbc-localization-noetherian make R Noetherian. By
   lem-ag-group-identity-local-dimension its Krull dimension is the global dimension.
2. By lem-weil-pbc-regular-local-cotangent-dimension, the cotangent space m/m² is
   finite dimensional, bounds dim R from above, and equality characterizes regularity.
   Apply lem-sc-rational-tangent-cotangent-duality to the identity morphism and then
   lem-sfb-linear-dual-dimension-rank: the tangent space is its finite-dimensional dual
   over F, with the same dimension. The local spectrum is nonempty, so dim R is
   nonnegative; its finite upper bound makes the global dimension a natural number.
3. In the equality case R is regular. Its residue field F is separable over F, so
   lem-sfb-regular-separable-affine-smooth-neighbourhood gives a smooth open
   neighbourhood V of the identity.
4. By lem-sc-translation-automorphism every rational point has a translated smooth
   neighbourhood, using lem-weil-pbc-smooth-restrict-open-subschemes for invariance.
   Every closed point is rational by lem-weil-pbc-closed-point-residue-field-base.
   The Jacobson property lem-sc-lft-over-field-jacobson-space makes these opens cover
   every point. Apply lem-weil-pbc-smooth-local-on-source, including every component.
5. Conversely smoothness restricts to the affine chart by
   lem-weil-pbc-smooth-restrict-open-subschemes; by
   lem-weil-pbc-smooth-ring-map-iff-smooth-affine its ring is smooth over F.
   Then lem-weil-pbc-smooth-over-field-regular-local makes R regular. Step 2 gives
   equality of global dimension and tangent dimension.
-/
theorem tangent_dimension_smoothness
    (F : Type u) [Field F] [IsAlgClosed F]
    (G : Over (Spec (.of F))) [GrpObj G] [IsAffine G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    Module.Finite F (schemeTangentSpace F G.left G.hom (onePoint G)) ∧
      (∃ d : ℕ, topologicalKrullDim G.left = (d : WithBot ℕ∞)) ∧
      topologicalKrullDim G.left ≤
        (Module.finrank F (schemeTangentSpace F G.left G.hom (onePoint G)) : WithBot ℕ∞) ∧
      (topologicalKrullDim G.left =
        (Module.finrank F (schemeTangentSpace F G.left G.hom (onePoint G)) : WithBot ℕ∞) ↔
          Smooth G.hom) := by
  sorry

end AlgebraicGeometry.GrpObj
