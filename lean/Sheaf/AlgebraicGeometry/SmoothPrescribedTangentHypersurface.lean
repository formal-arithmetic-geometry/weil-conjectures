module

public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
public import WeilConjectures.AlgebraicGeometry.DensePoints
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra
import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionLocalRingLocalization
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.RationalPointTangentDerivationIdentification
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme
import Sheaf.AlgebraicGeometry.RegularClosedPointComponents
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Localization.Basic
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Smooth hypersurfaces with a prescribed tangent hyperplane

Source: Milne, Abelian Varieties, Chapter I, Lemma 3.6, printed page 18;
Stacks Project, Tags 00NQ, 00TV, 01V9, 038X, 0B2E and 0B2F
(blueprint: lem-sfb-smooth-prescribed-tangent-hypersurface).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every tangent hyperplane at a rational point of a smooth geometrically integral variety
is realized by a smooth geometrically integral closed subscheme of an open neighbourhood.
The scalar field of `H` is the residue field at the rational point, canonically `k`.
The quotient finrank expresses codimension one. The differential is the canonical
`schemeTangentMap`; `HEq` identifies its target point with `p` using `hq`, without making
any choice of a tangent-space isomorphism.

Source: Milne, Abelian Varieties, Chapter I, Lemma 3.6, printed page 18;
Stacks Project, Tags 00NQ, 00TV, 01V9, 038X, 0B2E and 0B2F
(blueprint: lem-sfb-smooth-prescribed-tangent-hypersurface).

Proof:
1. Choose an affine finite-type neighbourhood of `p` (lem-pc-affine-finite-type-algebra).
   Its coordinate ring is a domain. Its stalk `R` is its localization at the rational
   maximal ideal (lem-weil-pbc-affine-open-stalk-localization), is regular by
   lem-weil-pbc-smooth-scheme-over-field-regular, and has dimension `d` by
   lem-weil-pbc-finite-type-domain-dimension-local-ring-localization,
   lem-weil-pbc-spec-topological-krull-dimension-ring and
   lem-sc-integral-locally-algebraic-opens-dimension.
2. The cotangent space `E` has dimension `d` (lem-weil-pbc-regular-local-cotangent-dimension).
   Rational tangent-cotangent duality (lem-sc-rational-point-tangent-derivation-identification)
   expresses `H` as the annihilator of a nonzero `v` in `E`: choose a linear equation for
   `H` and use finite-dimensional double duality. Lift `v` to `f` in the maximal ideal,
   outside its square.
3. Represent `f` by a fraction on the affine chart and invert its denominator
   (lem-weil-pbc-affine-open-stalk-localization,
   lem-weil-pbc-principal-localization-open-immersion), obtaining an actual section `h`.
4. Extend `v` to a cotangent basis and lift that basis. Nakayama
   (lem-weil-pbc-nakayama-local-generators) makes these a minimal generating set of the
   maximal ideal. The regular-parameter theorem
   (lem-weil-pbc-regular-local-generators-regular-sequence) gives `R/(f)` regular of
   dimension `d - 1`.
5. Form the zero scheme of `h` (lem-pc-zero-scheme-properties). Its point over `p` has
   stalk `R/(f)` (lem-weil-pbc-localization-at-prime-of-quotient) and residue field `k`.
   Apply lem-sfb-regular-separable-affine-smooth-neighbourhood and lift its principal-open
   section to the ambient chart. Localization and quotient commute
   (lem-weil-pbc-localization-quotient-commute), so the smooth open is still closed there.
6. Smooth components are disjoint and open (lem-wf-smooth-components-disjoint).
   Take a principal neighbourhood of the point inside its component, and lift its
   defining element to the ambient ring. This gives `D` closed in an open `V` of `Y`.
   Smoothness persists (lem-weil-pbc-smooth-restrict-open-subschemes). Its nonempty
   irreducible space and regular, hence domain, stalks (lem-sc-regular-local-domain)
   make it integral (def-pc-integral-scheme).
7. Principal localizations preserve finite type. The affine `D` is separated because its
   diagonal is induced by the surjective multiplication map on the tensor product
   (lem-weil-pbc-fibre-product-affine-spectra). The stalk at its rational point remains
   `R/(f)`; finite-type domain dimension and spectrum dimension give `dim D = d - 1`.
8. The cotangent quotient is `E/kv`. By rational tangent-cotangent duality and
   lem-weil-pbc-scheme-stalk-map-composition, the canonical tangent map is precomposition
   with `E -> E/kv`. It is injective with image the annihilator of `v`, exactly `H`.
9. Every finite extension of the algebraically closed `k` is `k`. Thus base change of
   the affine domain of `D` to such an extension remains a domain. The finite-extension
   test (lem-per-geometric-integrality-finite-field-test) proves geometric integrality.
   The retained rational point `q` maps to `p` throughout all shrinkings. -/
theorem exists_smooth_hypersurface_prescribed_tangent
    (k : Type u) [Field k] [IsAlgClosed k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (.of k)) [Smooth pY] [IsSeparated pY]
    [GeometricallyIntegral pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    (p : pY.fieldPoints k) (d : ℕ) (hd : 2 ≤ d)
    (hdim : topologicalKrullDim Y = (d : WithBot ℕ∞))
    (H : Submodule (Y.residueField (p.1 default))
      (schemeTangentSpace k Y pY (p.1 default)))
    (hH : Module.finrank (Y.residueField (p.1 default))
      (schemeTangentSpace k Y pY (p.1 default) ⧸ H) = 1) :
    ∃ (V : Y.Opens) (_ : p.1 default ∈ V) (D : Scheme.{u}) (j : D ⟶ V.toScheme),
      IsClosedImmersion j ∧ Smooth ((j ≫ V.ι) ≫ pY) ∧
      IsSeparated ((j ≫ V.ι) ≫ pY) ∧ GeometricallyIntegral ((j ≫ V.ι) ≫ pY) ∧
      LocallyOfFiniteType ((j ≫ V.ι) ≫ pY) ∧ QuasiCompact ((j ≫ V.ι) ≫ pY) ∧
      topologicalKrullDim D = ((d - 1 : ℕ) : WithBot ℕ∞) ∧
      ∃ (q : ((j ≫ V.ι) ≫ pY).fieldPoints k)
        (hq : q.1 ≫ (j ≫ V.ι) = p.1)
        (he : Function.Bijective ((j ≫ V.ι).residueFieldMap (q.1 default)).hom),
        Function.Injective (schemeTangentMap k D Y ((j ≫ V.ι) ≫ pY) pY
          (j ≫ V.ι) rfl (q.1 default) he) ∧
        ∀ v : schemeTangentSpace k Y pY (p.1 default),
          v ∈ H ↔ ∃ w : schemeTangentSpace k D ((j ≫ V.ι) ≫ pY) (q.1 default),
            HEq (schemeTangentMap k D Y ((j ≫ V.ι) ≫ pY) pY
              (j ≫ V.ι) rfl (q.1 default) he w) v := by
  sorry

end AlgebraicGeometry
