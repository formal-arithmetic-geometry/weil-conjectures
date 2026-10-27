module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.AlgebraicSpaceLocalDimensionChartInvariance
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineAtlasOpenCover
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.SpaceChangeBase
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.EtaleLocalNoetherianDescent
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.GroupoidScheme
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductPoint
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus

/-!
# Scheme neighbourhoods at points of local dimension at most one

Source: Stacks Project, Spaces over Fields, Tag 0ADD,
lemma-codim-1-point-in-schematic-locus (blueprint: lem-sfb-space-schematic-near-height-one).
The base is arbitrary; only the local ring at the specified chart point has bounded dimension.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A separated locally Noetherian algebraic space has a scheme open neighbourhood of
any point represented by an étale chart point with stalk dimension at most one.
An open immersion from the representing scheme specifies the open subspace; membership
in its point image says precisely that the neighbourhood contains the given image point.

Source: Stacks Project, Spaces over Fields, Tag 0ADD,
lemma-codim-1-point-in-schematic-locus (blueprint: lem-sfb-space-schematic-near-height-one).

Proof:
1. By lem-sfb-space-local-dimension-chart-invariance the image point has local dimension
   at most one. Use lem-a1-space-affine-atlas-open-cover to restrict to a quasi-compact
   neighbourhood Z over an affine open S₀ of S. Its diagonal remains closed by
   lem-weil-pbc-closed-immersion-base-change. Affine chart pairs have affine fibre products
   (def-weil-closed-immersion and lem-weil-pbc-affine-scheme-qcqs), so after
   lem-sfb-space-change-base-to-integers the criterion
   lem-sfb-etale-affine-pairs-test-quasiseparated makes Z absolutely quasi-separated.
   Local Noetherianity restricts, hence Z is Noetherian.
2. Take a finite surjective scheme cover Y → Z by lem-sfb-qcqs-space-finite-scheme-cover.
   Pull it back to an affine étale atlas T of Z. The resulting scheme P is finite over T,
   hence locally of finite type (def-weil-finite-integral-morphism), and locally Noetherian
   by pqf-lem-locnoeth-lft. Its surjective étale map to Y is supplied by
   lem-trf-space-fibre-products-etale-covers; lem-trf-etale-local-noetherian-descent
   makes Y locally Noetherian.
3. A finite map is integral by pqf-lem-finite-integral-lft, hence separated by
   lem-sfb-space-integral-qcqs-permanence. Use lem-sfb-space-separated-fp-composition
   and lem-sc-separated-over-affine-scheme-separated to make Y absolutely separated.
4. The cover is locally quasi-finite by lem-sfb-finite-space-morphism-topology. Apply
   lem-sfb-space-local-ring-dimension-quasifinite to bound all stalk dimensions over x
   by one. No other stalk dimension is bounded.
5. The scheme R = Y ×_Z Y is a finite groupoid (def-a1-groupoid-scheme), with the usual
   pair, identity, inverse and composition maps. Its orbit above x is the entire fibre,
   by lem-a1-space-fibre-product-point. Apply
   lem-sfb-finite-groupoid-height-one-affine-open to obtain an invariant affine open W
   containing this fibre.
6. Invariance and lem-a1-space-fibre-product-point show that W is saturated. The cover
   is closed and surjective by lem-sfb-finite-space-morphism-topology, so its image is
   open. Use lem-a1-space-etale-open-image and lem-a1-space-point-open-calculus to form
   this open subspace Z′ with pullback W. Thus W → Z′ is finite surjective and x lies in Z′.
7. The image of the quasi-compact affine scheme W is quasi-compact. Local Noetherianity
   restricts, and quasi-separatedness follows from lem-sfb-space-integral-qcqs-permanence.
   Hence Z′ is Noetherian. By lem-sfb-noetherian-space-finite-affine-descent it is a scheme.
   Composing its open immersion with Z → X, and its structure map with S₀ → S, gives
   the required scheme over S and the stated containment. -/
theorem exists_scheme_open_of_stalk_dimension_le_one {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hsep : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj)))
    (hnoeth : ∀ (T : Over S) (t : yoneda.obj T ⟶ X.obj.obj),
      IsEtale t → IsLocallyNoetherian T.left)
    (V : Over S) (a : yoneda.obj V ⟶ X.obj.obj) (ha : IsEtale a) (v : V.left)
    (hdim : ringKrullDim (V.left.presheaf.stalk v) ≤ (1 : WithBot ℕ∞)) :
    ∃ (U : Over S) (j : yoneda.obj U ⟶ X.obj.obj),
      IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j ∧
      schemePointMap a v ∈ Set.range (schemePointMap j) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
