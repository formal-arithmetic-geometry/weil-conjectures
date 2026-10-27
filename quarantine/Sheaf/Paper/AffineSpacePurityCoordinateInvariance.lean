module

public import Sheaf.Paper.AffineSpacePurityCompositionMaps

/-! # Coordinate invariance of the ordered affine-space purity comparison

Source: current blueprint, sec-smooth-purity/sk-prop-sp-composition,
prop-pur-affine-space-composition-law.proof.md, Steps 3--4, with the expanded
trace argument in the parent DAG.
(blueprint: lem-pur-affine-comparison-coordinate-invariance).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.AffineSpacePurity
open AffineLinePurity VectorIntegrationSite

/-- Transport by any actual polynomial coordinate permutation fixes the comparison.
This isolates coordinate invariance from the consecutive-block regrouping equation.
Source: current blueprint composition-law proof, Steps 3--4; parent DAG Steps 3--5
(blueprint: lem-pur-affine-comparison-coordinate-invariance).

Proof: set T_m=A(m)[2m], V_m=Rp_m!T_m, and let I_m be the counit transpose of the
ordered comparison at the coefficient unit, in OrderedAffineTranspose coordinates.
First use the ordinary affine-line top-trace calculation, with annihilator ell^r,
and vectorIntegrationSiteComparison to obtain V_1 isomorphic to the coefficient unit
and base-change compatibility of the actual normalized trace. The compared finite
Tate line is flat of rank one, shifted by 2. Apply affine_space_product_domain to
this line to get finite-Tor constructibility of all V_m and invertibility of their
canonical binary compact-support products; identify the relative external powers
with T_m by pullback/tensor composition and even-shift additivity.
The orderedAffineTranspose_projection theorem identifies the transpose at K with
the inverse coefficient-first projection followed by 1_K tensor I_m and the unitor.
Its line normalization, together with affineSpaceTraceFactorization, gives the
recurrence I_(m+1)=(I_m tensor t) kappa_(m,1). Use these actual binary product maps,
not arbitrary product isomorphisms. The hypotheses just checked permit applying
evenLineProductIntegrationSymmetry. Its last clause fixes the coefficient-first
transpose for every permutation. The signed Tate interchange is the canonical
pullback identification: both line degrees are -2 and the degree-zero rank-one
Tate multiplication is symmetric. Pullback composition identifies its concrete
coordinate map with coordinateIso (both have the same coordinate pullbacks).
Finally the coordinateSourceIso, isoExceptional and compositionInverse in
transportedComparison are exactly the adjunction-preserving transports: transpose
their composite using the pasted counit and the inverse-image comparison. Under
sourceIso this is the coefficientAction followed by the same coefficient trace.
Its invariance therefore makes the transposes equal. Injectivity of the bounded
etale-origin exceptional Hom bijection proves the displayed comparison equality.
This argument includes r=0 (one coordinate, hence identity permutation), arbitrary
ramified positive coefficient levels, and empty bases. It asserts no all-sheaf
pro-etale adjunction and never moves K past a shifted Tate factor. -/
theorem affineSpacePurity_coordinateEquation (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (Ring P) Y) (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (hKe : etaleFiniteTor (Ring P) Y Ke)
    (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj) (r : ℕ)
    (σ : Equiv.Perm (Fin (r + 1))) :
    HEq (transportedComparison P Y aY K Ke hKe eK r
      (coordinateIso Y (r + 1) σ) (iteratedAffineLineProj Y (r + 1))
      (hg' := purityProjectionCompactification Y (r + 1))
      (coordinateProjection Y (r + 1) σ))
      (positiveComparison P Y aY K Ke hKe eK r) := by sorry

end AlgebraicGeometry.ProEtale.AffineSpacePurity
