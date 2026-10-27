module

public import Sheaf.Paper.AffineSpacePurityCompositionMaps

/-! # Ordered blocks of the affine-space purity comparison

Source: current blueprint, sec-smooth-purity/sk-prop-sp-composition,
prop-pur-affine-space-composition-law.proof.md, Steps 1--2.
(blueprint: lem-pur-affine-comparison-ordered-blocks).
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

/-- Regrouping preserves the specified ordered comparison, with the actual source
reassociation and inverse exceptional compositor, before any coordinate permutation.
Source: current blueprint composition-law proof, Steps 1--2
(blueprint: lem-pur-affine-comparison-ordered-blocks).

Proof: all intermediate exceptional inputs have the retained finite-Tor etale origin
by stage_applicability, and every tower base is separated finite type by tower_geometry.
On these classes form the interval functors P=Rp_!, G=Rp^!, and F=Lp^*(-)(a)[2a].
Use the canonical compact-support compositors for alpha; their conjugates are the
specified compositionInverse maps, by their defining pasted counit. The source phi
is blockSourceIso. Its associativity follows from canonical pullback/tensor composition
and associativity of the actionAddIso recursion. The normalized zero intervals give
the identity functors and their unit constraints. The affine-line comparisons are natural:
transpose their natural projection-formula augmentation through the natural exceptional
Hom bijection. Thus orderedAdjointTower_regrouping applies to this interval tower.
The recursive gamma is the comparisonStep recursion: sourceReassociation is its actual
one-factor phi, lineComparison its adjacent map, and exceptionalComposite its inverse
conjugate. Uniqueness in the three coordinate-transport existence theorems identifies
these maps, including the initial identity unitor. Evaluate the ordered block formula
at K, cutting after e+1 factors. Reidentify the upper interval with the tower based on
iteratedAffineLine Y (e+1) using blockSchemeEq and blockProjection. Naturality of the
canonical pullback and exceptional adjunction along this equality gives precisely
transportedComparison on the total interval, and blockComposite on the two intervals.
This proves the displayed heterogeneous equality in their specified coordinates.
No interchange or symmetry assertion is used. For d=e=0 this is the two-line
regrouping, and the normalized interval units handle the empty intervals occurring
in the induction; no nonempty-base hypothesis is required. -/
theorem affineSpacePurity_orderedBlockEquation (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (Ring P) Y) (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (hKe : etaleFiniteTor (Ring P) Y Ke)
    (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj) (d e : ℕ) :
    HEq (transportedComparison P Y aY K Ke hKe eK ((e + 1) + d)
      (eqToIso (blockSchemeEq Y (e + 1) (d + 1)))
      (iteratedAffineLineProj (iteratedAffineLine Y (e + 1)) (d + 1) ≫
        iteratedAffineLineProj Y (e + 1))
      (hg' := blockProjectionCompactification Y (d + 1) (e + 1))
      (blockProjection Y (d + 1) (e + 1)))
      (blockComposite P Y aY K Ke hKe eK d e) := by sorry

end AlgebraicGeometry.ProEtale.AffineSpacePurity
