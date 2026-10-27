module

public import Sheaf.Paper.AffineSpaceTraceProductData

/-! # Last-line contraction in the ordered affine tower

Source: current blueprint sec-smooth-purity/sk-prop-an, Integration paragraph,
and Step 1 of lem-pur-affine-space-trace-factorization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.AffineSpaceTrace
open AffineLinePurity AffineSpacePurity VectorIntegrationSite OrderedAffineTranspose

/-- The canonical source change from the next Tate power to the last-line source.
Source: ordered recursion and its coefficient-unit source identification
(blueprint: def-pur-affine-space-last-line-contraction). -/
@[irreducible]
def successorSourceIso (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ) :
    tate P Y (d + 2) ≅ projectionSourceObject (Ring P) (lastProjection Y (d + 1))
      (coefficient P.coefficients.l P.extension (P.level - 1)
        (iteratedAffineLine Y (d + 1)) P.level (annihilates P)) (tate P Y (d + 1)) := by
  let e := (tateSourceIso P Y (d + 2)).symm ≪≫
    sourceReassociation P Y aY (unit (Ring P) Y) (d + 1) ≪≫
    (lineSource P (iteratedAffineLine Y (d + 1))).mapIso (tateSourceIso P Y (d + 1))
  exact e ≪≫ eqToIso (lineSource_obj_eq P _ _)

/-- Contract the last affine line before integrating the preceding coordinates.
This is the actual inverse compact-support compositor, change of compactification,
and canonical inverse projection followed by normalized line trace. The origin and
projection arguments are proofs; they choose no operation or map.
Source: alpha inverse followed by Rp_!(b) in the Integration paragraph
(blueprint: def-pur-affine-space-last-line-contraction). -/
@[irreducible]
def lastLineContraction (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY] (d : ℕ)
    (h : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (Ring P))
      (iteratedAffineLine Y (d + 2)) (externalTate P Y (d + 1)))
    (hq : ProjectionInvertible (Ring P)
      (affineTraceLineCompactification (iteratedAffineLine Y (d + 1)))
      (coefficient P.coefficients.l P.extension (P.level - 1)
        (iteratedAffineLine Y (d + 1)) P.level (annihilates P)) (tate P Y (d + 1))) :
    (compact P Y (d + 2)).obj (tate P Y (d + 2)) ⟶
      (compact P Y (d + 1)).obj (tate P Y (d + 1)) := by
  letI := (projection_geometry Y (d + 1)).2
  letI := (projection_geometry Y (d + 2)).2
  letI : HasCompactification
      (lastProjection Y (d + 1) ≫ iteratedAffineLineProj Y (d + 1)) :=
    HasCompactification.of_eq (f := iteratedAffineLineProj Y (d + 2))
      (iteratedAffineLineProj_succ Y (d + 1))
  letI : LocallyOfFiniteType (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).1
  letI : QuasiCompact (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).2.1
  letI : IsSeparated (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).2.2
  let e := successorSourceIso P Y aY d
  let W := projectionSourceObject (Ring P) (lastProjection Y (d + 1))
    (coefficient P.coefficients.l P.extension (P.level - 1)
      (iteratedAffineLine Y (d + 1)) P.level (annihilates P)) (tate P Y (d + 1))
  have hW : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (Ring P))
      (iteratedAffineLine Y (d + 2)) W :=
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (Ring P)) _).prop_of_iso
      (externalTateIso P Y aY (d + 1) ≪≫ e) h
  let c := affineTraceLineCompactification (iteratedAffineLine Y (d + 1))
  let b := BaseChangedLineTrace.originChange (Ring P)
    (HasCompactification.compactification (lastProjection Y (d + 1))) c W hW
  let t := projectionTensorTrace (Ring P) c
    (coefficient P.coefficients.l P.extension (P.level - 1)
      (iteratedAffineLine Y (d + 1)) P.level (annihilates P)) (tate P Y (d + 1))
    (AffineLineEvaluation.trace P _ (towerBase aY (d + 1))) hq
  exact (compact P Y (d + 2)).map e.hom ≫
    (originCompositionAmbient (Ring P) (lastProjection Y (d + 1))
      (iteratedAffineLineProj Y (d + 1))).inv.app ⟨W, hW⟩ ≫
    (compact P Y (d + 1)).map (b.hom ≫ t)

/-- The successor transpose contracts the last line and then integrates the old block.
Source: current blueprint sec-smooth-purity/sk-prop-an, Integration paragraph;
lem-pur-affine-space-trace-factorization, proof Step 1
(blueprint: lem-pur-affine-space-trace-successor-contraction).

Proof: apply AffineLineEvaluation.composite_transpose at p=p_(d+1), M=T_(d+1),
K=A_Y and t=gamma_(p,A_Y). The shifted Tate power is finite-Tor constructible:
tensoring a constant sheaf by each locally free Tate line and shifting by two
preserves this class. Choose its ordinary etale representative only for this proof.
Unfold the ordered successor comparison. Its source change is exactly
successorSourceIso: first undo tateSourceIso at d+2, use sourceReassociation, and
apply the line source to tateSourceIso at d+1. Naturality of the line evaluation
moves this last isomorphism from the comparison to its source. The inverse
compositor and the compactification comparison then give lastLineContraction.
The canonical projection inverse agrees with the one in evaluation because both
invert the same specified projection. The remaining compact-support image of
gamma followed by its counit is integration at d+1. Functoriality and associativity
supply the displayed equality. This also holds for the empty scheme and zero
coefficient ring; no trace base-change or binary-product assertion is needed. -/
theorem integration_successor_contraction
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY] (d : ℕ)
    (h : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (Ring P))
      (iteratedAffineLine Y (d + 2)) (externalTate P Y (d + 1)))
    (hq : ProjectionInvertible (Ring P)
      (affineTraceLineCompactification (iteratedAffineLine Y (d + 1)))
      (coefficient P.coefficients.l P.extension (P.level - 1)
        (iteratedAffineLine Y (d + 1)) P.level (annihilates P)) (tate P Y (d + 1))) :
    integration P Y aY (d + 2) =
      lastLineContraction P Y aY d h hq ≫ integration P Y aY (d + 1) := by sorry

end AlgebraicGeometry.ProEtale.AffineSpaceTrace
