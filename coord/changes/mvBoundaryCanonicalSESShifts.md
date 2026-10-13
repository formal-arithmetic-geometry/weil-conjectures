# mvBoundary_equation

## Reason

Repair reviewer X-62c4d E1/E2: the old equation quantified arbitrary boundaries
and independent CommShift data, while distinguishedness constrained neither shift.
On the identity square for P1 over characteristic zero, O(-2) and its standard
cover have a nonzero pushed-forward boundary. Multiplying only the source shift
in degree n by (-1)^n preserved every old hypothesis but negated the left side.
The corrected equation must specify both the SES boundary and its shift structures.

The new interface constructs the boundary from the concrete SES of the fixed
K-injective resolution. Its explicit open-image comparison is transported by
the fixed resolution isomorphism and normalized to mvOpenRestrictionAdjunction.
Pullback shifts are constructed by the unique adjunction mate of the existing
right-derived direct-image shift, under precisely mvDerivedPullbackAdjunction.
The delivered proofs establish unit/counit compatibility, the explicit shifted
Hom-equivalence identity, triangulatedness, and distinguishedness of these exact
SES triangles and their images. The generic base-change shift calculation is
proved from the existing pinned-base-change theorem and uniqueness of shift mates.
The cover boundary naturality step before subsequent direct image is split off.
This establishes the required shift compatibility; image distinguishedness is
not used as a normalization hypothesis.

## Old

```lean
theorem mvBoundary_equation
    {X S X' S' : Scheme.{u}} [IsAffine S] [IsAffine S']
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] (hsq : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    (hUV : IsCompact ((U ⊓ V : X.Opens) : Set X)) (hcover : U ⊔ V = ⊤)
    (hK : schemeDerivedQCohProperty X K) (hK' : schemeDerivedQCohProperty X' K')
    (ψ : (derivedPullback g').obj K ⟶ K')
    (δ : (schemeDerivedDirectImage (U ⊓ V).ι).obj
      ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.obj K) ⟶ K⟦(1 : ℤ)⟧)
    (δ' : (schemeDerivedDirectImage (g' ⁻¹ᵁ (U ⊓ V)).ι).obj
      ((schemeOpenRestriction X' (g' ⁻¹ᵁ (U ⊓ V))).mapDerivedCategory.obj K') ⟶ K'⟦(1 : ℤ)⟧)
    (csF : (schemeDerivedDirectImage f ⋙ derivedPullback g).CommShift ℤ)
    (csG : (schemeDerivedDirectImage f').CommShift ℤ)
    (hT : mvBaseChangeTriangle X U V (U ⊓ V) (homOfLE inf_le_left)
      (homOfLE inf_le_right) (mvOpenRestrictionAdjunction X U)
      (mvOpenRestrictionAdjunction X V) (mvOpenRestrictionAdjunction X (U ⊓ V)) K δ ∈
      distTriang (schemeDerivedCategory X))
    (hT' : mvBaseChangeTriangle X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) (g' ⁻¹ᵁ (U ⊓ V))
      ((Opens.map g'.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U)))
      ((Opens.map g'.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V)))
      (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ U))
      (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ V))
      (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ (U ⊓ V))) K' δ' ∈
      distTriang (schemeDerivedCategory X')) :
    (schemeDerivedDirectImage f ⋙ derivedPullback g).map δ ≫
        (letI := csF;
          (schemeDerivedDirectImage f ⋙ derivedPullback g).commShiftIso (1 : ℤ)).hom.app K ≫
        (schemeDerivedBaseChangeMap f f' g g' hsq.w K ≫
          (schemeDerivedDirectImage f').map ψ)⟦(1 : ℤ)⟧' =
      mvBaseChangeOpenMap f f' g g' hsq.w K K' ψ (U ⊓ V) ≫
        (schemeDerivedDirectImage f').map δ' ≫
        (letI := csG; (schemeDerivedDirectImage f').commShiftIso (1 : ℤ)).hom.app K'
```

## New

```lean
theorem mvBoundary_equation
    {X S X' S' : Scheme.{u}} [IsAffine S] [IsAffine S']
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] (hsq : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    (hUV : IsCompact ((U ⊓ V : X.Opens) : Set X)) (hcover : U ⊔ V = ⊤)
    (hK : schemeDerivedQCohProperty X K) (hK' : schemeDerivedQCohProperty X' K')
    (ψ : (derivedPullback g').obj K ⟶ K') :
    let δ := mvCanonicalBoundary X U V (U ⊓ V) rfl hcover K
    let δ' := mvCanonicalBoundary X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) (g' ⁻¹ᵁ (U ⊓ V))
      (Scheme.Hom.preimage_inf g').symm
      (by rw [← Scheme.Hom.preimage_sup, hcover, Scheme.Hom.preimage_top]) K'
    let csF := mvCanonicalSourceShift f g
    let csG := mvCanonicalTargetShift f'
    (schemeDerivedDirectImage f ⋙ derivedPullback g).map δ ≫
        (letI := csF;
          (schemeDerivedDirectImage f ⋙ derivedPullback g).commShiftIso (1 : ℤ)).hom.app K ≫
        (schemeDerivedBaseChangeMap f f' g g' hsq.w K ≫
          (schemeDerivedDirectImage f').map ψ)⟦(1 : ℤ)⟧' =
      mvBaseChangeOpenMap f f' g g' hsq.w K K' ψ (U ⊓ V) ≫
        (schemeDerivedDirectImage f').map δ' ≫
        (letI := csG; (schemeDerivedDirectImage f').commShiftIso (1 : ℤ)).hom.app K'
```

`mvCanonicalBoundary` in
`Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisCanonicalData`
is the inverse fixed comparison followed by `triangleOfSESδ` and the shifted
fixed resolution isomorphism. `mvCanonicalPullbackShift` is
`(mvDerivedPullbackAdjunction g).leftAdjointCommShift ℤ` using the existing
right-derived shift. `mvCanonicalSourceShift` composes that shift with the
existing direct-image shift; `mvCanonicalTargetShift` abbreviates the existing
right-derived shift. No shift or boundary data is chosen from a bare existence
of triangles. No global instance is installed by any new module.

`mvBoundary_data` keeps its original signature and returns exactly these choices.
The new proved `mvBoundary_canonical_data` specifies distinguishedness for these
very boundaries and shifts, permitting the unchanged consumer to use them.

## Users

Read all 431 downstream modules with tools/downstream.py --uses, then whole-word
searched the library. The only consumer of either old declaration is the first
row below; the second is the item itself. No target declaration uses the new
definitions in its statement. Challenge.lean and all five target statements
are unchanged. No existing public definition's body is changed, so this repair
does not change the meaning of any target through a definition.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisBoundary | unclaimed | Forced proof adaptation only: use the explicitly specified canonical data and the corrected equation; its complete signature and visibility are identical. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisBoundaryData | T4 | Correct equation signature; preserve mvBoundary_data; prove both declarations and add the proved canonical-data refinement. |

The added public canonical-data import reexports the original Maps module through
its own public import, preserving the original exported definitions. It additionally
exports the real canonical constructions needed in the corrected equation's type.

The equation node's `lean.statement` is the exact corrected signature. Its
natural-language statement and `statement_change` now explicitly describe fixed
SES boundaries and adjunction-mate shifts. Its sole DAG citer is
`lem-pc-rf-mv-base-change-connecting-square`: its use still holds because its
unchanged existential claim is assembled from those same fixed choices. The
parent proof record is updated accordingly.

## Status

landed 20261013T222417-L-1227906 2026-10-13 (merge of deliver/T4/Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisBoundaryData)
