# AlgebraicGeometry.Etale.RawModuleScalarComparison.derivedPullbackIsoImpl and derivedPullbackIso

## Reason

Repair verification, 2026-10-23 14:44 UTC: this record is delivered as
`coord/changes/P2-derived-pullback-reuse.md`. Any reader correction for the
approved d62288e2e4c packet must preserve that full relative path. A fresh
fourteen-module lcompile.py run passed with exit code 0 and no Lean diagnostics.
The live/quarantined consumer audit has no missing records or remaining
imports of the withdrawn concrete source-square module. The retained
implementation and its inverse-comparison equality below are unchanged.

This record is retained in the resubmission requested for reviewer-approved
head d62288e2e4c (reviewer C-d6228). Landing failed because --apply-fixes
referred to P2-derived-pullback-reuse.md as a bare basename. Its delivery path
is coord/changes/P2-derived-pullback-reuse.md; this record is included at that
full path with Status open. The delivery is rebuilt on current sheaf-dag and
the retained Lean files are recompiled on the server. The reviewed mathematical
construction and consumer adaptations below are preserved.

For the landing reader: apply a correction to this record only at
`coord/changes/P2-derived-pullback-reuse.md` relative to the delivery root.
`P2-derived-pullback-reuse.md` alone is not a delivery path. All five change
records are new files on the refreshed base and retain Status open; the
landing operation records their eventual landing status. The current packet
has been recompiled through the project-server backend without diagnostics.

Use the inverse of the existing canonical forward derived comparison instead of
rebuilding the reverse composite. The private proved equality
reverseDerivedComparison shows that derived lifting preserves inversion and that
reversing the three factors gives exactly the inverse forward comparison.
derivedPullbackIsoImpl_eq_formula specializes it to these sheaf functors. Thus
the implementation is equal to its previous formula, with the exact public
signature preserved. derivedPullbackIso reuses this existing implementation.

The unshifted coefficient and shift-compatibility theorems already exist in the
adopted upstream module, using the forward comparison's hom. With the new
implementation, this is definitionally the historical comparison's inv.
Reexport those proved theorems. The same identification permits reexport of the
shifted coefficient square and scalarCoefficientFactor from its upstream twin.
The latter definition agrees verbatim after expanding the forget abbreviation.
The public theorem statements retain their meaning, all hypotheses and universes.

All source-library signatures, attributes, public imports and bodies are left
verbatim. No target statement, mathematical node statement or unit route changes.
No axiom, hole, new module or mathematical obligation is introduced. Targets using
these definitions require the ordinary definition review; the displayed equality
preserves the actual comparison, not just its source and target. The generic
identity covers zero objects, identity maps and every integer shift.

## Old

```lean
noncomputable def derivedPullbackIsoImpl (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus ⋙
        (forget Λ X).mapDerivedCategoryPlus ≅
      (forget Λ Y).mapDerivedCategoryPlus ⋙
        (upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso
    (upperStar (ModuleCat.{u + 1} Λ) f) (forget Λ X)).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (pullbackIso Λ f) ≪≫
      Functor.mapDerivedCategoryPlusCompIso
        (forget Λ Y) (upperStar AddCommGrpCat.{u + 1} f)
```

```lean
noncomputable def derivedPullbackIso (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus ⋙
        (forget Λ X).mapDerivedCategoryPlus ≅
      (forget Λ Y).mapDerivedCategoryPlus ⋙
        (upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso
    (upperStar (ModuleCat.{u + 1} Λ) f) (forget Λ X)).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (pullbackIso Λ f) ≪≫
      Functor.mapDerivedCategoryPlusCompIso
        (forget Λ Y) (upperStar AddCommGrpCat.{u + 1} f)
```

## New

```lean
noncomputable def derivedPullbackIsoImpl (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus ⋙
        (forget Λ X).mapDerivedCategoryPlus ≅
      (forget Λ Y).mapDerivedCategoryPlus ⋙
        (upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus :=
  (moduleAbelianDerivedUpperStarIso Λ f).symm

/-- The inverse canonical comparison is exactly the historical reverse composite.
Source: the natural-isomorphism symmetry identity for exact derived functors.
Proof: derived lifting sends an inverse natural isomorphism to the inverse lifted
isomorphism. Reversing the three factors and associating composition gives the
canonical forward comparison's inverse.
(blueprint: def-sbc-raw-scalar-derived-pullback-iso). -/
theorem derivedPullbackIsoImpl_eq_formula (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Functor.mapDerivedCategoryPlusCompIso
      (upperStar (ModuleCat.{u + 1} Λ) f) (forget Λ X)).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso (pullbackIso Λ f) ≪≫
      Functor.mapDerivedCategoryPlusCompIso
        (forget Λ Y) (upperStar AddCommGrpCat.{u + 1} f) =
      derivedPullbackIsoImpl Λ f := by
  unfold derivedPullbackIsoImpl moduleAbelianDerivedUpperStarIso
  exact Functor.reverseDerivedComparison
    (upperStar (ModuleCat.{u + 1} Λ) f) (forget Λ X) (forget Λ Y)
    (upperStar AddCommGrpCat.{u + 1} f) (moduleAbelianUpperStarIso Λ f)
```

```lean
noncomputable abbrev derivedPullbackIso (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus ⋙
        (forget Λ X).mapDerivedCategoryPlus ≅
      (forget Λ Y).mapDerivedCategoryPlus ⋙
        (upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus where
  hom := (moduleAbelianDerivedUpperStarIso Λ f).inv
  inv := (moduleAbelianDerivedUpperStarIso Λ f).hom
  hom_inv_id := (moduleAbelianDerivedUpperStarIso Λ f).inv_hom_id
  inv_hom_id := (moduleAbelianDerivedUpperStarIso Λ f).hom_inv_id
```

Reviewer correction (cc review of head 5fd9dbe307d3, 2026-10-23): the delivered
`def derivedPullbackIso := derivedPullbackIsoImpl Λ f` broke the direct importer
Sheaf.AlgebraicGeometry.RawModuleAbelianHomSourceFormula: its statement uses
`(derivedPullbackIso Λ f.left).inv.app`, while the reexported upstream
rawModuleScalar_source_class_formula uses `(moduleAbelianDerivedUpperStarIso Λ f.left).hom.app`,
and the closing `simpa … using ht` failed with "Type mismatch: After simplification"
(line 70). derivedPullbackIso is now a reducible abbreviation written as the explicit
inverse structure, so its `inv` reduces to the forward comparison's `hom` at reducible
transparency. It is literally `(moduleAbelianDerivedUpperStarIso Λ f).symm`, i.e.
definitionally `derivedPullbackIsoImpl Λ f`; signature, data and meaning are unchanged.
With it the importer compiles unchanged; derivedPullbackIso has no other user.
This correction was lost when heads d62288e2e4cb and 677039e4ec2e were rebuilt from the
delivered files; it is re-applied by the cc review of 677039e4ec2e (2026-10-24).
A re-delivery must start from the reviewer's corrected files, not the delivered ones.

RawModuleScalarCoefficientUnshifted publicly imports its canonical upstream twin
and the existing compatibility module. It keeps the derivedPullbackIso definition
above and reexports rawModuleScalar_derivedPullbackIso_commShift and
rawModuleScalar_coefficient_unshifted.

RawModuleScalarCoefficientSquare now consists of the following reexports:

```lean
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientSquare
public import Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted
```

Its public scalarCoefficientFactor, rawModuleScalar_coefficient_square and
rawModuleScalar_coefficient_square_of_unshifted names come from the existing
canonical upstream module. Their existing DAG nodes attach to those declarations.
The previous duplicate private congruence metaprogram is unnecessary.

derivedPullbackIsoImpl_eq_formula is a proved public equation for the existing
definition node, recorded in that node's declarations. It exposes the already
required three-factor formula to consumers without exposing private upstream
imports. This is the existing definition's API, not a new obligation or split.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomSourceFormula | unclaimed | Same comparison by the proved inverse identity; canonical public names and all hypotheses remain available. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomTargetFormula | unclaimed | Same comparison by the proved inverse identity; canonical public names and all hypotheses remain available. |
| Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientSquare | unclaimed | Same comparison by the proved inverse identity; canonical public names and all hypotheses remain available. |
| Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted | unclaimed | Same comparison by the proved inverse identity; canonical public names and all hypotheses remain available. |
| Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso | unclaimed | Same comparison by the proved inverse identity; canonical public names and all hypotheses remain available. |
| Sheaf.AlgebraicGeometry.RawModuleScalarHomCompositeFormula | unclaimed | Same comparison by the proved inverse identity; canonical public names and all hypotheses remain available. |
| Sheaf.AlgebraicGeometry.RawModuleScalarHomEvaluation | unclaimed | Same comparison by the proved inverse identity; canonical public names and all hypotheses remain available. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceClassFormula | unclaimed | Reexports the existing proved canonical theorem with the same comparison and hypotheses. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceSquare | unclaimed | Unused module withdrawn; stale definition references repaired in P2-prune-unused-concrete-source-square.md. |

The table lists the current downstream whole-name users of the changed definitions
and reexported coefficient declarations, as well as the adapted coefficient and source-square modules.
The scalar-forgetting compatibility users are also recorded in the main retirement
record. All listed modules are unclaimed. The unused concrete source-square module is
withdrawn, as recorded in P2-prune-unused-concrete-source-square.md; no remaining
proof needs to transport its generic formula.

RawModuleScalarSourceClassFormula reexports the existing canonical theorem,
whose forward comparison is definitionally derivedPullbackIso.inv in this
packet. Its existing source-prefix definition is also reexported (see the
construction-reexports record). The old concrete source-class proof both
reported a comparison type mismatch and exceeded the compile limit when
transport was inserted; the existing canonical proof already handles symmetry
and the coefficient-complex equations. Reusing that proof avoids duplicating
those calculations. All public hypotheses and the actual comparison are kept.

The final 2026-10-23 source reconciliation retains RawModuleScalarPullbackComparison as a compatibility reexport with no duplicate declarations, because its H9 consumer is now quarantined. The quarantined consumer is not restored or edited. The canonical construction and equality proofs in this record are unchanged.

## Status

landed 20261024T015347-L-2367834 2026-10-24 (merge of deliver/P2/Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison)
