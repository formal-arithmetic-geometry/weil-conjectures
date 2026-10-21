# AlgebraicGeometry.Scheme.strictHenselization_regular_divisor_quotient

## Reason

Complete the zero-hole retirement listed in `coord/retire-items.tsv`, row 1975.
The item duplicates a proved upstream theorem, using the small representative colimit
instead of the full affine-neighbourhood colimit. Its public duplicate is withdrawn,
its four direct consumers are adapted, and its mathematical node is retained on the
upstream theorem. The source tree under `lean/WeilConjectures/` is unchanged.

## Old

The retired small-colimit declaration has this exact signature:

```lean
theorem strictHenselization_regular_divisor_quotient
    (R : CommRingCat.{u}) [IsRegularRing R] (f : R)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY)
    (hg : ¬ IsUnit (b.hom f)) :
    IsNoetherianRing (strictHenselizationRing barY) ∧
      IsRegularRing (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) ∧
      IsDomain (strictHenselizationRing barY ⧸ Ideal.span {b.hom f})
```

Four direct consumers privately import:

```lean
import Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotient
```

Six direct or transitive consumers publicly import:

```lean
public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
```

`RegularDivisorStrictLocalLimit` additionally privately imports
`Sheaf.Paper.StrictHenselizationFunctoriality` for its residue theorem.
That import also exposes the old structural-map helper.

## New

Withdraw the item with `deleted.txt`; the delivery tool writes the empty module.
Attach its existing node to the retained upstream declaration, whose exact signature is:

```lean
theorem strictHenselization_regular_divisor_quotient
    (R : CommRingCat.{u}) [IsRegularRing R] (f : R)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY)
    (hg : ¬ IsUnit (b.hom f)) :
    IsNoetherianRing (strictHenselization barY) ∧
      IsRegularRing (strictHenselization barY ⧸ Ideal.span {b.hom f}) ∧
      IsDomain (strictHenselization barY ⧸ Ideal.span {b.hom f})
```

The four direct consumers privately import the upstream quotient module and
`Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison`.
Each has a proved private `small_regular_divisor_quotient` transport lemma.
The canonical `smallStrictHenselizationColimitIso` and the already proved
`smallStrictHenselizationColimitIso_toBase` identify the two prescribed base maps.
Apply the upstream theorem to `b` followed by the comparison. Its inverse carries
units back to units, so the nonunit hypothesis transfers. Transfer Noetherianity by
`isNoetherianRing_of_ringEquiv`; transfer quotient regularity and the domain property
by the explicitly induced `Ideal.quotientEquiv`, `IsRegularRing.of_ringEquiv`, and
`MulEquiv.isDomain_iff`. No new public declaration or unproved fact is introduced.

All six structural-map imports above become:

```lean
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
```

This supplies the same small-colimit ring, scheme and structural map definitions.
It drops the obsolete duplicate public helper whose name conflicts with the upstream
full-colimit helper. The first bare upstream import replacement failed with:

```
import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap failed,
environment already contains 'AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_eq'
from WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
```

The three transitive consumer files change only that single import line.
In `RegularDivisorStrictLocalLimit`, replace the private functoriality import with
`WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality` and the existing
`Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility`. Transfer the closed-point
identity through the same canonical comparison, using `AlgebraicGeometry.Spec_closedPoint`.
Strict henselianity uses the existing small-model compatibility theorem. The strict-local-limit
declaration uses scoped transparency options for the spectrum/colimit identifications;
no file-level option is added. All existing
public signatures, declaration docstrings, definitions and visibility remain verbatim.

The mathematical regular-divisor quotient node keeps both Noetherianity and regularity
proof dependencies and its statement. Four consumer node copies record the actual
comparison theorem used by their private proofs. The two further DAG parents in
`sec-deligne-laumon-a1` keep their mathematical dependency: the theorem still exists,
now on the upstream owner, and the canonical comparison identifies its presentation.
No unit statement or step is bypassed. No target definition changes, so no target
statement review is reopened. No arbitrary mathematical object is selected.

## Users

`tools/downstream.py` reports seven downstream modules; a declaration search finds
five call sites in four direct consumers. A scan of `lean/` and `quarantine/` finds
no other direct import of the retired module. A parsed scan of `stmt_deps`,
`proof_deps`, and proof-step `uses` finds the four adapted consumer nodes and the
Kummer-root and semistable-coordinate-divisor purity nodes. All six mathematical
parent edges remain valid. All seven modules were unclaimed when checked.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictLocalLimit | unclaimed | Direct consumer; replace the private quotient import, transport its two applications, and recover the small closed-point identity from the upstream residue theorem. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationFinite | unclaimed | Direct consumer; replace the private quotient import and transport Noetherianity and quotient properties. Replace the public structural-map import to remove the colliding helper. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationGenericEtale | unclaimed | Direct consumer; same private transport and public structural-map import migration. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData | unclaimed | Direct consumer; same private transport and public structural-map import migration. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootTameNormalization | unclaimed | Transitive consumer; change only the public structural-map import to remove the collision. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel | unclaimed | Transitive consumer; change only the public structural-map import to remove the collision. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictHenselRootSection | unclaimed | Transitive consumer; change only the public structural-map import to remove the collision. |

`lcompile.py --all` compiled all seven downstream modules individually in import order
with exit 0 and no warnings (3.1–11.2 seconds per file).
A source comparison verifies that every pre-existing public declaration signature
is preserved, and that node edits touch only `lean`, `proof`, `proof_deps`, and
`proof_origin`. All delivered Lean files have zero `sorry` tokens.
The transport retains zero divisors as parameters when allowed (in particular
`f = 0`, needed to recover ambient regularity); it requires only the original
nonunit hypothesis. A geometric point excludes the zero base ring, and a unit
parameter cannot satisfy that hypothesis. Fields and arbitrary universes are retained.

## Status

landed 20261021T140748-L-2740975 2026-10-21 (merge of deliver/A3/Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotient)
