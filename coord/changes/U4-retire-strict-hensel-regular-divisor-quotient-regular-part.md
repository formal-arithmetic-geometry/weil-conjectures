# AlgebraicGeometry.Scheme.strictHenselizationRing_regular_divisor_quotient_part

## Reason

Complete the zero-hole retirement listed in `coord/retire-items.tsv` for `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularPart`.
The upstream twin has a complete proof, using the full affine-neighbourhood colimit
`strictHenselization`. The two current direct Sheaf consumers use the canonically
isomorphic small colimit `strictHenselizationRing`. Replacing their import alone
would supply a theorem about the wrong presentation. Move the canonical comparison
argument into each consumer as a proved private helper and an explicit quotient
transport, then withdraw the duplicate.

The consumers are unclaimed. No source-library file, target statement or definition
is changed. The mathematical node remains needed and points to the upstream owner;
its two parent nodes retain their dependency edges and record the actual transport.

## Old

The retired small-colimit theorem had the exact signature:

```lean
theorem strictHenselizationRing_regular_divisor_quotient_part
    (R : CommRingCat.{u}) [IsRegularRing R] (f : R)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY)
    (hg : ¬ IsUnit (b.hom f)) :
    IsRegularRing (strictHenselizationRing barY ⧸ Ideal.span {b.hom f})
```

Both direct consumers imported:

```lean
public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
import Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularPart
```

Each applied `strictHenselizationRing_regular_divisor_quotient_part R f barY b hb hg`
directly. The item also contained the proved private `comparison_base`, a proof
of compatibility between the small and full structural maps.

## New

Withdraw the item using `deleted.txt`; the delivery tool supplies its empty module.
Attach its node to the retained upstream theorem:

```lean
theorem strictHenselizationRing_regular_divisor_quotient_part
    (R : CommRingCat.{u}) [IsRegularRing R] (f : R)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY)
    (hg : ¬ IsUnit (b.hom f)) :
    IsRegularRing (strictHenselization barY ⧸ Ideal.span {b.hom f})
```

Both direct consumers now import:

```lean
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularPart
```

The public structural-map import still supplies precisely the ring and structural
map in their existing signatures. Its old Sheaf wrapper also exports a different
`strictHenselizationStructuralMap_eq`, which conflicts with the upstream full-colimit
equation needed by the replacement proof. Use the upstream owner, as the retired
item already did. Both consumer theorem signatures, visibility and existing
docstrings are verbatim; their definitions are unchanged (neither has any).

For `e = smallStrictHenselizationColimitIso barY`, the private `comparison_base`
proves `Spec.map e.hom ≫ strictHenselizationStructuralMap barY =
strictLocalizationToBase barY`. Its proof is copied from the retired item: apply
the final-functor coprojection equation and the two structural-map equations.
Thus `b ≫ e.hom` satisfies the upstream base-map hypothesis. If its image of `f`
is a unit, mapping the unit through `e.inv` contradicts `hg`.

Apply the retained upstream regularity theorem to this composite. The inverse
ring equivalence sends its principal ideal to `Ideal.span {b.hom f}` by
`Ideal.map_span`, `Set.image_singleton` and inverse cancellation. The resulting
`Ideal.quotientEquiv` sends the full quotient to the original small quotient;
`IsRegularRing.of_ringEquiv` yields the required regularity. In DomainPart the
remaining local-quotient and regular-local-domain argument is untouched. In Regular
the regularity result is paired with the unchanged domain theorem application.

No hypotheses are added. The comparison and quotient argument work also for
`f = 0`, zero-dimensional rings and arbitrary nonunit generators. A zero base
ring cannot admit the displayed geometric point; no new nontriviality assumption
is introduced. No arbitrary mathematical data is chosen: the category object in
the comparison proof only witnesses a property of the fixed canonical maps.

The regularity node's `lean` attachment now records the upstream module and its
verbatim full-colimit signature. Its proof records assembly from the same auxiliary
node as the upstream proof. The DomainPart and Regular nodes preserve all existing
mathematical dependency edges and now describe the Lean transport. Their statement,
unit, source, and existing Lean attachment remain unchanged. No DAG node is deleted.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularPart --uses strictHenselizationRing_regular_divisor_quotient_part`
finds eleven downstream modules and exactly the two direct callers below. A source
scan of `lean/` confirms these are all current direct imports; `quarantine/` contains
no import of the retired module and no use of its declaration. A parsed DAG scan
finds the same two actual parents through `proof_deps` and proof-step `uses`; both
are updated here. Other textual mentions are provenance. The unit
`sk-prop-input-spreading` is unchanged and its regular-divisor route is preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictHenselRootSection | unclaimed | Transitive consumer. No source, statement or definition change; checked against the adapted consumers. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictLocalLimit | unclaimed | Transitive consumer. No source, statement or definition change; checked against the adapted consumers. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotient | unclaimed | Transitive consumer. No source, statement or definition change; checked against the adapted consumers. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientDomainPart | unclaimed | Direct caller. Import the upstream owner and explicitly transport regularity across the colimit and principal-quotient comparisons. Signature, visibility and docstring unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientNoetherian | unclaimed | Transitive consumer. No source, statement or definition change; checked against the adapted consumers. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegular | unclaimed | Direct caller. Import the upstream owner and explicitly transport regularity across the colimit and principal-quotient comparisons. Signature, visibility and docstring unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel | unclaimed | Transitive consumer. No source, statement or definition change; checked against the adapted consumers. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationFinite | unclaimed | Transitive consumer. No source, statement or definition change; checked against the adapted consumers. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationGenericEtale | unclaimed | Transitive consumer. No source, statement or definition change; checked against the adapted consumers. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData | unclaimed | Transitive consumer. No source, statement or definition change; checked against the adapted consumers. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootTameNormalization | unclaimed | Transitive consumer. No source, statement or definition change; checked against the adapted consumers. |

The original DomainPart fails against the compiled withdrawn stub at line 31 with
`Unknown identifier strictHenselizationRing_regular_divisor_quotient_part`.
The original Regular fails against that stub at line 26 with the same error.
All eleven downstream modules compile as individual files against the adapted
consumers and the withdrawn stub, without warnings (2.1–10.2 seconds each).
The delivery's compiler and axiom probe check the final two-module set. Unchanged
verification copies are removed from the delivery.

## Status

landed 20261021T021028-L-2694045 2026-10-21 (merge of deliver/U4/Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularPart)
