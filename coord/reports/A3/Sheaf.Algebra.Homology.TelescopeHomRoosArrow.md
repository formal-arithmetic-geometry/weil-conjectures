## What changed

Filled `CategoryTheory.telescopeHom_roos_arrow_iso` in
`Sheaf.Algebra.Homology.TelescopeHomRoosArrow`. The source is identified with the
ordinary inverse limit by the proved internal-Hom colimit cone universal property.
The target is identified with the Roos fibre using the coproduct universal property
and an explicit signed first-variable Hom/cone isomorphism. The two given
restrictions on `f` identify the arrow's two coordinates.

The proof reuses the fully proved coordinate API of `SignedDoubleHomCone` through
`import all`, together with `RingedHomComplexColimitCone`, `InternalHomCoproduct`,
and the fan-isomorphism transport and tower product-shift APIs. These imports are private proof imports. All
new helpers are private and proved. Existing public imports and the theorem's
signature are preserved. The item's DAG proof and proof dependencies describe
this construction. No other library module changes.

## Proved and sorry left

Closed the single original hole in
`CategoryTheory.telescopeHom_roos_arrow_iso`
(`lem-weil-pbc-telescope-hom-roos-arrow`). Zero holes remain in the item;
zero holes are added and zero obligations are split off.

Validation: the complete file compiled successfully through `lcompile.py` in
52.7 seconds. The temporary profiling settings used for timing were removed.
The statement, original public imports, line lengths, and allowed DAG fields
were also checked against the shared source.

## No longer needed

No modules or imports are withdrawn. The former direct proof edge to
`def-pur-hom-complex` is refined into the actual projection, coproduct, and
colimit universal-property APIs used by the proof. The underlying Hom-complex
definition remains a statement dependency and is still imported publicly.
The unit's realized route is preserved.

## Where the brief, the DAG or earlier work was wrong

The statement and its sign convention are correct. The existing proof plan
omitted the available proved coordinate API in `SignedDoubleHomCone`, the
coproduct internal-Hom fan, and the internal-Hom colimit cone. Reusing these
closes the obligation without another split. The cone-coordinate construction
uses no injectivity or exactness assumption.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
