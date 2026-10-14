## What changed

Repaired the duplicate identified in upstream review #1428: in
Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed, SheafOfModules.tensorClosed is now a
transparent compatibility abbreviation of the existing tensor-closed API, rather than another
independently stated theorem. Its type, binders, universe and visibility are identical. Its body
uses SheafOfModules.monoidalClosed, tensorHomEquiv, the three naturality lemmas, and the
MonoidalFree additive tensor functor instances. No tensor or internal-Hom data are reconstructed.
Updated the node's Lean record and proof-origin note. No downstream adaptation is required.
Change record: coord/changes/tensorClosed-compatibility-abbreviation.md.

Validation: the delivered module compiles without warnings; its signature was compared verbatim
against the previous declaration after replacing only `theorem` with `abbrev`. Three unchanged
callers compile against the sandbox overlay: Sheaf.Algebra.Homology.KFlatClosure (6.2 s),
Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat (3.5 s), and
Sheaf.Paper.ModuleCupNaiveMap (48.4 s). They exercise the closed-structure projection, an
existential elimination, and public definitions choosing the additive/closed instances.
The dry run compiles the delivery, checks its axioms, and passes preflight apart from the
second reading reserved for the independent reader. Nothing is pushed.

## Proved and sorry left

This is a duplicate repair, not a new proof or decomposition. The checkout already had zero
sorries in this module. Holes closed: none. Holes added: none. Sorries left: none.
SheafOfModules.tensorClosed remains completely proved from the existing source API.
Its node is lem-pc-sheaf-modules-tensor-closed. The dry-run axiom probe checks the delivered
abbreviation. No new declarations or nodes are added.

## No longer needed

No imports, nodes or modules are newly pruned. The module's current route already avoids the
separate lem-pur-sheaf-hom-is-sheaf proof dependency: InternalHom and MonoidalClosed supply it.
The public TensorProduct import is retained for downstream compatibility; its change-of-rings
and tensor-power constructions are not used by the tensorClosed proof.

## Where the brief, the DAG or earlier work was wrong

The dispatched brief says the module still contains sorry. The checked-out module is already
proved, and its node records a prior reviewed proof. coord/repairs.txt instead lists this module
for the upstream #1428 duplicate repair. This delivery therefore repairs the duplicate as an
abbreviation and claims zero proof progress. The unit realized record has no statement or step
for this node; its route is preserved. The node's mathematical statement does not change.

## Second reading by T4

1. I compared the delivered module with the repository version. The declaration keeps the
same parameters, universes, local instances, conjunctions, existential family, and naturality
equation byte for byte; only its kind changes from `theorem` to transparent `abbrev`, and the
docstring explains that it packages the existing API. Verdict: unchanged statement and no
accidental hypothesis or conclusion change.
2. I compiled the module with `lcompile.py`; it succeeds without errors or warnings and contains
no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The abbreviation body is
fully elaborated from `monoidalCategory`, `symmetricCategory`, `monoidalClosed`,
`tensorHomEquiv`, the naturality lemmas, and the additive tensor functor maps. Verdict: valid
proof term with no new holes.
3. The compatibility abbreviation is not a new mathematical statement: it exposes exactly the
already established source structures and equivalence. I checked the edge cases retained by the
signature (arbitrary site, zero objects, and empty-site instances) and found no strengthened
hypothesis or weakened conclusion. No split-off statement or node was added. Verdict: true and
exactly as strong as the existing declaration.
4. The imports remain those required by the public type and proof body; no import is newly
public solely for the proof. The node's `proof` and `proof_deps` describe the API used by the
body, and the compatibility change record documents the interface change and its downstream
users. Verdict: metadata and pruning are consistent.
5. The unit route is preserved: the module still uses the existing tensor product,
sheafification, internal-Hom, and MonoidalFree structures named by the node. The unit's
realized record needs no update because this repair introduces no new route or statement.
Verdict: route preserved.

I changed only the declaration kind and explanatory docstring, and recorded that repair in
`coord/changes/tensorClosed-compatibility-abbreviation.md`; no declarations, nodes, imports, or
downstream modules required further changes.
