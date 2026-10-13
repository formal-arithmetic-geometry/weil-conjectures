## What changed

Proved `AlgebraicGeometry.Scheme.finite_normal_iso_of_dense_open_etale_comparison`
without changing its signature or visibility. Added proof-only imports of
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen` and
`Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDenseOpenIso`.

The private, locally complete `normal_stalks_of_etale` helper transports base-stalk
normality to affine prime localizations, applies `RingHom.Etale.isNormalRing`,
and transports the resulting normality back to the stalks of the etale source.
The inverse image of U in E is dense because U is nonempty in the integral base
and p is open. The existing general comparison then supplies the isomorphism.
Updated the item's DAG proof, proof dependencies and proof origin to this route.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.finite_normal_iso_of_dense_open_etale_comparison`
(node `lem-sbc-finite-normal-dense-open-comparison`).
There are no sorries left in the delivered module, and no holes were added or
split off. The private helper `normal_stalks_of_etale` has no local holes. Its axiom audit
still contains inherited `sorryAx` through `RingHom.Etale.isNormalRing` and its
existing dependencies; this is a reduction over the current stated library,
not an axiom-free proof of the entire dependency closure.

The proof uses the existing stated theorem
`AlgebraicGeometry.Scheme.finite_normal_iso_of_dense_open`
(node `lem-sbc-finite-normal-dense-open-iso`), whose module still contains its
original sorry. This is an existing dependency, not a new hole or a proof of that
dependency. All supplied normality and density hypotheses are proved in this item.

Validation: launcher single-file compilation succeeds without warnings. Empty
and disconnected sources are supported by the existing general comparison;
normality is proved point by point and density uses an open map, with no
surjectivity or nonemptiness assumption on either cover.

## No longer needed

Removed no original imports. The original public imports retain their visibility;
FunctionField exports the integral-scheme conventions used by the signature and
stalk-domain instance. The new proof imports are required (the comparison
theorem and openness), as is the existing EtaleNormalRing import.

Pruned the direct proof dependency `lem-weil-pbc-relative-normalization`
(`Mathlib.AlgebraicGeometry.Normalization`). The delivered module neither imports
nor uses that module directly. Its affine-normalization characterization and
explicit gluing are handled by the existing general comparison
`Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDenseOpenIso` instead.
This reports removal from this item's direct route, not global unreachability.
No unit statement or unit proof step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan did not name the already stated general comparison
`finite_normal_iso_of_dense_open`; it is sufficient after proving normality and
density for E. No interface was wrong. The assumption `hnU` is redundant for
this shorter route; it remains exactly as written in the original signature.
No new modules, new nodes, statement changes or forced adaptations are delivered.


## Second reading by E2

1. Compared the complete module and node with their repository versions. The
   existing theorem signature is byte-for-byte unchanged, including `hnU`, and
   no definition or existing declaration visibility changed. Restored its
   original docstring. There are no change records or forced adaptations.
2. Independently compiled the module and an axiom scratch copy. No local sorry,
   axiom, unsafe, opaque, implemented_by, extern, or data definition is present.
   Both declarations use only propext, Classical.choice, Quot.sound and inherited
   sorryAx. The normality helper inherits sorryAx from the existing
   RingHom.Etale.isNormalRing dependencies; the main theorem additionally uses
   the existing open finite_normal_iso_of_dense_open. No new hole was introduced.
3. No statements were split off. Read the existing general comparison and its
   componentwise integral-closure proof; density in both sources rules out
   additional components. Empty sources cause no exception, and disconnected
   normal sources are allowed. Reviewed the private normality helper: the
   localization equivalences transport normal-domain stalks in the correct
   direction. A fresh LeanFinder search for normal local rings of an etale
   source, and rg searches in Mathlib, Sheaf and WeilConjectures, found no shorter
   exact theorem. The upstream normal etale-cover theorem needs a separably
   closed function field and cannot replace this argument.
4. The proof genuinely supplies the two extra hypotheses of the more general
   existing comparison: affine-chart etale ascent proves normality, and openness
   pulls back density of the nonempty open in the integral base. Verified that
   the removed direct dependency is exactly the old proof_deps entry not used
   now: lem-weil-pbc-relative-normalization. The item and general comparison
   belong to sk-prop-input-spreading; its realized entries and statement/steps
   remain unchanged. EtaleNormalRing belongs to sk-thm-p1 and was already an
   original dependency; this delivery introduces no new unit detour. No unit
   step is bypassed. Removing UniversallyOpen in a scratch copy fails at
   p.isOpenMap. Removing FunctionField compiles locally, but changes the
   pre-existing public import interface: preflight requires a separate change
   record for that removal. Retained that original signature-supporting import
   to preserve the existing interface; no public import change is delivered.
5. The node's proof steps follow the actual helper, density argument and final
   application, with proof_deps exactly their uses union. Only proof, proof_deps
   and proof_origin differ; the statement and lean record are unchanged. No
   new nodes need auditing.

Second-reading changes: restored the original public theorem docstring and
clarified the report's inherited axioms. Retained the explicit use of hnU to
avoid an unused-variable warning without changing the theorem's signature.
