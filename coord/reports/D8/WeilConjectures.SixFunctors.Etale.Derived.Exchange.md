## What changed

Filled the original proof of
`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek`
without changing its signature, attributes, docstring, or any public import. The proof works
for the original arbitrary commutative coefficient ring and arbitrary ideal, on the original
unbounded categories.

Added one proved private helper, `constant_projection_of_preservesCoproducts`. It precomposes
the ordinary direct-image projection transformation with the constant-complex functor.
Both resulting functors are triangulated and preserve coproducts. The projection comparison
is invertible at the coefficient ring by the unit formula; the existing
`DerivedCategory.isIso_app_singleFunctor_obj` extends this to every coefficient module.
In particular it applies to the constant quotient module, without a perfectness assumption.

The main proof obtains coproduct preservation for the proper factor of the chosen
compactification from the existing source instance
`AlgebraicGeometry.Etale.CompactificationUpperShriek.isLeftAdjoint_rightDerivedLowerStar_of_isProper`.
It then combines the helper with the already-proved open projection formula through
`projectionMapOfCompactification_app_app`, and takes `asIso` of the canonical reduction map.
The new proof-only imports are `Derived.ConstantTensorProjection` and
`Derived.CompactificationUpperShriek` under `WeilConjectures.SixFunctors.Etale`.

Validation: the final assigned module compiled cleanly through `lcompile.py` in 42.0 seconds.
A source import-graph traversal confirms the legacy adjoint module already belongs to the
current `TargetsCheck` import closure; the new import of `ConstantTensorProjection` supplies
proved constant-functor and module-generation tools.

Preflight requested a change record for the helper's scoped
`omit [HasCompactification f] in` command. The record
`coord/changes/D8-exchange-private-helper.md` explains its private, single-declaration scope;
no existing section variable or public signature changes.

The original finite-coefficient corollary and all other existing theorem proofs remain as in
the current source. The earlier attempt's extra additive-torsion helper and its finite-case
refactor are unnecessary for this proof and are not included in the packet.

## Proved and sorry left

Original holes closed: **1 of 1**, in
`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek`.
New holes: **0**. Split off: **0**. No `sorry` remains in the assigned module or is added in
another module. The private helper is completely proved.

This is a proof FROM EXISTING LIBRARY STATEMENTS, as required by stage 3, rather than a claim
that every imported mathematical obligation is finished. In particular the unconditional
proper-direct-image left-adjoint instance named above still has its original `sorry` in
`WeilConjectures.SixFunctors.Etale.Derived.CompactificationUpperShriek`. This delivery neither
proves nor edits that stronger assertion. It is an existing source-library declaration,
not a new theorem restating the assigned theorem. Its full arbitrary-coefficient scope
remains a mathematical obligation, and should receive independent attention.

## No longer needed

None of the existing public imports, declarations, nodes, or modules is withdrawn.
No source dependency is pruned on the basis of zero importers. The unit's finite-reduction
compatibilities and its proper/open construction remain in place.

The earlier proposed extra hypotheses (additive torsion, perfect quotient, or finite
cohomological dimension) are unnecessary for the FORMAL REDUCTION from the existing
unconditional adjoint statement. This does not establish that those hypotheses can be
omitted from a geometric proof of that statement.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt overlooked the unconditional source instance in the legacy
`Etale.CompactificationUpperShriek` namespace. It supplies exactly the categorical condition
missing from the attempted constant-generation proof. Although its former project proof
was retired, the current adopted source retains its declaration and its original hole.
The source-library boundary requires preserving that API. This packet uses that CURRENT
statement explicitly, and does not restore or rely on any withdrawn Sheaf module.

The historical record `coord/changes/etale-compactification-upper-shriek-retirement.md`
explains why its finite-amplitude proof was insufficient at arbitrary coefficients, and
expressly does NOT claim a counterexample. The node
`lem-etale-proper-derived-lower-star-coproducts-for-grothendieck` was subsequently narrowed
and reattached to a finite-coefficient theorem in
`Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts`; that finite statement is not
silently used as an unrestricted one here. The pro-etale counterexample discussed in
`thm-sfb-finite-proper-pushforward-left-adjoint` is about a different coefficient/site API;
this proof makes no claim that it establishes or refutes the small-etale source instance.

No current node in `dag/nodes` mentions the assigned module or the assigned theorem. Its
older unit record `sk-prop-sf-pf-reduction` names the declaration and has empty realized
arrays. Its finite-coefficient proof is already available, but does not itself prove the
original arbitrary-ring signature. No existing node proof is changed or misrepresented.
The existing `STATEMENT-DISPUTED` comment is retained to expose this mathematical scope
issue; proving the formal implication from a stronger admitted assertion does not resolve it.

Searches in this resumed attempt: LeanFinder for arbitrary-coefficient proper direct image
and constant quotient tensor; Mathlib grep for projection/constant and derived coproduct
statements; Loogle for derived coproduct preservation (the query was rejected by its parser,
so it is not counted as evidence of absence); direct source searches for proper projection,
coproduct preservation and exceptional adjoints. The final source search found the legacy
instance. `tools/import_direction.py may` permits the proof import of
`Derived.CompactificationUpperShriek`. The downstream checker reports 394 importing modules,
and no executable occurrence of the assigned declaration outside its own module.

Edge cases: the helper applies to every module, including zero modules and the unit; thus
zero and unit ideals and the zero ring cause no special-case failure. It does not infer
perfectness or finiteness for an arbitrary quotient. Properness is used for the actual
proper factor of the given compactification, rather than for the original morphism.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
