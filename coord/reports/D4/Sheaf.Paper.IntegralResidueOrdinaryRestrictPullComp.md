## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_ordinaryRestrictPull_comp`
by the submitted specialization/cancellation proof, preserving its signature and docstring.
Its sole added import, `Sheaf.Paper.ComapUpperStarIsoComposition`, is proof-only.

The second reader proved the previously admitted general theorem
`AlgebraicGeometry.ProEtale.CondensedRing.comapUpperStarIso_comp`. The proof transposes the
composition square with Mathlib's horizontal mate and conjugate-whiskering laws, checks the
pushforward square on underlying sheaves, and transposes back. Added and fully proved
`AlgebraicGeometry.ProEtale.CondensedRing.comapUpperStarIso_mate` in its own module. Its
proof expands the one-map adjunction unit and the scalar-isomorphism comparison; it uses no
flatness or chosen data. The general modules publicly import only ChangeOfCoefficients,
which supplies their signatures. The mate import in the composition module is proof-only.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_ordinaryRestrictPull_comp`
(node `new-integral-residue-ordinary-restrict-pull-comp`): 1 of 1.

Also closed the first worker's proposed split-off hole in
`AlgebraicGeometry.ProEtale.CondensedRing.comapUpperStarIso_comp`
(node `new-comap-upper-star-iso-composition`). The new single-map theorem
`AlgebraicGeometry.ProEtale.CondensedRing.comapUpperStarIso_mate`
(node `new-comap-upper-star-iso-mate`) is fully proved. Added holes: none. Sorries left in
any delivered module: none. This is a proof, not a decomposition; the submitted set closes
one baseline hole and adds zero. Fresh `#print axioms` checks for all three public theorems
show exactly `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

The old node's sole proof dependency,
`def-weil-pbc-residue-exchange-comparison-interface`, is replaced as a direct proof dependency
by `new-comap-upper-star-iso-composition`. The interface remains a statement dependency and
its original public import remains: it supplies the integral coefficient constructions.
The general theorem no longer imports that integral-specific interface; it publicly imports
the ordinary coefficient-change module required by its signature.

No baseline import or whole library module is pruned. The first worker mentioned an
exploratory ExtendScalarsComp import; it was in neither the baseline nor the submitted item,
so it is not counted as a pruning. No unit-realizing node is bypassed.

## Where the brief, the DAG or earlier work was wrong

The first worker moved the entire coherence obligation to a stronger theorem and called it
a split. That was not a strictly simpler reduction. The second reading repaired it by
proving that theorem, including the genuinely lower one-map normalization. The item node's
old statement that the specialized equation was definitionally the target omitted the two
isomorphism cancellations; its proof record now describes those actual steps.

The shared checkout initially omitted the assigned module during refresh. After refresh,
the module and node were available and were compared directly with the delivery. No git
command was used in the shared repository and no change record is needed: no existing
signature, definition, visibility, or public import changed.

## New nodes

`new-comap-upper-star-iso-composition` records the fully proved general coherence theorem,
its single-map dependency, the pushforward argument and Mathlib mate laws. The formerly
speculative searches were replaced with actual searches recorded by msearch.py.

`new-comap-upper-star-iso-mate` records the fully proved one-map normalization, with explicit
source constructions, natural-language proof, all required creation/blueprint/unit/Lean
fields, and actual LeanSearch, Loogle, LeanFinder and grep searches. No change records or forced
adaptations are included.

## Second reading by D4

1. Interfaces: PASS. Compared the complete assigned-module diff with the refreshed shared
   repository. The existing declaration signature, context, docstring and public import
   are byte-for-byte unchanged. Only the proof and a plain proof import differ. Both
   support modules are new, so they change no existing interface. No target or definition
   changes, no adaptations of another group's module, and no unproved data choices occur.
2. Proofs: PASS after repair. All three modules compile together without errors or warnings
   (20.5, 8.1 and 6.1 seconds in the final exporting compile). Inspected every proof and
   searched all delivered Lean sources for sorry and forbidden mechanisms: none occur.
   Scratch copies with #print axioms show only the three permitted standard axioms for
   each public theorem, with no sorryAx. The delivery tool also audits all declarations.
3. Split statements: PASS after repair. The only submitted admitted statement had retained
   the whole problem; it is now proved. The single-map mate theorem is also proved. Checked
   orientations, scalar-isomorphism units, coefficient naturality and the homEquiv
   transposition, including identity coefficient maps, identity scheme maps, zero modules
   and empty schemes. Fresh LeanSearch, Loogle, LeanFinder and grep searches found ordinary ModuleCat analogues and the Mathlib
   mate/adjoint-uniqueness primitives actually used, rather than a matching internal-module
   coherence theorem. The sheaf-only extension comparison has different functors.
4. Route/pruning: PASS. Read downward from the assigned cancellation proof through the
   general square and the one-map calculation. It uses the canonical upperStarComp and
   comapUpperStarIso throughout. Public imports supply signature constructions; all added
   imports used only for proofs are plain. The old proof dependency is accounted for above.
   Read dag/units/sk-thm-properbasechange.json and its realized fields: the statement and
   all three unit steps stay unchanged. These support calculations are below unit level.
5. DAG: PASS after repair. Matched all three verbatim lean.statement fields to declarations.
   The item records specialization and cancellation, the composition node records the mate
   and underlying pushforward argument, and the mate node records the actual one-map unit
   computation. Each proof_deps list is the union of step uses. The two new nodes include
   their source, proof_origin, searches, chapter/unit, creation and blueprint ancestry.

Second reading changed the admitted general proof into a full proof, added the fully proved
one-map mate module/node, minimized the support imports, corrected the DAG proof/search
records, and replaced the inaccurate progress report. The assigned proof was retained.
