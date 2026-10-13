## What changed

Replaced the `sorry` in `AlgebraicGeometry.formal_flat_quotient_mate_data` by the
explicit quotient-system construction. The supplied adjunction on f is used in
the conjugate of the pushforward square. Its ordinary base-change map is the
existing `Scheme.Modules.moduleBaseChangeMap`. The completion pullback comparison
and equality transports define the completion comparison; the proved generic
diagram assembly constructs β₀ and t; inverse ordinary exchange
at F defines b. A private proved categorical helper establishes the projection equation; a
proved generic diagram assembly establishes the unit equation. The existing theorem statement and all public imports are unchanged.

One new module states the remaining ordinary-module exchange properties for
explicitly fixed maps, without any ideals, completion systems, G, β, or F₀. Its
source and complete proof in words are in its docstring and matching DAG node.
The new normalized completion-pullback module imports `FormalSystemsPullback`
with `import all` to use its already-proved private comparison and projection identity. The proof also
uses the existing source-library Noetherian finite-type theorem.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.formal_flat_quotient_mate_data`
(node `lem-weil-pbc-formal-flat-quotient-mate-data`), proving its conclusion from
ordinary exchange properties and the existing completion-pullback construction.
No `sorry` remains in the assigned module or its private helpers.

Added one hole, `AlgebraicGeometry.ordinary_flat_exchange_prescribed_adjunction`
(node `lem-weil-pbc-ordinary-flat-exchange-prescribed-adjunction`). It asserts
invertibility on quasi-coherent modules and the unit identity for the explicitly
constructed ordinary exchange and composition comparison. This is a decomposition:
one upper hole closed, one strictly smaller lower hole added, net zero holes.
No data is chosen from this unproved statement: the base-change transformation,
composition isomorphism and adjunction are fixed formulas in both statements.

## No longer needed

Removed direct proof imports `Sheaf.AlgebraicGeometry.FlatBaseChangeMapSections`
and `Sheaf.AlgebraicGeometry.FlatBaseChangeResolutionIso` from the assigned module.
They remain proof dependencies and imports of the new ordinary-exchange module,
so no claim is made that their modules or nodes leave the targets' import closure.
Removed the assigned module’s direct `FormalSystemsPullback` import; the proved
normalized-completion helper imports it and uses its existing construction. The original direct proof-dependency nodes no longer used directly are
`lem-weil-pbc-flat-base-change-map-sections`,
`lem-weil-pbc-flat-base-change-resolution-iso`, and
`lem-weil-pbc-formal-systems-pullback`. All three remain used through the new
helpers. `def-pc-module-pullback` remains a direct dependency. No original
proof-dependency node or module is globally pruned by this decomposition.

## Where the brief, the DAG or earlier work was wrong

The existing DAG plan is mathematically sound. Its resolution comparison declarations
do not directly state the ordinary natural transformation's invertibility and its
unit compatibility for an arbitrary supplied f-adjunction. The new node isolates
exactly that bridge. The ordinary map itself and its naturality already exist in
`ModuleBaseChangeMapOpenRestriction` and are reused. The original main statement
needs Noetherian X only internally, obtained from proper f and Noetherian Y.

Searches: LeanFinder found generic adjunctions and conjugation tools; Loogle found
unit naturality; Mathlib grep found no proper-flat ordinary exchange theorem.
Local library search found the ordinary map and its naturality, affine exchange
cases, and the resolution comparison. LeanSearch returned Internal Server Error.
Blueprint search for flat base change found nine nodes but no exact ordinary
prescribed-adjunction compatibility statement. The unit's realized steps are kept.
The zero/unit ideals, zero modules and empty schemes need no cancellation beyond
isomorphisms and functoriality; there is no faithful-completion assumption.

## New nodes

`lem-weil-pbc-ordinary-flat-exchange-prescribed-adjunction`, in
`dag/nodes/sec-proper-base-change/`, records the ordinary exchange bridge with
source Stacks 02KH part (1), 02N7 and adjunction conjugation (0B65). Its Lean module
is `Sheaf.AlgebraicGeometry.OrdinaryFlatExchangePrescribedAdjunction`.
It is strictly below the assigned theorem: it has no formal systems, quotient
projections, or algebraization isomorphism, and the assigned theorem constructs
these and proves both equations. The original node's proof fields follow this
construction. No definition/interface change or change record is needed.

`lem-weil-pbc-formal-system-exchange-mate-compatibility` records the generic diagram
transport identity, in `Sheaf.AlgebraicGeometry.FormalSystemExchangeMateCompatibility`.
Its theorem is proved by naturality and the private categorical `exchange_unit` helper.
It adds no hole and separates the categorical identity from concrete scheme conversions.

`lem-weil-pbc-formal-completion-pullback-normalized` records the projection-normalized
completion pullback, in `Sheaf.AlgebraicGeometry.FormalCompletionPullbackNormalized`.
It is proved directly from the existing completion isomorphism and quotient
projection identity, so it adds no hole. Its normalization determines the comparison
on every quotient; it is not arbitrary existence data.

Validation: the delivery dry run passed compilation, axiom checks and preflight
except for the second reading, which the independent reader supplies. Nothing
was pushed. All four sandbox modules compile. The assigned theorem compiles in
15.7 seconds with no warnings. The new ordinary-exchange theorem is the only
new `sorry`; both other new theorems and all private helpers are proved.

## Second reading by D2

1. Compared the assigned module with the repository using `diff`; separately
   compared the full existing theorem signature up to `:=` byte for byte.
   Verdict: identical hypotheses, conclusion, visibility and public imports;
   no existing definition changed. The other three modules are new, with
   declarations matching their node records; no interface change record is needed.

2. Independently compiled all four modules in import order with `lcompile.py`.
   Exactly one `sorry` occurs, as the entire proof of
   `AlgebraicGeometry.ordinary_flat_exchange_prescribed_adjunction`; none occurs
   in a definition or private helper. Inspected the concrete definitions of B,
   c, b, beta-zero and t: none selects arbitrary data from the unproved exchange
   theorem. The completion comparison comes from the existing explicit cokernel
   construction. Scratch-copy `#print axioms` checks and the delivery's probe
   check the standard axioms and remaining `sorryAx`; no forbidden construct is
   present. Verdict: a valid decomposition, with the ordinary exchange still open.

3. Read the new ordinary-exchange statement and its proof against
   [Stacks 02KH](https://stacks.math.columbia.edu/tag/02KH), part (1), and
   [02N7](https://stacks.math.columbia.edu/tag/02N7), augmentation and adjunction.
   Properness supplies quasi-compactness and quasi-separatedness; flatness of q
   is inherited from g. No Noetherian or finite-type hypothesis on M is needed.
   Read `moduleBaseChangeMap` and Mathlib `unit_conjugateEquiv_symm`: B uses the
   same chosen g,q adjunctions as c, while the supplied f-adjunction occurs in c.
   Taking g-adjoints and expanding composite units therefore gives precisely
   the claimed identity, even for an arbitrary supplied f-adjunction.
   Tested identity squares with a rescaled adjunction unit: c changes by the
   same rescaling, so the equation persists. Zero modules and empty schemes
   give the unique maps; zero/unit ideals in the main statement use the same
   cokernel projection equations. The lower statement omits G, beta, ideals,
   completion, quotient projections and the assembled witnesses; it is strictly
   smaller, not a renaming of the assigned theorem. Independent LeanFinder search
   for qcqs flat exchange found generic pullback adjunctions and flat affine
   section maps only. Loogle with an Adjunction-prefixed conjugation name found
   no identifier; Mathlib grep located the correctly namespaced
   `CategoryTheory.unit_conjugateEquiv_symm` at Mates.lean:311. Local and upstream
   searches found no ordinary-exchange isomorphism theorem completing the bridge.
   Verdict: true, sourced and needed; no quickly applicable theorem closes it.

4. Read the construction from the conclusion downward. The projection helper
   uses B naturality at the quotient map, cancels inverse B at F, then applies
   the normalized completion equation. The system helper uses B naturality at
   beta, the supplied mate equation, and p-unit naturality at the equality
   transport. The normalized helper reuses `completionPullbackIso` and
   `powerQuotientIso_pi` (Lean identifier `powerQuotientIso_π`) via `import all`;
   it does not repeat their constructions. Proof-only new imports are plain
   imports. Checked `dag/units/sk-thm-p1.json`: no realized statement or step is
   removed or bypassed, and every original dependency remains transitively used.
   The No-longer-needed section now explicitly names every removed direct node.
   Verdict: the reduction keeps the unit route; no global pruning is claimed.

5. Read all four node JSON files against the Lean modules. Each new node has
   source, full statement, proof steps, dependency union, origin, search records,
   creation, blueprint provenance and Lean record. The main node's three steps
   follow ordinary exchange, normalized completion, system assembly and the
   private projection calculation. Its original statement is unchanged.
   The generic system and normalized completion nodes are proved and add no
   holes. Verdict: DAG and Lean agree.

Changes made by this reading: expanded the ordinary-exchange docstring's unit
argument into the explicit composite-unit/Hom-equivalence calculation already
recorded in its node, and made the removed-direct-node list explicit in this
report. No proof or signature needed repair. One original hole closed, one new
ordinary-exchange hole added: decomposition, net zero holes; no module pruned.
