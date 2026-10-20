## What changed

Proved `AlgebraicGeometry.Etale.openExchange_adjunct` with its original signature and
both definitions unchanged. The proof identifies the literal open-composition square
with the inverse mate of open base change, descends this equality to the unbounded
derived categories, and proves the counit identity using proper-exchange naturality
and the adjunction triangles. The inverse adjunction bijection gives the second conjunct.
The proof uses the existing unbounded comparison, tower-adjunct and exchange-normalization
API, plus the proof-only import `Sheaf.AlgebraicGeometry.OpenExchangeTower`.

Proved `AlgebraicGeometry.Etale.openExchange_tower` in that new module. This expands the
second compactification tower, cancels the terminal comparisons, proves and applies the
derived direct-image right-unit formula, transports the two pullback-open presentations
by equality, and combines the derived open-composition factors. Its only new geometric
input is the general source-open composition law in
`Sheaf.AlgebraicGeometry.OpenSourceComposition`. This is a separate normalization result
in the source composition argument; it involves neither a target-open pullback square,
evaluation counit nor the conclusion of the assigned theorem.

The three-module launcher build verified both lower modules without diagnostics. The assigned
module then passed a direct launcher compile in 35.6 seconds, with its sandbox imports.
The tower's unused square binding was renamed and the cumulative heartbeat bound documented.
The parent proof uses local irreducibility annotations to prevent costly unfolding of
sheaf and derived functor constructions. All checked modules compile within the 60-second
file limit; no definition or statement was changed. The source-open theorem is the sole
retained hole. A later clean-set run timed out while elaborating its signature; local
irreducibility annotations for its sheaf, derived and compact-support constructions fixed
that check, and its direct launcher compile passed in 55.4 seconds.

The retained sandbox was checked against current sources and interrupted compile logs
before any repeated mutation; no previous delivery had been pushed. Earlier server retry
failures are superseded by successful compiles. The reference clock reset across resumed
dispatcher attempts: `resumed-dry-run.log` and `scratchpad/dry-node-sync.log` record the
fresh split-gate readings. No budget metadata or launcher file was changed.

## Proved and sorry left

Closed the assigned module's one original hole:
`AlgebraicGeometry.Etale.openExchange_adjunct` (one of one). Also proved the newly introduced
`AlgebraicGeometry.Etale.openExchange_tower`; it has no remaining hole.

Added one hole:
`AlgebraicGeometry.Etale.unboundedEtaleLowerShriekCompIso_open_source`, node
`lem-amb-compact-support-open-source-composition`, in
`Sheaf.AlgebraicGeometry.OpenSourceComposition`. Its proof is exactly `by sorry`.
The docstring and node give the complete identity-proper tower argument and sources.

This delivery is a decomposition: one original hole closed, one lower hole added, net zero.
The assigned module and the tower module have zero holes; the packet has one.
All private helpers are proved. There are no holes in definitions, new axioms, or changed
existing signatures. The remaining result is the source-open normalization of the first
tower: identify its restricted compactification with `(w,id)` by the pullback unit, identify
the refinement comparison with inverse open base change, and cancel the identity-proper
interchange and direct-image units. The entire second tower and the formal mate argument
are proved in Lean and are not postponed in this statement.

Identity and empty opens use the same pullback and adjunction units. The zero ring and
zero objects cause no exception, since all equations are functorial. No data is chosen
from an unproved mere-existence theorem.

## No longer needed

Removed these original proof-only imports from the assigned module:

- `Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChangeUnderivedCompatibility`
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`
- `Sheaf.Paper.UnboundedProperOpenInterchange`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`

All three original public imports support the existing statements or definitions and
remain unchanged. No entire original dependency module is claimed globally pruned: several
are public dependencies of `UnboundedEtaleCompactSupportComparisons` already.

The parent's direct proof dependencies are now
`lem-amb-unbounded-compact-support-comparisons` and the new
`lem-amb-shriek-open-tower-counit`. Its direct uses of
`lem-cbc-extension-zero-composition` and
`lem-weil-pbc-extension-by-zero-adjunction` are replaced by the proved private mate lemmas
and the lower tower formula; these two nodes remain in the lower normalization chain.
`lem-amb-etale-adjoint-locality` is not used as a theorem by either proof: the specified
termwise open adjunction is used directly. The new node does not depend on the general
etale adjoint-locality assertion.

`lem-cbc-derived-extension-zero-base-change-underived-compatibility` is not used: the
parent proves the needed open-square mate identity directly from the open definitions and
Mathlib's iterated mate formulas. `lem-amb-unbounded-proper-open-interchange` is removed
from the parent's direct dependencies because the precise adjunct clause needed is already
`unboundedEtaleCompactSupport_tower_adjunct` in the comparison module. It can remain below
that module. No general etale normalization construction or exceptional right adjoint is
used in the delivered proof. No blueprint unit statement or realized proof step is removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false. The original proof plan says the first tower
has identity bottom open. In the literal tower for `(v,f)`, we use `c` and `(v j,id)`;
the restricted proper projection is instead an isomorphism, removed using the pullback
unit and derived direct-image normalization. This is the separate source-open law.
For `(f_U,u)` the explicit tower uses `(u,id)` and the transported model `(v j,r)`;
its restricted model is the pullback compactification. The proved tower calculation
and the new node record this route. No blueprint unit statement or realized step is bypassed.

The old sandbox report left the second tower and the final open factors unfinished;
both are now proved. The lower proof uses a local cumulative heartbeat bound and
controlled transparency to avoid expensive unfolding of pullback constructions; it compiles
within the file limit. The parent's existing declaration-local recursion bound and explicit
functor-map rewrites likewise change neither definitions nor statements. All builds and
checks use the prescribed launcher tools.

## New nodes

`lem-amb-shriek-open-tower-counit`, module `Sheaf.AlgebraicGeometry.OpenExchangeTower`,
records the compactification composition identity on an arbitrary input before counits
and proper base change. Its historical id is retained. It is now proved from source-open
normalization, the existing second-tower formula, and the proved derived unit and
open-composition calculations. The parent supplies the inverse-mate identification,
counit identity, comparison transport and adjunction argument.

`lem-amb-compact-support-open-source-composition`, module
`Sheaf.AlgebraicGeometry.OpenSourceComposition`, is the source-open specialization of
Stacks Tag 0F7J's composition calculation, with the identity-proper normalization of
Tag 0F7B. For an arbitrary open `w` and compactification `c` of `f`, it identifies the
specified composition comparison with inverse derived open composition followed by the
comparison of `c.precomp w`. It is strictly below the pullback tower and contains no
mate or evaluation-counit assertion. Searches found no existing declaration of this
normalization. Its one retained hole and complete argument are recorded above.

No existing definition or statement changed. The conservative interface check flags local
proof commands; `coord/changes/etale-open-exchange-proof-elaboration.md` records their local
scope and the unchanged downstream consumers. The final preflight repair also adds the
required LeanSearch record for the source-open node.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
