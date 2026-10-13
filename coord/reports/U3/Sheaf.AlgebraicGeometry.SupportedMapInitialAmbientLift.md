## What changed

The original declaration `AlgebraicGeometry.Scheme.exists_supported_map_initial_ambient_lift`
now has a complete Lean proof from the existing exact extension-by-zero adjunction,
the existing restriction isomorphism, and one new local-perfectness transport theorem.
Its signature, universes, hypotheses and public imports are unchanged.

The proved private helper `exact_adjunction_lifts_map` descends the degreewise adjunction
through `DerivedCategory.Q` using `Adjunction.localization`. The composite-is-identity
comparison makes the derived left adjoint fully faithful. Its invertible unit supplies
the restriction isomorphism, and the adjunction equation proves the required map identity.
The source object is the actual extension-by-zero functor, composed with the inverse
open-site equivalence, applied to F; it is not an arbitrary existence witness.

The proved private helper `openRestriction_support` transports homology stalk vanishing
through exact restriction, `Modules.overFunctorEquiv` and `Modules.restrictStalkNatIso`.
It does not require closedness of T or any property of the ambient object outside U.

Added proof imports: `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction` and
`Sheaf.AlgebraicGeometry.OpenPerfectModelTransport`. The latter contains just the
remaining local-perfectness transport theorem. The main DAG node now records this route.

Both delivered modules compile together in import order with lcompile.py, with no
warnings, in approximately 21 seconds total. The general lifting helper also compiled
independently. No project build was run. The resumed worker rechecked the inherited proof and node
metadata, restored the original public theorem docstring, and reran the required
no-push delivery check successfully.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.exists_supported_map_initial_ambient_lift`
(node `lem-sc-supported-map-initial-ambient-lift`). There are no sorries left in the
item module. The map construction, restriction equation and stalk-support clause are
proved in Lean, not delegated to new holed statements.

Added one hole:
`AlgebraicGeometry.Scheme.local_perfect_of_openRestriction_iso`
(node `lem-sc-open-perfect-model-transport`, module
`Sheaf.AlgebraicGeometry.OpenPerfectModelTransport`). Its whole proof is `by sorry`.
It only transports a given perfect model across an open restriction isomorphism:
it has no E, alpha, beta, subset T, support assertion, or existence of an ambient lift.
It is strictly the local-perfectness part of the original argument.

This delivery is a decomposition: one hole closed, one simpler hole added, net zero
holes from these edits. It is not a claim that the theorem is proved without sorryAx.
Existing dependencies retain whatever upstream holes they already had.

Edge cases of the new statement were checked mathematically: the empty open has no
points, the total open uses the equivalence with the localized top site, the zero
object has the zero strictly perfect model, and arbitrary R outside U is permitted.
No compactness, quasi-coherence or support hypothesis is needed for local transport.

## No longer needed

Removed direct proof import `Sheaf.Algebra.Homology.ModuleExtensionByZeroStalkMaps` and
removed `lem-sc-module-extension-by-zero-stalk-maps` from this node's proof dependencies.
The proof of support now uses ordinary restriction-stalk comparisons. This does not
claim the stalk-map module leaves the entire targets closure: the retained
`OpenExtensionRestrictionIso` module still imports it internally.

Removed `def-pc-perfect-complex` as a direct proof dependency of this node; it remains
a statement dependency, and `Sheaf.AlgebraicGeometry.PerfectComplex` remains its required
public import. The new local transport node uses this definition.

The exact open adjunction and open-extension restriction-isomorphism nodes remain
needed. No unit statement or unit proof step was bypassed: the unit record
`sk-thm-picard-duality` has no realized binding for this node. No other pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The upstream `Adjunction.mapDerivedCategoryAdjunction` API carries additional monoidal,
flat-resolution and injective-resolution assumptions. These are not hypotheses of this
item. The simpler localization of the adjunction on complexes needs only the exactness
already supplied by `open_restriction_adjunction_exact` and works in the stated universe.

The original plan suggested the extension-by-zero interior stalk theorem for support.
Once the restriction isomorphism is available, exact restriction/homology and the ordinary
restriction-stalk comparison prove that clause directly.

The remaining site-transport glue was not supplied as a theorem by the original proof
dependencies. It is isolated in the new module rather than left inside a partial proof.
Its source and complete mathematical construction are recorded in its docstring and node.
No statement was disputed, weakened or otherwise changed.

The local Stacks .tex paths named by the repository were absent on this machine.
The actual Stacks pages for Tags 08BT, 00A7 and 08CM were read online. The new proof plan
is marked as written by an agent. LeanSearch returned Internal Server Error; this is
recorded as unavailable. The actual Loogle and Mathlib grep searches found the relevant
comparison APIs but no exact local transport theorem. Broad DAG/blueprint and library
searches likewise found no replacement for this clause.

## New nodes

`lem-sc-open-perfect-model-transport` states
`AlgebraicGeometry.Scheme.local_perfect_of_openRestriction_iso` in
`lean/Sheaf/AlgebraicGeometry/OpenPerfectModelTransport.lean`. It isolates step 3's
transport of strictly perfect representatives from the open subscheme to ambient opens,
using Stacks Definitions 08CM and 08C4 and the restriction comparison of Tag 08DW.
Its proof plan specifies the open image, the localized module equivalence, preservation
of finite-free retracts and degree bounds, and the derived restriction square.
Its statement is independent of the extension-by-zero construction and of supported maps.
No change record is needed because all existing interfaces and visibilities are unchanged.

## Second reading by U3

1. Existing interfaces: PASS. Read the repository/sandbox diff of the complete item
   module. The existing theorem signature is byte-for-byte identical, including
   universes and derived-category assumptions; its docstring and public import are
   unchanged. No existing definitions were edited. The existing node changes only
   `proof`, `proof_deps` and `proof_origin`. There are no forced adaptations or
   interface change records.

2. Proof and axioms: PASS as a decomposition. Recompiled both modules locally in
   import order (5.0 s and 15.3 s), with no errors or warnings. A scratch copy with
   `#print axioms` confirmed that both private helpers use only `propext`,
   `Classical.choice` and `Quot.sound`. The main theorem and the new transport
   theorem additionally use `sorryAx`, as reported. The only delivered `sorry`
   is the entire proof of `local_perfect_of_openRestriction_iso`. No forbidden
   declaration or hollow definition occurs. Read the localized adjunction, the
   unit cancellation and the homology/stalk isomorphisms in full. R is explicitly
   the derived functor of inverse open-site equivalence followed by the actual
   extension-by-zero functor applied to F; the adjunction/isomorphism witnesses do
   not select its underlying object.

3. Split-off statement: PASS. The transport statement is true and supplies exactly
   the local-model conjunct, independently of the map and support conjuncts. Its
   docstring constructs the image open, the exact equivalence, the transported
   bounded complex and finite-free retractions, and the representing isomorphism.
   Checked empty U, total U, zero F, and an ambient R with unrestricted behaviour
   outside U. Re-read Stacks [08CM](https://stacks.math.columbia.edu/tag/08CM) and
   [08C4](https://stacks.math.columbia.edu/tag/08C4); [08DW](https://stacks.math.columbia.edu/tag/08DW)
   mentions compatibility with open restriction in its proof, rather than stating
   this exact localized-site transport theorem. Independent Loogle `"IsPerfect"`,
   Lean Finder (bounded finite projective models under open-site identification),
   Mathlib grep `restrictFunctorComp|overMapCompOverEquiv`, and broader repository
   searches found comparison ingredients but no replacement. In particular,
   `PerfectCommonAffineModels` handles restriction between ambient localized sites;
   its helpers are private and it does not give the required change of ambient
   scheme. `PerfectOfOpenPullbacks` requires global derived-category instances,
   concerns derived pullback rather than this exact restriction, and is itself
   open. Neither closes this hole in a few minutes. The new theorem is strictly
   one component of the argument, not the original existential lift renamed.

4. Route and pruning: PASS. The degreewise adjunction and Mathlib localization
   provide a direct route without resolution or monoidal hypotheses. All current
   imports are needed: PerfectComplex for signatures, OpenExtensionRestrictionIso
   for its comparison and the exact adjunction, the upstream adjunction module
   for `mapHomologicalComplex`/localization, and OpenPerfectModelTransport for the
   local-model conjunct. Proof-only imports are plain imports. Compared all four
   original proof dependencies: both removed dependencies are listed under
   No longer needed, and both retained dependencies occur in the proof. The unit
   `sk-thm-picard-duality` has empty realized bindings for statement and step;
   this delivery changes no unit route or binding. No whole-module pruning is
   established, since the removed direct stalk-map import remains transitive.

5. DAG agreement: PASS. Read both delivered node files and the used dependency
   declarations. Both node Lean signatures match their files verbatim. The main
   proof steps name the exact adjunction, restriction isomorphism and new transport
   node; the support step uses the compiled homology/stalk comparison APIs. The
   new node has its source, complete proof plan, statement/proof dependencies,
   agent proof origin, searches, split status, creation record, blueprint ancestry,
   inherited chapter/unit and complete Lean record. No node statement was changed.

Second reading changed only this report, adding the independent checks and clarifying
why nearby local-perfectness APIs do not remove the remaining hole. Lean proofs and
node records required no repair. One original hole closed and one simpler hole added;
net zero, a decomposition rather than a completed axiom-free proof.
