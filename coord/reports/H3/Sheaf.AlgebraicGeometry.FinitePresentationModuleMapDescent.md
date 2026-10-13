## What changed

Repair of return H9 (reviewer X-9c257): added the non-public proof import
`Sheaf.Algebra.FinitePresentationColimit` immediately after the public
`Modules.PullbackUnit` import in both local-data modules. This restores
the recorded affine proof dependency in their Lean import routes.
The existing node records already retain that dependency and require no change.

Replaced the sorry in `AlgebraicGeometry.finitePresentation_module_map_descent`
by a Lean proof from two finite-stage local-data statements and existing library
gluing theorems. The binders, universes, names, and mathematical statement are unchanged. The
expanded canonical comparison in the intermediate theorem's signature is replaced
by its definitionally identical typed name; the new name is publicly imported.
The change record explains this abbreviation refactor and its callers.
Added proof imports of `FinitePresentationLocalDescentDatum`,
`FinitePresentationLocalMapDatum`, `WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent`,
and `WeilConjectures.AlgebraicGeometry.Modules.ZariskiDescent`.

The object proof glues a descent datum using the proved quasi-coherent effectivity
 theorem, descends finite presentation, pulls the gluing comparison to the limit
cover, recovers the global isomorphism by full faithfulness of cover restriction,
and identifies tensor pullback with usual pullback by uniqueness of left adjoints.
The map proof glues a morphism of restriction descent data, then detects the
specified equality on the pulled-back cover. Private helpers carry these
proved category-theoretic arguments; no private helper has a hole.

The two new modules expose only local compatible data on finite affine covers.
They assert neither a global stage module nor a global stage map. Their eventual
proofs follow the parent's finite affine and overlap construction. The statement
of the local map lemma names the comparison and pins it to the exact canonical
conjugate required by the original theorem, avoiding repeated expensive unfolding.

Validation: all four modules compile with saved module outputs (about 2–14 seconds
per file). The dry run printed OK, with only the second reading intentionally left
for the next worker; nothing was pushed. A scratch Lean example with the exact
original expanded statement was proved by applying the delivered theorem, checking
definitional equality of the signature refactor. The dry run ran the axiom probes.

## Proved and sorry left

Closed: `AlgebraicGeometry.finitePresentation_module_map_descent`
(lem-pc-fp-module-map-descent), 1 original hole.

Added holes:
- `AlgebraicGeometry.exists_finitePresentation_local_descent_datum`
  (lem-pc-fp-local-descent-datum).
- `AlgebraicGeometry.exists_finitePresentation_local_map_datum`
  (lem-pc-fp-local-map-datum).

This is a decomposition (one upper hole closed, two strictly local holes added),
not a sorry-free proof of the mathematical descent theorem. No hole remains in
the item's module. No object data are defined using an arbitrary existence witness:
the proof destructs existential witnesses only inside the final proposition.

## No longer needed

Removed the direct proof import `Sheaf.Algebra.FinitePresentationColimit` from
the item. Its node `lem-pc-fp-module-map-descent-affine` is removed from the parent
`proof_deps` and retained in both local-data nodes: the mathematical affine route
is still required. The affine module leaves this item's direct import route and remains in its
transitive import route through both local-data modules. No whole-library module or node is claimed
pruned; the maintainer's ledger determines the global closure effect. All original public imports are retained; the typed comparison adds one public import.
The new object module does not need `TensorPullbackAdjunction`; both new modules
use the minimal `Modules.PullbackUnit` for their descent-data signatures, rather
than importing `Modules.DescentEffective` publicly.

## Where the brief, the DAG or earlier work was wrong

The original sole proof dependency is ring-level (PartialOrder, explicit ring
colimit, linear maps). It does not provide the affine-scheme comparison or the
finite-cover overlap construction needed to apply it directly to this statement.
The new nodes isolate that gap without duplicating the global conclusion.
The affine node remains a dependency of these local steps. The unit record has
empty realized statement and steps; the parent's affine-then-Zariski route is kept.

Used `lem-pc-fpqc-descent` as a generic tool in its Zariski special case: effectivity,
finite-presentation locality, and full faithfulness. Concrete proved interfaces
are in `Modules.DescentEffective`, `Modules.FiniteDescent`, and `Modules.ZariskiDescent`.
No unit step is replaced by a different mathematical route.

Read the current Stacks Tag 01ZR first proof and Tag 05N7; the local checkout's
`literature/stacks-project` text is absent, so their official web pages supplied
the source. The local-data docstrings expand the finite overlap construction of
the original node rather than claim that the source spells out those details.

Edge cases: the fixed i witnesses nonempty I; equivalence classes handle a preorder
when applying the affine PartialOrder lemma. Empty Xi permits the empty cover,
unique descent datum and maps. Covers may contain empty affines. No separatedness
is assumed; overlaps are only quasi-compact and must be covered by finite affines.
Inverse and cocycle equations, including refinement compatibility, are retained.

Searches: LeanFinder query for finite-presentation quasi-coherent inverse-limit
descent returned finite-presentation definitions and local data, no inverse-limit
result. Loogle `SheafOfModules.IsFinitePresentation` returned definitions and
instances, not descent. Grep descent/finitePresentation found no short match.
For the local-data nodes, LeanSearch was unavailable (HTTP 500), Loogle reported
unknown identifier `AlgebraicGeometry.modulesPseudofunctor`, and logged grep
`local.*descent.*datum|descent.*datum.*finitePresentation` had zero hits. Direct
inspection of source descent files found the gluing interfaces used here.
Blueprint searches for finite presentation module, module-map, 01ZR, local modules,
and Zariski found no existing blueprint node stating either new local-data result.

## New nodes

`lem-pc-fp-local-descent-datum`: one finite-stage finite affine cover with finitely
presented quasi-coherent components, overlap descent datum, and an isomorphism to
the restriction datum of the limit module. Global gluing is proved in the item.
Module: `Sheaf.AlgebraicGeometry.FinitePresentationLocalDescentDatum`.

`lem-pc-fp-local-map-datum`: compatible local maps between fixed stage models at
one later stage, satisfying the prescribed comparison equality locally on the
limit cover. Global map construction and equality detection are proved in the item.
Module: `Sheaf.AlgebraicGeometry.FinitePresentationLocalMapDatum`.

`def-pc-tensor-pullback-composition-iso`: a typed name for the exact conjugation
already specified in the original statement. Its data are constructed by
`conjugateIsoEquiv`; there is no sorry in this definition. Naming the comparison
reduced local-map statement compilation from over 60 seconds to about 7 seconds.
Module: `Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso`.
Its construction uses Mathlib `conjugateIsoEquiv`, found by Loogle; logged
LeanSearch was unavailable and grep of both candidate names returned zero hits.
Blueprint searches for pullback composition and tensor pullback returned no exact
existing definition. The unrelated finite-pullback blueprint statement concerns
structure maps and does not name this module-functor comparison.

Change record: `coord/changes/finitePresentation-module-map-canonical-comparison.md`.
No mathematical statement changes; the original signature spells out the same
conjugate now named by the new definition. `Challenge.lean` is untouched.

## Earlier second reading (a previous round; superseded)

1. **Visible declarations: PASS.** Diffed the delivered item against the repository.
   The sole existing public declaration retains all binders, hypotheses and
   conclusions. Its only signature edit is the declared canonical-comparison naming
   refactor in `finitePresentation-module-map-canonical-comparison.md`. Read the
   new definition against the old conjugate expression, including the adjunction
   order and composition equality. Recompiled the scratch `SignatureCheck.lean`
   against freshly copied sandbox outputs: the exact original expanded statement
   follows by `exact finitePresentation_module_map_descent R c hc i f`.
   No existing definition or target changed; no forced adaptation is present.
2. **Proof and axioms: PASS as a decomposition.** Independently compiled all four
   delivered modules in import order without errors or warnings. Searched their
   entire text for forbidden declarations and holes: exactly the two reported
   named theorem holes, no definition hole or forbidden token. Explicit scratch
   `#print axioms` checks show only `propext`, `Classical.choice`, `Quot.sound`
   for the comparison definition, and those plus `sorryAx` for the item and the
   two open local theorems. The item actually constructs the glued object/map,
   applies finite-presentation locality, transports the comparison, and detects
   the equality by faithful restriction. Existential witnesses are eliminated
   inside proofs of propositions; no arbitrary witness supplies definition data.
3. **Local statements: PASS.** Read both full signatures and natural-language
   proofs against Stacks [01ZR](https://stacks.math.columbia.edu/tag/01ZR) and
   [05N7](https://stacks.math.columbia.edu/tag/05N7). The object lemma stops at
   compatible local modules; the map lemma stops at compatible local morphisms.
   Effectivity and full faithfulness are proved in the item, so these are proper
   intermediate steps rather than a renaming of the whole conjunctive item.
   The map lemma's universal condition is not vacuous: restriction on an open
   cover is full, and the item explicitly constructs its preimage. Checked the
   singleton/constant system, zero modules and zero map, empty scheme/empty cover,
   empty affine members, and non-antisymmetric preorders. Quasi-separatedness
   supplies finite covers of pairwise/triple/refinement overlaps; no separatedness
   or flat transition map is required. The affine construction includes inverse,
   cocycle and refinement equations at a common later stage. Both holes have
   complete docstrings and matching nodes. Independent LeanFinder search for
   inverse-limit descent on compatible affine covers returned only local
   finite-presentation definitions; Loogle `CategoryTheory.Pseudofunctor.DescentData`
   found the existing descent-data framework, not finite-stage lifting. Independent
   grep for descent/morphisms and local source inspection found no replacement
   for either local lifting statement. Neither can be closed in a few minutes
   from the existing affine ring interface: affine equivalences, colimit/base-change
   comparisons and the finite overlap construction are still required.
4. **Route and pruning: PASS.** Read the affine dependency and the existing
   `Modules.FiniteDescent`, `Modules.DescentEffective`, and `Modules.ZariskiDescent`
   interfaces. The reduction uses their already proved gluing/locality/fullness
   results directly; no shorter proved inverse-limit theorem was found. New
   public imports supply types or the named comparison appearing in signatures;
   local lifting and gluing proof imports in the item are private. All old direct
   proof dependencies removed from the item are accounted for: its sole affine
   node remains below the local lemmas. The unit `sk-thm-picard-semicon` has empty
   realized statement/step lists, and its ancestor's affine-then-Zariski route is
   retained. No whole-library module pruning is claimed.
5. **DAG agreement: PASS after a metadata repair.** Compared parent records:
   only `lean`, `proof`, `proof_deps`, `proof_origin` change. The parent proof
   uses the two local nodes, fpqc descent in its Zariski special case, and the
   tensor adjunction; the dependency list is exactly their union. New local
   nodes retain the affine step and all required creation/source/search/blueprint
   fields. The new definition is a real conjugate construction. Corrected its
   `lean.statement` to the exact multiline `def` signature from the delivered source. The preflight
   signature parser starts at `def` and excludes the `noncomputable` modifier;
   the first dry run exposed that metadata convention, and it is now followed.

Second reading changed no Lean proof or signature. It corrected the new definition's
signature metadata and clarified the distinction between removing the parent's
proof dependency/import and pruning a whole-library module. Accounting remains
one original hole closed, two local holes added, net minus one: a decomposition,
not a sorry-free proof.

## Second reading by H3

1. **Visible declarations: PASS.** Independently diffed the delivered item against
   the read-only repository. All original binders, hypotheses, universes, visibility
   and conclusions are preserved, except the explicitly recorded spelling change
   naming the canonical conjugate. The new definition expands to exactly the old
   expression, in the same adjunction order. Regenerated `scratchpad/lean/Sheaf/
   AlgebraicGeometry/SignatureCheck.lean` directly from the repository's original
   signature, refreshed its compiled sandbox dependencies, and compiled the example
   by applying the delivered theorem. Thus the original statement still holds by
   definitional equality. No other existing module, definition or target changes.
2. **Proof and axioms: PASS as a decomposition.** Compiled all four delivered modules
   in import order using lcompile.py (8.7, 2.3, 7.8 and 13.1 seconds), without errors
   or warnings. The full-text scan finds only the two reported named theorem holes,
   no forbidden declaration or definition hole. A fresh scratch `#print axioms`
   check reports propext, Classical.choice and Quot.sound for the new definition;
   the original theorem and the two local theorems additionally depend on sorryAx.
   Read the object proof's effectivity, finite-presentation locality, pullback of
   descent data, full-faithfulness and left-adjoint comparison, and the map proof's
   preimage construction and equality detection. These are actual proved reductions.
   Existential module/map witnesses occur only inside proposition proofs; no data
   definition selects an arbitrary witness from an unproved existence statement.
3. **Split statements: PASS.** Independently read both signatures, docstring proofs
   and nodes against Stacks [01ZR](https://stacks.math.columbia.edu/tag/01ZR) and
   [05N7](https://stacks.math.columbia.edu/tag/05N7). Their finite affine lifting and
   overlap compatibility steps are proper parts of the argument; global object/map
   gluing is proved in the item. In particular the map lemma's universal recovery
   condition is not vacuous, since restriction to the open cover is full. Checked
   constant/singleton systems, zero modules and maps, empty schemes and empty affine
   members, directed preorders without antisymmetry, and non-separated qcqs schemes.
   Finite overlap/refinement/triple covers suffice; inverse and cocycle equations
   are included. The fixed index supplies nonemptiness. New independent LeanFinder
   search for finitely presented quasi-coherent sheaves descending along inverse
   limits found only finite-presentation definitions/local presentations; Loogle for
   `CategoryTheory.Pseudofunctor.DescentData` found the general framework, not finite
   stage lifting; grep for inverse-limit modules, directed-colimit modules and
   compatible local maps found no replacement. Source inspection of the affine
   ring theorem confirms that affine equivalences, tensor/colimit comparisons and
   finite overlap lifting still need formalization; neither hole closes in a few
   minutes from that interface.
4. **Route, imports and pruning: PASS.** Read the original affine dependency and the
   proved gluing/locality/full-faithfulness interfaces. The affine-then-Zariski route
   is retained. Both new local-data modules now privately import
   `Sheaf.Algebra.FinitePresentationColimit`, matching their recorded proof route
   and repairing the reported H9 return. Public imports provide signature or
   definition dependencies; added proof-only imports are private. The parent's old
   sole proof dependency is completely accounted for under `## No longer needed`:
   it remains transitive through both local lemmas, so no whole module is pruned.
   The unit `sk-thm-picard-semicon` has no realized statement/step nodes to bypass.
   No shorter existing inverse-limit module theorem was found.
5. **DAG agreement: PASS.** Compared the existing parent node with the repository:
   only lean, proof, proof_deps and proof_origin changed. Checked each new node's
   required creation, source, searches, blueprint, chapter/unit and Lean fields;
   all references exist. Every proof_deps list equals the union of its proof steps'
   uses. The parent records the two local lemmas, Zariski descent via the fpqc node,
   and the tensor adjunction, matching the actual reduction. The new comparison's
   signature metadata already matches its source. No statement correction or
   forced adaptation is hidden in the delivery.

This second reading changed only the report and refreshed scratch validation.
No Lean proof, signature, import or node needed further repair. Accounting remains
one original hole closed and two local holes added (net minus one): decomposition,
not a sorry-free proof; no whole-library pruning is claimed.
