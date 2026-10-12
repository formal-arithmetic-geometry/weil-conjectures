## What changed
Reduced `constructible_of_mono_noetherian` to generic finite local constancy and a Noetherian-induction criterion. On every closed subscheme, pull back the monomorphism, preserve constructibility of its target, and apply the generic lemma. The criterion combines these local results into constructibility.

## Proved and sorry left
The proof body of the original theorem `constructible_of_mono_noetherian` is closed, conditional on the dense-open lemma below. The new criterion `constructible_of_closed_generic` is fully proved with standard axioms only. The criterion uses actual well-founded induction, the empty-scheme case, a strict closed-complement descent, pullback composition, and the existing open-closed gluing theorem.
`exists_dense_open_of_mono_noetherian` remains sorry, node `lem-weil-pbc-module-subobject-generic-constancy`.
No sorry remains in the induction criterion or the original item. Only the dense-open generic lemma remains sorry.

## No longer needed
No original import or geometric step was pruned. The unused original dependency `prop-weil-pbc-inverse-image-modules-exact` (module `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`) is pruned from this proof: it uses a different SheafOfModules encoding, whereas the source-library ModuleCat pullback already preserves monomorphisms. This does not assert that the module is globally unreachable. Two unnecessary draft imports were removed from the proved criterion: `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` and `WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian`. Mathlib’s existing closed-subscheme construction and a three-line derivation of source Noetherianity suffice. These two modules need not enter the closure through this delivery.

## Where the brief, the DAG or earlier work was wrong
The planned dependencies provide definitions and pullback machinery but do not directly state the geometric generic-neighbourhood argument or the induction criterion. These are stated separately, with no circular dependency on the parent theorem. The induction criterion is now fully proved. No statement or definition was changed, and the unit’s curve-devissage route is retained.

## New nodes
`lem-weil-pbc-module-subobject-generic-constancy`: the dense-open conclusion of the generic-stalk and descent argument, in `Sheaf.AlgebraicGeometry.ModuleSubobjectGenericConstancy`.
`lem-weil-pbc-constructible-closed-generic-criterion`: the proved Noetherian induction step, independent of coefficient Noetherianity, in `Sheaf.AlgebraicGeometry.ConstructibleClosedGenericCriterion`.

The existing `prop-constructible-open-closed` of another unit is used as a proved gluing tool, preserving the parent’s closed-complement route. Edge cases: the criterion handles empty schemes by the existing zero-sheaf lemma; density supplies a point only after assuming a nonempty closed subscheme. The generic lemma includes empty schemes (take the empty open), zero sheaves, and constant monomorphisms over arbitrary Noetherian coefficient rings.


## Second reading by S1

1. **Visible declarations unchanged — pass.** Compared the item against the repository with
   `diff -u`: the existing theorem's signature is byte-for-byte unchanged; its docstring,
   universes, two public imports and namespace are unchanged. Only three proof imports and
   the proof body were added. The two other delivered modules are new, each containing one
   public theorem and no definitions. There are no statement changes or change records.
2. **Kernel proofs — pass, with one explicitly open dependency.** Compiled all three files
   using `lcompile.py --all`, without errors or warnings. Scratch copies with `#print axioms`
   showed `[propext, Classical.choice, Quot.sound]` for `constructible_of_closed_generic`;
   the original theorem and `exists_dense_open_of_mono_noetherian` additionally use `sorryAx`,
   exactly because the latter is the sole delivered sorry. Scanned every delivered Lean file:
   no axiom, unsafe, opaque, implemented_by, extern, hollow definition or hidden sorry.
3. **Split statements — pass.** Read Stacks 09BH (59.74.1(3)), including the finite-generator
   lift, monic descent and equality argument, and 095E's stratification criterion. The dense-open
   lemma keeps Noetherianity of both scheme and coefficient ring, a monomorphism, and a
   constructible target; its conclusion is strictly the generic part of the original theorem,
   not constructibility on the whole scheme. Its docstring and node give that argument in words.
   Relations between the lifted generators vanish by their inclusion in the constant target.
   The resulting quotient embeds in constant M/N; an etale section nonzero in this constant
   target has nonempty open nonvanishing locus, which meets the generic point, so a zero
   generic stalk forces the quotient to vanish. Finite component opens produce a dense union.
   Tested empty schemes (empty open is dense), zero source, identity on a constant finitely
   generated module, and several intersecting components (remove the other components).
   The closed-generic criterion needs no coefficient Noetherianity: the written well-founded
   induction, trivial stratum and open-closed gluing prove it over any commutative ring.
   Repeated leanfinder with “subsheaf of a finite locally constant module sheaf becomes locally
   constant near generic points”, loogle with `"IsFiniteLocallyConstantSheaf"`, and grep with
   `closed.*generic|generic.*(mono|sub)|constructible_of`; searched `lean/` by subsheaf, generic,
   dense and of_mono. No matching theorem was found. Existing `constant_subsheaf_generic`
   requires a finite ring and finite underlying module, so cannot supply this arbitrary
   Noetherian-ring result. Existing `IsConstructibleSheaf.exists_dense_open` assumes source
   constructibility, so using it here would be circular. The remaining geometric argument
   cannot be closed in a few minutes from the current API.
4. **Route and pruning — pass after report repair.** Read the unit `sk-thm-p1.json`, including
   every `realized` entry: none is bypassed or edited. The curve-devissage route is kept through
   generic finite local constancy and induction on the closed complement. The strengthened
   induction claim ranges over closed immersions whose image is contained in C; injectivity
   and a point in the dense open prove C' < C, including when C is larger than that image.
   Empty schemes are handled before using density to choose a point. The proved source-library
   open-closed equivalence is a tool from the constructible-sheaf unit, not a replacement for
   the curve calculations. All added imports are proof-only; the new modules' public imports
   are needed by their signatures. The original direct proof dependencies now routed through
   the two new nodes are `def-constructible-constant`, `def-constructible-constructible`,
   `def-constructible-locally-constant`, `def-constructible-stratification`,
   `def-weil-pbc-geometric-stalks`, `def-weil-pbc-noetherian-ring`, and
   `prop-constructible-generic-constancy`; these remain used through statements or the split
   argument, rather than being pruned. `prop-weil-pbc-inverse-image-modules-exact` is the one
   genuinely unused old dependency, now explicitly listed under No longer needed.
5. **DAG agreement — pass after two citation repairs.** Checked the Lean signatures against
   each node's `lean.statement`, all proof-step uses against `proof_deps`, and all new-node
   metadata (source, searches, creation, chapter/unit and blueprint provenance). In the parent,
   removed `prop-weil-pbc-inverse-image-modules-exact`: its declaration concerns a different
   encoding and is never invoked. The step now identifies the actual source-library
   `Etale.preservesFiniteLimits_upperStar` instance supplying monicity. In the criterion,
   replaced `lem-weil-pbc-reduced-induced-closed-subscheme` by the existing Mathlib leaf
   `lem-weil-pbc-closed-subset-closed-subscheme`: the Lean uses `vanishingIdeal`,
   `range_subschemeι` and `coe_support_vanishingIdeal` directly, without the unproved full
   reduced-induced theorem. Its range and closed-immersion clauses suffice; reducedness and
   uniqueness are unnecessary. The noetherian-closed-subsets node matches the exact
   well-founded instance used. Pullback stability and open-closed gluing match the existing
   imported declarations. Proof dependency unions and proof origins were updated accordingly.

Second reading changed only DAG citations and the report's pruning and axiom accounting;
no Lean statement, definition, import or proof required repair. Scratch axiom probes were removed.
