## What changed
The existing signature and docstring of
`AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_comparison` are unchanged.
Its proof now obtains a natural equivalence of cocones across prime localization,
uses `IsColimit.extendIso` to transport the original universal cocone along `e`,
and constructs the localized colimit's `desc`, factorization and uniqueness proofs.
Agreement on R and `IsLocalization.ringHom_ext` prove the fixed structural-map equations.

The first worker's `EtaleResidueTriplesPrimeLocalizationCore` and its node were removed:
they retained the parent's universal cocone and essentially its entire conclusion.
The new module `Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationCoconeEquiv`
states only the natural cocone correspondence, without a universal cocone, vertex
isomorphism, vertex algebra structure, or compatibility hypothesis hC.

## Proved and sorry left
Hole closed: `AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_comparison`
(node `new-lem-sbc-etale-triples-prime-localization-comparison`).
Hole added and still open:
`AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_coconeEquiv`
(node `new-lem-sbc-etale-triples-prime-localization-cocone-equiv`).
Its sole proof is `:= by sorry`, with the full descent argument and source in its docstring.
This is a decomposition: one existing hole closed, one new hole added, net zero.
The parent is proved conditional on this lower descent statement; it is not an
axiom-clean completed target. No other hole is added and no definition is changed.

Both modules compile locally. Scratch copies with `#print axioms` show exactly
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for both declarations.

## No longer needed
The parent's direct proof imports
`Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations` and
`Sheaf.Paper.EtaleFiniteDataDescent` are replaced by the cocone-equivalence module.
Their nodes `lem-weil-pbc-localization-colimit-principal-localizations` and
`lem-weil-pbc-etale-finite-data-descent` leave the parent's direct `proof_deps` but
remain dependencies/imports of the open descent statement. Neither is pruned from
the transitive route. No old proof dependency is otherwise omitted; pruned modules: none.
The undelivered Core module/node from the first worker are discarded, not counted as pruning.

## Where the brief, the DAG or earlier work was wrong
The first worker's decomposition only changed equality on R_p to equality on R
while retaining all original hypotheses and the universal-cocone conclusion.
It did not isolate a strictly smaller descent step, provided no complete natural-language
proof for its hole, and left the parent's DAG proof pointing to its old direct dependencies.
The second reading repairs all three faults. The mathematical route still follows
principal localizations followed by finite-data descent and transport of cocones.

Source verification: [Stacks 04GW](https://stacks.math.columbia.edu/tag/04GW)
is the pointed-triple colimit presentation (its strict-henselization conclusion
requires a separable closure). The present correspondence only uses localization
and finite-presentation descent, so does not assert that conclusion for arbitrary K.
[00CR](https://stacks.math.columbia.edu/tag/00CR) supplies principal-refinement colimits;
[01ZM](https://stacks.math.columbia.edu/tag/01ZM) supplies object/morphism/equality descent;
[07RP](https://stacks.math.columbia.edu/tag/07RP) supplies descent of étaleness.

## New nodes
`new-lem-sbc-etale-triples-prime-localization-cocone-equiv`: the natural equivalence
of cocones with fixed vertex, including postcomposition naturality and agreement on R.
It is exactly the descent step; equivalence/inverse are used for colimit uniqueness
and existence, naturality for factorization, and agreement for the structural equation.
Its searches were actually run through msearch (leansearch, leanfinder, loogle, grep).
LeanSearch returned an Internal Server Error, recorded without a verdict; the
remaining searches were successful. Only generic
category-theory transport results were found. `IsColimit.extendIso` is used in the parent.
There are no change records because no existing statement or definition changes.

## Second reading by F1
1. Compared the parent with the repository using diff and separately compared its
   theorem signature byte for byte: identical. Its public imports, visibility and
   existing docstring are unchanged. The new module has no repository predecessor.
   Verdict: no existing statement, hypothesis, conclusion or definition changed.
2. Compiled the descent module and parent locally through lcompile. Both pass.
   Scanned delivered Lean for sorry and forbidden constructs; only the named descent
   theorem has a sorry. Axiom probes return only the three permitted axioms and
   sorryAx. No definition, unsafe declaration, opaque declaration or custom axiom
   was added. Verdict: the parent is a genuine conditional proof with one explicit hole.
3. Read the full new descent statement and checked its constructions. For R a field,
   localization is R and the correspondence reduces to transport along the compatible
   pointing. For a trivial vertex, both cocone sets are singletons and the equality
   is automatic. For a vertex admitting no compatible inverted base map, both sides
   are empty: principal refinements force invertibility on any R-cocone. A zero base
   ring has no p, so is excluded by the original hypotheses; K need not be separably
   closed. Verified source tags, supplied a complete docstring argument and matching
   node, and independently searched Mathlib and upstream/local Lean with different
   terminology. No duplicate of this pointed-diagram comparison exists in the searches.
   Verdict: the new hole is the cocone-descent step, not a renamed colimit theorem.
4. Read from the parent downward, used Mathlib for isomorphism transport and localization
   extensionality, and minimized the parent's direct imports. The two original descent
   dependencies remain at the lower step and are all accounted for above. Read
   `dag/units/sk-prop-input-spreading.json`: the item is below the unit's realized route
   and no unit statement or step is bypassed or changed. Verdict: route preserved;
   no transitive module pruning is claimed.
5. Updated the parent's `proof`, `proof_deps`, and `proof_origin` to its actual reduction.
   Checked the new node's signature verbatim against Lean, its statement dependencies,
   proof-step dependency union, source, searches, status, created/blueprint and Lean
   fields. Verdict: nodes agree with the Lean and accurately record the open descent.

Changes by this reading: replaced the near-restatement and its node by the natural
cocone-equivalence descent theorem; proved universal-cocone transport and structural
agreement explicitly in the parent; shortened isomorphism transport using Mathlib;
relocated proof dependencies, corrected DAG metadata, and rewrote the report to count
this delivery as a decomposition with net zero holes rather than a completed proof.

The first dry run required a separate LeanSearch entry (Loogle and LeanFinder count
as one search kind). Ran it, recorded its actual service failure, and retained the
successful alternative searches.
