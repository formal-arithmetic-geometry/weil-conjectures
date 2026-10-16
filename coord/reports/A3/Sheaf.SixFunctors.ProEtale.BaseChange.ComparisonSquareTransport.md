## What changed

Proved `AlgebraicGeometry.ProEtale.comparison_square_of_component` from two separate one-path normalization statements. `ComparisonSquarePaths` constructs both ordinary path isomorphisms and their common derived source/target factors. Its generic extensionality lemma proves ordinary path equality from exactly the supplied `ComparisonSquareComponent` hypothesis; the item carries that equality through the named exact derived path construction by congruence. The item combines these results with the two normalization statements. Its existing signature and public imports are unchanged.

The two added proof-only imports are `ComparisonSquareEtalePathNormalization` and `ComparisonSquareProEtalePathNormalization`. Their statements identify one path at a time and assume no coherence equation. They use `HEq` to retain the two definitionally equal presentations of the endpoint morphism types. The item combines these identities with ordinary congruence and converts the final heterogeneous equality to the original equality. All added definitions are explicit composites of existing canonical isomorphisms. No arbitrary witness is chosen.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.ProEtale.comparison_square_of_component` (node `stage3-proetale-comparison-square-transport`). Added two holes:

- `AlgebraicGeometry.ProEtale.comparisonSquareEtalePath_normalization`, node `stage3-proetale-comparison-square-etale-path-normalization`.
- `AlgebraicGeometry.ProEtale.comparisonSquareProEtalePath_normalization`, node `stage3-proetale-comparison-square-proetale-path-normalization`.

This is a decomposition, not a complete proof of the transport calculation: one hole closed, two added, net minus one. No other sorry remains in the delivered sources. The ordinary path extensionality theorem and the congruence argument in the item are fully proved.

The etale normalization still needs the compatibility of the bounded-below square map with exact derivation of its ordinary square, then the composition/whiskering coherence calculation for its two comparison maps. The pro-etale normalization still needs expansion of `leftDerivedFunctorNatIso` and `leftDerivedFunctorCompIso`, naturality and cancellation of the internal exactness comparisons, and equality induction for the square's commutativity transport. Both require only the existing exact derived functor APIs; the detailed proofs are recorded in their docstrings and nodes.

## No longer needed

No original imports, existing DAG nodes or existing modules are removed. The unused trial import `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate` was removed from both new normalization modules; their statements need only `ComparisonSquarePaths`. The proof does not import `ComparisonSquare` or `ComparisonSquareComponent` and does not use the theorem proving underived coherence. It uses only the supplied component hypothesis. `DerivedExactSquare` was searched but is not imported: its composition hypothesis differs from the given square-component hypothesis. No blueprint unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The node labels the whole exact derived transport calculation elementary, but gives no ready-made project-specific normalization declaration. The remaining work is isolated as two independent path identifications, rather than restating the square-coherence theorem. The first draft's cancelled reformulation was equivalent to the original theorem and was discarded; neither that draft module nor its node is part of this delivery.

Concrete rewriting through the derived sheaf functor structures caused expensive type inference and kernel conversion. Keeping the original `IsPullback` argument in the normalization statements, rather than projecting the component expressions from a separately supplied chosen square, removed the expensive conversion. The ordinary path equality is handled generically and its image by congruence. All four delivery modules compile in approximately 5–7 seconds each with the standard limit. No pre-existing definition or signature is changed.

## New nodes

`stage3-proetale-comparison-square-paths` records the concrete path and endpoint-factor constructions, generic component extensionality, and the explicit exact derived path composite. Its module is `Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquarePaths`. The constructions use no sorry.

`stage3-proetale-comparison-square-etale-path-normalization` identifies the left derived path with the derived ordinary etale path between the common endpoint factors. Its module is `Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquareEtalePathNormalization`.

`stage3-proetale-comparison-square-proetale-path-normalization` identifies the right derived path with the derived ordinary pro-etale path between the same endpoint factors. Its module is `Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquareProEtalePathNormalization`.

No change record is required: no existing statement, definition or public import is changed, and no consumer adaptation is needed.

Validation: all four delivered modules pass compilation. The original theorem signature was checked byte-for-byte against the shared source, and all four node signatures match the delivery parser. The final required dry run printed `OK (dry run): commit ef8c10e3bd compiles and passes the preflight except for the second reading, which the second reader writes; nothing pushed.` The initial preflight's search-record and signature-metadata issues were corrected, and redundant local commands were removed. The dry-run tool explicitly leaves the independent reading to the second reader; no second-reading section was written by this worker.

## Second reading by A3

1. **Existing interface: PASS.** Read the shared and sandbox transport modules in full
   and compared them with `diff -u`. The only original Lean declaration is
   `AlgebraicGeometry.ProEtale.comparison_square_of_component`; its complete signature
   is byte-for-byte identical (also checked by extracting the text before `:= by`).
   Its docstring, universes, namespace, visibility and original public imports are
   unchanged. The two added imports in that module are plain proof imports. The
   other three modules are new; no existing definition, target or consumer changes.
   The existing node differs only in `proof`, `proof_deps` and `proof_origin`.

2. **Proof and constructions: PASS as a decomposition.** Independently compiled all
   four modules with `lcompile.py --all`. Inspected every construction in
   `ComparisonSquarePaths`: each is a displayed composite of supplied isomorphisms,
   exact derived composition comparisons, or inverse exactness comparisons. No
   witness is selected from an existence statement. `comparisonSquarePaths_eq`
   applies `Iso.ext`, `NatTrans.ext` and component extensionality to exactly
   `(h F).symm`; expanding the whiskerings gives `ComparisonSquareComponent` with
   the right order of all three factors. The transport proof applies congruence
   to the entire ordinary path isomorphism and joins the two HEq identities in
   the correct direction. The final `eq_of_heq` has exactly the original goal.
   A scratch copy with `#print axioms` for all eleven delivered declarations
   reports only `propext`, `Classical.choice`, `Quot.sound` for the eight closed
   constructions/lemmas, and those three plus `sorryAx` for the two normalizations
   and the original transport theorem. The only source holes are precisely the
   two public named theorems listed above; no forbidden declaration or data hole
   occurs. Thus one original body is closed, two strictly smaller holes remain,
   and net closure progress is minus one, not a completed transport proof.

3. **Split statements: PASS, proof descriptions repaired.** Read the definitions
   of `comparisonSquareData`, `ComparisonSquareComponent`, `etaleComparisonSquare`,
   `proEtaleComparisonSquare`, `leftDerivedUpperStarComparisonIso`,
   `Etale.pullbackSquareComparison`, `Etale.upperStarPlusComp`,
   `leftDerivedUpperStarSquareIso`, `leftDerivedFunctorNatIso` and
   `leftDerivedFunctorCompIso`. The etale normalization identifies only the path
   through `se`, `c₂'`, `c₁'`; the pro-etale normalization identifies only the
   path through `c₂`, `c₁`, `sp`. Neither assumes component coherence or compares
   the two paths. Their common endpoint factors have the necessary orientations:
   the source comparison is inverted and the target uses the inverses of the
   exactness comparisons. These are separate compatibility calculations, not
   renamed versions of the original square equation. Arbitrary commutative rings
   remain allowed. Checked the identity-edge case against the composition and
   transport definitions: equality transport becomes reflexive and the same
   composition factors cancel. Zero input and the zero coefficient ring give
   equality of the unique zero morphisms; no nonzero, finite, smooth or qcqs
   condition enters the argument. The pullback identification itself is used
   only to supply the chosen square, with the same commutativity proof.

   Repeated independent searches through `msearch.py` using the query about
   whiskered composites under exact derivation (LeanFinder), the right-whiskering
   coherence name (Loogle), and composition/whiskering/normalization expressions
   (grep). LeanFinder returned generic derived natural-transformation composition
   results; Loogle did not index the project-specific whiskering lemma. Direct
   `rg` in `lean/WeilConjectures` and `lean/Sheaf` found the actual whiskering and
   associativity lemmas in `MapDerivedCategoryMate`, the proved generic
   `mapDerivedCategorySquareIso_paste` in `DerivedSquarePasting`, and related
   calculations in `RawFixedDerivedComparisonNaturality` and
   `ProfinitePointPullback`. None supplies these normalizations with both the
   fixed D+ square map and the total-left-derived endpoint comparisons.
   `DerivedExactSquare` has a different ordinary composition hypothesis and an
   open composition theorem, so importing it would not close either hole.
   The two substantial normalization calculations were not closed by a short
   existing lemma. Replaced their duplicated all-path prose proofs by separate
   derivations naming the exact whiskering, D+ restriction, naturality and
   cancellation equations each path needs. In particular the etale proof no
   longer calls on a pro-etale square calculation, and conversely.

4. **Top-down route and pruning: PASS.** Read the source blueprint lemma
   `lem-weil-pbc-transport-identifies-exchange.md` (the paragraph expanding and
   conjugating the unit--square--counit composite), its existing expanded
   comparison-square/transport nodes, and
   `dag/units/sk-thm-properbasechange.json` including all `realized` entries.
   This is solely the existing comparison-square transport subcalculation. The
   proof uses the given `hcomp`, not the theorem proving underived coherence and
   not the parent `comparison_square`. It therefore neither creates a cycle nor
   bypasses any unit statement or step. The old transport `proof_deps` is empty,
   so there are no omitted old dependencies to list under No longer needed.
   All original imports remain needed for the unchanged statement; both new
   proof imports supply normalization lemmas actually applied. Each new module's
   public import supplies names used in its signatures or exposed constructions.
   No original module is pruned. A trial with narrower upstream imports was
   reverted after the published library reported duplicate declarations across
   its old/new pro-etale module paths; the final import set is the compiled one.

5. **DAG and source agreement: PASS after documentation repair.** Opened all four
   delivered JSON records. The transport node lists exactly the paths construction
   node and the two normalization nodes used by its proof. Their Lean records
   name the delivered modules and exact declarations; no new statement is left
   without its matching node. Each new node has its source, item/group/date,
   chapter/unit, searches, blueprint origin, status and Lean record. The paths
   node describes actual data and the proved generic extensionality result.
   The normalization nodes describe the two one-path HEq statements, without a
   coherence hypothesis; their `proof_deps` are empty because their remaining
   arguments use the explicit constructions in `stmt_deps` and generic exact
   derivation APIs. Replaced each duplicated normalization proof paragraph by
   three path-specific steps, matching its repaired Lean docstring. No existing
   statement field or unit record was changed.

**Second-reader changes:** added source/blueprint information to the three new
module docstrings and the two generic path-construction docstrings; replaced the
two normalization docstring proofs and their DAG proof steps by separate arguments;
wrote this independent reading. No Lean signature, definition body, theorem proof,
import in the final set, or hole count changed during the second reading.
