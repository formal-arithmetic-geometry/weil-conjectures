## What changed

Proved `AlgebraicGeometry.Scheme.finiteLocallyConstant_pullback_stratum` in
`Sheaf.AlgebraicGeometry.ConstructibleEtaleSetPullbackStratum`, with its signature
unchanged. The existing `finiteLocallyConstant_of_iso` in
`Sheaf.AlgebraicGeometry.PullbackFiniteLocallyConstant` transports finite local
constancy across set-sheaf isomorphisms. The repair uses `import all` to access that private theorem and removes the
duplicate private helper from the item. The imported module is unchanged.
The abelian inverse-image comparison transfers the hypothesis into the form required
by the existing `pullback_finite_locally_constant`. Apply it to the first projection
of the pulled-back stratum. The Cartesian-square equation and `Etale.upperStarComp`
identify the result with the abelian pullback along the new immersion; the forgetful
comparison then transfers it back to the required set pullback. No data definitions or existing public statements changed. The node's proof, dependencies, and proof origin now
record this route. The unit record has empty realized statement and step lists; no
unit statement or designated step is bypassed.

The LeanFinder query for finite locally constant etale pullback returned topological
and condensed comparisons, without an exact Mathlib match. Loogle did not recognize
`Sheaf.isConstant_congr`; the logged grep query returned no hits. Direct repository
reading found the already proved preservation theorem in
`Sheaf.AlgebraicGeometry.PullbackFiniteLocallyConstant`, whose interface fits exactly
after the two forgetful comparisons. The proof compiled using `lcompile.py`.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.finiteLocallyConstant_pullback_stratum`
(node `lem-stage3-finite-lc-pullback-stratum`).

No `sorry` remains in the item's module, and no new holes or modules were added.
The existing `finiteLocallyConstant_of_iso` is fully proved and reused; no new
helper is declared in the item. Imported existing
lemmas may still depend on their previously recorded holes; this delivery does not
claim to close those dependencies.

## No longer needed

Removed these four direct proof imports and their direct DAG dependencies:

- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`:
  `lem-weil-pbc-sets-etale-inverse-image-composition-units`.
- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageStalkGerm`:
  `lem-weil-pbc-sets-etale-inverse-image-stalk-germ`.
- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheaf`:
  `lem-weil-pbc-sets-etale-inverse-image-constant-sheaf`.
- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageRestriction`:
  `lem-weil-pbc-sets-etale-inverse-image-restriction`.

The direct dependency `lem-weil-pbc-etale-covering-base-change` is also removed:
cover base change is handled inside the existing finite-local-constancy theorem.
These facts can still be reached through other modules; removal here is not a claim
that each becomes unreachable globally. Retained the original three public imports,
`EtaleInverseImageAlgebraicStructures`, and `PullbackFiniteLocallyConstant`.

## Where the brief, the DAG or earlier work was wrong

The original proof plan expanded preservation of finite local constancy into site
comparisons unnecessarily: the existing `pullback_finite_locally_constant` already
supplies this step, and was already imported. It requires the underlying abelian
pullback rather than set pullback, so both forgetful comparisons are essential.
The original theorem statement is correct and unchanged. The source paths for the
blueprint are recorded in the DAG but their document bodies are absent from this
read-only clone; the proof uses the existing sourced theorem and the supplied node
proof. No new unproved source-dependent assertions were introduced.


Repair of the returned delivery: the original private helper duplicated the
existing theorem in `PullbackFiniteLocallyConstant` word for word. Removed it and
used `import all Sheaf.AlgebraicGeometry.PullbackFiniteLocallyConstant` to access
and apply the existing private theorem. The imported module needs no changes.
Compiled against the unchanged library module with `lcompile.py`; no new holes.
The previous second reading applied to the returned version and has been removed
for a fresh reading. No change record or adapted module is needed.

## Second reading by F2

1. PASS. Diffed the sole delivered Lean module against the repository. The existing
   theorem signature is byte-for-byte identical (checked separately by text extraction).
   No declarations, definitions, hypotheses, or conclusions were added or changed.
   The three public imports are unchanged; both remaining proof imports are private.
   No adapted modules or change records are required. Restored the original declaration
   docstring; the new module comment and proof remain.
2. PASS. Independently compiled the repaired module with `lcompile.py`, without errors
   or warnings. There is no `sorry` or forbidden declaration/attribute in the delivery.
   Replaced the obsolete scratch axiom test with a copy of the actual repaired module.
   `#print axioms finiteLocallyConstant_pullback_stratum` reports only `propext`,
   `Classical.choice`, `Quot.sound`, and inherited `sorryAx`. Separate checks show that
   both existing `etaleInverseImageAlgebraicStructures` and
   `pullback_finite_locally_constant` already depend on `sorryAx`; `upperStarComp`
   uses only the three standard axioms. Thus the original local hole is closed, but
   this is not a claim that the theorem's entire dependency closure is proved.
3. PASS. No statements are split off, no new nodes or helper declarations exist, and
   no data is chosen in a definition. Read the existing private isomorphism-invariance
   proof: it retains the trivializing cover and transports fiber finiteness along an
   equivalence. The two comparison witnesses are eliminated solely inside a theorem
   proving a proposition, not used to define arbitrary data. Checked the vacuous
   zero-stratum case, identity base change, and empty pulled-back strata; none needs
   a nonemptiness or surjectivity hypothesis. Repository searches for pullback and
   isomorphism variants confirm that the reused private lemma fits the set-sheaf
   predicate; the upstream coefficient-sheaf variants concern different predicates.
   An independent logged grep query for 'locally constant sheaf invariant isomorphism'
   found no additional candidate. No duplicated intermediate theorem remains.
4. PASS. The proof takes the existing preservation theorem, then the Cartesian-square
   equality and composition isomorphism, with the forgetful comparisons in the correct
   directions. The first comparison transports `hS i` to the underlying abelian
   pullback; the last comparison transports back to set pullback. Four obsolete direct
   proof imports are removed. All five old proof dependencies absent from the new
   route are listed under `No longer needed`, including covering base change. The
   retained public imports supply the statement's notions, and the two private imports
   supply proof declarations. Read `dag/units/sk-prop-sf-cbc.json`: both `realized`
   lists are empty, and this fixed-stratum reduction bypasses no designated unit step.
5. PASS. Diffed the existing node: only `proof`, `proof_deps`, and `proof_origin` change.
   The dependency union matches the five proof steps. Checked the dependency nodes'
   Lean records and `Stratification.pullback`: its domain is the chosen fiber product
   and its immersion is the second projection, precisely as used in the proof. The
   statement and its Lean record are unchanged, and no new-node obligations arise.

Second-reading changes: restored the original theorem docstring, refreshed the scratch
axiom check to test the repaired `import all` version, and recorded this independent
review. No proof or DAG repair was needed. Holes closed: the one declaration named in
`Proved and sorry left`; holes added: none. Direct imports pruned: four; no global
unreachability or whole-closure completion is claimed.
