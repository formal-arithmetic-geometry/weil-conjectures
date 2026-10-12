## What changed

Replaced the single hole in `Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap`
by a compiling assembly of two strictly smaller steps of its source argument:
`StalkFiniteEtaleModel` constructs only a stalk model and its local comparison;
`FiniteEtaleStalkNeighbourhoodSpreading` spreads an arbitrary such model and comparison.
Both imports are proof-only. The existing theorem signature and public imports are unchanged.
The existing node records the two actual proof dependencies and the final witness assembly.
No existing definition, statement, visibility, instance or target changed; no adaptations.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.GaloisCover.exists_local_finiteEtale_model_overlap`
(node `lem-sbc-local-finite-etale-model-overlap`) by a complete Lean proof.
This is a decomposition, not a completed geometric proof: one hole closed, two added,
net minus one before accounting for the existing dependencies. The original module has no holes.

The two added holes, each a whole public theorem proof `:= by sorry`, are:

- `AlgebraicGeometry.Scheme.GaloisCover.exists_stalk_finiteEtale_model`
  (node `lem-sbc-stalk-finite-etale-model`). This is the local claim of 0EYJ;
  it produces no open neighbourhood and performs no spreading.
- `AlgebraicGeometry.Scheme.FiniteEtale.exists_neighbourhood_model_of_stalk`
  (node `lem-sbc-finite-etale-stalk-neighbourhood-spreading`). This is relative
  finite-presentation descent in 0BQ5 and 0EY3. It assumes the local extension
  has already been supplied and uses no section, group, normality or smoothness.

Every delivered module compiled individually in dependency order with lcompile.py.
The upper proof explicitly passes the selected stalk model and comparison to the
spreading theorem and combines the resulting witnesses with the outside-U proof.
No arbitrary witness is used to define data and there are no new definitions.

## No longer needed

None. There were no proof-dependency imports in the original module to remove.
All seven original public imports remain for the existing statement and its interface.
The two added proof imports are both used. Neither a blueprint unit nor any step
of its prescribed route has been bypassed; the trait and depth-two branches remain
inside the local claim, and finite-presentation spreading remains the next step.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt was identical to the unproved original module and had
no report, new statements or proof. The original node described three substantial
steps with empty `uses` and `proof_deps`, so it had no stated Lean dependencies to
assemble. The new nodes isolate those missing interfaces rather than assuming the
full global spreading theorem (which would create a cycle through this item).

Read Stacks pione.tex, label lemma-extend-covering (0EYJ), and limits.tex,
labels lemma-glueing-near-point (0BQ5) and lemma-glueing-near-point-properties
(0EY3). The spreading lemma works relatively over C, using the qcqs hypothesis
on c and local finite presentation; it does not spread a stalk cover over S alone.
Smoothness provides the local finite-presentation instance in the original proof.

Edge checks: U is nonempty since it contains the generic point; its complement
is nonempty since U is proper. The chosen local ring has positive dimension,
so the trait/depth-two distinction covers it. Disconnected torsors are allowed:
the split rational section fibre meets every component and stabilizer orders divide
|G|. For spreading, U may be empty or all of S and the local overlap may be empty;
no density or s-outside-U hypothesis is used. Empty covers and trivial G cause no
exception. The pullback projections have codomains C_U and the local family,
respectively, so the comparison is over the same scheme on both sides.

Searches were run through msearch.py and are logged in searches.jsonl.
LeanSearch returned Internal Server Error and is recorded as unavailable.
LeanFinder and Loogle yielded no matching theorem; Mathlib grep found only
unrelated rational-map and quasi-finiteness stalk lemmas. Repository searches
found generic full faithfulness and general limit/descent tools, but no local
extension or neighbourhood-with-comparison interface.

Existing tools of other units occur only in the natural-language plans of the
new holes: normal-local depth and flat local depth, and the stalk limit and
finite/etale property descent. These are general tools quoted by the same Stacks
argument; they do not replace the spreading unit's route. Their modules are not
imported into a theorem whose proof is still wholly deferred. No change records
are needed because no existing interface changes.

## New nodes

`lem-sbc-stalk-finite-etale-model`, in
`Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel`: the strictly local
extension over Spec O(S,s), including its punctured-family comparison. Its
self-contained statement retains all of the original local-claim hypotheses;
its docstring and node describe the trait and depth-two arguments separately.

`lem-sbc-finite-etale-stalk-neighbourhood-spreading`, in
`Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleStalkNeighbourhoodSpreading`:
the general relative descent of an already supplied local model and comparison.
Its conclusion only gives a neighbourhood cover and its overlap isomorphism;
it neither constructs the local model nor chooses a point outside the original open.

## Second reading by F2

1. **Statements and signatures.** Compared each delivered module with the repository version. The existing theorem signature is byte-for-byte unchanged; the two added declarations have self-contained statements matching their DAG nodes. Verdict: pass.
2. **Proof and axioms.** Compiled all three modules with `lcompile.py --all`. The target has no `sorry`; the only remaining `sorry`s are the two named split theorems. No forbidden declarations or hollow definitions were added. Verdict: pass, with the two documented open nodes.
3. **New statements.** Checked both split statements against the Stacks sources and their documented edge cases: spreading permits empty overlaps and arbitrary points, while the stalk result retains all local-claim hypotheses. Neither duplicates the target. Verdict: pass.
4. **Pruning and imports.** The two new imports are proof-only and both are used by the target proof; all original public imports remain needed for its interface. No old proof dependency is unused, and the unit route `sk-prop-input-spreading` is retained. Verdict: pass.
5. **DAG agreement.** The target node records exactly the two theorem uses, and the auxiliary nodes record their declarations, sources, proof steps, and dependencies. Verdict: pass.

Changed after this reading: appended this review record only; no Lean statements, definitions, proofs, imports, or node metadata were changed.
