# Stage-1 delivery: lem-sfb-normal-fixed-subscheme-quotient-action

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-normal-fixed-subscheme-quotient-action.json: complete six-step split; statement unchanged; not in Mathlib.
- citations.json: a verbatim part of the cited statement for every step/use pair.
- report.md: this report. searches.jsonl records actual msearch calls; milne.txt is a sandbox-only extraction for reading.

New nodes: 0. New Mathlib leaves: 0. The existing descent, base-change, refinement and gluing statements suffice. No lemma is postponed into a restatement of the item.

## Attachments

None. Searched the live lean/WeilConjectures/ for the exact blueprint tag and fixed-subscheme, normal/fixed, and quotient/fixed concepts; no declaration states this scheme-theoretic result. A supplementary read of lean/Sheaf/AlgebraicGeometry likewise found no exact declaration.

## WANTED

None. Milne's book and the Stacks TeX sources are locally available.

## Findings and corrections

The item was unsplit, with no existing sandbox attempt. The imported statement is sound and is preserved byte for byte. There is no released repair note. The inherited blueprint.from.node is null: blueprint_refs.py ancestor confirms that the recorded created.item chain has no imported blueprint ancestor. I retained the detailed existing place and via chain rather than inventing an ancestor. Whole-blueprint searches for “fixed subscheme”, “normal subgroup”, “quotient action” and “fpqc” found no duplicate of this item. I read the current latest chapter and sketch statement; this supplies a below-unit prerequisite to the inherited normal-series fixed-point route, not a change to that route.

The source does not write out this quotient-action proof: Milne 16.51 only uses the normal-series induction. Accordingly proof_origin.by is agent. Milne 7.1 supplies the fixed-scheme interpretation; Stacks 023Q supplies the only descent theorem. The argument never treats surjectivity of q on schemes as surjectivity on A-valued points.

Generic tool use declared in split_report: lem-pc-fppf-affine-refinement (another unit), used only to verify the fpqc covering definition. The other off-unit proof inputs are existing Mathlib leaves. None replaces the unit's mathematical route.

## Not duplicates

No new nodes. In particular I reused lem-sfb-universal-fixed-subscheme instead of creating an invariant-subscheme clause, lem-weil-pbc-fpqc-representable-descent instead of another 023Q node, lem-trf-fppf-covering-base-change for cover pullbacks, and lem-pc-fppf-affine-refinement for the finite-affine covering condition.

## Review by Q20

I read Milne Theorem 7.1 and its proof on printed pp.138–139, including the quantification over every algebra extension, and Theorem 16.51 on printed p.343. The latter motivates this prerequisite but does not prove it in its displayed text. I also read Stacks descent.tex lemma-fpqc-universal-effective-epimorphisms (023Q), especially its precise overlap condition and unique morphism conclusion; topologies.tex definition-fppf-covering, lemma-fppf, lemma-fppf-affine, and the proof that fppf coverings are fpqc. No SGA source is used. There are no new-node sources to review.

Step 1 uses def-pc-fppf-site exactly for flat/locally-finitely-presented/jointly-surjective covers. lem-trf-fppf-covering-base-change explicitly preserves those covers under arbitrary pullback. lem-pc-fppf-affine-refinement explicitly gives finitely many source affine opens over any affine target. These meet precisely the two clauses of def-weil-pbc-fpqc-covering, so I do not assume a rational point lift, or quote a finite-flat quotient lemma for this possibly nonfinite quotient. The same argument applies to both successive covers used for associativity. I checked the cited statements themselves rather than their proof sketches.

Step 2 uses def-sc-group-scheme-subgroup's normality over every k-algebra for the conjugate g^-1 n g, and lem-sfb-universal-fixed-subscheme's final arbitrary-W factorization clause. The latter is stronger than fixedness only on k-points and is exactly what constructs the morphism on G times Y. The equations are checked on arbitrary affine charts of the whole source with their tautological points, so lem-weil-pbc-scheme-morphism-gluing's explicit equality clause promotes them to scheme identities. Injectivity of j on each algebra's points comes from the representing inclusion in the fixed-subscheme statement; this and the same gluing clause give the cancellation used later. No closed-set containment is substituted for factorization.

Step 3 only cancels this j in the given action identities. The fixed-subscheme statement explicitly says the restricted N-action is projection, giving the remaining equality. This is an elementary step with the exact inputs named. Step 4 is also elementary: the definition of the fibre product gives equal q-images; the stipulated scheme-theoretic kernel gives n over the very same algebra, without extension; the three equalities use the laws proved in step 3. The gluing statement is cited for promoting the affine-chart computation on the kernel pair to equality of morphisms.

Step 5 uses exactly the existence/uniqueness conclusion of lem-weil-pbc-fpqc-representable-descent with T=Q times Y, source cover G times Y, and target Y. Step 4 supplies its compatibility, step 1 its cover. Applying its uniqueness to maps into Spec(k) checks k-linearity of the descended morphism. Step 6 uses that same uniqueness twice, on successive base changes of q, to prove associativity. The unit pulls back along the already specified identity lift. For uniqueness of the action, the required equation first cancels j (as justified in step 2), then uniqueness in the descent statement cancels p. Every node in uses has a corresponding exact quotation in citations.json.

Edge cases checked: N=1 gives Y=X and a descended action through a kernel-trivial fppf quotient; N=G and Q=1 gives the trivial action on X^G. Empty X or empty Y gives the unique map throughout. Trivial G gives the identity action. Nonreduced test algebras and infinitesimal subgroups, including characteristic-p kernels, are covered by the universal fixedness and scheme-theoretic kernel clauses; no geometric-point density, reducedness, smoothness, or properness appears. For example trivial alpha_p action gives Y=X and the argument still descends along alpha_p to the trivial quotient. No statement dispute was found.

Against delivery-errors B–E: no new data or statement-only node is introduced; every cited notion has its existing definition or the item's inline meaning; source tags/labels were read locally; no search was invented. The msearch results were read, then a second semantic phrasing was tried. The abstract group fixed-point declarations in Mathlib/GroupTheory/GroupAction/SubMulAction.lean:595–609 were read and do not construct or descend a scheme morphism. Every non-elementary input is an existing node with its required hypotheses verified above. There are no hidden long steps: all steps are below 1100 characters. The conjugation and kernel-pair calculations remain in the item, so this is not relabelling or moving a clause to a new node. The graph and route are checked by the required server dry run.

## Unfinished work

None in this one-level split. Existing dependency nodes retain their own stage status. No Lean was written, no compiler or build was run, and nothing in the shared repository or launcher was edited.

## Validation

The first required server dry run passed (12567f0c839). A final source-label audit corrected the explanatory fppf-to-fpqc source tag in step 1 from 022B to 022C, using the checked tags/tags mapping; no statement or argument changed. The final dry run is rerun after this correction.
