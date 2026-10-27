# Stage-1 report: lem-sfb-space-maximal-flat-lfp-base-open

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-maximal-flat-lfp-base-open.json`: statement, now split into six proof steps; no Mathlib match.
- `citations.json`: fifteen step/node records, checked as literal substrings of the cited statements.
- `searches.jsonl`: five actual search-command records retained verbatim. The item's older searches are also preserved.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No unit record is changed.

## Attachments

None. Searched the project `lean/WeilConjectures` by the exact blueprint id and maximal/largest open, flatness and local-presentation notions. The generic `AlgebraicGeometry.Scheme.Hom.maximalOpen` and `restrict_maximalOpen` in `WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/IsIso.lean:45-75` concern schemes and do not prove the algebraic-space statement or its fppf compatibility. They are not an attachment.

## WANTED

None. Every source used is present locally. No SGA source is used.

## Findings and corrections

The statement agrees with Stacks Tag 06R2, `spaces-descent.tex`, lemma-largest-open-of-the-base, for the conjunction flat and locally of finite presentation and the fppf topology. Tags 041W and 041T supply target locality. No statement correction or STATEMENT-DISPUTED is needed; statement and statement dependencies are unchanged. The imported node had no proof. The new argument supplies both clauses rather than referring wholesale to a generic maximal-open theorem.

The construction indexes good *open subspaces* via the set of opens of the point space. It does not form a possibly proper-class-indexed union of all fppf test morphisms. The reverse-inclusion proof descends over the open image of the restricted map, where surjectivity is proved, rather than assuming the original base-change morphism is surjective.

The ancestor command prints `blueprint.from.node = None`. The inherited null ancestor and via chain are retained, with the existing precise place through Tags 06RC/06R4. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-images proof (3). The item is a supporting geometric input on the inherited chain; no unit route is replaced. Whole-DAG searches for Tags 06R2, 041W, 041T, 03BZ and maximal-good-open keywords, plus whole-blueprint searches for largest open, maximal flat, flat locally finitely, 06R2, 041W and 041T, found reusable inputs but no blueprint duplicate of the item. `same_as` remains empty.

## Not duplicates

No new node is created. In particular no extra 03BZ correspondence node, 041W/041T descent node, 042S open-image node, or restatement of one clause of the item is introduced. Existing nodes supply each of these inputs.

## Search assessment

Ran the prescribed search command for the item with LeanFinder (two genuinely different phrasings), Loogle, grep and LeanSearch. All services answered. Read the hits: Mathlib's `UniversallyOpen.of_flat` is for schemes (`UniversallyOpen.lean:145-149`); flat base-change stability is in `Flat.lean:78-86`; local-presentation base change is in `FinitePresentation.lean:85-92`; the grep hit `Sites/Fpqc.lean:49` identifies the fppf precoverage. The second LeanFinder returns scheme Zariski-local constructors. None proves the target-open construction and fppf comparison for algebraic spaces. Queries and actual returned summaries are recorded without inventing searches or claiming an unavailable service was negative.

## Review by Q40

I read the entire source proof of Tag 06R2 in `spaces-descent.tex:1042-1092`, and its locality sources 041T (`lemma-descending-property-locally-finite-presentation`) and 041W (`lemma-descending-property-flat`). I also read 03BZ (`spaces-properties.tex`, lemma-open-subspaces), 03IE (lemma-factor-through-open-subspace), 03H4 (lemma-points-cartesian), and 042S (`spaces-morphisms.tex`, lemma-fppf-open). For the generic representable-map calculus I checked the algebraic-space compatibility in `stacks-properties.tex` Tag 04XC (lemma-property-spaces-too). The cited calculus applies to algebraic spaces as discrete stacks, with exactly the chartwise properties used in the item. There are no new-node sources to check.

Step 1 uses only the *unconditional* open-subspace/open-subset correspondence in `lem-a1-space-etale-open-image`, whose statement I read. Although its title concerns etale images, that correspondence is stated before any hypothesis on the map q. The family of good opens is a subset of the set of opens. Its union and the corresponding subspace therefore exist without a finiteness or separation hypothesis.

Step 2 uses `lem-a1-space-open-factor-scheme-tests` for the inverse-image opens, `lem-a1-space-open-chart-tests` for etale scheme tests of open inclusions, and the explicit composition, etale-implies-smooth-implies-flat-and-lfp, and open-source-cover clauses of `lem-sfb-stack-chartwise-smooth-etale-calculus`. I read all three statements; none is merely a definition of flatness being substituted for a locality theorem. The maps checked on the source cover are X_V to V to W. They really are the restrictions of f_W with target W, so composition is essential. Pulling the inverse-image opens back to any scheme gives an actual open cover; no claim of affine intersections is used. Step 3 is elementary: largestness follows from the indexed union and uniqueness from two inclusions.

Step 4 uses the open-pullback clause of `lem-a1-space-open-factor-scheme-tests` and arbitrary-base-change stability from the same calculus. Its good map is f restricted over W(f), not f itself, which has no flatness assumption.

Step 5 checks each hypothesis before invoking an image or descent. The inclusion W' into Y' is etale, so its composite h with g is flat and locally of finite presentation. `lem-sfb-flat-lfp-space-universally-open` states exactly that such a map has open point image; it does not require properness, despite also defining that notion in its statement. I use the correspondence from `lem-a1-space-etale-open-image` only to realize this open subset, not its theorem about *etale* images. `lem-a1-space-open-factor-scheme-tests` proves that h factors through I and that W' times_Y I is W'. Hence q is a base change of h and retains both properties. Surjectivity follows from the definition of I, and the point-pullback formula in `lem-a1-space-point-open-calculus` makes it stable under scheme tests. I did not assume that a nonrepresentable map is representable by schemes: morphisms between algebraic spaces are representable by algebraic spaces, which is the representability required by the cited descent theorem.

Step 6 applies `lem-sfb-representable-fppf-etale-open-descent`, whose statement explicitly says the same assertion holds for morphisms of algebraic spaces and treats the two properties independently. The map q is now surjective, flat and locally of finite presentation; f_I is arbitrary. Its pullback along q is identified by the fibre-product universal property with (f') restricted over W'. Thus both properties descend, making I one of the good opens. The inverse-image and inclusion clauses in the two open/point-calculus statements then give the reverse inclusion as subfunctors. The equations compare open subspaces, not merely point images.

I tested Y empty, X empty, W(f) empty, an already-flat-lfp f, and a nonsurjective open-immersion g. If X is empty all opens are good; if W' is empty the reverse inclusion is automatic and the empty descent cover is over I empty. For a genuine non-flat example take Spec k at 0 into A^1_k: W(f) is the complement of 0 and f is empty over it. A nonsurjective open base change has exactly the expected good locus. Taking g instead to be the closed point at 0 would make f' the identity while the inverse image of W(f) is empty; that map is not flat, confirming why the base-change hypothesis is indispensable. No arbitrary nonflat base-change claim is hidden here.

Against delivery-errors B--E: there are no new statements to be hollow, duplicated, unsourced or accidentally stronger; the imported statement remains byte-identical. Each cited non-elementary input is a literal part of the corresponding node statement, as recorded in citations.json. No cited node is the item or was created by this split. Only Step 3 is marked elementary, with its argument written out. All six proof steps are below 2000 characters, and no long step hides a separate comparison lemma. The off-unit open-subspace tools are declared in split_report.tool_uses, since the unit has no replacement for this generic topology input. No claim is made that an existing node is completed merely because its statement is cited.

## Unfinished work

None in the authorized one-level stage-1 split. The required server dry run and delivery are the remaining operational checks.
