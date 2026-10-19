1. Files written

- `dag/nodes/sec-trace-formula/lem-trf-fitting-ideal-independence-base-change.json`: statement, split in eight proof steps; no Mathlib match. The statement is byte-for-byte unchanged; its notion dependencies are completed.
- `dag/nodes/sec-trace-formula/lem-trf-fitting-ideal-minor-inclusions.json`: one new statement-only node, status `unsplit`; Stacks 07Z7(1)-(3), with (2)-(3) transposed for the row convention. No Mathlib match.
- `citations.json`: a verbatim statement quote for every node cited by each proof step.

2. Attachments

None for this item. Searches for its blueprint tag and for Fitting/determinantal ideals in both read-only project source trees found no declaration stating it. The existing `lem-weil-pbc-tensor-right-exact` and `lem-weil-pbc-localization-module-tensor` are Mathlib leaves and are reused.

3. WANTED

None. Every mathematical source used is in `literature/stacks-project/`.

4. Faults found and corrected

The imported item had no proof. I read the entire More on Algebra Fitting-ideals section around 07Z7, 07Z8, and 07ZA, checked each label against `tags/tags`, and wrote the proof. The ancestor/unit is `lem-trf-local-term-locality`/`sk-i-curve-zero`; the imported first-Fitting dependency lies below its nodal-family geometry route, with no separate Fitting clause in the ancestor text. I retained that ancestry and did not change any chapter, unit, target, or coefficient category.

Self-review removed a proposed intermediate node for stable equivalence of presentations: the explicit pair of invertible shears is a short elementary argument and is now Step 5. I also replaced an overly specialized determinantal node (which packaged conclusions too close to the item's clauses) with the generic finite-matrix inclusions of 07Z7. Thus the new node has no module, presentation, Fitting ideal, or base-change assertion. Step 6 now explicitly cites the existing tensor right-exactness theorem; the kernel after tensoring is the image of the old kernel tensored with R', not necessarily that tensor itself. Step 7 proves the determinant/base-change assertion directly from the Leibniz formula. I corrected an initial source-tag typo: 07Z6 is the section; the matrix-minor lemma is 07Z7. The item statement itself is correct and unchanged.

The inherited Mathlib search entries are retained as history. Fresh meaningful searches were run with `msearch.py` for the item and final new-node statement, with the actual results in the JSON and unchanged query logs. Two early dry runs found log-location/duplicate-report omissions, then missing definition citations and Unicode notation in the draft nodes; these have been repaired. No SGA source, Lean write, compiler, Lake command, or local preflight script was used.

5. Unfinished work

The one new generic matrix-minor node is intentionally statement-only. Its proof is the next stage-1 item; the current item's eight-step proof is complete relative to that statement and existing nodes. No mathematical question is left open for the current item.

## Not duplicates

The final new node cites 07Z7, not the item's 07Z8/07ZA; there are no existing DAG nodes carrying 07Z7 or `lemma-ideals-generated-by-minors`. I searched the entire DAG for the tag, that label, determinantal ideals, and matrix-minor keywords, and the whole blueprint using `blueprint_refs.py search '07Z7'` and `search 'ideals minors'` (both zero matches). I opened the relevant candidates below.

- lem-trf-fitting-ideal-minor-inclusions vs lem-trf-fitting-ideal-independence-base-change: the new node states generic inclusions for finite-matrix minor ideals; the item concerns equality of module-presentation Fitting ideals under changing a surjection and tensor base change. Neither conclusion of the item is a clause of the new node.
- lem-trf-fitting-ideal-minor-inclusions vs lem-weil-pbc-cauchy-binet: the existing statement is a determinant-of-product formula for rectangular matrices, not the descending or appended-column minor-ideal inclusions. It is a possible ingredient for a later split of the new node, not an exact or one-line specialization.
- lem-trf-fitting-ideal-minor-inclusions vs lem-weil-pbc-matrix-left-inverse-minors: that node relates a maximal-minor ideal to a matrix left inverse up to scalar; it does not state any of the three general minor-ideal inclusions.
- lem-trf-fitting-ideal-minor-inclusions vs def-trf-first-fitting-singular-subscheme: the existing definition constructs the first Fitting ideal of relative differentials and its closed subscheme, whereas the new statement concerns arbitrary finite matrices and contains no scheme or differential module.

## Review by Q78

I checked the item against 07Z8 and 07ZA(3), with More on Algebra 07Z7 and Algebra 00DF available in the local Stacks source. I read the item's two original definition dependencies and all added notion dependencies: finite free modules, matrices, submatrices, the Leibniz determinant, scalar extension, and principal localizations of rings and modules. I read the unit record and both master/current ancestor texts. The item is a generic algebraic support lemma for the imported first-Fitting construction; no unit-level proof step is replaced.

For the new node I checked all three assertions directly against `lemma-ideals-generated-by-minors` at 07Z7: (1) is unchanged, and transposing both factors in (2)-(3) changes “first rows” to “first columns” and `CA` to `AC`. Rows and columns are always finite; determinants of transpose are the same by the permutation formula. I kept the source's empty-minor value 1 and oversize-minor ideal 0. I tested `[a]`, `[a b]`, a zero matrix, the 2 by 2 diagonal matrix, empty rows, empty columns, r=0, oversize r, and square C=0/identity/invertible. In particular appending d columns can yield a unit only when the remaining required size r is zero, and the stated inclusion then has target R. The LeanFinder/LeanSearch results named `Ideal.matrix_monotone` and variants, which define ideals of matrices with entries in I rather than ideals generated by minors; I opened `Mathlib/LinearAlgebra/Matrix/Ideal.lean` and verified this distinction. Loogle's quoted minor search returns Lean recursor/version names and order-theory names, not a minor ideal. The source grep for determinantal/Fitting/minor-ideal names returns no hits. Two concept phrasings and all four search kinds are logged.

Step 1 uses the new node's definition of J_r to reconcile finite relation-row lists of any length with the item's r-row generators. Step 2 uses only the determinant definition: in a block diagonal matrix with an identity block, the Leibniz terms force the identity indices to be fixed, leaving precisely the old determinant. Step 3 uses exactly clause (2) of the new node on the matrix of arbitrary stabilized kernel rows; its first n columns really have rows in K. I treated n<=k separately, selecting t of the d new identity coordinates when 0<t=n+d-k<=d; this repairs a possible negative-minor-size gap. Step 4 uses exactly clause (3), then its application to C inverse; no claim about arbitrary row operations is taken from a definition.

Step 5 uses the basis definition of finite free modules to choose f and g lifting finitely many images under surjections. I checked the displayed inverse of U by substitution and the intertwining equation: pi'(y)+pi(x-fy)=pi(x). This carries the actual embedded kernels, so it avoids misusing the existing abstract Schanuel statement, which says only K plus P2 is isomorphic to L plus P1. The shears and their inverse are a few lines of calculation, so no extra node is justified. With Steps 2-4 they prove presentation independence.

Step 6 cites the full statement of `lem-weil-pbc-tensor-right-exact` with K -> R^n -> M -> 0; all its hypotheses are present, and no flatness or finite generation of K is needed. The tensor definition supplies both pure-tensor generation and the displayed coordinate identification, whose inverse I checked on pure tensors and standard coordinates. Step 7 cites the determinant's actual Leibniz formula; distribution over the finite row sums yields the displayed sum, and applying a ring map to that same finite formula yields the reverse inclusion using image rows. This remains valid over rings with zero divisors and for a non-flat quotient map. Step 8 cites the existing natural tensor/localization isomorphism, which explicitly carries pi tensor 1 to pi_g; this is exactly the compatibility needed, not just an abstract module isomorphism. The quotes in `citations.json` are copied verbatim from these statements.

I tested the item on M=0, M=R free with pi the identity (I_0=0, I_k=R for k>=1), M=R/(a) (I_0=(a)), redundant generators and different source ranks, n=0, n<=k, the zero ring, arbitrary quotient base change, and localization at 0 or a unit. All eight steps have fewer than 2000 characters. The only new node has no proof and no hidden reference to an unspecified setting. The proof-dependency list is exactly the union of the uses, and no definition depends back on the item. Existing off-unit inputs are definitions or Mathlib leaves, so `split_report.tool_uses` is empty.
