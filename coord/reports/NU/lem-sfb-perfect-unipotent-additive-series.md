## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-perfect-unipotent-additive-series.json: statement node split into five steps; no Mathlib match for the item.
- citations.json: thirteen step/node entries with verbatim quotes from the cited statements.
- report.md: this report. searches.jsonl is the search command's unmodified log.

No new nodes, no Mathlib leaves, no unit changes. The statement is byte-for-byte unchanged.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag, perfect/unipotent/additive-series terms, and unipotent found only unrelated biproduct unipotentUpper calculations, not a declaration of this result. Existing project declarations for affine-space smoothness and dimension are used through their existing DAG nodes, not claimed as attachments of the item.

## Sources and searches

Read Milne, Algebraic Groups (2017), printed pp.330--331: Theorem 16.21 and Corollaries 16.22--16.24. Corollary 16.24 explicitly proves this by induction from the central additive subgroup. Also read printed pp.104--105 (5.20--5.29, quotient geometry and dimension), pp.24--25 (1.62--1.63, smooth quotients and kernels), p.114 (5.59, connected extensions and quotients), pp.281--283 (14.5--14.12, unipotence and field extension), and pp.297--298 (14.55, central additive subgroup; 14.58, additive groups). No unavailable literature is needed. No SGA is used.

Read GOAL.md, chapter/unit records, and the latest blueprint chapter, unit and direct-images proof. This remains the inherited supporting algebraic-group lemma of the alteration prerequisite chain; it changes no chapter or unit route. blueprint_refs ancestor returns None, as already recorded by from.node=null; the inherited precise place and via list are retained. Whole-blueprint searches for unipotent, central normal series and unipotent quotient found only the unrelated finite local-system filtration. The whole DAG contains the central Ga, affine-normal quotient, quotient image, and homogeneous dimension results already. In particular, the one central subgroup node is strictly weaker than the whole series and is reused, not recreated.

Ran leanfinder, loogle, grep and leansearch through the prescribed msearch.py command. The two natural-language phrasings ask respectively for a central series and a split-unipotent filtration. LeanFinder returns abstract nilpotent group central series; LeanSearch returns module filtrations, abstract group extension splittings, and Jordan--Chevalley/perfect-field facts. Those do not produce algebraic subgroup schemes, smoothness or represented Ga quotients. Loogle and source grep have zero hits. The item's inherited searches are retained; the new searches are appended with their actual queries and results. No new-node search record is needed.

## WANTED

None.

## Problems and corrections

The imported item had no proof. No mathematical statement dispute was found. The perfect-field convention in the existing central-subgroup node is given using pth powers rather than separability; step 2 writes the short equivalence implication it needs. The quotient-image node is only over algebraically closed fields, so step 3 explicitly applies it after base change, with its normal subgroup equal to its whole source, and uses the field-extension detection clause of the existing unipotent-to-multiplicative node. It would be incorrect to apply the quotient-image statement directly over the original perfect field.

The only off-unit nonclosed statement used is lem-sbc-smooth-fixed-dimension-over-field: a generic tool calculating dim(Ga)=1, declared in split_report.tool_uses. Affine-space smoothness is already Lean-closed, separatedness is a Mathlib leaf, and all algebraic-group results lie in the item's unit. The item is not the key statement of its unit, so no realized field is changed.

## Unfinished work

None at this splitting level. Existing unsplit prerequisites stay existing items; they are not resplit here. Stage 1 only: no Lean written, no compiler/Lake/build tools invoked, no repository or launcher files changed.

## Review by NU

I checked the proof against the actual induction in Milne 16.24 rather than replacing it with an invocation of a new series theorem. All non-elementary ingredients are existing nodes whose complete statements I opened. There is no new node restating a clause of the item. The five steps are each under 2000 characters and hide no additional comparison lemma.

In step 1, def-sc-gm-ga gives the polynomial affine line underlying Ga, sbc-lem-affine-space-smooth supplies relative smooth dimension one, and lem-sbc-smooth-fixed-dimension-over-field supplies its absolute Krull dimension; the identity supplies nonemptiness. I also read the existing upstream dimension theorem in lean/WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean to verify what the DAG node records. Affine-source separatedness is precisely lem-weil-pbc-affine-source-morphism-separated. The homogeneous-quotient dimension statement gives finite nonnegative dimensions even before the induction begins, by using the identity quotient by the trivial subgroup. Thus the induction is on a natural number, not an unspecified dimension. The trivial-group base produces an empty list of quotient requirements.

In step 2, lem-sfb-unipotent-central-additive-subgroup supplies a closed smooth connected central Ga under exactly the perfectness, smoothness, connectedness and nontriviality in force. I checked its Milne 14.55 source and the alternative 16.23 statement on p.331. Centrality gives normality on all algebras. The connected-rational-point node applies to the identity section over k, so its geometric connectedness conclusion is available to the affine-normal-quotient node. That quotient node explicitly supplies affineness, finite type, the kernel, faithful flatness, finite presentation and smooth/geometrically connected descent. None is inferred merely from the word quotient.

In step 3, I checked each variable in the algebraically closed quotient-image node: A is V over the algebraic closure, its normal unipotent subgroup is all of A, I=D is Q over that field, j is the identity and u=f is the quotient map. Faithful flatness survives because the quotient geometry node itself identifies the base-changed quotient. Its conclusion gives the required geometric unipotence. The unipotent-to-multiplicative node expressly states both the smooth geometric-matrix equivalence and detection under field extension; I use these clauses, not that node's unrelated vanishing conclusion. Proposition 5.23's existing homogeneous quotient node has no smoothness or normality restriction and gives the needed dimension equality. The represented fppf quotient is the same homogeneous quotient: coset fibres follow from the kernel and local lifts from faithful flatness/finitely presentedness. Since Ga has dimension one, dim(V)=1+dim(Q); this both makes the inductive call smaller and rules out a nontrivial dimension-zero case.

In step 4, I reread every clause of lem-sfb-affine-normal-quotient-geometry. It says that inverse images of normal subgroups are normal, inverse images are smooth connected when kernel and subgroup are so, and quotients of inverse-image pairs are the corresponding quotient pairs. Those are precisely the statements used to define P_i and obtain both P_i/P_(i+1)=Q_i/Q_(i+1) and V/P_(i+1)=Q/Q_(i+1). The final inverse image is the scheme-theoretic kernel N. Appending 1 adds one quotient Ga. This is the assembly in Milne, with all geometric properties cited.

Step 5 is elementary: it applies the already constructed group-scheme isomorphisms to products of sections on every test scheme, so centrality transfers on every base change. The final centrality is the chosen centrality of N itself. This avoids inferring scheme-theoretic centrality only from rational points.

I tested V=1 (m=0), V=Ga (quotient trivial, m=1), products Ga^d, and the three-dimensional upper unitriangular group, whose central Ga quotient is Ga^2. Positive-characteristic Witt unipotent groups are allowed: no assertion that V splits as a product of groups is made. Imperfect wound forms, nonsmooth alpha_p and disconnected constant p-groups are excluded by the stated hypotheses. No characteristic-zero assumption entered. The centrality calculation remains valid over nonreduced algebras. I checked that every cited node exists, is unmerged and has no dependency path back to this item; every quote in citations.json is literally in its statement. The union of the step uses is exactly proof_deps. I checked delivery-errors B--E, including absence of elementary/duplicate/new-clause nodes and the domain of each cited theorem.

The first dry run required longer citation excerpts for three short formulas; these entries now quote the complete cited statements, preserving literal text and making the supplied hypotheses visible.
The server wording check also rejected two occurrences of “the item's” in proof prose; these now spell out the induction class and refer to the explicit geometric-matrix criterion. Multi-clause citations for the central subgroup and quotient geometry now quote their complete statements.
