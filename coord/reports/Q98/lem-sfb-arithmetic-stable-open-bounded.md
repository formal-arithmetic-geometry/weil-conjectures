# Q98 stage-1 report: lem-sfb-arithmetic-stable-open-bounded

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-arithmetic-stable-open-bounded.json`: statement, split into eight proof steps; no Mathlib match. The statement and its five statement dependencies are unchanged.
- `citations.json`: 21 step/node entries, each quote checked as a literal substring of the cited statement.
- `searches.jsonl`: the five Mathlib searches actually run by msearch.py in this attempt. Earlier searches in the live node are retained.
- `report.md`: this report. `write_split.py` is a sandbox-local writing aid, not a delivered project file.

No new nodes and no new Mathlib leaves. The proof uses 17 distinct existing nodes. No Lean was written and no compiler, Lake, build, local DAG checker or git command was run.

## Attachments

None. The project source search in `lean/WeilConjectures` for the exact blueprint tag and for stable-curve notions returned no declaration stating this item. The only broad stable-curve terminology hit concerned base change of an unrelated IsCurve morphism. Existing sorry declarations are not treated as finished proofs.

## WANTED

No additional document is required for this split. I read the local Stacks sources listed below. I did not claim to have read the archival Bourbaki PDF mentioned by the existing Hilbert-scheme node; that node is reused by its statement, while the boundedness argument follows the Hilbert construction explicitly present in the available Stacks proof of 0E96.

## What needed repair

The imported item had no proof. Its assertion is arithmetic and allows every scheme as a test base. The existing `lem-sfb-stable-and-smooth-family-open-loci` and `lem-sfb-nodal-curve-stack-smooth` both have a field-base hypothesis, so neither can be applied over the integers. I instead use the already existing arithmetic nodal-stack statement and the arbitrary-base h0/genus, dualizing, ample-locus and evaluation nodes. In particular I do not substitute relative ampleness for the requested global projective-bundle embedding: step 3 constructs that embedding with the same exponent 3 on every component of every base.

The boundedness proof expands the Hilbert-scheme construction in 0E96 used by 0E9B. It constructs the stable open V inside the fixed-polynomial Hilbert scheme, rather than citing a new node saying the stable stack is quasi-compact. No invocation of properness, a finite-type atlas, or quasi-compactness of the stable stack appears among its inputs.

The inherited blueprint ancestor is null: `tools/blueprint_refs.py ancestor lem-sfb-arithmetic-stable-open-bounded` printed exactly that null ancestor. I retained the existing from.node, from.place and via chain. The latest direct-image proof and unit were read; the arithmetic stable-moduli input remains in its existing alteration/level-structure prerequisite chain. Searches of all imported blueprint nodes for stable genus, prestable, tricanonical and Hilbert found no equivalent imported node (the Hilbert results concern other moduli functors or numerical notions).

## Source detail

The local proof of 0E9B uses P(t)=(6g-6)t+1-g. For a complete tricanonical linear system I use n=h0(omega^3)-1=P(1)-1=5g-6. The displayed source instead chooses the larger n=P(3)-1; that also allows an embedding by a linear inclusion but is not the minimal complete-system dimension. Its displayed pullback of O on P^1 has a superscript typo: the line is O on P^n. Neither issue changes the item statement, and I make no STATEMENT-DISPUTED claim.

## Not duplicates

No new node was created. Existing `lem-sfb-stable-and-smooth-family-open-loci` is restricted to schemes over a field; the present statement is over Spec Z and additionally proves algebraicity and quasi-compactness. Existing `lem-sfb-stable-moduli-regular-universal-atlas` is an ancestor that uses this item, so citing that atlas here would be circular. I checked transitive statement/proof dependencies of the proposed principal inputs: none reaches this item.

## Review by Q98

I read the statement against moduli-curves.tex Tags 0E76 (lemma-stable-curves), 0E78 (lemma-stable-one-piece-per-genus), and 0E9B (lemma-stable-quasi-compact), including their proofs. For the comparison of families I also read 0E6R and the relative-dualizing discussion, 0E74, 0E6U and 0E6V; curves.tex 0E8X; and spaces-descent.tex 0D3D and its fibre criterion. For boundedness I read moduli.tex 0E96 including its universal Hilbert family. I opened every one of the 17 cited node statements; below I specify what each step takes from them. There are no new nodes needing a separate source review.

1. `lem-sfb-arithmetic-nodal-curve-stack-smooth` expressly allows an arbitrary scheme S and gives algebraicity of the ambient category and the base-change-compatible nodal open. I instantiate S=Spec Z. `lem-sfb-curve-h0-genus-strata` expressly allows a proper flat finitely presented algebraic-space family with fibres of dimension at most one, gives schematic fibres, a universal scalar-H0 open, and the open-and-closed rank-g locus. Its final geometrically reduced fibre clause identifies the scalar-H0 condition with geometric connectedness. Nodal fibres meet that hypothesis. This realizes the prestable and genus loci of 0E6U/0E6V without applying the field-only sibling.

2. `lem-sfb-nodal-relative-dualizing-line` applies to the same proper flat finitely presented family, now with nonempty pure-one nodal fibres, and supplies the invertible line with arbitrary base change and the fibre identification. `lem-sfb-space-relative-ample-locus` is stated for a proper algebraic space over any scheme, gives exactly the factorization characterization and base-change assertion, and explicitly gives a schematic total space. The geometric fibres are schemes by step 1. `lem-sfb-nodal-canonical-positivity-tricanonical` has exactly the connected, reduced, proper, pure-one, algebraically closed, nodal, genus-at-least-two hypotheses in force, and its stability inequalities are the component inequalities of the unpointed definition. It also records the tricanonical conclusion used next.

3. The geometric H1 vanishing and very ampleness come from the last clause of `lem-sfb-nodal-canonical-positivity-tricanonical`, not from the definition of ampleness. `lem-sfb-fibrewise-very-ample-evaluation` is stated for schemes with these exact proper/flat/finitely-presented and geometric-fibre assumptions, and explicitly gives finite local freeness of E, the global closed evaluation immersion into P(E), and arbitrary base change. This avoids adding a quasi-compact or Noetherian hypothesis to A. No descent from field-valued projectivity is assumed.

4. I checked `def-sfb-stable-pointed-moduli-groupoids` and `def-sfb-stable-pointed-curve`: for r=0 the marking requirements are vacuous and the data otherwise match exactly. Their projective-bundle requirement is proved by step 3. In the reverse direction `lem-trf-projective-bundle-proper` supplies the properness needed to regard a stable scheme family as an object of the ambient category, and the positivity criterion supplies ampleness. The universal properties of N, B and A give both implications for every base map. `def-sfb-open-moduli-substack` says that the subcategory is full and characterized by these scheme tests; uniqueness of factorization through an open gives the indicated test groupoid. Scheme representatives and the same cartesian arrows yield the equivalence, with no quotienting of automorphism groups.

5. `lem-sfb-open-stack-algebraic-lfp` needs an algebraic ambient stack and open scheme pullbacks. The former is furnished by the arithmetic nodal-stack theorem (its ambient clause), the latter by step 4. I use only its algebraicity clause, not a finite-presentation assertion about this stack. The source is algebraic.tex 05UN, which is explicitly named in the step.

6. `lem-sfb-stable-curve-pluricanonical-linear-series` is applied only after steps 1--4 have established the stable family comparison. It is stated over every field and gives the exponent-3 embedding, h0=5g-5, H1=0 and the Euler polynomial 6(g-1)t+1-g. `lem-sfb-projective-hilbert-polynomial-dimension` equates that Euler polynomial with the coordinate Hilbert polynomial and gives dimension one for the universal fibres. The polynomial is nonzero since g>=2; the empty subscheme has zero polynomial. `lem-sfb-projective-hilbert-polynomial-representability` applies to the identity embedding of P^n over the Noetherian base Spec Z, and gives the universal flat finitely presented closed family with fixed polynomial and a finite-type representing scheme. `lem-trf-projective-bundle-proper` makes that family proper. Thus all hypotheses required to reuse steps 1--4 on H really hold. The elementary specialization n=3 in the pluricanonical formula is not a new lemma.

7. `lem-weil-pbc-finite-type-over-noetherian` states both the general Noetherian conclusion and explicitly the Spec Z instance, so I do not hide an arithmetic base hypothesis. `lem-weil-pbc-noetherian-open-subscheme-noetherian` explicitly says the open V is quasi-compact. Choosing a basis over each individual field and using the already cited Hilbert universal property gives a point lying in V and representing exactly the original curve. The step claims only surjectivity on field-point classes, which is all the proof needs. It does not claim V is a smooth atlas or infer representable surjectivity from the point calculation.

8. `lem-sfb-stack-point-topology` applies over an arbitrary base scheme, defines the same common-field-extension equivalence relation, and states continuity of every stack morphism for the smooth-atlas topology. It therefore supplies exactly the topology comparison, not the analogous field-only topology node. The finite-subcover argument is written out: pull back the cover, use V's quasi-compactness, and use point-surjectivity to push the finite coverage back. No topological compactness input for the stable stack is presupposed.

I checked B1--B10: no new unsplit helper, no unintroduced helper object, no fake Mathlib leaf, sources use verified Stacks tags/labels, TeX has single mathematical backslashes, and the original search/provenance fields are retained. I ran the required Mathlib tools and read all their hits; a second semantic phrasing returned Chevalley bounds and affine-space facts, not this moduli theorem. No service failure is recorded as absence.

I checked C1--C8: the non-elementary inputs above are all existing cited statements, proof_deps is their union, every citation has a verbatim quote in citations.json, and no cited statement is read as if it contained its proof's extra objects. The only off-unit proof citation is the generic projective-bundle-proper theorem, declared in split_report.tool_uses. No cycle is introduced. I did not modify a maintained tool or another node.

I checked D1--D5: neither a clause nor the whole theorem is moved into a new helper. The proof actually constructs the open and the relative embedding, and actually constructs the point-surjective finite-type parameter space. The repeated application to H uses the already completed open-locus construction, not the boundedness conclusion being proved. All eight steps are below 1000 characters, and none hides a long inline lemma.

I checked E1--E7 on empty T, empty fibres, disconnected bases with different fibre genera, nonreduced bases, reducible nodal fibres, and fields in characteristics 2 and 3. Empty fibres fail the nonempty nodal predicate, while the empty base factors through every open uniquely. Disconnected bases are handled by rank-g loci rather than an assumed global constant genus. Genus 2 gives h0=5, n=4, P(t)=6t-1. A genus-zero component with two nodal branches fails stability, while three branches pass; a genus-one component needs a branch. The exponent 3 is an ordinary tensor power, so no inversion of 3 is used. The construction preserves nilpotents in its open subschemes and all arbitrary-base-change statements are supplied by the cited nodes. These checks found no statement dispute.

## Unfinished work

None within the one-level split. The reused unsplit prerequisites remain their own items. Required server checks and direct delivery are run after this report is written.
