Files written:

- `dag/nodes/sec-trace-formula/lem-trf-finite-projective-bundle.json`: statement split into six steps; statement and hypotheses unchanged; no new nodes and no Mathlib leaves.
- `citations.json`: 16 verbatim statement citations, covering every node cited in each step.

Attachments: none. I searched the project declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the blueprint tag and by finite/projective-bundle terminology. The hits concern finite projective modules and blow-ups, and no project declaration proves this arbitrary finite-morphism projective-bundle statement. The read-only master reference also gives no attachment. The item has no existing Lean declaration listed to inspect.

WANTED: none.

What was wrong: the imported item had no proof. Its numbered Stacks citation was stale; the source now names Tag 0B3I and the actual label `lemma-finite-projective`, and Definition 01W8 clause (1). Its mathematical statement is correct and unchanged. No target or coefficient category is changed. Nothing remains unfinished in the stage-1 split.

## Proof and sources

I read Stacks `morphisms.tex`, Tag 0B3I, and the projective-bundle convention 01W8(1), together with `constructions.tex` 01OB. The proof keeps the source's witness E=h_*O_T and its canonical closed embedding into P(E). To verify that embedding explicitly, I form the graded algebra B with B_0=O_S and B_n=E for n>0 and show Proj(B)=T by homogeneous-prime and fraction calculations. The surjection Sym(E) -> B then gives the required closed immersion. This is an agent-written verification of the same embedding; `proof_origin.by` is therefore `agent`. It uses existing relative-Proj restriction and graded-surjection statements (Stacks 01N0 and 07ZI) and the standard-open chart (01M4). No universal-quotient theorem is silently taken from a definition.

The chapter and unit records, `sec-trace-formula` and `sk-i-curve-zero`, were read. The unit remains the contracting-correspondence route: this item is only the existing finite-projectivity tool in its Stein/alteration branch. No unit-level step is replaced, and the item is not the unit's key node, so no unit record is changed. I retained all inherited metadata and searches and filled the precise blueprint place. Blueprint searches for 0B3I, finite morphism, finite projective bundle and the affine algebra formulation found no equivalent blueprint statement.

The item searches ran through `msearch.py`: both semantic phrasings give absolute Proj or properness declarations, while the fully qualified Loogle query gives finite/proper criteria. I corrected an inherited grep's overly prefixed subdirectory by running the actual `AlgebraicGeometry` subdirectory and recording its zero hits. Neither Mathlib nor the project source supplies the item's exact projective-bundle factorization. Logged exploratory searches are retained even though no new node is delivered.

## Not duplicates

No new node is delivered. Tag 0B3I also occurs in `lem-wf-curve-normal-smooth-compactification` and `lem-trf-stein-smooth-generic-curve`; these are curve compactification/Stein statements, rather than another statement of this unrestricted finite-projectivity tool. The relative-Proj, chart, symmetric-algebra and module-coproduct facts are cited from existing nodes. The local chart calculation is written directly in the item's proof.

## Source error

In the stored Tag 0B3I proof, the sentence describing the map from the unit projective-space chart writes a map R[x_1,...,x_n] -> Sym_R^*(A) sending x_i to a_i. The intended coordinate-map target is A, not the entire graded symmetric algebra (the preceding sentence names X=Spec A). That typo is not reproduced. Also, a closed immersion into the unit affine chart alone gives an immersion into projective space; global closedness needs the source's proper-image argument. The delivered proof establishes global closedness instead by a surjective graded map, whose Proj is already identified with T; it never drops the closed-image issue.

## Review by N8

I read the statement of every cited node in full. The 16 citation entries copy those statements directly, so they can be checked verbatim. I checked B--E of `coord/delivery-errors.md` against the final six steps: no statement-only child has been created, no item clause is repackaged as a node, and all non-elementary sheaf/Proj facts are statements of existing cited nodes.

Step 1 uses exactly the finite-morphism definition's affine and finite-type quasi-coherent pushforward-algebra clause; it assumes no flatness, Noetherian base or local freeness. The projective-bundle definition permits any finite-type quasi-coherent module. Step 2 constructs B's multiplication and restriction maps explicitly from E. The graded-sheaf definition describes precisely these operations; the coproduct-closure lemma ensures quasi-coherence, and the affine tilde/global-sections equivalence with colimit preservation identifies its affine section algebra C=R plus positive copies of A. The grading is a categorical sheaf sum; the proof does not assume that arbitrary sheaf sums are sectionwise sums on non-affine opens.

Step 3 uses the sheaf symmetric algebra's universal property to construct q; the symmetric-degree lemma verifies the grading, and a[n]=q(j(a)j(1)^(n-1)) proves its degreewise surjectivity, with the identity in degree zero. The relative-Proj functoriality statement explicitly says that a surjective degree-preserving map induces a closed immersion in the opposite direction. All its hypotheses hold: both algebras are quasi-coherent graded O_S-algebras, the map preserves degrees and the base-algebra map, and no base-change theorem is being applied with an unstated flatness hypothesis.

Step 4 is the direct prime-ideal calculation: if t is in a homogeneous prime, the relation a[n]^2=t(a^2)[2n-1] places every positive homogeneous element in that prime. The definition of Proj excludes precisely those primes, so the entire space is D_+(t). The standard-open node supplies its scheme identification with the spectrum of the degree-zero localization. Step 5 proves the ring identification with A in both directions, including representatives initially in degree zero and the localization equivalence relation; multiplication by t preserves every positive coefficient, so there is no cancellation assumption. The spectrum node supplies the induced scheme isomorphism over R. These two steps are elementary uses of the stated definitions and chart theorem, with their arguments written out, rather than hidden new lemmas.

Step 6 uses the relative-Proj statement's affine restrictions and compatibility. On affine refinements of every overlap, the same coefficient formulas commute with restriction. The scheme-map gluing node gives both maps and uniqueness, proving the two composites are identities; no affine-intersection hypothesis is used. Finally, precomposing a closed immersion by an isomorphism preserves both conditions in the closed-immersion definition, and the projective-bundle definition gives exactly the item's conclusion. I declared every nontrivial generic off-unit tool in `split_report.tool_uses`; the definition nodes are notions, and no trace-unit argument is bypassed.

I checked the empty base, T empty over an arbitrary base (A=0), A=R (the identity), a non-flat finite quotient A=R/I, dual numbers over a field, and a product A=R x R. Keeping C_0=R, even when R -> A is not injective, is essential and is explicit in the construction. If A=0 then t=0 and Proj(C) is empty, so the calculation still works. No reducedness, surjectivity, flatness or global finite generating family is used. Every step is shorter than 2000 characters; the prime and fraction steps are direct calculations, not omitted comparisons. No SGA source, Lean writing, compilation, Lake, or build tool was used.
