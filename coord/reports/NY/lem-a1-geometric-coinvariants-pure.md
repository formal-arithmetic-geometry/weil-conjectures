# NY: lem-a1-geometric-coinvariants-pure

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-a1-geometric-coinvariants-pure.json`: item, split in five steps; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-a1-lisse-sections-stalk-evaluation.json`: new statement-only lemma, unsplit; no Mathlib match. It contains no weight claim: it supplies finite stalk detection, finite-dimensionality and evaluation compatibility with powers of Frobenius.
- `citations.json`: verbatim statement quotes for every citation in every item proof step.
- `searches.jsonl`: actual search-command log, preserved across the interruptions.

## Attachments

None. I read `WeilConjectures/WeilSheaf/GeometricCoinvariants.lean`, including the actual proof of `AlgebraicGeometry.WeilSheaf.isPureOfWeightOver_geometricCoinvariants` at line 275. The theorem has no textual sorry and its argument is useful reference material. It is not an exact attachment to the imported update: it has a section-level quasi-compactness hypothesis, and its `WeilSheaf` is the constructible pro-etale adic category (Category.lean:168). The current blueprint names the absent `AlgebraicGeometry.LAdicWeilSheaf.isPureOfWeightOver_geometricCoinvariants`. The DAG's traditional lisse convention is the finite coefficient-stage category in `def-pod-lisse-l-adic-sheaves`; I did not identify these categories by a renaming or assume an unproved realization comparison. The source declaration also does not itself state the connected fundamental-representation identification, which the item retains and explains separately.

## WANTED

None. The split is agent-written following the locally available current blueprint, with the source Lean used as reference for the finite-stalk argument. It does not claim to be a proof extracted from a human-written document. No SGA source is used.

## Statement corrected

STATEMENT-DISPUTED: the current `blueprint_update` drops the finiteness needed to make its conclusion a Frobenius module in the cited definition. Let X_0 be the disjoint union, indexed by the positive integers, of Spec(F_q), and take the constant rank-one sheaf with Frobenius the identity. This is locally of finite type and punctually pure of weight zero. Its global sections are the infinite product of copies of the coefficient field. Their algebraic dual is infinite-dimensional, so W is not a finite-dimensional Frobenius module in `def-weil-frobenius-module-weights`. The missing assumption is quasi-compactness. I replaced “locally of finite type” by “finite type”, equivalently quasi-compact and locally of finite type over the field. This keeps all smooth-curve applications and allows empty and disconnected schemes.

There is also a typing issue in the lisse convention used by this chapter: `rem-dl-a1-conventions` explicitly makes lisse mean `def-pod-lisse-l-adic-sheaves`, whose domain is Noetherian separated schemes. Accordingly the corrected statement explicitly works on separated finite-type schemes; separatedness here makes the given convention applicable, rather than silently extending it or changing to another coefficient category. The original curve statement, the unit's endpoint application, and the other three direct DAG users are in this domain. The generalized nonseparated statement would require a separately specified extension of that convention; this delivery does not supply one.

I also made the dual Frobenius explicit: F_W=(T^{-1})^*, the contragredient dual, not the transpose T^*. For X_0=Spec(F_q) and a rank-one pure sheaf with Frobenius alpha, the dual sheaf has Frobenius alpha^{-1}, so the coinvariants must have Frobenius alpha. The transpose-only reading would give alpha^{-1} and negate the intended weight. This is a clarification of the intended quotient action.

The current proof still speaks about a connected curve U_0 after its statement was generalized to X_0. A single constant quotient/stalk argument does not justify that generalization when Frobenius permutes geometric connected components. The repaired proof uses eigenvectors of global Frobenius and the local degree-power identity, which handles the permutations.

## Blueprint and duplicate searches

I read both the statement and proof under `literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-l-dl-a1-endpoints/`, the current unit statement, the recorded unit and chapter, and the chapter's coefficient conventions. I preserved the item's imported source and blueprint-update metadata; the split's proof sources and origin identify the current snapshot explicitly. The item is not the unit's key statement, so no unit realization record is written.

Whole-DAG searches included global sections, stalks, invariants, eigenvalues, geometric coinvariants, and the exact project declaration names. `tools/blueprint_refs.py search` was run for global sections, coinvariants, stalk, lisse, evaluation, sections, globalSectionsToStalk and stalk evaluation, and its ancestor command fixes the new node's ancestor as this item. No blueprint node states finite jointly injective lisse stalk evaluation together with the local Frobenius-power compatibility. The existing `p-real-sections` only identifies sections with invariants on an open of a smooth geometrically connected curve; it does not give the finite detection and compatibility theorem on general finite-type schemes.

## Not duplicates

lem-a1-lisse-sections-stalk-evaluation vs p-real-sections: the new lemma is a finite detection and local Frobenius-power statement on arbitrary separated finite-type schemes; p-real-sections concerns one connected curve and its fundamental-group invariants.
lem-a1-lisse-sections-stalk-evaluation vs cor-galois-lisse-representations: the latter gives fibre equivalences on connected schemes, not finite stalk detection and the geometric/global versus closed-point Frobenius comparison.
lem-a1-lisse-sections-stalk-evaluation vs aux-etale-global-sections-injective: the latter concerns abelian sheaves over Spec of a field with a stipulated discrete representation equivalence; it does not apply to these adic sheaves on a finite-type scheme or provide degree-power equivariance.
lem-a1-lisse-sections-stalk-evaluation vs lem-sc-etale-global-sections-galois-invariants: that statement also concerns Spec of a field and discrete integer representations, and provides no finite set of stalks or Weil comparison.
lem-a1-lisse-sections-stalk-evaluation vs lem-a1-geometric-coinvariants-pure: the new lemma has no purity hypothesis or conclusion and no dual coinvariants; the eigenvector and weight argument stays in the item's steps 1–3.

## Review by NY

I checked B–E of delivery-errors against the written nodes, rather than treating the imported proof as already split. For the item I read the current blueprint statement and both proof paragraphs, and for the new evaluation lemma I read the actual construction in `WeilSheaf/Stalk.lean` (the finite evaluation family and finite-dimensionality) and the evaluation/Frobenius-power statement and proof in `WeilSheaf/StalkFrobeniusPow.lean`. I also read the eigenvector/stalk comparison and purity proof in `WeilSheaf/GeometricCoinvariants.lean`. These readings establish the intended mathematical subproblem but are not recorded as an exact Lean attachment in a different coefficient category.

Step 1 cites the actual statement of `lem-tw-dual-negation`, which supplies both that the dual is lisse and that it is punctually pure of weight -w. Its finite-type, finite-rank and coefficient hypotheses are all present. The new evaluation lemma then supplies finite-dimensionality, invertibility and the finite jointly injective family, independently of any purity. I did not infer these from a definition of global sections.

Step 2 uses precisely the evaluation and positive degree furnished by that lemma. For a nonzero eigenvector a, at least one evaluation is nonzero; the stated identity makes it an eigenvector with eigenvalue beta^d. I checked the equation uses the closed-point degree d and cardinality q^d, and wrote the positive-real power argument explicitly. The definition `def-weil-punctual-weights` supplies the local modulus equality, and `def-weil-frobenius-module-weights` supplies the meaning of the conclusion. No spectral semisimplicity is used.

Step 3 uses the inverse-eigenvalue formula that is explicitly in the statement of `p-linear-spectra`, and the purity definition, on a finite-dimensional space with invertible T as already proved. The final Frobenius is the contragredient action, so the weight sign reverses a second time. This is a short specialization of a cited linear theorem, not a new purity node restating the item.

Step 4 uses the exact tensor equivalence in clause (2) of `cor-galois-lisse-representations`; the geometric scheme is connected here, Noetherian and separated, and ell is invertible. The explicit section-to-unit-morphism and invariant-functional arguments are written out. The Weil degree-one operator is the one actually specified in `def-wf-fundamental-representation`; `def-real-weil-representation-operations` supplies the invariant, coinvariant and inverse dual-action formulas. Invariance of a functional is exactly its annihilation of gv-v, so the double-dual identification and maximal quotient property require no new lemma. All the displayed identifications are natural, which is what makes them respect the specified Weil isomorphism.

Step 5 uses clause (2) of `lem-sfb-finite-type-composition-base-change` for the geometric fibre, the statement of `lem-weil-pbc-finite-type-over-noetherian` for Noetherianity over the field, and the local-finiteness conclusion of `lem-sc-locnoeth-components-locally-finite`. Quasi-compactness gives finitely many irreducible components from this local-finiteness statement. The finite intersection-graph argument for connected components and the disjoint-cover gluing argument are both written out; no assertion from a cited node's proof is being borrowed. I read Stacks Tag 0052, label `topology-lemma-Noetherian`, including its finite-irreducible-component argument, as the topological source. Off-unit generic tools are declared in split_report.tool_uses for the maintainer's review.

I checked the empty scheme, the zero sheaf, a constant sheaf on a geometric connected component, the case Spec(F_{q^d}) with its cyclic Frobenius permutation of the geometric points, and a nonsemisimple Frobenius Jordan block. The argument only detects eigenvectors and does not require diagonalization. The infinite-disjoint-union test gives the explicit missing-finiteness counterexample above. The separatedness adjustment is recorded as a typing correction, not hidden as an innocuous restatement.

The new node has a self-contained statement, no proof or proof dependencies, explicit coefficient and scheme conventions, a precise blueprint ancestor/place and an empty same_as list after searches. It is neither an elementary few-line consequence of the cited nodes nor a new clause of the purity statement. Its general finite detection and Frobenius comparison are the substantive non-elementary input. Every Mathlib record corresponds to a query actually run with msearch.py; I read the hits, including Mathlib's representation invariants, topological section extensionality and ellAdicSheaf definitions. Those do not provide the lisse-adic and Weil comparison. No service failure was recorded as absence. No non-elementary step exceeds 2000 characters.

## Unfinished work

Only the new statement-level evaluation lemma remains unsplit, as required for one-level splitting. No Lean files, compilers or build tools were used. The report records the source discrepancy and coefficient-domain correction for independent maintainer review.
