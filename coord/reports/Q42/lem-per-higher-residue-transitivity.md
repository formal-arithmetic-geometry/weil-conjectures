## Worker report

Files written:
- `dag/nodes/sec-deligne-laumon-a1/lem-per-higher-residue-transitivity.json`: split item; unchanged statement; no Mathlib match.
- `citations.json`: verbatim statement passages for every proof citation.

## New nodes

None. Zero new Mathlib leaves. Creating a further general-transition node would duplicate `lem-per-normal-top-residue-class`, whose first paragraph already supplies prime-power transitions, their naturality, normalization, strict-local compatibility and composition. Creating a geometric chain lemma would duplicate the finite-factorization assertion already in `lem-per-general-costalk-transitions`.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the blueprint tag, higher residues, and residue/transitivity combinations; no project declaration states the item. The upstream master checkout is reference material only, not attachment evidence.

## WANTED

None. The cited Gabber volume is available locally and was read directly, after extracting its text to this sandbox.

## Corrections and reuse

The item had no proof. Its statement is retained verbatim: prime-power coefficients, arbitrary bounded-below complex, arbitrary cohomological degree, and specified geometric specializations are all retained. The proof now cites existing nodes rather than making a new copy of Theorem XVII.3.1.2. `lem-per-general-costalk-transitions` has prime-field coefficients, so it is used solely for its geometric finite-factorization sentence. Instantiating its complex by zero leaves exactly the geometric assertion needed; there is no scalar-extension argument or unjustified identification of coefficient categories.

The inherited `lem-per-normal-top-residue-class` says “with the identity when c=0”. This needs care: the source, XVII Remark 1.4.2, says transport in the absolute Galois groupoid. The proof uses the dependency's positive-codimension maps and compatibility with strict-local restriction, and defines zero-codimension transport directly on the geometric fibre. It does not deduce that every Galois element acts trivially. For example, over a finite field a rank-one finite etale local system with Frobenius acting by -1 (odd ell) has nonidentity Frobenius transport. If the dependency's “identity” is meant literally for every specified zero-codimension arrow, that wording is STATEMENT-DISPUTED; it should mean identity after the specified transport identification. This is a wording issue in an existing node outside this delivery, not a change or weakening of this item's correct statement.

## Searches and duplicates

Searched the entire DAG for residue/transitivity, higher-codimension transitions, and finite immediate factorizations, and opened `lem-per-normal-top-residue-class`, `lem-per-general-costalk-transitions`, `lem-per-geometric-immediate-catenary`, `lem-per-immediate-specialization-criterion`, `lem-per-regular-specialization-geometry`, and the potential-dualizing definitions. Whole-blueprint searches using `tools/blueprint_refs.py search` included `residue`, `transition`, `immediate specialization`, and `higher.codimension|costalk.*transition|transition.*costalk`; none is a blueprint statement equal to this item. Its nearest blueprint ancestor is `lem-per-artin-gabber-affine-curve`.

Five further Mathlib queries were run through the required `msearch.py`; their exact outputs are preserved in `search-0.txt` through `search-4.txt`, their command records in `searches.jsonl`, and their results and verdicts in the item. All services responded. Two semantic phrasings, Loogle, grep and LeanSearch found ordinary structure-sheaf stalk maps, residue-field maps, or unrelated group-cohomology text; none gives etale costalk transitions. In particular `Scheme.stalkSpecializes_stalkMap` and `TopCat.Presheaf.stalkSpecializes` have neither these costalks nor the shift by twice codimension, so they are not Mathlib leaves for this item. The earlier queries and results inherited from the repository were preserved.

## Review by Q42

I read ILO, Expose XVII, Definition 1.1.1 (costalks), Definition 1.4.1 and Remark 1.4.2 (normalization and geometric transport), Theorem 3.1.2 (printed p.268), and Definitions 3.5.1–3.5.2 and the end of the proof of 3.1.2 (printed pp.275–278). I also read XIV Section 2.1 for geometric versus Zariski specializations. The chapter and unit remain the affine-line perverse/Fourier route; this lemma is a tool on the existing finite-coefficient dualizing branch of its dimension-normalized Verdier-duality argument. No SGA source is used.

Step 1 uses the actual first paragraph of `lem-per-normal-top-residue-class`, not its normal-local-class conclusion or its proof. That paragraph has exactly the present excellent Noetherian scheme, invertible prime, ring Z/ell^n, arbitrary M in D+, arbitrary a, positive codimension and normalized immediate transitions. `def-per-potential-dualizing-complex` defines the same residue-field-valued costalks, geometric fibres, signed twists and immediate normalization. I read its full statement; it is not cited as an existence theorem for higher transitions. For codimension zero the proof writes the transport on representatives of the fibre colimit. The identity/Galois distinction above was checked against the source and made explicit.

Step 2 uses the composition and strict-local compatibility clauses of `lem-per-normal-top-residue-class` and the signed-twist convention of `def-per-potential-dualizing-complex`. I wrote the two intermediate cohomology groups explicitly: the second map acts on M(c) in degree a+2c, so its target is M(c)(d) in degree a+2c+2d. This is the exact final degree and twist. For an intervening zero-codimension arrow, strict-local naturality identifies the maps after its geometric-fibre transport. For two such arrows, functorial transport gives the formula on each representative section. This uses the dependency's stated restriction compatibility rather than claiming that naturality in M alone supplies Galois equivariance.

Step 3 is elementary from Step 2: the square has equal specified geometric composite arrows, so both paths give the map attached to that same arrow. I did not replace equality of geometric arrows by equality of underlying Zariski endpoints.

Step 4 quotes exactly the finite-factorization sentence in `lem-per-general-costalk-transitions`. I checked that this is a conclusion about the scheme and geometric specialization and has no coefficient or complex in it. Its hypothesis that ell be invertible holds here, and its prime-field derived object may be chosen to be zero. Hence this use is valid for the present geometric specialization without importing that node's prime-field cohomology maps. A zero-dimensional arrow itself supplies the transport, with no immediate steps.

Step 5 is a finite induction, with empty, one-arrow and successor cases written out. It only invokes the preceding established composition formula. Thus it proves independence of factorization and does not merely assert that “the same calculation commutes”. Every non-elementary input has a node citation, and `citations.json` copies contiguous passages from each actual statement. None of the five proof steps is over 2000 characters or hides a new lemma.

I checked the small cases c=0, c=1, c=d=0, an identity arrow, a nontrivial Galois automorphism, an empty immediate chain, n=1, and n>1. The statement does not assume regularity, normality, a global dimension function, finite type over a field, or a trivial stalk action. The existing normal-local top-class conclusion is not used, so its extra normality hypotheses are never imposed on T. Dependency closures were checked for a path back to the item, before submission. No new statement or hollow definition is introduced. No Lean file was written and no compiler, Lake or build tool was run.

## Unfinished work

None in this one-level split. The cited existing unsplit theorems remain their own stage-1 items; their proofs are not duplicated here.
