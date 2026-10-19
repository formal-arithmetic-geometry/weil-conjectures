# Q33: lem-trf-etale-ring-map-weakly-etale

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-etale-ring-map-weakly-etale.json`: existing statement, now a Mathlib leaf. Exact match after the explicit lifting-hypothesis equivalence: `Algebra.WeaklyEtale.instOfEtale`, `Mathlib/RingTheory/Etale/Weakly.lean:55`, with the hypothesis conversion and the two projection declarations identified below. Zero new nodes; one Mathlib leaf.
- `citations.json`: `[]`, since a Mathlib leaf has no proof steps or cited proof nodes.
- `report.md`: this report. `searches.jsonl` was produced by the prescribed search command and retained unmodified.

## Attachments

None. Searched the exact blueprint id, the formal-etale lifting notion, weakly-etale ring maps and multiplication-flatness terminology in the project declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` (and Comparator), and read the relevant project `RingTheory/ProEtale/WeaklyEtale.lean`. The project file imports Mathlib's forward etale-to-weakly-etale instance and proves other assertions; it does not provide a project declaration with this item's complete hypothesis and conclusion. The Mathlib declaration is a leaf, not a project attachment. The upstream master checkout was treated as reference only.

## WANTED

None.

## Corrections and observations

The statement is true and is unchanged, including both independent flatness conclusions. There is no STATEMENT-DISPUTED and no change to the hypotheses or the unit/chapter route.

The inherited Mathlib searches said that no declaration gave the complete criterion. Targeted Loogle `Algebra.WeaklyEtale` finds `Algebra.WeaklyEtale.instOfEtale`, and the source itself contains the complete result. The inherited searches remain in the node as historical records; every search performed by Q33 is appended with the exact tool and query and the actual log record. In particular, the first natural-language searches did not find this instance, but a second phrasing and a direct name search resolved it. All services used here answered successfully; none was silently treated as unavailable or fabricated.

The source field is maintainer-owned and was preserved. Its citation to Cotangent Tag 08R2, case (5) reduced to (1), contains this fact only as the assertion that etale maps are a special case of weakly etale maps; it is not the most direct proof source. The direct sources, read locally, are Algebra Tag 00UR (`lemma-formally-etale-etale`, algebra.tex:41199), More on Algebra Tag 092N(2) (`lemma-when-weakly-etale`, more-algebra.tex:30454), and Definition 092B (`definition-weakly-etale`, more-algebra.tex:30189). More on Morphisms 094P is the analogous scheme definition, whereas 092B directly defines the two ring-flatness conclusions. No correction of the source text itself is necessary for the mathematics, and I did not edit this protected field.

## Not duplicates

No new node was created, so there are no new/existing node pairs to distinguish. Whole-DAG tag and keyword searches and `tools/blueprint_refs.py search` found `det-pe-morphisms-etale-comparison` (several scheme-theoretic assertions, including etale implies weakly etale and the affine criterion), `lem-weil-pbc-ind-etale-stability` (ind-etale and stability assertions), and `lem-weil-pbc-etale-ring-map-iff-etale-affine` (affine etale comparison). These are related, but none is exactly this standalone square-zero lifting criterion. They need not be used to detour through schemes when the precise ring result is already in Mathlib. The existing blueprint ancestry and its non-unspecified place were retained; `same_as` is empty. No unit realization field needs editing because this is a supporting node, not the unit's key statement.

## Unfinished work

None. No Lean file was written, no compiler/Lake/build tool was run, and no shared repository or launcher file was edited.

## Review by Q33

I read the worker brief, stage-1 rules, all of delivery-errors B through E, the three levels of SETUP, GOAL and dag-sync, and this item's chapter and unit before checking the mathematical claim. This review is my own self-check under the direct-delivery brief, not a claim of independent second review.

For the item I read Stacks Algebra's formal-etale finite-presentation equivalence at Tag 00UR and More on Algebra's weakly-etale definition and etale case at Tags 092B and 092N(2). The latter proof says that the multiplication map is itself etale as a map between etale algebras and hence flat. Cotangent 08R2 indeed treats the etale case as a special case of weakly etale; no cotangent-vanishing theorem is used in the leaf, avoiding any return through the parent `lem-trf-etale-cotangent-vanishing`. I also read More on Morphisms 094P to distinguish the scheme definition from the ring definition. There is no SGA source.

The replacement has no numbered proof steps because it is a Mathlib leaf. Instead I verified all parts of the match explicitly against the actual local Mathlib source:

1. `Algebra.FormallyEtale.iff_comp_bijective`, Etale/Basic.lean:86-94, has exactly the reduction map on algebra homomorphisms in the statement: composition with `Ideal.Quotient.mkₐ R J`, for every commutative R-algebra D and ideal J with J squared equal to zero. Thus the given bijection supplies precisely the formal-etale field, including uniqueness, rather than just formal smoothness. The theorem requires only test rings in a universe containing R and C, which the item's quantification over every R-algebra includes. No hypothesis about nilpotent ideals of higher exponent is substituted.
2. `Algebra.Etale`, Etale/Basic.lean:206-208, has only the formal-etale and finite-presentation fields. The given finite presentation is exactly the notion of the existing `def-weil-pbc-finitely-presented-algebra`, whose statement and Mathlib match I opened. Constructing this structure after applying the lifting equivalence introduces no extra algebraic theorem or geometric comparison.
3. `Algebra.WeaklyEtale.instOfEtale`, Etale/Weakly.lean:55-60, accepts exactly that Etale instance and concludes WeaklyEtale R C. I read its whole body. The two fields in the class at lines 38-39 are `Module.Flat R C` and `(Algebra.TensorProduct.lmul' R (S := C)).Flat`. The corresponding projections are `Algebra.WeaklyEtale.flat` and `Algebra.WeaklyEtale.flat_lmul'`. They give every clause of the item; the second is flatness with respect to multiplication from the tensor square, rather than flatness with respect to an inclusion of one factor. I opened `def-weil-pbc-flat-ring-map` and verified its statement and existing Mathlib match interpret these two outputs as exactly the stated notion of flatness. The Mathlib class docstring has a typographical codomain R in one sentence, but the actual field type and its surrounding module documentation both use codomain C, which is what I matched.

These source checks justify a leaf: after the explicit equivalence of lifting hypotheses and packing the two fields of Etale, the instance is one direct specialization; the conclusion is just the two fields of WeaklyEtale. No new lemma that restates the item or one of its clauses is needed. There are no proof citations, hidden non-elementary steps, long steps, off-unit tool citations, cycles, or new statements requiring their own definitions. `citations.json` is consequently empty, rather than containing quotes that pretend a definition proves flatness. The two statement dependencies were retained because their exact notions still occur in the statement.

I tested the unchanged statement at C=R, including a nonreduced base R=Z/4Z: the reduction map on R-algebra homomorphisms is between singletons, multiplication R tensor_R R -> R is an isomorphism, and both flatness clauses hold. For C=0, a homomorphism from C into D/J exists only if D/J is zero; if J squared is zero this forces D=0 (1 belongs to J and hence 1=0), so the lifting property holds, and both zero modules are flat. This confirms no nonzero-ring restriction has slipped in. As a negative hypothesis check, Z -> Z/pZ is finitely presented but fails the lifting property for D=Z/p^2Z, J=(p), since the identity modulo J has no lift; so the item does not falsely deduce flatness for this standard nonflat finite-presentation example.

B1-B9 are satisfied by a statement-only leaf, existing definitions, explicit file/line/declaration and real searches; B10 was checked by the project search. C1-C8 are vacuous for proof edges, while the actual Mathlib conclusion and both hypotheses were read instead of assumed. D1-D5 are avoided because no relabelled or circular sublemma was made. For E1-E6 I checked every ring, algebra structure, quotient, tensor-square map and hypothesis as above; E7 revealed no false source statement. The only repairs were the earlier missed Mathlib match and recording the direct source locations in this report.

## Dry-run repair

The first server preflight rejected a null `proof_origin`, even for this proof-free Mathlib leaf. I supplied the direct literature origin (More on Algebra 092N(2), with Algebra 00UR), retaining the empty proof and the exact Mathlib match. This is source metadata only and changes neither statement nor dependencies.
