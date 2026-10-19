# prop-trf-frobenius-factorization — NC stage-1 report

## Files written

- `dag/nodes/sec-six-functors/prop-trf-frobenius-factorization.json`: existing statement, now split in three elementary steps. Mathlib verdict: no exact result or one-line specialization found.
- `citations.json`: nine verbatim statement excerpts, one for each step/node citation.
- `report.md`: this report.

Zero new nodes; zero new Mathlib leaves. `prepare.py` is sandbox-only preparation material, and `searches.jsonl` is the search command's log.

## Attachments

None. I searched `WeilConjectures/` for the exact blueprint id and for the notion, then read `AlgebraicGeometry/{Frobenius,AbsoluteFrobenius,GeometricFrobenius}.lean` and the relative-factorization result at `SixFunctors/ProEtale/TraceFormula/Frobenius.lean:466–497`. The latter states the base-change description of a relative Frobenius into a twisted fiber product; it does not state this item's absolute/Galois factorization. `Scheme.iterateFrobenius` supplies the already attached absolute-Frobenius definition, not this equality. The equality in the implementation-notes paragraph of `GeometricFrobenius.lean` is prose, not a declaration. No project declaration stating every clause of this item was located.

## WANTED

None. All sources used are present locally.

## Problems found and corrections

STATEMENT-DISPUTED: read as a standalone proposition, the imported text has unbound symbols `X`, `q`, `Phi`, and `g_sigma`; its `stmt_deps` is empty. Its intended setup is in the immediately preceding blueprint definition. This is a scope/type problem, not a counterexample to the intended equality. I repaired it by explicitly quantifying the global finite-field datum and finite-type model `X_0`, setting `X=X_0 ×_(k_0) k`, and identifying the two endomorphisms and the absolute Frobenius through existing definition nodes. The equality, its range `m >= 1`, and the intended hypotheses are preserved. No target statement is changed.

The imported proof did not justify iteration, extension from pure tensors to arbitrary elements, or equality of scheme morphisms from the affine calculation. It also omitted statement dependencies on the finite-field setup and absolute Frobenius. The three steps now give these arguments. The equality is over `k_0`; neither the arithmetic Galois map nor absolute Frobenius is asserted to be a `k`-morphism. Arithmetic Frobenius is `b -> b^q`, with no inversion.

The container unit is the exceptional-pullback preservation proposition; this item is explicitly recorded in advance within it. I read `dag/chapters/sec-six-functors.json`, `dag/units/sk-prop-sf-rf-shriek-preservation.json`, and the current node/proof in `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/`. This is not the unit's key statement, so I changed neither its binding nor its realization. The chapter is preserved. The proof remains the blueprint's affine two-factor calculation; no off-unit theorem replaces a unit step.

## Unfinished work

No mathematical part of this one-level split is deferred. Existing definition nodes remain responsible for their own constructions and properties. In particular this proof never uses the finiteness or radiciality assertion inside `def-trf-scheme-frobenius`.

## Not duplicates

No new nodes were created. Whole-DAG and whole-blueprint searches for absolute Frobenius, scheme Frobenius and Frobenius factorization found the existing definitions and the relative-factorization nodes, but no other blueprint node stating this equality. The relative-factorization nodes have a twisted fiber-product target and are different statements.

## Review by NC

I read the current blueprint statement and its complete one-paragraph proof with the original item and the cited nodes open. I also read Stacks `varieties.tex`, tag 03SM (`definition-absolute-frobenius`) and its following paragraph, and tag 0CC7 (`lemma-frobenius-endomorphism-identity`); `schemes.tex`, tag 01I1 (`lemma-morphism-into-affine`) and tag 01HB (`definition-locally-ringed-space`); and `sheaves.tex`, tag 0091 (`definition-ringed-space`). The absolute Frobenius is identity on the space and a power map on sections; this is consistent with the affine incarnation in the item. No new-node source requires review, because there are no new nodes.

Step 1 uses `def-trf-scheme-frobenius`, which explicitly defines both product maps, the arithmetic substitution and the affine formula for `Phi`, and `def-weil-absolute-frobenius-scheme`, which explicitly says the model Frobenius is identity on points. Thus base-changed model affine charts are preserved, and the arithmetic map lies over the model identity. I checked that the chart maps are the ones the cited definition describes. I wrote the zero and successor cases of the iteration, rather than treating the exponent formulas as an additional theorem. The power identity in the induction requires only multiplication of exponents.

Step 2 uses that same statement for the factor maps, `def-weil-ring-frobenius` for the fact that the `p^(am)`-power map is a ring endomorphism, and `def-weil-pbc-module-tensor-product` for generation by pure tensors. I read each statement: the last one explicitly says it is generated by pure tensors, and the Frobenius node explicitly includes all nonnegative iterates. On each pure tensor both orders give exactly `u^(q^m) tensor b^(q^m)`. Tensor multiplication gives the same formula for its power, and additivity extends it to finite sums. No perfectness or reducedness of the model ring is used, and no linearity over the algebraic closure is claimed.

Step 3 uses `def-weil-absolute-frobenius-scheme` for restriction to affine opens and its affine power-map description; `def-weil-affine-spectrum` for contravariance and the uniqueness of a scheme map with a given affine ring map; and `def-weil-locally-ringed-space-morphism` for exactly the continuous-map plus sheaf-map data of a scheme morphism. All these assertions are in the cited statements themselves, not borrowed from their proofs. The affine-spectrum correspondence is already a Mathlib leaf. Equality on the cover implies equality of continuous maps pointwise, and equality of the sheaf maps follows by restricting to the cover and applying uniqueness of sheaf gluing. Finally `def-trf-scheme-frobenius` supplies the `k_0`-maps. No new gluing/existence theorem is invoked. The finite-field constants, exponent hypotheses and composition order have been checked throughout.

For B1–B10, I checked the scoped statement and its definitions, kept TeX as single escapes in the parsed strings, preserved imported metadata and the original source field, filled `blueprint.same_as`, and recorded only searches the command actually ran. For C1–C8, every mathematical input beyond the displayed elementary computations is an existing cited statement; there is no unsupported property, circular edge, or off-route theorem use. The citation file uses exact excerpts from those statements. For D1–D5, the argument remains in the item itself, with no clause moved into a new node and with both induction cases supplied. For E1–E7, I tested the hypotheses and examples below and found no false inference or altered coefficient category. The only scope repair is reported above.

Small cases: for the empty model, all maps and equalities are the unique empty-scheme map and the zero-ring calculation is harmless. For `X_0=Spec k_0`, `Phi` is identity and the factorization is the arithmetic Frobenius power on `k`. For `A_0=k_0[t]`, the formulas send `t` to `t^(q^m)` and a scalar `b` to `b^(q^m)`, so the arithmetic/geometric sign is fixed. For `A_0=k_0[e]/(e^2)`, nilpotents are killed by the power maps and both composites agree on them; injectivity is never assumed. No intersection of affine charts is asserted affine. The induction even includes `m=0` as an auxiliary calculation, while the item retains `m>=1`.

The Mathlib command ran two semantic phrasings, two Loogle queries, LeanSearch and source grep. I read the returned hit types: ring `iterateFrobenius`, finite-field Frobenius automorphisms, tensor-map multiplication/powers and purely inseparable field lemmas do not state this scheme equality. The scheme-Frobenius grep has no hits. No service failure was reported as absence. The exact tools/queries and returned names are in `mathlib_searches` and the search log.

## Validation

The required server checks and delivery dry run are being run by the second reader. No Lean source was written and no compiler, Lake or build command was run. No git command was run in the shared repository.

## Second reading by NC

- Item statement: checked against the current blueprint node and the finite-field, scheme-Frobenius, and absolute-Frobenius definition nodes; the finite-field datum, base change, map directions, exponent range, and both composition orders are explicit and consistent. The original unbound-symbol scope fault is repaired.
- Step 1: checked against the complete statement of `def-trf-scheme-frobenius` and `def-weil-absolute-frobenius-scheme`; the affine maps and the induction from exponents $q^m$ to $q^{m+1}$ are supplied, with no extra geometric hypothesis.
- Step 2: checked against the statements of `def-trf-scheme-frobenius`, `def-weil-ring-frobenius`, and `def-weil-pbc-module-tensor-product`; pure-tensor computation, finite-sum extension, and nilpotent edge cases are stated explicitly.
- Step 3: checked against `def-weil-absolute-frobenius-scheme`, `def-weil-affine-spectrum`, `def-weil-locally-ringed-space-morphism`, and `def-trf-scheme-frobenius`; affine equality is promoted to equality of scheme morphisms and the $k_0$-structure is retained.
- New nodes: none; therefore B1--B7, duplicate checks, and Mathlib-leaf checks introduce no new node to audit. Existing cited nodes were opened and their quoted statements match the uses.
- Edge cases: rechecked the empty scheme, $\operatorname{Spec}k_0$, a polynomial algebra, a square-zero nilpotent algebra, and the auxiliary $m=0$ induction case; all maps and equalities behave as stated.

Changes made during second reading: none. The worker's scope repair, three expanded proof steps, exact citation excerpts, and recorded search log already satisfy the delivery contract; no node or citation needed alteration.
