# Worker report: thm-rp-real-lisse-purity-affine

## Files written

- `dag/nodes/sec-purity-real-sheaves/thm-rp-real-lisse-purity-affine.json`: existing theorem node, now `split`; no new nodes.
- `dag/units/sk-p-real-purity.json`: realized fields bind the theorem node to the unit statement and its four route steps.
- `citations.json`: verbatim quotations for every cited node in every proof step.
- `searches.jsonl`: four Mathlib searches run with `msearch.py`.

## Attachments

None. The reference declaration `AlgebraicGeometry.WeilGroup.isPunctuallyPure_of_isConstituent_of_isReal` in `WeilConjectures/EtaleCohomology/Purity/RealSheaves/Purity.lean` has a `sorry` body, so it is not a finished attachment.

## WANTED

None.

## What was checked and corrected

The statement was compared with the item source and with the current `main-20261015` blueprint proof. It is unchanged: it treats a smooth geometrically connected curve (possibly proper), reduces pointwise to an affine open, and concludes punctual purity of every irreducible constituent at its determinant weight. The Lean reference theorem has the affine hypotheses and is only a sorry-backed reference, so it supplies no completed proof.

The existing DAG nodes were searched by every cited id and by the blueprint references. All dependencies used below already exist; no duplicate or new statement node was needed. The proof source read was `literature/blueprint/main-20261015/blueprint/sec-purity-real-sheaves/sk-p-real-purity/thm-rp-real-lisse-purity-affine.proof.md` (Steps 0–4), together with the statements of each cited node. The imported proof was refined into sixteen steps, with the previously null elementary flag made explicit and the long exterior-power paragraph separated into the direct-sum eigenvalue step, determinant-product calculation, and dual lower-bound step.

## Review by N6

I checked the affine reduction (steps 1–5) against `def-weil-punctual-weights`, `def-wf-iota-real`, `lem-wf-dense-open-pi1-surjective`, `lem-wf-determinantal-weight-exists`, `def-wf-determinantal-weight`, and `def-real-weil-representation-operations`. The first node supplies the pointwise purity condition; the reality node supplies the characteristic-polynomial condition; the dense-open node explicitly gives exact restriction and preservation of irreducibility on curves; the determinant-weight nodes give the unique determinant purity weight and its normalization; and the operations node supplies determinant compatibility. The local-Frobenius identification in step 5 is the direct stalk identification and is marked elementary.

For the affine semisimple reduction and global estimates (steps 6–9), I read `lem-wf-real-semisimplification`, `lem-mg-normal-restriction-semisimple`, `def-rp-weight-blocks`, `lem-rp-upper-bound`, `p-linear-spectra`, and `lem-tw-dual-negation`. Their statements give respectively preservation of local polynomials and reality, geometric semisimplicity, the weight-block/rank-sum definitions, the eigenvalue upper bound by the largest determinant weight, inverse spectra under duality, and negation of the punctual weight under duality. The curve, smoothness, geometric-connectedness, lisse, reality, and nonzero constituent hypotheses are exactly those required by these uses. The ordering calculation that identifies the largest block weight is written inline.

For the exterior-power estimate (steps 10–15), I checked `cor-mg-det-weight-exterior`, `lem-rp-exterior-reality`, `lem-mg-exterior-direct-sum`, `def-real-weil-representation-operations`, `lem-wf-determinantal-weight-exists`, `def-wf-determinantal-weight`, and `lem-tw-multiplicativity`. The exterior corollary states the admissible rank-counted determinant sums; exterior reality and the upper-bound lemma apply to the resulting nonzero exterior power; the direct-sum lemma supplies the determinant-line tensor summand; the operations definition identifies top exterior powers with determinant lines; the determinant-weight existence/definition nodes identify each block determinant weight; and multiplicativity turns those weights into the displayed products of absolute values. The dual construction uses the same statements with inverse eigenvalues and negated weights. The rewritten steps are all under 600 characters except the routine bound step, so no hidden lemma is being concealed in an oversized paragraph.

Step 16 applies the definition of punctual purity to the two-sided equality and ranges over every nonzero block, giving every constituent the corresponding determinant weight. I checked edge cases in the route: a rank-one block (`n=0`), a single weight block (the exterior power is the representation itself), negative determinant weights (all inequalities use positive `q_x`), repeated constituents inside one block, and a proper curve (the affine-open reduction still contains the chosen closed point). No statement is weakened and no additional coefficient category is introduced.

The Mathlib searches found no theorem stating this project-specific purity result. LeanSearch and LeanFinder returned only generic irreducibility, scheme, and representation results; Loogle returned no result and reported the project identifier as unknown; the Mathlib grep found no matching declaration. These are recorded verbatim in `mathlib_searches` and `searches.jsonl`.
