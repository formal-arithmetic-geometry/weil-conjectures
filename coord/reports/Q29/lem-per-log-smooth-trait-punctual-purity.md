## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-log-smooth-trait-punctual-purity.json`: item, split into three steps, statement unchanged.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-regular-log-smooth-monomial-chart.json`: statement; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-monomial-trait-punctual-purity.json`: statement; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-punctual-purity-etale-locality.json`: statement; no Mathlib match.

All new nodes are unsplit and carry statements only. The supporting search outputs and actual command log are retained in the sandbox; `citations.json` quotes each statement used by each item step. No unit realization was changed: this item is a supporting lemma, not the unit's key statement.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact item id, its blueprint docstring tag, logSmooth/LogSmooth, punctual purity and log-smooth terminology found no declaration stating this theorem. The rank-one Weil-weight purity declarations concern Frobenius eigenvalues, not local cohomology. The upstream master is reference material only, and supplied no closed attachment.

## WANTED

None. The complete ILO volume is available locally.

## Problems found and corrected

The imported item had a correct statement and no proof. Its source names Proposition 3.6.3 but the actual final reduction of Theorem 3.6.2 uses Proposition 3.6.5 and Proposition 3.5.12. I exposed these two inputs and the etale locality needed to pass through both arrows of a chart. The statement, finite coefficients, sign of the twist-shift, and absence of excellence remain as imported.

I checked the beginning of section 3.5 on printed p.248: its trait is arbitrary. The complete strictly henselian mixed-characteristic assumptions of the surrounding alteration argument must not be imported into this theorem. I also checked that the model with arbitrary multiplicities need not be smooth over the trait; only the chart arrow into the model is etale. No SGA source is cited or used for this split: the three inputs are located in ILO XVI.

An initial supporting source description referred to Theorem 2.3.2 for flat-base-change naturality. That theorem is the composition theorem. I removed this inaccurate reference from the locality node; its source is the explicit strict-henselization invariance after Definition 3.2.1 and its application on p.253.

## Unfinished work

No unfinished part of this item's one-level split. The three new lemmas intentionally remain statement-only for subsequent stage-1 splitting. No Lean was written or compiled.

## Not duplicates

lem-per-regular-log-smooth-monomial-chart vs lem-per-log-smooth-trait-punctual-purity: the new lemma is geometric and has no cohomological conclusion or coefficient prime; it produces two etale arrows and an explicit hypersurface. The item proves purity using this chart and two other results.

lem-per-regular-log-smooth-monomial-chart vs lem-trf-log-regular-completed-chart: the existing statement concerns completed strict local rings and Cohen/monoid presentations of arbitrary log-regular schemes. It does not produce an etale morphism into a monomial hypersurface over the original trait; a formal completed chart would not supply Step 1.

lem-per-regular-log-smooth-monomial-chart vs lem-trf-face-localization-fs: the existing lemma is only the algebraic fs property of a monoid localized along a face, not a scheme chart theorem.

lem-per-monomial-trait-punctual-purity vs lem-per-log-smooth-trait-punctual-purity: the new lemma is the explicit polynomial model theorem ILO XVI 3.5.12, with arbitrary exponent tuple; it has no log-scheme hypothesis and is strictly the local-model input to 3.6.2, rather than another formulation of that theorem.

lem-per-monomial-trait-punctual-purity vs lem-per-gabber-regular-pair-purity: the existing absolute theorem is more general but is the ancestor whose proof depends on this item. Using it to prove this model would be circular. The new model theorem records the independent input 3.5.12 used before the alteration proof of the ancestor.

lem-per-punctual-purity-etale-locality vs lem-per-regular-immersion-class-calculus: the existing statement constructs classes and states flat/localization compatibility. It does not assert equivalence of punctual purity at points related by an etale map, which also requires comparison of the relevant local rings and detection after strict localization.

lem-per-punctual-purity-etale-locality vs lem-a1-finite-map-purity: the existing statement concerns Frobenius weights of finite-etale direct images of Weil sheaves; the new statement concerns exceptional inverse images of the constant finite sheaf on arbitrary Noetherian regular schemes.

## Review by Q29

I read ILO XVI printed pp.243--244 (Definitions 3.1.4 and 3.2.1--3.2.2), pp.248--251 (the scope of section 3.5, the model in Definition 3.5.11, Proposition 3.5.12 and its proof using Lemma 3.5.13), and pp.252--253 (Definition 3.6.1, Theorem 3.6.2, chart Proposition 3.6.3 and Proposition 3.6.5). The item is exactly Theorem 3.6.2 with the coefficient prime invertible and Noetherian regularity made explicit. The chart statement is Proposition 3.6.5, with an affine regular neighbourhood chosen by shrinking the etale neighbourhood; it does not assume strict semistability or bound the exponents. The monomial statement is Proposition 3.5.12 for F_ell. The locality statement is the pointwise consequence of the strict-henselization invariance explicitly stated on p.244: at corresponding geometric points of an etale morphism the strict local rings agree, so the same local supported class is being tested. It is recorded as a real input to split later, not called elementary here.

Step 1 uses the statement of `lem-per-regular-log-smooth-monomial-chart`: I opened the written node and checked that it gives the point above v, both etale arrows, a regular affine Noetherian U, and precisely the monomial model over the original S for the chosen uniformizer. Its log-smooth definition was copied from the item's explicit fs chart convention. Choosing a generator of the principal maximal ideal is elementary.

Step 2 uses the statements of `lem-per-monomial-trait-punctual-purity` and `lem-per-punctual-purity-etale-locality`. I checked that the former supplies regularity as well as punctual purity, and that its exponents are allowed to be zero, divisible by ell, or divisible by the residue characteristic. The chart supplies n >= 1 and a tuple not identically zero; the item's invertibility assumption passes through every R-algebra. The locality statement requires both schemes regular Noetherian; U has that property by the chart statement and T by the model statement. It asserts the pointwise implication used at every z in U, not merely a theorem about ordinary etale stalks or weights.

Step 3 again uses the full pointwise equivalence in the locality statement, now in the other direction along U -> V at u. Both schemes satisfy its hypotheses and the chart gave a(u)=v. Purity at an arbitrary point, rather than only at closed points of V, yields the required all-points assertion. None of the three proof steps exceeds 2000 characters or hides another comparison proved inline. Every non-elementary input is a named cited node, and I read back each verbatim quote in citations.json against its statement.

I searched the entire DAG for the source places 3.6.5 and 3.5.12 and for monomial, log-smooth, punctual-purity and etale-locality terminology. I ran `tools/blueprint_refs.py ancestor` on the item, and searched the whole blueprint index for monomial/trait, log-smooth and punctual/etale. The only relevant apparent overlaps are distinguished above; weight purity and completed log charts do not state these inputs. The generic absolute-purity ancestor is unusable as an input because it depends on this theorem. All three new nodes inherit the item's chapter and unit and its complete blueprint ancestry (with the item prepended to via); none repeats an existing blueprint assertion. I read the defining-node statements for regular schemes, residue fields, dimension, spectra, fs log structures, smooth and etale morphisms, and the regular-immersion class-calculus statement. These cover the notions actually used; no theorem is inferred from a definition alone.

For every new node I ran two distinct LeanFinder formulations, Loogle, a grep of the pinned Mathlib source, and LeanSearch with the required msearch command. I read all results: ordinary standard-smooth polynomial charts lack logarithmic monomial conclusions; standard-etale algebra and valuation declarations lack supported cohomology; polynomial monomial support is not sheaf cohomology with support; finestTopologySingle is an accidental substring hit on Gysin. All services answered, all three verdicts are no match, and no Mathlib leaf is claimed. Their exact query strings and full returned output are in the node records and the preserved search files.

I tested the statements on n=1,e_1=1 (the trait itself), n=2 with exponents (1,0) (an affine-line factor), n=1,e_1=ell (the ramified uniformizer-root trait), and e_1 equal to the positive residue characteristic (the potentially inseparable generic fibre). These cases require the general model theorem, not a smooth-generic-fibre shortcut. The all-zero tuple is explicitly excluded in both model inputs. For locality I checked the identity, an open immersion, and a finite separable residue-field extension; strict-local testing explains why the same twist-shift is used without demanding equal residue fields. Empty V and empty etale cover members are harmless; the proof chooses a point only after fixing v. No hypothesis or coefficient category was silently changed, no new node contains a proof sketch, and no new node cites this item or the absolute-purity ancestor as a dependency.

This is the authorized direct-delivery self-review; no second worker or sub-agent was started. The only correction during this review was the inaccurate supporting source reference described above. Server preflight and dry-run results are reported below after execution.

## Validation

The required `deliver.py Q29 lem-per-log-smooth-trait-punctual-purity --no-push` completed with exit 0 and printed `OK (not pushed)` at fbd3a2fe25: server preflight passed. The command's citation and recorded-search checks also passed. The final delivery command reruns the server gate on this report-inclusive commit.
