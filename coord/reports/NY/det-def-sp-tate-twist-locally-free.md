# Stage-1 report: det-def-sp-tate-twist-locally-free

Files written:

- `dag/nodes/sec-smooth-purity/det-def-sp-tate-twist-locally-free.json` — existing item, split into four proof steps; no new nodes.
- `citations.json` — verbatim citations for every node used by every proof step.

Attachments: none. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the blueprint tag and for Tate-twist/root-of-unity declarations; no sorry-free declaration states this item exactly.

WANTED: none.

The imported proof's citation to `lem-pur-finite-kummer-level` was removed: that node is restricted to the special rings `A_{E,n}`, whereas this item quantifies over every finite ring killed by a power of `ell`. Clause (2) is proved directly on the compatible-generator cover. The existing `lem-pur-twist-sheaf-locally-free` node is used as a cross-unit tool for the compatible root generators and the integral rank-one assertion; the maintainer should record that tool use at merge. I also restored the imported completed-integral-limit dependency in clause (3), since the coefficient line in that clause is the completed inverse-limit sheaf before localization.

## Review by NY

I read the target node, the chapter and `sk-prop-an` unit records, the main-20261015 blueprint statement and proof, and the full statements of `def-pur-roots-of-unity-sheaf`, `lem-pur-twist-sheaf-locally-free`, `det-prop-sfb-qlbar-colimit-x-integral-limit`, `det-prop-sfb-qlbar-colimit-x-invert-ell`, and `def-coefficient-twists-detailed`. I also checked the corresponding source prose in the blueprint files and searched the slopmaster2 source for the tag and candidate declarations.

Step 1 uses only clause (2) of `lem-pur-twist-sheaf-locally-free`: its single pro-etale trivializing cover and quotient isomorphisms provide the compatible images of (1), hence the ζ_n and their generator maps. Step 2 is elementary after that cover: both tensor products are the constant (A)-line, and the Kummer map sends the chosen generator to the chosen generator; local isomorphisms descend. I checked the edge cases (r'=r) and (A=0), where this is the identity map.

Step 3 treats the coefficients separately. The finite ring case is the same constant-line calculation. The cited integral clause of `lem-pur-twist-sheaf-locally-free` gives the completed rank-one line; `det-prop-sfb-qlbar-colimit-x-integral-limit` identifies the completed coefficient sheaf with its finite-level inverse limit, and `det-prop-sfb-qlbar-colimit-x-invert-ell` identifies its ℓ-localization with (E_X) and supplies flatness. The common-stage scalar-extension sentence of `def-coefficient-twists-detailed` gives the ℚ̄ℓ case. Each quote in `citations.json` is copied verbatim from the cited node statement, including the newly restored integral-limit and scalar-extension citations.

Step 4 follows the displayed definition of Λ(m) and K(m) in `def-coefficient-twists-detailed`. On a trivializing cover, tensor powers and duals of a free rank-one module are free rank one, evaluation is an isomorphism, and flatness identifies derived and ordinary tensoring; these local identities glue and give the inverse functor. I checked (d=0) gives the coefficient unit and that the two composites are the identity locally.

The mandated Mathlib searches for the item were run with `msearch.py`: LeanSearch query `Tate twists of roots of unity sheaves are locally free rank one and twisting is an autoequivalence` (generic cyclotomic and twist-shift hits only); Loogle query `Module.Invertible, SheafOfModules, tensor, equivalence` (0 hits; unknown identifier `tensor`); LeanFinder query `Tate twists roots of unity sheaf pro-etale locally free rank one` (generic cyclotomic-character hits only); and grep query `TateTwist|tateTwist|rootsOfUnitySheaf|invertible.*module` in `AlgebraicGeometry` (0 hits). No Mathlib declaration states this sheaf result.

What was wrong in the imported split: the finite Kummer-level node did not cover arbitrary finite rings, and the proof omitted the completed-integral-limit fact needed before inverting ℓ. Both are corrected above. The first reading did not change the statement and needed no new node; the second reading records and repairs the statement-scope defects described below, and nothing remains unfinished.

## Second reading by NY

- Item statement: checked against the main-20261015 blueprint node and `def-coefficient-twists-detailed`; the original statement left (E,\mathcal O_E,\overline{\mathbf Q}_\ell) unbound and asserted autoequivalences of ambient categories not defined there, so I repaired the quantifiers and category scope.
- Step 1: checked against clause (2) of `lem-pur-twist-sheaf-locally-free`; verdict pass, since its pro-etale trivializing cover and quotient isomorphisms give the compatible generators.
- Step 2: checked against clause (1) of the item and the Kummer transition definition in `def-pur-roots-of-unity-sheaf`; verdict pass, with the constant-line calculation written explicitly and valid for every finite commutative (A) killed by ℓ^r.
- Step 3: checked against clauses (1) and (3) of `lem-pur-twist-sheaf-locally-free`, `det-prop-sfb-qlbar-colimit-x-integral-limit`, `det-prop-sfb-qlbar-colimit-x-invert-ell`, and the scalar-extension clause of `def-coefficient-twists-detailed`; verdict pass.
- Step 4: checked against the displayed twist definition and category restrictions in `def-coefficient-twists-detailed`; verdict pass after stating the inverse equivalence on each defined coefficient category.
- New nodes: none; all cited facts are existing nodes, and the elementary calculations are retained in the proof steps.
- Kept the imported item's blueprint ancestry as `from: null` (the blueprint node is imported); the exact proof places are recorded in `split_report.blueprint`.
- Added the constant-sheaf and coefficient-twist definition dependencies needed for the repaired self-contained statement.

## Statement dispute

STATEMENT-DISPUTED: the imported statement did not quantify the coefficient data (E,\mathcal O_E,\overline{\mathbf Q}_\ell), and its final autoequivalence claim used (D(X_{\mathrm{proét}},E)) and (D(X_{\mathrm{proét}},\overline{\mathbf Q}_\ell)), whereas `def-coefficient-twists-detailed` explicitly says the bounded constructible categories are the only categories defined at those coefficients. The repaired statement fixes both defects while preserving the blueprint's intended theorem.
