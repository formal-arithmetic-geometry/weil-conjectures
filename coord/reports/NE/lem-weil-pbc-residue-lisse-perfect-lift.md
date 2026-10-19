# Stage-1 report: lem-weil-pbc-residue-lisse-perfect-lift

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-residue-lisse-perfect-lift.json`: existing statement node completed as `split`; no statement or proof text was changed.
- `citations.json`: 37 step/node entries, each quoting the cited node statement verbatim.
- No new DAG nodes were needed: all notions and lemmas used by the six proof steps already exist in the shared DAG.

## Attachments

None. The read-only slopmaster2/source checkouts contain no declaration tagged `(blueprint: lem-weil-pbc-residue-lisse-perfect-lift)`; the archived upstream source is reference material and does not provide a finished declaration for this item.

## WANTED

None.

## Problems checked

The imported item already contained a six-step split and a complete dependency list, but its status remained `unsplit`; I corrected that metadata in the sandbox. I found no statement error, duplicate node, circular dependency, missing dependency, or SGA citation. The item’s blueprint ancestry remains `thm-weil-pbc-finite-extension`, with the stated local perfect-lifting place, and the existing `same_as` search is empty. Every proof dependency is an existing unmerged node. The item’s adic coefficient datum supplies the Noetherian, finite quotient, and adic-completeness hypotheses used by the completion and finite-level lemmas.

## Review by NE

I read the item node, its six proof steps, the unit `sk-thm-properbasechange`, and the chapter `sec-proper-base-change`. I checked every cited node’s statement in the shared DAG and wrote its exact statement into `citations.json`; the 37 entries cover all uses in steps 1–6.

Step 1 uses the weakly-etale localization equivalence to pass to a connected affine component, exact countable products and the derived countable-product core for the Roos calculation, the strict-tower homotopy-limit statement, and the constant/completed-coefficient equivalence to preserve completeness. The adic-coefficient-datum statement supplies the normalized quotient tower; `pqf-lem-locnoeth-lft` applies because the residue-trivializing etale maps are locally of finite type, and the etale-morphism definition supplies that hypothesis. I checked that restriction to the slice is exact by the section formula and that the argument does not replace the coefficient datum’s canonical transitions.

Step 2 uses the constant-completion comparison, exactness of finite constant sequences, finite-level site comparison, derived tensor descent, K-flat resolutions, the locally-constant derived Serre property over the finite Noetherian quotient rings, and the long exact cohomology sequence. I verified the induction starts with the given perfect residue model, that `J_n = I^n/I^(n+1)` is finite because it is a submodule of the finite quotient, and that the resulting bounds and finite locally constant cohomology are conclusions rather than extra assumptions.

Step 3 uses the pro-etale constructibility definition, finite-ring constructible derived origin, site comparison and finite-level comparison, derived tensor pullback, and nilpotent-reduction lissity. I checked the one-stratum constructibility argument on the connected neighborhood, the identity coefficient inverse-image, reflection of boundedness through the finite-level unit, and the normalization maps needed for the nilpotent-reduction theorem. The coefficient category remains the finite quotient category throughout.

Step 4 uses exact geometric stalks, ringed-topoi derived tensor pullback, the constant-sheaf geometric-stalk identification, finite-ring derived local constancy, the algebraic perfect inverse-limit reconstruction lemma, and the perfect-complex definition. I checked that stalk normalization maps are induced from the given quotient maps, not arbitrary choices, that the quotient cocycle is retained, and that the residue stalk is perfect before applying inverse-limit reconstruction.

Step 5 uses finite-ring derived local constancy and the compatible finite-derived-trivializations lemma. I checked the hypotheses: each finite-level complex is bounded with finite locally constant cohomology, the normalization maps and their cocycles are supplied, and the isomorphism sheaves have nonempty finite locally constant stalks. Thus one pro-etale cover gives compatible trivializations at all levels.

Step 6 uses the constant-module section properties, exact countable products, the derived countable-product core, the strict-tower homotopy-limit statement, constant/completed-coefficient equivalence, completed-constant reduction, the triangulated-category definition, and long exact cohomology. I checked the idempotent-summand argument for finite projective terms, sectionwise surjectivity of the reduction tower, the Roos `1-s` computation, flatness of the completed coefficient sheaf, and the morphism-of-triangles argument transferring the compatible tower isomorphism to the derived limits. The empty-scheme case is handled by the empty cover.

I also tested the stated edge cases recorded by the prior split review (empty `X`, zero and unit ideals, and a complete power-series coefficient ring) and found no change needed. The server-side `check_dag` preflight passed after the status correction.
