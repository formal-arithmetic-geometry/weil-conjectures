# Q102 stage-1 delivery

## Files written

- `dag/nodes/sec-six-functors/lem-pod-smooth-oriented-exchange-comparisons.json`: split the item in six steps using existing nodes; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement quotations for every step/node pair.

## Attachments

None. Searches for the blueprint tag and smooth-oriented exchange in `lean/WeilConjectures/` found no declaration stating the item. The finite-coefficient `DualPerfect.lean` declarations concern dual-perfect identifications, rather than the simultaneous coefficient orientation and Verdier exchange squares at all four stages.

## WANTED

None. The proof is an agent expansion of the available blueprint and existing DAG interfaces, explicitly marked `proof_origin.by = agent`.

## What needed repair

The imported item was statement-only. Its distinction between site-perfect Hom on X, finite-Tor Hom at the point, and finite-quotient ordinary direct image is essential. The elementary operation-reduction lemma does not assert that last finite-quotient comparison. The split now cites the separate comparison theorem on its finite-Tor domain. The statement and its hypotheses are unchanged. The specified simultaneous integral family is retained; no uniqueness of integral lifts is claimed.

## Unfinished work

None for this one-level split. Existing cited nodes remain responsible for their own proofs. No Lean was written and no compiler, Lake, or local DAG/preflight checker was run.

## Not duplicates

No new nodes. The DAG and whole imported blueprint searches for `purity coefficient`, `smooth purity`, and `Verdier exchange` identified existing purity-transport and exchange interfaces, which are reused. Existing broader package statements are not replacement leaf declarations in Mathlib.

## Review by Q102

I read the item, its ancestor's second proof paragraph in `main-20261015/.../thm-pod-global-verdier-duality.proof.md`, the six-functors chapter and package unit, and the cited current blueprint proofs for operation reduction, finite purity reduction, adic reconstruction, rational purity, finite Hom and finite direct image. The supplied item is a refinement of the ancestor's coefficient-compatibility paragraph, not the package unit's key node; no unit realization record is changed. Every cited DAG statement was opened. There are no new-node source claims to audit.

Step 1 uses the exact commuting finite-reduction square in `thm-pur-finite-reduction-of-purity`, with f the smooth separated structure map and input the unit of Tor interval [0,0]. Its right comparison is the exceptional comparison at that unit. The inverse square is proved by composition with the two inverses; it is not a separately assumed compatibility. Pure dimension zero and identity coefficient change give the identity equations. Neither properness nor a model over a finite field enters.

Step 2 uses `thm-pur-adic-reconstruction` only for its specified lift and exact reduction property, which its statement expressly supplies. For integral extension `lem-pur-adic-purity-scalar-naturality` gives the simultaneous family and the exact equation, and its statement defines b by the counit transpose. I checked that these are h_Q and z_Q at the coefficient unit, not isomorphisms chosen by conjugation with purity. This avoids the invalid inference that equality of all reductions proves equality of arbitrary integral lifts. The coefficient extension may be ramified: the cited comparison is the completed/ordinary tensor identification already included in that node, not a new flatness assumption about quotient rings.

Step 3 uses the rational purity theorem for the rationalized map, `lem-pur-rational-scalar-comparison-identification` for actual localized operations and their counit-preserving exceptional mate, and `lem-pur-common-stage-smooth-operation-identification` for operation actions and preservation of equations represented at a common finite stage. The latter statement includes equations of compatible transformations, not just object formulas. The hypotheses are the simultaneous integral family already selected in step 2 and the separated finite-type smooth setting of the item.

Step 4 checks all finite-Tor intermediate domains with `thm-sf-ctf-stability`, including compact supports and internal Hom. `lem-fix-site-perfect-scalar-hom` really permits arbitrary coefficient-sheaf maps and uses precisely the site's perfect first variable K. At the point, `thm-coef-finite-hom` covers both finite sites and general finite-Tor inputs, including C; site-perfectness of C is not smuggled in. `lem-coef-finite-direct-image` explicitly covers its actual pro-etale counit-defined comparison. The input D_X K is finite-Tor by the cited stability statement. For higher stages `lem-fix-operation-reduction` explicitly covers integral reduction, ordinary direct image on its stated domains, and rationalized/common-stage comparisons with evaluation and units/counits. Taking n=m, n=1, or zero K presents no exception. In particular I never treat A_m as perfect or flat over A_n when m<n.

Step 5 cites `fix-cor-verdier-exchange` for its actual coefficient-compatible canonical exchange, not merely existence of some isomorphism. Its f and structure-map admissibility hypotheses are the item's hypothesis on a_X and the identity adjunction on s, for which the bound is zero. `def-sf-verdier-exchange-data` is used solely to specify the arrows (evaluation transposes and the counit-normalized ordinary-direct-image map), not as a proof of their compatibility: that is the exchange theorem's assertion. Expanding its input comparison requires precomposition by u_Q inverse, whose type is C' to Q_s C. The opposite direction would not type. All coefficient arrows are the actual maps covered by step 4.

Step 6 writes the identification of the final oriented comparison out. Transposing gives the two explicitly specified evaluation maps followed by h_Q Q(eta) and eta' z_Q; the inverse purity square proved above equates them. Uniqueness here is just injectivity of the closed adjunction's Hom-set bijection, not uniqueness of a reconstructed tower map. Naturality of ordinary direct-image comparison then supplies the displayed equality before pasting with step 5. Thus the final arrow is the tensor/internal-Hom comparison itself. This step is elementary relative to the already cited evaluation-preserving operation comparisons and the preceding purity square; it does not hide another geometric lemma.

Against delivery-errors B--E: all dependency statements were read and quotations in citations.json are literal; no elementary or duplicate nodes, no clause-renaming nodes, no missing coefficient-domain hypothesis, no unproved transport identification, and no circular citation were introduced. Reachability checks on every chosen existing dependency found no path back to this item. All six steps are below 2000 characters. The logged Mathlib searches include leanfinder twice, loogle, leansearch and grep; their hits concern general scalar adjunctions, orientations of modules, smooth rings, and manifold sheaves and do not state this item. The original item's prior search records were retained as provenance. No prohibited SGA source was used; finite purity remains on the diagonal/deformation route already specified in the item and its finite-reduction theorem.
