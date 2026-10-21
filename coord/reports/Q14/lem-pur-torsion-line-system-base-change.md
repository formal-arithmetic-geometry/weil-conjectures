# Stage-1 report: lem-pur-torsion-line-system-base-change

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-torsion-line-system-base-change.json`: statement, split into eight steps; not a Mathlib leaf. Statement and statement dependencies retained verbatim. Filled the proof, proof dependencies, origin, split report and blueprint search result; retained all inherited searches and metadata and appended Q14's actual logged searches.
- `citations.json`: 18 verbatim statement quotations, one for each cited node in each step.
- `report.md`: this report.

No new nodes, no new Mathlib leaves, no Lean files, no changes to the read-only repository. `write_split.py` is a sandbox-only preparation script, not project tooling.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the blueprint tag, torsion-line-system names, and compatible torsion/tensor terminology. No declaration states this item. Generic pullback, scalar-extension and tensor results do not state its exponent-system and mixed-transition clauses.

## WANTED

None. The required source is available locally.

## Source and route

Read the chapter record `sec-smooth-purity`, the unit record `sk-prop-an`, and the current main-20261015 proof of `det-prop-sfb-cartesian-coefficients-twists`, especially its **Finite A** paragraph. This item realizes that paragraph's ordinary tensor argument; it does not replace the purity route. Read Stacks `sites-modules.tex`, Section 03EK, the balanced-bilinear universal-property display following Tag 0GMW (lemma-sheafification-tensor), and Tag 03EL (lemma-tensor-product-pullback), including the adjunction proof. The system coherence arguments below are explicit agent-written expansions of that source, so `proof_origin.by` is `agent`.

The blueprint ancestor command identifies `det-prop-sfb-cartesian-coefficients-twists`. Whole-blueprint searches for `torsion line`, `normalized tensor extension` and `compatible torsion` found no matching blueprint node; broader `torsion`, `exponent` and `tensor` searches located the Tate-twist and existing tensor infrastructure, which I read at statement level. Existing general tensor nodes make further nodes unnecessary. The item already has a precise `blueprint.from.place`, which is retained; `same_as` is empty.

## Problems found and corrections

The imported item is a statement-only node with no argument. I supplied the argument rather than moving its clauses to new nodes. There is no statement dispute: arbitrary modules, rather than locally free lines, are sufficient under the explicit reduction-isomorphism hypotheses already present. No assumption that the prime is invertible on the schemes is used or needed in this abstract tensor-system statement. The proof uses neither flatness nor pointwise detection of sheaf isomorphisms.

A key potential error was treating all sections of an inverse image or a sheaf tensor as single pure unit sections. Step 3 uses adjunction and the existing balanced-bilinear universal property instead. Likewise exponent independence is proved for the prescribed reduction map, not for an unspecified isomorphism. All coefficient comparison squares are checked against the constant-section normalization.

## Not duplicates

No new nodes were created, so there are no new/existing-node pairs to distinguish. In particular the existing `lem-pur-proetale-inverse-image-tensor-comparison` supplies tensor pullback, and `lem-pc-sites-sheaf-tensor-bilinear-universal` supplies balanced-tensor uniqueness. Neither is recreated or stated as a new torsion-system clause.

## Review by Q14

I checked sections B through E of `coord/delivery-errors.md` against the written node and the local sources, including the duplicate imported checklist. The source for the item is the Stacks tensor section and the blueprint Finite A paragraph described above. There are no new-node sources to audit. The JSON keeps single TeX escaping, introduces no new definitions, and preserves the complete original statement and its varying scalar rings.

Step 1 uses the statements of `def-weil-proetale-inverse-image` (the ring adjunction and its constant-section structure map), `def-weil-pbc-constant-sheaf` (sheafified constant presheaf), `def-weil-pbc-sheafification` (unique extension), and `prop-weil-pbc-proetale-constant-ring-map` (that particular comparison is invertible). These statements give exactly the adjunction and normalization needed. Comparing the two adjuncts on constants proves coefficient naturality; I do not assume it merely because two abstract ring sheaves are isomorphic. The maps from each residue ring to each coefficient ring exist because of the stated annihilation hypotheses and unital ring homomorphisms.

Step 2 uses clause 1 of `lem-pur-proetale-inverse-image-tensor-comparison` with the ring sheaf R_r and modules P_r and A, not a theorem confined to scheme isomorphisms or structure-sheaf modules. Its statement explicitly supplies invertibility and the local pure-tensor formula for an arbitrary scheme map. The second arrow and its inverse use the bijection in `lem-pc-sites-sheaf-tensor-bilinear-universal`, along the invertible coefficient comparison supplied by `prop-weil-pbc-proetale-constant-ring-map`. Semilinearity follows from the second-factor action. I checked that P_r is a module over R_r, A is annihilated by the same prime power, and the ring identification agrees with the module scalar square from step 1.

Step 3 uses the inverse-image adjunction stated in `def-weil-proetale-inverse-image` and the Hom/Bilin bijection stated in `lem-pc-sites-sheaf-tensor-bilinear-universal`. Giving the direct image the action through the coefficient map makes the adjuncts linear; naturality of the unit identifies their values on pure tensors. This proves an equality test and uniqueness in a few lines from those statements. It does not cite a definition as though it asserted a separate generation theorem.

Step 4 uses the same Hom/Bilin bijection. I wrote the balancing equation for a section b of R_s, checked semilinearity over A to B on the second factor, and used q composition and ring-map composition to establish the diagram laws on pure tensors. These are assumptions of the item, not hidden lemmas. The conditions s >= r, ell^s A = 0 and ell^r B = 0 are exactly what make the two scalar routes agree.

Step 5 uses that bijection twice to construct both directions of tensor reassociation, and checks both composites. In particular it does not apply an ordinary-module tensor identity directly to sections of an already sheafified tensor. Step 6 uses the reduction isomorphism assumed in the item and tensors its actual inverse. Its pure-tensor formula identifies the result with the already constructed exponent arrow. No unproved exactness or flatness assertion enters these steps.

Step 7 uses the inverse-image adjunction and the Hom/Bilin bijection as in step 3. I calculated both composites for every mixed transition, using the assumed c/q compatibility in the first factor and the proved constant-ring naturality in the second. This simultaneously gives all coefficient and exponent squares. Inverting the components of these actual squares proves that the diagram comparison is an isomorphism. There is no appeal to an unspecified coherence or an unstated comparison theorem.

Step 8 uses `sk-def-sfb-sheaf-tensor` for the abelian sheaf monoidal structure and `det-def-sfb-sheaf-tensor-local-iso` for monoidality of local equivalences. Together with the chosen small sites and universes these meet the stated hypotheses of `def-weil-pbc-internal-abelian-sheaf-module-equivalence` and `lem-pe-internal-section-tensor-comparison`. The former explicitly preserves underlying abelian sheaves and maps. The latter explicitly preserves relative tensors with the identity pure-tensor formula. I apply it over R_r to P_r and A and check the additional A-action by multiplication on the second factor. The equality test from step 3 then identifies both the comparison and all transition arrows in the two interpretations.

Each non-elementary fact is therefore an existing cited statement; each short elementary step writes its balancing, inverse, or equality calculation. `citations.json` contains quotations taken literally from those statements, not their proofs. Existing off-unit statements are declared as generic tool uses in `split_report.tool_uses`, with their roles explained; none changes the unit's purity route. I checked the dependency closures of the tensor-pullback, tensor-universal-property, and internal-comparison nodes: none depends on the present item, so these citations do not introduce a cycle.

I tested the identity scheme map, repeated exponents s = r, identity coefficient maps, a noninvertible coefficient reduction Z/ell^2 to Z/ell, zero modules, the zero coefficient ring, and the empty scheme. All formulas still define the prescribed maps; the empty-site and zero-module maps are the unique isomorphisms, and the mixed squares reduce to the stated c/q equation. Rank-one freeness is not silently used. All proof steps are below 1100 characters, so no step crosses the 2000-character review threshold or hides a long comparison argument.

## Unfinished work

None within this one-level stage-1 split. Existing dependencies retain their own project status. Required server dry run and delivery follow this report.

## Validation repairs

The first dry run rejected two constant-ring quotations as shorter than 40 characters. I expanded them to the literal defining constant-section map and its invertibility assertion, and made the tensor-structure and inverse-image adjunction quotations complete passages. The proof and statement did not change.
