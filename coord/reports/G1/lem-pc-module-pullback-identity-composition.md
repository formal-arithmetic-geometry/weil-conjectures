# `lem-pc-module-pullback-identity-composition`

## Worker Notes

I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` with `rg -n -i` for module pullback, pullback identity/composition, and the blueprint tag `lem-pc-module-pullback-identity-composition`. No declaration states this item exactly, and no declaration carrying that blueprint tag was found. The search was read-only; no source build or edit was performed. The item therefore remains a DAG split rather than a Lean attachment.

The source does contain sorry-free uses of Mathlib's abstract `Modules.pullbackId` and `Modules.pullbackComp` (for example `WeilConjectures/AlgebraicGeometry/PicardFunctor.lean:263,269`), but those declarations do not state the tensor-formula functor `P_a` in this node, so they are not B10 exact attachments.

The source is `literature/stacks-project/sheaves.tex`. Tag 0097 (lines 3189–3202) states that pushforwards compose strictly and that pullbacks along a composite have a canonical isomorphism. Tag 0095 (lines 3116–3152) defines module pullback and pushforward. The proof uses the existing `lem-pc-module-pullback-adjunction` and the generic composite/identity adjunction statement `def-weil-pbc-composite-adjunction`: pushforward composition is checked sectionwise, and the generic uniqueness theorem `lem-weil-pbc-conjugate-iso-unit-equation` (Stacks Categories 0B65) gives both the identity and composition isomorphisms. That cited uniqueness node is already a reviewed Mathlib leaf, so it needs no extra `tool_uses` edge.

The Mathlib search found `AlgebraicGeometry.Scheme.Modules.pullbackId` and `pullbackComp` in `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean` (and the corresponding `SheafOfModules` declarations), but Mathlib's pullback is an abstract left adjoint rather than the displayed tensor formula. Thus these are candidates only; the Stacks adjunction comparison is required and no Mathlib leaf was attached.

## Review by G1

I read Stacks Tags 0095 and 0097 in `literature/stacks-project/sheaves.tex`. The item statement introduces the schemes, morphisms, module categories, tensor-formula pullback functor, and both natural isomorphisms exactly as the source's module pullback composition result. No extra hypothesis was added. The slopmaster2 search found no exact declaration or matching blueprint tag; abstract `Modules.pullbackId`/`pullbackComp` results are not exact statements of this tensor-formula node.

Step 1 uses the cited module-pullback adjunction and composite-adjunction definition to identify the identity pullback as a left adjoint to the identity pushforward; the cited uniqueness-of-left-adjoints node supplies the natural isomorphism. Step 2 checks pushforward composition sectionwise, then applies the same two adjunction statements and uniqueness theorem to the composite. The sectionwise equality is elementary from inverse-image and restriction along the composite ring map; all other nontrivial facts are cited statements. The left-adjoint orientations are correct: $P_g\dashv g_*$ and $P_h\dashv h_*$ compose to $P_gP_h\dashv h_*g_*$. 

Against A-F/B9/B10, this is one item and one report with no new nodes, exact Tag 0095/0097 source places, valid TeX, no cycles, and an explicit whole-source attachment audit. The split is a genuine proof expansion, not a restatement. I checked identity and composite edge cases and found no missing hypothesis or source error. The cited `lem-weil-pbc-conjugate-iso-unit-equation` is an existing reviewed Mathlib leaf, so no `tool_uses` field is needed. `review_split.py` and `check_dag.py --cycles` pass; preflight follows after rebasing.

