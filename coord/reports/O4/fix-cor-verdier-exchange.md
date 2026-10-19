# Worker report: fix-cor-verdier-exchange

## Files written

- `dag/nodes/sec-six-functors/fix-cor-verdier-exchange.json`: statement split; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement quotations for all cited nodes in all three proof steps.
- `report.md`: this report.

New nodes: 0. Mathlib leaves: 0. The item is not a unit key node, so no unit record was edited.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the exact item id, Verdier-exchange vocabulary, `verdierDual`, and the declaration names in the source. `AlgebraicGeometry.Etale.nonempty_iso_verdierDual_rightDerivedLowerShriek` in `WeilConjectures/SixFunctors/Etale/Derived/TensorHom.lean:397-403` has a one-line proof, but it is only a `Nonempty` isomorphism for finite commutative coefficients with compactification and quasi-compactness assumptions, while this item asserts a canonical isomorphism in the six-functor datum, with the stated admissibility hypotheses and coefficient compatibilities. It therefore does not state this item exactly and is not an attachment. The related declarations `nonempty_iso_rightDerivedUpperShriek_dualizingComplex` and `nonempty_iso_derivedHom_rightDerivedLowerShriek` likewise do not state the item.

## WANTED

None. The shared repository does not materialize `literature/`, so I read the canonical source at `/home/ubuntu/weil-launcher-nt/literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/fix-cor-verdier-exchange.md`, together with the chapter and unit records in the repository.

## Not duplicates

No new nodes were created. I searched the whole DAG and blueprint for `Verdier exchange`, `tensor-Hom exchange`, `Rf_* RHom`, and the cited Stacks/blueprint identifiers. `thm-sf-verdier-exchange` is a later summary theorem that cites this item, and `lem-sf-tensor-hom` is a different tensor-Hom route; neither duplicates this node.

## Review by N4

I read the item source, `sec-six-functors` chapter record, and `sk-prop-sf-biduality-general` unit record. The imported statement agrees with the source clause by clause: it uses the six-functor datum, exceptional admissibility of (f,a_X,a_Y), the two dualizing complexes and internal-Hom duals, the finite-Tor constructible input (M), and naturality plus finite-reduction, scalar-extension, and shift compatibility. I retained the source hypotheses and removed `def-weil-derived-pullback-tensor-hom` from `stmt_deps` because that operation is already supplied by the six-functor datum and is not needed to parse the item statement; `def-weil-exceptional-adjoint-admissibility` remains because “exceptionally admissible” is its notion.

Step 1 cites `thm-sf-comp-composition` for the canonical compact-support composition isomorphism and `fix-prop-adjunctions` for the pasted exceptional adjunction units and counits and their mate under composition. These statements give exactly the mate calculation identifying (Rf^!Ra_Y^!\Lambda) with (Ra_X^!\Lambda); the structure morphism relation (a_X=a_Y\circ f) is the one in the item setting. I checked that the composition node's morphism direction is harmlessly inverted when taking the mate.

Step 2 cites `fix-lem-tensor-adjunction`, whose statement is the isomorphism (Rf_*R\mathcal Hom_X(M,f^!N)\cong R\mathcal Hom_Y(Rf_!M,N)), and `def-weil-exceptional-inverse-image`, whose statement explicitly restricts (Rf^!) to bounded constructible and carries finite-Tor objects to finite-Tor objects. With (N=\omega_Y), the displayed exchange has the reverse orientation of the tensor-Hom node, so I corrected the proof to use its inverse. The second arrow is transport along Step 1, and the resulting source and target are precisely (D_Y(Rf_!M)) and (Rf_*D_X(M)).

Step 3 is now an explicit proof step rather than text hidden at the end of Step 2. It cites the tensor-Hom statement for naturality and coefficient/shift compatibility, and cites the composition and adjunction nodes for compatibility of the mate identification from Step 1. The three-step proof follows the source's three labeled steps and `proof_deps` is the union of the uses. Every citation in `citations.json` is a verbatim substring of the cited node's current statement; I opened each cited node and checked the quote against its actual JSON text.

I checked the coefficient and domain edge cases mentioned by the source: (M=0), identity (f), zero-dimensional schemes, and (n=1) finite coefficients. The formulas remain typed, and the identity case reduces to the adjunction's unit/counit identities. No new mathematical lemma was needed, so there are no new-node duplicate, source, or small-case obligations. The imported metadata and blueprint fields were preserved; `blueprint.same_as` is now the required empty list and the split report records the three source steps.

All required Mathlib searches for the item were run with `msearch.py`: LeanFinder returned only general category-theory/tensor-Hom declarations, Loogle returned zero hits with `RHom` unknown, Mathlib grep returned 25 generic Verdier/triangulated-category hits but no project-specific exchange declaration, and LeanSearch was unavailable and recorded as such. Since the exchange is project-specific, no Mathlib leaf is claimed.

## Dry run

The required command `python3 /home/ubuntu/weil-launcher-nt/deliver.py N4 fix-cor-verdier-exchange --no-push` printed `OK (not pushed) deliver/N4/fix-cor-verdier-exchange at 1d6ad32e6b: preflight passed`. The report was then checked against that accepted sandbox state; no node or citation changes were made afterward.


## Second reading by N4

- Item statement: compared hypothesis by hypothesis with the archived master blueprint `fix-cor-verdier-exchange.md`, the general-biduality unit and six-functor chapter records, and the current operation-datum and admissibility definitions; PASS, with all coefficients, the finite-Tor input, the dualizing definitions, and the stated compatibilities retained. This source is blueprint Markdown, with no Stacks tag in its `source` requiring a `.tex` comparison.
- Step 1: read the full statements of `thm-sf-comp-composition`, `fix-prop-adjunctions`, and `def-fix-six-functor-datum`; FIX. The composition theorem is finite-level and uses an etale-origin domain. At the other coefficient stages the argument now explicitly uses the composition law already supplied by the operation datum, and the mate is written as four Hom bijections with inverse directions checked.
- Step 2: read `fix-lem-tensor-adjunction`, `fix-prop-adjunctions`, and `def-weil-exceptional-inverse-image`; FIX. The constant coefficient object has Tor interval [0,0], the exceptional adjunction restricts to the finite-Tor categories, and the tensor-adjunction isomorphism is inverted in the displayed direction. Replaced the old citation of merely bounded constructibility by the exact finite-Tor preservation clause. Wrote the second arrow as the functor applied to the named mate.
- Step 3: read `fix-lem-tensor-adjunction`, the pasted-unit/counit clause of `fix-prop-adjunctions`, the coefficient-mate clause of admissibility, and all of `lem-fix-operation-reduction`; FIX. Naturality is the two bifunctoriality squares. Coefficient compatibility is the displayed identity between the two composites from C(f^!omega_Y) to omega_X, checked after the injective Hom adjunctions by the same pasted counit. Shifts are checked on each of the two arrows. The earlier composition-associativity quotation did not assert coefficient compatibility and has been replaced by citations that do.
- New nodes: none; checked the sandbox inventory. No new-node statements, duplicate checks, source-tag checks, or new-node Mathlib searches are therefore required, and no Mathlib leaves are claimed.
- Small cases: M=0 gives the unique zero-to-zero map; f=id reduces the mate to the adjunction identity and the exchange to the internal-Hom identity; the empty source has zero pushforwards and zero internal Hom, so the exchange is zero-to-zero; a point gives the coefficient dual of a finite-Tor complex; n=1 is allowed and no flatness of a quotient A_n to A_m is used. All constructions remain typed.
- Lean attachment: independently read the relevant finite-coefficient declarations in read-only slopmaster2 `WeilConjectures/SixFunctors/Etale/Derived/TensorHom.lean`, including lines 397-406, and searched its source by the item and exchange names. The `Nonempty` isomorphism there does not state the canonical, natural, all-coefficient exchange with the specified comparison clauses. It is not an exact attachment; no Lean was written or compiled.
- Citation audit: regenerated all ten quotes directly as exact substrings of the complete current cited statements and checked that each step's uses equals its citation inventory. The additional existing dependencies do not reach the item, so they introduce no cycle.

Changes and reasons:

1. Expanded Step 1 into explicit Hom bijections and named the operation datum as the source of composition outside the finite stage; this repairs the domain mismatch with the finite-level composition theorem without adding hypotheses.
2. Added the finite-Tor domain check for the dualizing complex and compact-support image, retained the first worker's inverse tensor-adjunction arrow, and specified the functorial second arrow.
3. Replaced the unsupported coefficient-coherence assertion by the mate identity and its common-counit verification, citing the existing operation-reduction statement for preservation of units and counits and the admissibility definition for the exceptional coefficient mates. No comparison is asserted invertible beyond its stated domain.
4. Regenerated `citations.json` and aligned `proof_deps` and `split_report` with the repaired three-step argument. The statement and the first worker's report sections are unchanged.

The existing `lem-fix-operation-reduction` is used as a generic comparison tool: it supplies preservation of the adjunction units and counits under coefficient passage, which is not in the composition theorem's statement. This keeps the unit's mate-and-tensor-adjunction route. Any required cross-unit tool approval is for the maintainer to record; no `tool_uses` field was written.
