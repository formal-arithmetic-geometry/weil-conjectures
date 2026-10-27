# Worker report

1. Files written: `dag/nodes/sec-six-functors/lem-pur-finite-geometric-purity-mate.json` (statement, split; no Mathlib match); `citations.json`; this report. The existing item was copied from the live read-only repository and all original provenance and searches retained. No new nodes, Mathlib leaves, unit edits or Lean edits.
2. Attachments: none. Searches of `lean/WeilConjectures/` for the blueprint tag and semilinear/retagging/purity terminology found no declaration giving all clauses. Existing generic orientation interfaces do not establish this normalization or the semilinear mate identity.
3. WANTED: none. The proof follows the current local blueprint, with the additional formal retagging calculation explicitly agent-written.
4. The imported item had a statement and searches but no proof. Its statement is unchanged. The split now distinguishes the original semilinear scheme square from its k-linear retagging, uses the unique counit-preserving adjoint identification, compares the tensor-map transpose explicitly, and retains the canonical Tate comparison. No statement dispute, source error, or route change was needed.
5. Nothing unfinished in this one-level split. The cited unsplit statements remain existing DAG work; none is duplicated or newly relabelled here.

## Sources and searches

Read the current source `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-factors.md` whole, its `_section.md`, and the ancestor `sec-six-functors/sk-thm-sf-package/thm-pur-weil-equivariance-of-purity-and-trace.proof.md` whole. Also read the chapter and unit records, the finite smooth-purity definition and theorem, and the statements of every cited node. These are the lecture-notes diagonal/deformation route already represented by the DAG, with no SGA citation. The proof is marked agent-origin because the supplied blueprint is agent-written and the retagging/mate calculation is expanded here.

Searched the whole DAG by retagging, geometric purity, orientation, exceptional base change and counit mate; ran `blueprint_refs.py ancestor` for the item and searches for purity, retag and counit mate. The existing `lem-pur-orientation-ground-field-retagging` handles the diagonal orientation, and `det-sp-purity-bc-factors` handles the two finite base-change identities and defines the exceptional exchange by its counit transpose. Their statements have been read; no replacement node is needed. The existing tower-only tensor-retagging result is not cited for a finite assertion.

The five new msearch invocations are recorded verbatim in searches.jsonl and the item, with actual results. Two semantic phrasings found ordinary etale algebra and scheme diagonal formulas, LeanSearch found smoothness stability and underived presheaf transport, Loogle purity found Lean compiler purity, and the source regex found no match. None states the derived purity normalization and counit-mate identity. The original item's searches are retained; they are not falsely represented as rerun by Q110.

## Not duplicates

No new node was created. In particular the existing orientation-retagging node, finite base-change factors node and right-adjoint uniqueness node are cited directly rather than restated.

## Review by Q110

I checked the requested B–E requirements against the actual statements and current blueprint. The finite ring is O_E/varpi_E^n, not a silently substituted ell-adic tower. All equalities are morphism equalities in the ordinary derived category, not merely per-degree consequences. No new unsplit node hides a proof, no new node is a clause of the item, and no elementary step has been promoted to a node. All eight proof steps are below 2000 characters.

Step 1 uses precisely the automorphisms, commutation and Cartesian assertion in `lem-weil-frobenius-square-cartesian`. The structural-map equation is its final particular assertion applied to the structure morphisms of X_0 and Y_0. I wrote out k-linearity and the finite-type/diagonal arguments so no k-linearity of the original semilinear automorphism is presumed. Retagging does not change the underlying smooth morphism or its relative dimension.

Step 2 uses the actual underlying-site constructions in `def-weil-pbc-proetale-operations` and chosen-compactification formula in `def-exchange-projection`. The same sites permit the same resolutions and adjunction maps. `det-sp-unique-right-adjoint` says both existence and uniqueness of the counit-preserving natural isomorphism, so this step does not invoke a merely fully faithful or merely objectwise uniqueness result.

Step 3 uses the finite-A clause of `lem-pur-orientation-ground-field-retagging` with sigma equal to geometric Frobenius; its hypotheses are the k-scheme and smoothness hypotheses already checked. Its statement compares exactly the normalized diagonal orientations under the same compactification and counit-preserving identification. Its tower clause is not used.

Step 4 opens the formula defining projection in `def-exchange-projection` and the formula for the tensor transpose in `def-pur-co-smoothness`. Equality under identity of sites is substitution in those formulas. I explicitly transposed both sides and used the counit equation to identify the resulting C_K maps. Then `def-pur-smooth-purity-map` gives the composite with inverse orientation and twist reassociation. No unexplained naturality of a chosen purity isomorphism is assumed.

Step 5 uses `lem-weil-l-adic-extension-integers-dvr` for finite residue field, the uniformizer filtration and maximal ideal; I corrected the initial draft that referred only to coefficient conventions for finiteness. The short filtration argument and ell in the maximal ideal establish the precise hypotheses of the finite-ring case of `det-sp-purity-bc-factors`. That node explicitly supplies the compact-support isomorphism and defines the exceptional exchange by the pulled-back counit followed by inverse exchange. The formula in `def-exchange-projection` is the same chosen-compactification formula used by B. I checked the direction and objects of the transpose and wrote the equation proving that postcomposition with rho gives the e_K of the item.

Step 6 uses the two displayed assertions of `det-sp-purity-bc-factors` separately, at the coefficient object and at arbitrary K. It substitutes them into the full formula of `def-pur-smooth-purity-map`; this is the requested argument rather than a new node restating the whole item. The additional factor b is displayed through the twist comparison, rather than suppressed by an ambiguous source identification.

Step 7 uses clause (3) of `lem-pur-roots-of-unity-inverse-image-iso` and clause (2) of `lem-weil-proetale-isomorphism-inverse-image` to identify the maps at roots of unity and their inverse limit. The tensor, quotient and power formulas in `def-weil-frobenius-coefficient-twists` define exactly tau_d. The canonical twist in `det-sp-purity-bc-factors` is therefore this map. This does not set the geometric-Frobenius scalar q^(-d) to one in a chosen constant basis; it shows no additional scalar is inserted into the specified sheaf comparison.

Step 8 applies the actual isomorphism assertion of `thm-pur-finite-coefficient-smooth-purity`. The site equivalence of `lem-weil-proetale-isomorphism-inverse-image` carries the same local constructibility and Tor tests, so PK remains in its domain. The final formula is cancellation of Q(Gamma_K), with no assertion that every mate of an isomorphism is invertible.

I tested d=0 (unit twist), K=0, empty X or Y, f the identity, n=1, ramified E and a nontrivial geometric Frobenius. No nonempty chart, positive dimension or unramified coefficient hypothesis is used. The argument for the root comparison works on each site object and hence retains its actual Weil normalization. For every cited step/node pair citations.json contains the verbatim node statement, including all clauses used. The generic off-unit tools are declared in split_report.tool_uses; this retains the package unit's imported smooth-purity/base-change route.
