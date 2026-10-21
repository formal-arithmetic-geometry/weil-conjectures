# Stage-1 report: lem-weil-constant-scalar-strict-unit

## Files written

- dag/nodes/sec-smooth-purity/lem-weil-constant-scalar-strict-unit.json: existing statement split into six explicit elementary steps; not a Mathlib leaf.
- citations.json: one verbatim statement excerpt per step/node pair (17 entries).
- report.md: this report. searches.jsonl is the unmodified search-command log.

New nodes: 0. New Mathlib leaves: 0. The statement is unchanged.

## Attachments

None. Searches of lean/WeilConjectures for the blueprint tag, constantScalar, constant_scalar and strict-unit terminology found no declaration stating the item. The related theorem WeilConjectures.constantCoefficientScalarUnit_existsUnique in lean/Sheaf/Paper/ConstantCoefficientScalarNormalization.lean:59 has an explicit sorry at line 76, and does not prove the item's additional K-flatness and finite reduction clauses. It is background for the intended normalization, not an attachment.

## Literature wanted

None.

## Findings and changes

The item was unsplit, with no existing sandbox copy or report. Its inherited Mathlib searches were retained and the seven searches in this sandbox were actually run and read. Loogle supplies general mapping-cocone constructors; LeanSearch supplies generic complex constructors; LeanFinder supplies ordinary module flatness and homotopy-cofiber facts. None states the completed-ring-sheaf scalar normalization. The second phrasing and the SheafOfModules search likewise gave no match. The file-specific grep command prints its line numbers as file fields because rg omits a filename for a single-file input; this output was retained faithfully, and the candidate source itself was read at lines 27-128. No line number from that malformed display is used as a Mathlib match.

The original statement is true as written when derived scalar extension means change of rings from the completed sheaf, exactly as def-weil-integral-scalar-extension specifies. It must not be read as an assertion that a discrete constant sheaf is the completed ring sheaf. Every use of the symbol tensor over O_E in the proof retains that convention. The split never uses surjectivity of quotient projections, exactness of countable products, a derived-limit comparison, constructibility or a quasi-isomorphism of eta.

All steps are under 2000 characters. No separate lemma is hidden in them: the tensor identity is the balancing identity, K-flatness is the defining total tensor with a single nonzero term, transition compatibility is written on generators, and the cone argument is a two-term complex calculation. The existing unit record concerns a much broader ambient-adjoint datum; this worker changes neither it nor the chapter. The nearest blueprint ancestor is def-weil-ordinary-compact-cohomology. Its current snapshot path is under sec-six-functors-basics, and its coefficient-object paragraph (order 1869) is the place realized here. The imported unit/chapter and source metadata were preserved.

## Not duplicates

No new nodes. Whole-blueprint searches for “mapping cocone”, “regular module”, “scalar unit”, and “K-flat”, together with a whole-DAG statement scan for tensor units, flat regular sheaves and degree-zero K-flatness, found no blueprint statement equal to this item's combined strict normalization. Generic tensor-unit nodes concern other monoidal coefficient categories or much stronger constructions; no such identification is needed by the direct sheaf calculation here.

## Review by NP

I read Bhatt–Scholze, Definition 3.5.2 on printed p. 24 and Lemma 6.8.2(1), including its proof, on pp. 58–59. The former explicitly uses derived tensor over the completed ring, and the latter identifies the completed coefficient sheaf as the inverse limit. Neither claims the strict normalized cone map; that part is explicitly agent-written. I also read the current blueprint coefficient-object paragraph and the source/docstring of the sorry theorem ConstantCoefficientScalarNormalization.lean:49–76. For the elementary algebra I read Stacks sites-modules.tex, Tag 03EK (section-tensor-product), Definition 03ER (definition-flat), and sites-cohomology.tex Definition 06YN (definition-K-flat). There are no new nodes requiring separate sources.

For Step 1 I opened def-pur-sheaf-tensor-product, def-weil-presheaf-modules-sheafification, def-pc-flat-sheaf-modules, def-pc-tensor-complex-sheaves and def-pc-kflat-complex. They respectively define the sheafified tensor, its extension universal property, exact tensor-flatness, the signed direct-sum total tensor and acyclicity test for K-flatness. The proof supplies the inverse x maps to x tensor 1, rather than taking the flatness of the ring sheaf from a citation that only defines flatness. The total tensor has a single summand in every degree, so its differential is literally the original differential. This also proves flatness of the zero terms.

Step 2 uses the tensor and sheafification definitions and def-weil-integral-scalar-extension. I checked that the latter defines rho_m, the target coefficient-module structure and the K-flat termwise model over R_E. The two composites of the multiplication map and its inverse are calculated from balancing. Thus no flatness of the target quotient over R_E is asserted or needed.

Step 3 uses def-weil-integral-scalar-extension for reduction compatibility of rho_m and pi_m, def-weil-integral-derived-reduction for the identity K-flat model, and def-weil-integral-reduction-tower for the explicit formula c_m=[gamma_m][q]^{-1}. All three statements were opened. The proof displays the transition equation and evaluates u_m gamma_m on r. Choosing q=id is legitimate by Step 1, also when L=E.

Step 4 uses the coefficient maps in def-weil-integral-scalar-extension, limit projections in def-weil-completed-integral-coefficients and sectionwise linear morphisms in def-weil-sheaf-of-modules-category. I checked these statements before quoting them. The formula h_m(bs)=b h_m(s) uses exactly restriction along pi_m^L. Coordinatewise gluing constructs the product map without invoking an exact-product theorem. Its composite with 1-shift is zero coordinate by coordinate.

Step 5 uses def-weil-abstract-derived-category, whose statement includes the cone differential and signed shift, not merely the localization definition. The normalized strict cocone has graded coordinates B^n and B^{n-1}, with the sign in its first projection absorbed. In these coordinates the differential is (d_B x,Dx-d_B y); I checked the corresponding signed first projection and graded decomposition in Mathlib's MappingCocone.lean. Since B is in degree zero, the only nonzero equation for eta is D h=0, already explicitly proved. This establishes a strict chain map, rather than a morphism known only after localization.

Step 6 uses the same cone formula and the module-sheaf definition. Equality of both graded coordinates is equality into the direct sum, while equality of the product coordinates is equality of tuples. The source vanishes away from degree zero. The displayed linearity calculation proves that fixing the unit section on every site object determines every section, without wrongly assuming all sections come from a global constant element.

I checked B1–B10: no new statement-only obligations are needed, all additional notions cite existing definitions, TeX is singly escaped in the JSON, no false Mathlib match or unrun search is recorded, and blueprint ancestry is preserved. For C1–C8 I opened every cited statement and recorded verbatim excerpts; no proof of a cited node is used, no off-unit statement theorem is invoked, and there is no new edge back to this item. For D1–D5 the item itself contains every calculation and no content is moved into a new clause node. For E1–E7 I checked the actual coefficient rings and restriction maps, the cone degree convention, and the linearity argument. No statement dispute or weakening was required.

Small cases checked: L=E gives exactly pi_m, including m=1; ramification only changes rho_m and never requires quotient-flatness; disconnected site objects do not require sections to be constant; on an empty object or zero ring of sections the same identities hold with 1=0; arbitrary Y is allowed since all arguments are in its ringed site and no finite-type or qcqs property is used. The only correction during drafting was to make the cone's normalized sign convention explicit and to cite sheafification's universal property alongside the tensor definition.

## Unfinished work

None within the assigned one-level split. This is a stage-1 natural-language proof; no Lean files were written and no compiler, Lake or build tool was run. Independent maintainer review remains part of the delivery process.
