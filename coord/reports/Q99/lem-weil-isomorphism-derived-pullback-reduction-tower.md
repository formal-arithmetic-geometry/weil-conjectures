# Q99: lem-weil-isomorphism-derived-pullback-reduction-tower

## Files written

- `dag/nodes/sec-smooth-purity/lem-weil-isomorphism-derived-pullback-reduction-tower.json`: existing statement split into ten steps; no Mathlib match. Statement and statement dependencies retained.
- `citations.json`: 24 verbatim statement quotations for the proof citations.
- `searches.jsonl`: the actual search-command log for this attempt.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the slopmaster2 project under WeilConjectures by the exact blueprint id and by reduction-tower, integral-reduction, and pullback/tensor concepts. There is no project declaration giving this entire completed-coefficient tower comparison with its resolution-comparison clause. Upstream master sorry declarations are not treated as finished proofs.

## WANTED

None. The argument is agent-written from the existing interfaces and Stacks source available here, rather than attributed to an unwritten blueprint proof.

## Findings and corrections

The item was a statement-only child of the previously split isomorphism-derived-pullback lemma; the sandbox had no prior node or report. Its statement is mathematically sound and was not changed. It is not itself the statement of its assigned historical unit, so no unit realization record is edited.

The actual blueprint ancestor is `def-weil-ordinary-compact-cohomology`. I read its main-20261015 coefficient-object paragraph: integral coefficients mean the inverse-limit coefficient sheaf. I also read the fixed chapter record and the assigned unit record. This split provides the tower calculation extracted by the parent, without changing the unit route. Blueprint searches for “reduction tower”, “isomorphism tensor”, and “K-flat comparison” did not identify an imported node stating the whole item. The already existing tensor and reduction interfaces suffice; no new lemmas were created.

The proof distinguishes the uncompleted constant sheaf from the completed coefficient ring throughout. Quotient and transition equations are interpreted after restriction to the completed ring; the final comparison equation lives in the finite-coefficient derived category. The tower-well-defined node supplies the meaning of the canonical comparison, not a theorem that this comparison commutes with inverse image. The last equation is proved here by a common K-flat refinement and explicit cancellation. In particular, no direct chain map between two arbitrarily chosen resolutions is assumed, and no proof of a cited node is used as its public interface.

The existing `lem-pur-isomorphism-inverse-image-tensor-hom` and general K-flat pullback theorem provide the relevant non-elementary facts. All off-unit statement tools are declared in `split_report.tool_uses`. The arithmetic finite-field parameters in the existing reduction conventions play no role in the formal change-of-rings calculation; no geometric finiteness, flatness of a quotient ring, or enough-projectives assumption is introduced.

## Mathlib and duplicate review

The searches were run only with msearch.py. Both semantic phrasings returned ordinary scalar-extension, flat-module or sheaf-equivalence results, rather than the complete statement here. LeanSearch returned the sheafCongr inverse functor and component formulas; LeanFinder returned sheaf-free-module formulas and ordinary adic-completion maps, then ModuleCat scalar-extension composition and module-flatness criteria. Loogle's first query had an unknown namespaced identifier and produced no hits; the corrected `SheafOfModules.pullback` query returned the pullback functor, identity, composition and sheafification comparisons. I read the pullback construction in Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean. It does not state completed reduction-tower compatibility or the K-flat resolution-comparison square. Both grep queries returned no hits in the specified module-sheaf subdirectories. Existing inherited searches were retained and the actually run searches appended with their exact query text.

## Not duplicates

No new nodes. The general inverse-image tensor theorem is cited, not restated as a new leaf; the canonical reduction comparison is cited only for its advertised derived-functor computation. The ten proof steps carry the argument of this item.

## Review by Q99

I checked B–E of delivery-errors against the finished node and opened the statements of all 15 distinct cited nodes. Each use is backed by its own verbatim statement quotation in citations.json. For sources I read Stacks sites-modules.tex, section-tensor-product (03EK), its bilinear universal property, and lemma-tensor-product-pullback (03EL); sites-cohomology.tex, lemma-K-flat-resolution (06YS), lemma-derived-tor-quasi-isomorphism-other-side (06YT), lemma-pullback-K-flat (0G7E), and lemma-derived-base-change (06YY); and derived.tex, lemma-acyclic (05RT) and lemma-find-existence-computes (06XN). The source of the complete assembly is the agent, with those exact tags recorded at the relevant steps. No SGA source is used.

Step 1 uses the inverse-image node's canonical limit comparison and ring-map naturality together with the completed-coefficient definition. This gives exactly the projection square, since its composite with every projection is specified; the inverse component maps show invertibility. Step 2 uses the tensor node's sigma and its local normalization, plus the sheaf-tensor definition, to check the balancing relation and construct the inverse by the inverse coefficient map. Step 3 uses the actual total-complex definition and the tensor node's naturality: the coefficient complex has only degree zero, so there is no unproved infinite-sum interchange.

Steps 4 and 5 use the actual quotient and transition formulas in the reduction-tower definition. I evaluated both sides on local tensors, using unitality and the inverse-image node's ring-homomorphism naturality. Equality descends from the presheaf tensor product by its sheafification universal property. The coefficient projection square ensures completed-ring linearity. Step 6 invokes tensor naturality on a chain map, and its explicit two-sided local formula agrees.

Step 7 uses exactness of abelian inverse image, the module category's sectionwise kernel/sheafified-cokernel description, and the exact-functor derived-factorization theorem. Thus applying F really defines a derived functor at both coefficient levels and sends the stated resolutions to quasi-isomorphisms. Step 8 uses the right MS2 clause and two-out-of-three of the quasi-isomorphism node; the K-flat-resolution theorem applies to the resulting complex on the small pro-etale ringed site. The general ringed-pullback theorem requires K-flatness and flat terms, both supplied for T. Its algebraic pullback is identified with the action-transport functor by the normalized scalar-extension ring-isomorphism lemma. This verifies K-flatness of F(T) without assuming it. K-flatness of F(P) and F(P') is already a hypothesis of the item.

Step 9 uses change-of-rings clause (1) for the reduced refinement maps and clause (2) for their canonical computations. The left-derived-computation node explicitly states a natural epsilon with invertible components on the computing class. The displayed algebra derives the roof formula for the particular comparison named by the tower-well-defined node, rather than claiming that node states inverse-image compatibility. The same calculation applies on X after checking all three K-flat inputs. Step 10 is precisely naturality from Step 6 followed by inversion and cancellation of these isomorphisms; it proves the final equation in the finite-coefficient derived category.

I tested the identity isomorphism (all coefficient maps reduce to identity), n=1, the zero complex, equal resolutions, and differing resolutions without any direct map between them. The argument needs no flatness of B_n over the completed ring, and no boundedness of P or T. Tensoring with B_n is computed from a K-flat source, so the quotient need not itself be K-flat over the completed ring. All steps are shorter than 2000 characters; the refinement and canonical-roof claims use cited general theorems and are not hidden new lemmas. There is no statement dispute and no unfinished mathematical clause.

## Unfinished work

None in the requested one-level split. Existing cited unsplit dependencies remain separate DAG items. Required server dry run and direct delivery follow this report.
