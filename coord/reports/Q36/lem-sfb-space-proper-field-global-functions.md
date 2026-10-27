# Q36: lem-sfb-space-proper-field-global-functions

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-proper-field-global-functions.json`: statement node, now split; statement and statement dependencies unchanged, no Mathlib match. Four proof steps, using existing nodes only.
- `citations.json`: twelve step/node pairs with verbatim statements or relevant clauses.
- `searches.jsonl`: actual five additional item searches from msearch.py, supplementing the imported search records without replacing them.
- `report.md`: this report. No new nodes, no new Mathlib leaves. No Lean written or compiled.

## Attachments

None. Whole-project searches for the exact blueprint tag and for global-function/properness terminology found no declaration for this algebraic-space statement. `AlgebraicGeometry.Scheme.globalSectionsRingHom_bijective_iff_geometricallyConnected` in `GlobalSectionsGeomConnected.lean:28`, and `globalSectionsBijective_iff_geometricallyConnected` in `GlobalSectionsProper.lean:57`, are scheme statements. They do not cover the item. Mathlib `AlgebraicGeometry.isField_of_universallyClosed` and `finite_appTop_of_universallyClosed` in `AlgebraicGeometry/Morphisms/Proper.lean:150,161` likewise concern integral schemes. They neither state nor specialize to the present algebraic-space assertion.

## WANTED

None.

## Problems found and corrected

The live item was unsplit, with an empty proof, but its statement is correct. It already explicitly assumes reduced, nonempty, connected base change to every algebraically closed extension. There is no released stage-1 repair note for it and no earlier sandbox split to retain.

The wording of Stacks 0DMY(7), “geometrically reduced and connected”, must be read as geometric connectedness as well. If “connected” were interpreted only over k, the conclusion would be false: take k=R and Z=Spec C. This is proper, nonempty, reduced and connected, and geometrically reduced, but Gamma(Z,O)=C. After algebraic closure its two points are disconnected. The proof of 0DMY(7) uses geometric irreducibility of the constants, established in (5) from geometric connectedness. Our item already avoids that ambiguity; no correction of its statement or weakening of its hypotheses is made.

I expanded two identifications that a compressed proof would hide: the affine evaluation of the small-etale flat-base-change isomorphism, and the fact that this comparison sends 1 tensor c to the structural section of c. The final descent is an explicit basis argument; no finiteness of A is assumed before it is proved one-dimensional. The long inherited provenance is retained, including from.node=null: the ancestor command prints None, not a missing id that may be invented. I read the latest blueprint's unit and direct-images proof, as well as the recorded chapter/unit; this is a proper field-fibre supporting input on the inherited chain, not a new route for the six-functor theorem.

## Unfinished work

Nothing needed for this one-level stage-1 split remains. The existing proper reduced connected function-field lemma remains an unsplit dependency owned by its own work item; its statement, rather than its proof, is used here.

## Not duplicates

No new node is created. `lem-sfb-space-proper-connected-function-field` already gives finite field-valued global functions under properness, reducedness and nonempty connectedness. Apply it over the algebraic closure instead of creating a second 0DMY leaf. `lem-sfb-space-flat-direct-image-base-change` already gives the degree-zero comparison needed; its affine evaluation is assembled using the existing scheme comparison and affine pullback-section nodes rather than introducing a specialization as a new node. The whole-blueprint searches “global sections” and “global functions” found scheme or curve statements, notably the Picard h0 nodes, but no equivalent algebraic-space blueprint node. The item’s same_as remains [].

## Review by Q36

I read Stacks `spaces-over-fields.tex`, Tag 0DMY (`lemma-proper-geometrically-reduced-global-sections`), its full statement and proof of (1)--(8). I also read `spaces-cohomology.tex` Tag 073K (`lemma-flat-base-change-cohomology`), its displayed comparison and affine-base clause, and Tag 08AS (`lemma-proper-over-affine-cohomology-finite`) behind the already existing finite-field lemma. For proper base change I read `spaces-morphisms.tex` Tag 04WP (`lemma-base-change-proper`). No new node has a source needing separate review.

In step 1, the algebraic-closure definition node explicitly includes existence of an algebraic closure. The locality/permanence node explicitly preserves properness under arbitrary algebraic-space base change, and does not require the base change to be finitely presented. The connected-function-field node says its global-function ring is a finite-dimensional field under properness, reducedness and nonempty connectedness. These hypotheses hold directly for Z_Omega by our item; there is no appeal to descent of reducedness, no assumed integrality, and no substitution of a scheme theorem for a space theorem.

In step 2, `lem-pc-finite-extension-alg-closed` explicitly makes the given field homomorphism from an algebraically closed field to a finite field extension bijective. I checked its Mathlib witness at `FieldTheory/IsAlgClosed/Basic.lean:220` and the precise hypotheses: the finite field B from step 1 is a domain and integral over Omega. Its actual structural homomorphism is used, so the one-dimensional conclusion is correctly Omega-linear.

In step 3, I opened all six cited statements. The field-extension-flat node supplies the flat scheme-base morphism. The quasi-coherence definition accepts the trivial presentation of the structure module. The direct-image theorem explicitly accepts a quasi-compact separated algebraic-space source, and yields quasi-coherence of N. I read its source `spaces-morphisms.tex` Tag 03M9 (`lemma-pushforward`). Properness supplies those two properties. The flat-direct-image node explicitly states the canonical adjunction-mate isomorphism for flat g, without any coherence or Noetherian assumption. I read `descent.tex` Tags 03DX and 03LC, `proposition-equivalence-quasi-coherent` and `proposition-equivalence-quasi-coherent-functorial`: the cited comparison node says its inverse is restriction to Zariski opens and that it compares tensor pullbacks for every scheme morphism. The affine-pullback-section node then gives the pure-tensor formula and bijectivity over the entire affine bases. Its source is Schemes Tag 01I9 (`lemma-widetilde-pullback`), with 01IA/01HV for reconstruction and sections. The map alpha is identified using the mate specified in the flat-base-change statement, not by claiming its proof gave an extra assertion. Its unit normalization is checked on the local tensor: pulled-back unit times c is the structural section c. Thus the argument uses no abstract unnormalized ring isomorphism.

In step 4, the basis-through-vector node explicitly permits a basis containing the nonzero unit. The scalar-extension definition explicitly states that tensors of a basis are a basis after extension. I read their Mathlib witnesses, `LinearAlgebra/Basis/VectorSpace.lean:52,90` and `LinearAlgebra/TensorProduct/Basis.lean:64`. The remaining argument is elementary: a second basis element in B is a multiple of 1, hence dependent; so A is spanned by 1. The nonzero unit is established from its image in B, and injectivity of k->A is checked by multiplying a putative nonzero scalar in the kernel by its inverse. This proves the specified structural map is bijective, and its inverse is a k-algebra map. I marked only this assembly step elementary; the substantial inputs have node citations.

For the B--E checks: the item introduces its own fields, maps and algebraic spaces, with notions explicitly defined or named in statement dependencies. Every non-elementary fact used in the proof is a cited statement, and citations.json copies its actual words; no citation reaches into another node's proof. No new statement-only nodes or Mathlib leaves are invented, so no clause is relabelled as a prerequisite. All sources are identified by tag and label; no SGA route is used. The off-unit QCoh direct-image, scheme comparison, and affine-section inputs are declared as generic tools in split_report.tool_uses, each for its particular role. No step exceeds 2000 characters. I checked the small cases: Z=Spec k gives the identity; an empty space is excluded by the nonempty geometric fibre; two geometric components violate connectedness; Spec k[epsilon]/epsilon^2 violates reducedness. A reducible but reduced geometrically connected proper space is allowed, and the proof never assumes it integral. Finite separable nontrivial constants and purely inseparable nontrivial constants are excluded by geometric connectedness and geometric reducedness respectively. There is no statement dispute in the item.

The searches added here were run through msearch.py with their exact logged queries. The two semantic phrasings returned scheme/ring results, Loogle returned no GlobalSectionsBijective hit, and the Mathlib source grep returned no algebraic-space hit. I read the relevant returned proper-scheme declarations before recording no match. I preserved the earlier item searches as provenance rather than representing them as searches I ran.
