# Stage-1 report: lem-sfb-perfect-coinduction-tor-independent-exchange

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-perfect-coinduction-tor-independent-exchange.json: statement item, now split into six steps; Mathlib searches found no match for the full item.
- citations.json: one verbatim statement quotation for each of the 20 step/node citations.
- report.md: this report. No new DAG nodes; zero Mathlib leaves created. Searches remain in searches.jsonl; write_split.py and repair_cycle.py are sandbox-only preparation code, with the latter recording the cycle repair.

## Attachments

None. Searches of lean/WeilConjectures/ for the exact blueprint tag, coinduction, perfect coinduction, Tor-independent coinduction and RHom base change found no declaration stating every clause of this item. Existing sheaf-coinduction adjunction declarations concern a different setting; they do not finish this derived module statement.

## WANTED

None. Both Stacks source files needed for the argument are present and were read.

## Corrections and source audit

The statement is unchanged. Its Tor-independence condition is essential. More on Algebra's equation-comparison-map runs from the base-derived tensor to the algebra-derived tensor, whereas the displayed theta in this item runs the other way. Step 1 defines theta as the inverse of that canonical comparison, rather than representing it by a chain map in the wrong direction.

I read dualizing.tex, section-base-change-trivial-duality, equation-base-change, lemma-check-base-change-is-iso and Tag 0BZP (lemma-bc-surjection), and more-algebra.tex, equation-comparison-map and Tag 0661 (lemma-base-change-comparison), together with equation-base-change-RHom and Tag 0A6A (lemma-base-change-RHom). Stacks uses unrestricted ring maps, assumes perfectness only for invertibility, and imposes neither flatness of the new base nor boundedness of the target complex. The construction is an actual coinduction mate in the algebra-derived category, so an underlying linear isomorphism is never used to manufacture a missing algebra action.

The blueprint's latest direct-images proof paragraph (3) is the inherited geometric route above this algebra prerequisite. The current item and its predecessor have an inherited null blueprint ancestor; blueprint_refs.py ancestor confirms None. I retained that field and recorded the exact current blueprint place and the inherited prerequisite purpose, instead of falsely labelling a new imported ancestor. No unit/chapter file is changed; this item is not the unit's key statement.

## Not duplicates

No new nodes were created. The existing lem-sfb-perfect-coinduction-tor-independent-base-change has a near-overlapping statement. The first dry run detected that the server's current version of that node depends back on this item; the local read snapshot did not yet contain that reverse edge. I therefore removed every citation of that node. The final proof instead derives the underlying comparison by explicit uncurrying of the existing evaluation adjunctions and proves invertibility using the existing normalized finite-projective Hom-complex scalar-extension theorem. No near-duplicate theorem is assumed. The assigned item retains its own argument and all its clauses.
The DAG/blueprint searches also located existing lem-pc-perfect-ring-hom-scalar-extension, def-pc-perfect-rhom-base-change-map, lem-pc-perfect-ring-hom-kflat and the general Tor-independent K-flat resolution-tensor lemma. In particular no new lemma was introduced for the finite-projective formula or the generic scalar comparison. Whole-blueprint searches for coinduction, Tor independence and Hom base change supplied no imported statement covering all the item's clauses.

## Review by NI

I checked the delivery-errors B--E against the actual node statements and the source. There are no new statement-only nodes to audit, no relabelled child carrying the item, and no new search record without a corresponding invocation. The existing item search history is preserved; the five new command records are the exact queries in searches.jsonl, including the second semantic phrasing. LeanFinder returned cotangent and ordinary scalar-adjunction facts first, then K-projective/Ext facts on the second phrasing; LeanSearch returned generic derived-category and ring-map base-change facts; Loogle and grep returned no hits. These do not give the counit-defined coinduction comparison. No service failure has been called a negative search.

Step 1 uses lem-pc-kflat-resolution for resolutions of arbitrary complexes, not bounded ones. The statement of lem-pc-tor-independent-kflat-resolution-tensor explicitly allows an arbitrary A-K-flat Q and a base-K-flat quasi-isomorphism into its restriction, with no flatness of the rings. Its conclusion is exactly the quasi-isomorphism s tensor T needed here. Lem-pc-base-tensor-ordinary-iso gives the balanced complex isomorphism with the specified generator formula. Lem-pc-derived-tensor-second-factor-functor supplies the localized tensor functor and canonical comparisons of resolutions. The resulting theta is a map in D(T), and its orientation is checked above.

Step 2 uses the statement of lem-trf-derived-coinduction-adjunction: ordinary unbounded module categories, the actual right adjoint, specified precomposition action and evaluation-at-one counit. Its Hom bijection applies to X and Y as written. The two naturality squares are displayed in the step and transposed, so no claim about projective resolutions or perfectness is smuggled into the construction. The tensor functor's morphism action is precisely the other cited input.

Step 3 uses lem-trf-algebraic-shriek-derived-hom-adjunction for its actual evaluation-at-one Hom-complex isomorphism, with explicit inverse g maps to (x maps to (a maps to g(ax))). This is stronger than citing only the existence of an adjoint: it specifies exactly why evaluating after the algebra action equals evaluation at the argument. Lem-sf-ringed-derived-closed-symmetric-monoidal provides the natural tensor-Hom bijection and its specified evaluation counit. Uncurrying both comparisons therefore gives the same scalar-extended evaluation, so uniqueness identifies the underlying mate with the normalized perfect-source comparison of def-pc-perfect-rhom-base-change-map. No equality of algebra-linear derived maps is inferred from equality of their restrictions; this step only identifies the restriction of the already constructed mate.

Step 4 now proves the perfect case directly, rather than citing the near-overlapping base-change theorem. For arbitrary unbounded M choose Q K-flat using lem-pc-kflat-resolution. Lem-pc-ring-bounded-projective-extension supplies K-flatness of F and projectivity after extension; Tor independence makes F tensor T resolve A_T. The precise representative factorization of def-pc-perfect-rhom-base-change-map computes the underlying mate; lem-pc-perfect-ring-hom-kflat ensures its source is a correct scalar-extension model, and lem-pc-perfect-ring-hom-scalar-extension makes the chain map an isomorphism with no boundedness of Q or flatness of T. Conservativity explicitly stated in lem-trf-derived-coinduction-adjunction gives invertibility in D(A_T). The requested formula is the specialization Q=L[0], whose K-flatness again follows from bounded projectivity. Thus the proof does not impose boundedness on general M.
Step 5 uses the precise coordinate formula of def-pc-perfect-rhom-base-change-map. I evaluated both precomposition and postcomposition squares on z tensor s; the common formulas are written in the proof. This is the only step marked elementary: it is a direct computation from the cited formula followed by functorial localization. It does not claim that naturality of an arbitrary unnormalized representative follows by fiat.

Step 6 uses lem-pur-system-scalar-coherence for the canonical derived scalar associators and their compatibility with cochain comparisons. After identifying A_T with the first derived tensor, its successive tensor with T' identifies with A tensor_P^L T', so the stated hypothesis on A,T' supplies Tor independence for the second square as well. The equality of the two balancing maps is checked by the same pure-tensor formula. The adjunction statement makes transposition injective; substituting the counit equation twice gives the direct transpose. Generic off-unit inputs are declared in split_report.tool_uses; they are ordinary module/resolution tools, not replacements for the unit's geometric route.

Small cases: P=A gives the unit scalar comparison and the ordinary scalar adjunction. The zero complex and the zero coefficient ring give the unique zero comparison. For a nonflat but permitted extension take P=k[x,y], A=P/(x), T=P/(y): x stays regular modulo y, so the length-one Koszul resolution remains a resolution, and the displayed Hom formula is termwise the expected identity. By contrast P=k[x], A=T=k violates Tor independence: Tor_1^P(k,k)=k. The degree -1 contribution prevents theta for N=A from identifying the base-derived tensor with the degree-zero A-tensor. That case is excluded, as it must be. All uses of a bounded finite projective model are confined to the perfect case and the requested resolution formula; step 1 and step 2 remain unbounded throughout.

All six steps are shorter than 2000 characters. Sources and quotations were checked against the read clone. The only missing future proofs are those already represented by the cited existing DAG nodes; no claim of completed Lean proofs is made.

## Unfinished work

None for this stage-1 split. No Lean was written, no compiler/Lake/build tool was run, and nothing was written to the shared repository or launcher.
