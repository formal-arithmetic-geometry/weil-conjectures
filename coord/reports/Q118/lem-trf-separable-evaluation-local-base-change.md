# Q118: lem-trf-separable-evaluation-local-base-change

## Files written

- dag/nodes/sec-trace-formula/lem-trf-separable-evaluation-local-base-change.json: statement, split, no whole-item Mathlib match; eight proof steps, no new nodes and no new Mathlib leaves.
- citations.json: a verbatim statement quote for every step/node citation.
- searches.jsonl: actual msearch.py results; inherited item searches retained in its JSON.

## Attachments

None. Searched WeilConjectures/ by the exact blueprint tag and by separable evaluation, local base change and faithfully flat concepts. No project declaration states the whole item. The existing Sheaf finite-separable-tensor-field-reduced declaration contains sorry, and is used through its existing DAG statement rather than asserted finished.

## WANTED

None. All mathematical source material used is in the read clone.

## Findings and corrections

The statement is correct and unchanged. The statement dependencies additionally cite the existing algebra-tensor pushout universal property: the module tensor definition alone does not specify the tensor ring structure or its evaluation algebra map. No source or blueprint error is claimed. The imported item had no proof; its current ancestor chain identifies the pointwise nodal field-change ingredient beneath local-term locality. I read the chapter and unit records and the current main-20261015 local-term-locality text; the local algebra here refines that existing chain and changes no chapter or unit route.

The dimension-equality hypothesis in Varieties 0C50 is deliberately not invoked: finite dimensionality of F tensor K implies directly that each prime quotient is a field. The prime r is then minimal, and the existing 00EU localization theorem supplies the field upstairs. No separability of K/k is assumed. No assertion that the whole tensor is a field is made.

Mathlib queries were run via msearch.py, with the actual results retained. The item searches returned integral-closure localization and unramified-residue criteria, not the whole statement. The quotient-localization searches were exploratory; their unknown-identifier Loogle response is preserved as returned. They led to no new node: the needed quotient-localization calculation is written explicitly using the fractions definition, in the pattern of Stacks 00CT. No new search was inferred from an unrun query.

## Unfinished work

None for the one-level stage-1 split. The existing finite-separable tensor reducedness lemma remains a separately queued/owned result. It is a generic tool of sk-thm-p1, declared in split_report.tool_uses; none of the trace-formula unit's own results replaces this algebra fact. All other substantive imported tools used here are existing Mathlib leaves.

## Not duplicates

No new nodes were created. Existing flat localized map, faithful flatness, finite-type Noetherianity, separable tensor reducedness, quotient base change and reduced minimal-prime localization nodes are reused.

## Review by Q118

I read Varieties Tag 0C4Y (lemma-change-fields-flat) and Tag 0C50 (lemma-change-fields-algebraic-unramified), including the affine proof and its omitted identification of the local fibre. I read Algebra 00CT (proposition-localize-quotient), 00FN (lemma-Noetherian-permanence), 00HT (lemma-flat-localization), 00HR (lemma-local-flat-ff), 00DF (lemma-tensor-product-exact), 030U (lemma-separable-extension-preserves-reducedness), 00EU (lemma-minimal-prime-reduced-ring), and the finite-dimensional algebra discussion 00J6. There are no new-node sources to review.

For step 1 I opened the algebra-tensor pushout statement: it provides precisely the multiplication and unique evaluation homomorphism from the two algebra maps. Surjectivity and contraction then follow from 1 tensor lambda and injectivity of iota, not a point-lifting assumption. For step 2 the finite-type definition provides actual algebra generators, the module-tensor statement says pure tensors generate, and the finite-type Noetherian statement applies separately over k and K. Both base rings are fields, whose ideals are zero and one, so its Noetherian hypothesis holds.

For step 3 the field-extension-base-change faithfully-flat statement gives S to C itself. The definition quoted explicitly says faithful flatness implies flatness. I opened the localized-flat-map theorem and checked that it gives the displayed fraction map, locality, and Noetherianity under exactly the S,C hypotheses established in step 2. The flat-local-hom theorem then applies to these actual local rings. This avoids citing just a definition of flatness for a preservation theorem.

For step 4 quotient base change states the isomorphism for an arbitrary ideal, with the direction and formulas needed here. I supplied both tensor-associativity formulas, so the identification is not an unspecified transport. The tensor pushout statement supplies e. Its composite with pi equals epsilon on both tensor factors, hence on every tensor. For step 5 I opened the prime-localization definition, whose fraction equality and zero relation give well-definedness and the kernel calculation. Every numerator and denominator in D can be lifted along the surjection pi; avoiding r is equivalent to avoiding q for a lift. Thus the localized map really is surjective and has kernel pB=mB. This step proves the quotient comparison explicitly; it does not use a stronger conclusion from the proof of another node.

For step 6 the module-tensor statement supplies bilinearity and generation, giving the finite spanning family after extending a finite basis. The existing finite-separable-tensor-field-reduced statement allows any extension E/L, so E=K requires no extra separability; K'=F has precisely the two assumed finiteness and separability hypotheses. Step 7 is the elementary finite-dimensional-domain argument, including both injectivity and surjectivity of multiplication by a nonzero element, which proves every prime maximal and r minimal. It is not a new lemma moved out of the item.

For step 8 the 00EU node explicitly states that localization at a minimal prime of a reduced ring is a field and its extended prime is zero. Steps 6 and 7 establish both hypotheses. The induced evaluation map is unital, has nonzero denominators, is injective as a field homomorphism, and surjects onto K by constants. I computed the composite on fractions and its kernel qB, and compared with the already proved kernel mB. The cited localization definition identifies qB as the maximal ideal. Each citation has a literal statement quote in citations.json.

I tested the boundary cases S=k and F=k: evaluation is the identity on K and both maximal ideals are zero. For S=F a nontrivial finite separable extension embedded in K, the tensor may have several factors (for example a quadratic extension split over K); the proof localizes only the factor specified by iota and does not discard the others globally. Nilpotents in S are allowed: S=k[t]/(t^2), p=(t), F=k gives B=K[t]/(t^2) localized at (t), with mB=qB and reduced fibre K, exactly as stated. A purely inseparable example in characteristic p would yield a nonreduced tensor fibre and invalidate step 6; the existing separability hypothesis rules it out. These tests cover trivial extensions, non-domain S, positive characteristic, and the distinction between the tensor and its local factor.

Against delivery-errors B–E: every used notion is already defined or spelled out, no statement-only new node hides a proof, no clause is relocated into a duplicate node, every non-elementary input is a cited existing statement, the fibre formula is written with its actual numerator and denominator, and no dimension-equality or separability hypothesis was added. All steps are below 2000 characters. No Lean file, compiler, Lake, repository write, direct git command, or launcher edit was used.
