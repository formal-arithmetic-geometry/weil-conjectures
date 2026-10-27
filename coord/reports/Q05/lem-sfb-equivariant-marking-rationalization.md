# Q05 stage-1 report: lem-sfb-equivariant-marking-rationalization

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-equivariant-marking-rationalization.json: item split into seven steps, with its statement unchanged. Mathlib searches found infrastructure but no matching theorem.
- citations.json: one verbatim cited-statement entry per step/node pair.
- report.md: this report. No new nodes, no new Mathlib leaves, no Lean edits or builds.

## Attachments

None. Searched the project WeilConjectures source for the exact blueprint tag and for marking/rationalization/normalization terminology. There is no declaration of the whole item. Ordinary rationalization of coefficient categories is unrelated. Mathlib normalization and etale field classification do not prove the item.

## WANTED

WANTED: literature/de-jong-families-curves-alterations-1997.pdf, §§3.2, 3.6, printed pp.605,608, for lem-sfb-equivariant-marking-rationalization. The publisher PDF was read online at https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf; no literature file was downloaded or changed.

## Findings and corrections

The imported statement is retained, including nonfaithful semilinear actions, the empty marking, all kernel fixed fields, and arbitrary inseparable geometric component maps. The proof is an agent assembly of existing DAG statements, following de Jong's constant-extension route; his §3.2 uses a reduced base change whereas this node uses its finite normalization. The existing finite normal relative curve-model statement gives precisely the stronger normalized model required here. No flatness or extension of markings as sections over the entire base is used or asserted.

The ancestor command reports None: following created.item encounters a broken inherited creation chain. The imported item's existing from.place and via already identify det-thm-sf-ctf-stability-direct-images, and lem-sfb-admissible-direct-image points directly there. That imported ancestor exists and has blueprint_kind. I filled from.node with that documented ancestor, retained the inherited via/place, and searched the whole blueprint for marking, normalization and Galois. None states this equivariant rationalization lemma. No parent or other repository node was changed.

## Not duplicates

No new nodes were created. Existing polynomial-envelope and finite normal relative model nodes were reused instead of creating variants of them; existing genus monotonicity includes inseparability.

## Review by Q05

I read de Jong's publisher PDF §§3.2, 3.3, 3.5 and 3.6, especially the finite constant-extension construction on printed p.605 and rationalization preserving the genus condition on p.608. I read the actual local Stacks etale-over-field statements (morphisms.tex, Tag 02GL, lemma-etale-over-field; algebra.tex, Tag 00U3, lemma-etale-over-field), the lifting and fixed-field results (fields.tex, Tags 0BME and 09I3), and the curve sections for Riemann--Hurwitz and inseparable factorization (Tags 0C1B, 0CD2 and 0CD0). I opened and read every cited DAG statement; citations.json copies their statements literally, rather than quoting an external source as a substitute for a node. No new-node source needs checking because no new node is delivered.

In Step 1, the etale-fibre node explicitly gives a disjoint union of spectra of finite separable residue fields, applied to the single fibre of M over Spec K. Finiteness of M makes the index finite. The primitive-element node applies to each of those finite separable extensions; the singleton-factor polynomial presentations satisfy the envelope hypothesis.

In Step 2, the polynomial-envelope node explicitly allows a nonfaithful finite group and an empty index set. Its fields K,H,F specialize here to K,G,B; its output M is our K'. Its conclusion includes finite Galois over both bases, the residue embeddings, complete factorizations, the surjection, the kernel and its fixed field. I do not infer these from a definition of Galois.

In Step 3, I checked the full constant-extension clause of lem-sfb-finite-normal-relative-curve-model, not merely its proof. The hypotheses match normal integral projective S, integral finite-type X, projectivity, pure geometric curve fibres and smooth geometrically integral generic fibre. It explicitly includes the tensor product being a field finite separable over F, the generic base-change curve, the finite surjection onto the full fibre product, normal finite-type models and pure fibre dimension. No unmentioned flatness is needed.

In Step 4, I wrote the balancing identity because g and sigma may act nontrivially on K and k. This checks the compatible field action needed by that model theorem's semilinear functoriality clause. The tensor-invariants node accepts any K-vector space and a group with fixed field K; F, K' and N satisfy exactly this, giving the specified embedded invariant field F.

In Step 5, I wrote the polynomial tensor presentation and the inverse generator maps. The polynomials are separable, so their split roots are pairwise distinct. The cited polynomial-quotient CRT node says exactly that evaluation gives the product of copies of K'; there are no hidden repeated-root or nilpotent assertions. Equivariance gives setwise stability without requiring individually fixed marked points. The empty marking gives the empty union.

In Step 6, finite-morphism permanence gives the finite map between fibres over the same algebraically closed Omega. Restriction to a reduced source component is checked by quotienting a finite algebra. The proper-closed-image node applies because a finite map is proper by the permanence node. The integral-injective-dimension node is applied to the image domain included in the component domain, not to a ring map with a kernel. The nonempty-open dimension node ensures the affine calculation computes each entire integral finite-type curve's dimension. Thus the image has dimension one and is a component of the pure curve fibre, so no component can contract to a point.

In Step 7, projective base change and projective-implies-proper apply to these fibres; a reduced closed component inherits the displayed projective embedding. Normalization-properties explicitly supplies finite birational, proper, dimension-preserving normalizations and smoothness over a perfect field. Dominant lifting through normalization applies because the source normalization is normal and Step 6 gives dominance. I made the geometric-integrality check explicit: the field theorem uses algebraic closedness of Omega in each function field, its generic-point criterion supplies geometric irreducibility, and perfect-field reducedness supplies geometric reducedness. Only after these checks is genus monotonicity applied; its statement allows inseparability. The arbitrary b bound follows by transitivity of the numerical inequality.

I checked delivery-errors B--E against the written files: all objects and notions remain introduced by the item, every non-elementary use is a cited statement, no newly created node is elementary, a duplicate or a disguised clause, no circular citation is introduced, and no absent hypothesis is imported. Small cases tested were empty marking, trivial action, an action with a nontrivial kernel, zero-dimensional base, genus zero and genus one bounds, positive characteristic inseparable maps, and reducible/nonreduced special fibres after passage to reduced components. Normalization is used only on integral reduced components, not claimed to commute with taking fibres. No step exceeds 2000 characters. Generic off-unit tools are declared in split_report.tool_uses; they do not change the unit's alteration route.

## Unfinished work

None within stage 1, subject to the required server dry run and delivery. No Lean proof is claimed.
