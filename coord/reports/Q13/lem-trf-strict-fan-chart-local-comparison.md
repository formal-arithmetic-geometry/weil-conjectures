# Q13: lem-trf-strict-fan-chart-local-comparison

## Files written

- dag/nodes/sec-trace-formula/lem-trf-strict-fan-chart-local-comparison.json: item, statement, split into five proof steps; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-affine-fan-hom-universal.json: new statement-only node, unsplit; no Mathlib match. It states the natural affine sharp monoid-spectrum universal property for arbitrary spaces with sharp monoid sheaves.
- citations.json: one entry per step/node citation, using verbatim statement excerpts.
- searches.jsonl: actual msearch.py searches, with the returned signatures read during this session. The existing item's four inherited searches are retained; five fresh searches for the item and five for the new node are appended/recorded.

## Attachments

None. Searched WeilConjectures/ in the read-only slopmaster2 source for the exact item id and blueprint tag, strict/fan/chart language, and MonoidalSpace/KatoFan/MonoidSpectrum. No project declaration states either the item or the new supporting lemma. The upstream master is reference material, not evidence of a finished proof.

## Wanted literature

None. All needed passages are in literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf. These are ILO VIII results about monoidal fans, not Stacks results; I have not assigned an unrelated Stacks tag to them. No SGA source is used.

## What needed correction or clarification

The imported item has an empty proof. Its statement agrees with the strict specialization of ILO VIII, proof of Theorem 3.3.15, printed p.109. It is unchanged. The source treats monoidally smooth morphisms; strictness makes its monoid homomorphism an isomorphism. No smoothness or etaleness of the underlying scheme map is needed.

The two implicit source arguments are now explicit: (a) a fan localization is an affine open with monoid equal to the point stalk; (b) equality of the section homomorphisms is obtained by shrinking once for each of finitely many generators. This is equality of morphisms of sharp monoidal spaces, not just agreement of their stalks at one point. The non-elementary passage from section homomorphisms to fan morphisms is a separate, genuinely general supporting statement, ILO VIII Lemma 3.1.8(ii).

The supplied chapter and unit were read. The node's historical ancestry through the monoidal-resolution/nearby-duality branch is retained. The present sk-i-curve-zero unit and its realization use the contracting-correspondence argument; this auxiliary split does not claim to replace that argument or to realize the key unit afresh. No chapter/unit fields or realized fields are changed.

## Not duplicates

lem-trf-affine-fan-hom-universal vs def-trf-fine-fan-blowup: that definition supplies monoid spectra, sheaves, and fan morphisms, but does not state the bijection between maps to an affine fan and homomorphisms to global sections.

lem-trf-affine-fan-hom-universal vs lem-trf-log-fan-chart-blowup: that statement defines fan charts and gives their existence and blowup pullback; it does not give the affine sharp-spectrum universal property for arbitrary sharp monoidal spaces.

lem-trf-affine-fan-hom-universal vs lem-trf-strict-fan-chart-local-comparison: the new lemma has no log scheme, strict morphism, pair of charts, or shrinking conclusion; it is an affine representability tool, and the item's steps prove the comparison by characteristic quotients and finite generators.

lem-trf-affine-fan-hom-universal vs lem-trf-monoidal-resolution-tower: the latter constructs log blowup towers with free final characteristic monoids, rather than a Hom bijection.

lem-trf-affine-fan-hom-universal vs lem-trf-coherent-log-ideal-chart-construction: the latter constructs and descends log blowup schemes from monoid-algebra charts; neither its statement nor its universality clause represents maps from arbitrary sharp monoidal spaces to a monoid spectrum.

The whole-DAG searches used 3.1.8, sharp monoidal, affine fan, monoid spectrum, represent/monoid combinations and the proposed id. The whole-blueprint searches for monoidal space, fine fan and 3.1.8 returned no match, and the broader monoidal/fan searches provided no equivalent blueprint node. The blueprint ancestor command returned lem-trf-local-term-locality. No existing node states this universal property or a generalization that specializes to it. No other new nodes are created for finite-generator or localization calculations.

## Review by Q13

I read ILO VIII 3.1.1--3.1.10, printed pp.98--100, and the complete point-local paragraph in the proof of 3.3.15, printed p.109. For the new node I read Lemma 3.1.8(ii), its proof from prime ideals defined by inverse images of nonunits, and the morphism definition in 3.1.6. The sharp-stalk hypothesis and contravariant monoid-map direction agree with that source. The new node is statement-only and introduces every object; its source is the precise numbered ILO lemma. It does not take the local comparison conclusion as a hypothesis or restate a clause of it.

For Step 1 I opened def-trf-fine-fan-blowup and checked its finite-generation, basic-open, localization, sharpening and local-model clauses. The proof supplies the needed localization fact directly: the complement of a prime is generated by the original generators outside it, their sum defines the smallest open, and localization/sharpening gives the stalk monoid. Every open containing the point contains all its generalizations, even outside the chosen affine chart, so the smallest-open description is intrinsic. Primes and structure sheaves correspond under quotienting by units. The finite generators and their inverses give fineness of the localized monoid, and their images generate its sharpening. This is a direct definitions calculation, not an uncited affine-fan comparison theorem.

For Step 2 I opened both lem-trf-log-fan-chart-blowup and def-trf-fs-log-blowup. The former's first paragraph explicitly gives strictness and the inverse-image-sheaf chart isomorphism; the latter gives the associated-log pushout and characteristic quotient. At the actual point, the local ring map reflects units. Therefore forming the pulled-back log structure introduces only the source units, and quotienting them gives the original characteristic monoid. The chart maps and this strict map are all isomorphisms, giving alpha=b^{-1}ta in the required P-to-Q direction. No claim about smoothness of the scheme map enters this step.

For Step 3 I checked the new node's full statement, specifically its natural Hom bijection and naturality in P. Its hypotheses hold because Step 1 gives fine sharp P and Q and the fan structure sheaves have sharp stalks. The inverse is induced by alpha^{-1}; injectivity/naturality identifies the composites with identities. Thus this is a genuine fan isomorphism with the prescribed section map, not merely a stalk isomorphism extended without justification.

For Step 4 I again checked the first paragraph of lem-trf-log-fan-chart-blowup and the fineness clause of def-trf-fine-fan-blowup. They give the sheaf maps from the two charts and finite monoid generators. The two existing section homomorphisms have equal germs by Step 2; each generator therefore gives an equality on a neighborhood by the definition of stalk equivalence. Their finite intersection gives equality of homomorphisms on all of P. No finite-presentation theorem or extension of an arbitrary germ homomorphism is being used: both section homomorphisms already exist on U_0.

For Step 5 I checked that the new lemma says a bijection of actual monoidal-space morphisms, including continuity and local stalk maps, not just a bijection of stalk maps. Naturality identifies the composite's section map with phi alpha. Its injectivity therefore proves the whole chart equality. The required neighborhood containment was retained in the construction of U_0, and the monoid-section composite is exactly the one in the imported statement.

I tested the zero monoid (no generators), where all local fans are points and U=U_0; P=N at its closed and generic primes, where the local fans are respectively Spec_mon N and Spec_mon 0; and the face localization of N^2 at a rank-one point, where inverting the generator outside the prime and sharpening leaves N. I also checked the identity strict morphism with two charts, as used by the parent, and an arbitrary strict morphism whose underlying scheme map is not smooth. All arguments are stalk-local and work in these cases. Empty Y is vacuous. No global quasi-compactness or finiteness of either entire fan is used. With non-strict maps such as the multiplication-by-n log-point map, t need not be an isomorphism; the proof does not silently cover that case.

Against delivery-errors B--E: the only new node is self-contained, has no proof/proof_deps, and records actual searches and no match; naturality is explicitly stated for both its uses. I checked all statement citations against the open JSON files and wrote exact excerpts in citations.json. No supporting node is a local-comparison clause or an elementary finite-generator step. All dependencies point downward to definitions or the independent universal property. The item statement, source and inherited blueprint/import metadata are preserved. Every proof step is below 2000 characters, and each has a source and a Boolean elementary flag. No off-unit proof tool is needed. There is no statement dispute, missing literature, or mathematical part left unfinished.

## What could not be finished

Nothing mathematical remains unfinished. The supporting universal property is intentionally statement-only, as required for a one-level split.

## Delivery validation

The required deliver.py --no-push exited successfully and printed OK (not pushed) at 2442429e15, with server preflight passed. All seven citation pairs were also checked locally as verbatim statement excerpts, the item statement is unchanged, and every new-node search has an exact tool/query entry in searches.jsonl. Direct push is the remaining delivery operation.
