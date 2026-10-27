# Q37: lem-sfb-etale-stalk-invariants

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-etale-stalk-invariants.json: existing statement, now split into six steps; no full Mathlib match.
- citations.json: 22 verbatim statement quotations, one for every step/node pair.
- searches.jsonl: six searches made with the required msearch.py command in this session. The node retains its inherited searches and records the new searches as well.

New nodes: 0. New Mathlib leaves: 0. No Lean source was written, and no compiler or build was run.

## Attachments

None. I searched WeilConjectures by the exact blueprint id and by the regularity/normality/dimension/stalk notions. AlgebraicGeometry.isRegularLocalRing_stalk_of_etale (Regular.lean:96) only proves regularity ascent with a hypothesis on all target stalks. Scheme.isDomain_and_isIntegrallyClosed_stalk_of_etale_of_isDomain (NormalEtale.lean:55) likewise only proves normality ascent with a hypothesis on all target stalks. Neither states the pointwise equivalences and dimension assertion of this item. FieldSectionsStalkInvariants.lean concerns geometric sheaf sections, a different meaning of invariants. There is no exact attachment.

## WANTED

None for this item. All source arguments used here are in the supplied Stacks checkout. No SGA source is used.

## Findings and corrections

The item was unsplit and the sandbox contained no previous node or report. I kept its statement, stmt_deps, creation metadata and blueprint ancestry verbatim. The statement is true without global Noetherian assumptions; regularity itself includes the requisite local Noetherianity. No STATEMENT-DISPUTED correction is needed.

A stalk homomorphism of an etale scheme morphism need not be a finitely presented etale ring map. I avoid applying finite-presentation ascent theorems directly to A→B. Instead, take a genuine affine etale chart R→S and localize the base to A=R_p. The intermediate algebra C=(R\p)^{-1}S is still etale over A, while B=C_Q is only a prime localization of C. Smooth ascent is applied to A→C, and localization is a separate cited operation. This also avoids treating a definition of regular rings as a theorem about localizations of regular local rings: the latter is explicitly cited.

## Not duplicates

No new nodes are created, so there are no new/existing pairs to distinguish. Whole-DAG title, statement, source-tag and Lean searches found the existing nodes cited below, particularly lem-sc-etale-local-dimension (07QP), lem-weil-pbc-etale-over-normal-ring-normal (033C), lem-sfb-faithfully-flat-normal-ring-descent (033G), and the regularity ascent/descent/localization nodes. I reuse them instead of creating ring versions of the item's clauses. Blueprint searches for etale regular, etale dimension, normal etale and 07QP yielded no imported node stating this full stalk-map package. The ancestor command returns null for the inherited creation chain; its explicit inherited place and via list are retained rather than inventing an ancestor.

## Mathlib search reading

The first leanfinder search returned scheme etale/smooth instances and locality of ring-map etaleness. Loogle with the quoted Etale and IsRegularLocalRing names returned zero hits. The exact regularity/normality/dimension grep returned zero hits. LeanSearch returned localization-away etaleness, RingHom.Etale locality and Krull-dimension invariance under ring equivalence, none of which proves this item. A second semantic phrasing returned formal-etale localization maps and IsEtaleAt, and the second grep found the standard-smooth-relative-dimension-zero characterizations. I read the returned types: these concern etaleness, not the three local-ring invariants, and do not specialize to the full item in one line. All six services/commands completed successfully. No unavailable search is misreported as a negative result.

## Review by Q37

I read delivery-errors B through E in full and checked them against the delivered file. There are no new unsplit nodes to conceal arguments, duplicate existing facts or restate clauses. The six proof steps contain the scheme-to-ring assembly; every non-elementary ingredient is an existing cited statement. All steps are shorter than 2000 characters. The proof-dependency set is exactly the union of uses. Every quoted citation is copied from the actual statement, not its proof or docstring. I checked the relevant dependency closures for a path back to this item and found none.

For the item I read more-algebra.tex, lemma-dimension-etale-extension (07QP) and lemma-regular-etale-extension (0AH0), including the preceding observation about flat local maps. I also read algebra.tex, lemma-local-flat-ff (00HR), lemma-localization-of-regular-local-is-regular (0AFS), lemma-regular-goes-up (07NF), lemma-descent-regular (07NG), lemma-localize-normal-domain (00GY), lemma-normal-goes-up (033C) and lemma-descent-normal (033G). I checked morphisms.tex, lemma-etale-characterize (02GJ) and lemma-base-change-etale (02GO), schemes.tex, lemma-spec-sheaves (01HV), and the etale-ring-map definition 00U1. These sources impose no missing global finiteness condition. There are no new-node sources to review.

Step 1 uses def-weil-etale-morphism for flatness, def-weil-flat-morphism for its exact stalkwise meaning, def-weil-locally-ringed-space-morphism for locality, and the actual flat-local-faithfully-flat theorem for faithful flatness. Both rings are local because they are scheme stalks. This step does not mistake the definition of faithful flatness for a proof of it.

Step 2 uses the affine covering clause of def-weil-etale-morphism, then lem-weil-pbc-spec-map-stalk-localization for both stalk identifications and the actual structural map. The cofinal-neighbourhood argument is written in the step. The statement of lem-sc-etale-local-dimension requires a genuine etale R→S and a prime q over p, precisely the chosen chart and its point. It does not require Noetherianity or finite dimension.

Step 3 uses the one-component specialization of lem-sbc-finite-affine-tensor-base-change; that statement permits arbitrary commutative rings and does not require its algebras to be finite. Its projection equation identifies the correct base-changed structural map. The etale base-change clause is explicitly in lem-weil-pbc-etale-base-change-finite-limits(1). I wrote both tensor/fraction directions and both iterated-localization directions. The condition p=φ^{-1}q makes all the denominators units. The actual etale-affine criterion gives finite presentation, H₁=0 and Ω=0; by def-weil-pbc-smooth-ring-map this is smooth since the zero module is finite projective. These are elementary specializations after the two geometric inputs, not a new hidden comparison theorem.

Step 4 uses lem-weil-pbc-regular-local-localization to convert regular local A into a regular ring. The smooth-ascent theorem applies to A→C, and the localization-of-regular-ring theorem applies to C_Q. The regular-ring definition then gives regular locality at the unique maximal ideal. Step 5 uses the same local-to-ring theorem on B and the faithfully-flat regular-ring descent theorem with the map from step 1. Thus the result includes local Noetherian descent and never assumes the entire schemes Noetherian. The final localization at a maximal ideal is an identity by the universal property, since all its denominators are already units.

Step 6 uses the normal-domain localization theorem to convert an integrally closed domain into a normal ring. Normality ascent is applied only to the etale map Spec C→Spec A from step 3; the normal-ring definition then gives the domain and integral-closure property of C_Q. Conversely, the faithfully-flat normal-ring descent statement has no Noetherian hypothesis; combined with step 1 it gives normal A, whose maximal localization is itself. This avoids assuming that C is a domain or that the two local rings have equal residue or fraction fields.

I checked small cases: identity maps; open immersions; finite separable extensions of fields (both dimensions zero and both regular/normal, though residue fields differ); products of etale algebras, where the chosen localization singles out one prime and no domain hypothesis on C is warranted; singular identity maps, where the regularity/normality predicates can both be false; non-Noetherian identity maps, where the normality statement still makes sense; and empty schemes, where no point u is available and the assertion is vacuous. Regularity ascent and descent are conditional only on one local ring being regular. Infinite dimension is allowed in step 2.

The off-unit nodes declared in split_report.tool_uses are generic algebra or affine base-change tools. They do not replace any part of the fixed alteration route: the item still supplies the stalk comparisons needed on the two legs of a common pointed etale neighbourhood. The chapter and unit records were read and left untouched.

## Unfinished work

None in this one-level split. The maintainer's independent review remains the next stage after delivery.
