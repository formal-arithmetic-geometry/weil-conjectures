# Worker report: lem-per-local-blowup-tower-globalization

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-local-blowup-tower-globalization.json: statement; split by a direct twelve-step induction; no Mathlib match.
- No new nodes; zero Mathlib leaves. citations.json contains verbatim statement quotations for every step citation.

## Attachments

None for the item. Read-only searches in lean/WeilConjectures for the blueprint id, schematic closure, local blowup towers and the blowup extension vocabulary found no declaration stating the complete item. The available affine localization and extension declarations cover smaller pieces. Existing closed dependencies are cited without recreating them: the schematic-image flat-base-change and strict-transform-is-blowup interfaces in particular have actual project proofs.

## Wanted sources

WANTED: Michael Temkin, Functorial desingularization of quasi-excellent schemes in characteristic zero: the non-embedded case, arXiv:0904.1592v2, Lemma 2.1.2, section 2.2.6/Lemma 2.2.1, section 4.2.1/Lemma 4.2.1, Lemmas 4.2.4--4.2.5 and section 4.3 Extension n+1, printed pp.7,11,28--31, for lem-per-local-blowup-tower-globalization. Read the author's PDF online at https://math.huji.ac.il/~temkin/papers/Non_Embedded_Desingularization.pdf; no archived copy is present in the permitted literature directory. No download was made. Proof_origin remains agent: the actual proof is an explicit assembly of existing DAG interfaces and the locally available Stacks sources, rather than an unarchived reference treated as a proof.

## STATEMENT-DISPUTED: generic-point reconstruction under arbitrary flat pullback

The original last sentence identifies two operations: pull back the full local-center maps, and replace those maps by their restrictions to the new generic local bases before closing. Flat base change of schematic images proves the first operation; the second can discard embedded structure. This fails even with a reduced Noetherian new ambient scheme, reduced local centers, and the same integer r.

Let k be any field, X=Spec k[t], S={(t)}, P=X and p=id. Take the length-one local blowup with reduced center (t) on Spec k[t]_(t). It is nowhere dense, r=1, and its global center is V(t). Set

B=k[a,b,c,d]/(ac,ad,bc,bd), t=a+c, and X'=Spec B.

The defining ideal is (a,b) intersect (c,d); hence B is reduced and Noetherian. Its injection into the product of the domains k[a,b] and k[c,d] shows that every nonzero h(t) acts injectively: its restrictions are h(a) and h(c). Thus B is torsion-free over the PID k[t], so X'->X is flat (one can check flatness directly using the principal-ideal criterion: multiplication by any nonzero polynomial is injective).

The full pulled-back center has coordinate ring

B/(t)=k[b,c,d]/(c^2,cd,bc,bd).

Here c is a nonzero nilpotent killed by b,c,d. Its two generic points are the primes (b,c) and (c,d), corresponding in B to (a,b,c) and (a,c,d). At the first, d is a unit and the local ring is k[c,d]_(c); at the second, b is a unit and the local ring is k[a,b]_(a). Both have dimension one, and the local pulled-back center is the reduced closed point of a DVR. These are the required new synchronized local centers with all the original local hypotheses. Their schematic closure has ideal (a,c), not (a+c): the kernel of restriction of B/(t) to its two generic fields is exactly (c). All schemes P'=X' and X' are reduced Noetherian; p'=id is proper. The old and new nonempty center ideals differ. Since the item remembers ideals, an identity of the underlying Cartier blowup morphism cannot repair this failure.

Correction: retain arbitrary flat compatibility for schematic images of the FULL pulled-back local schemes and for the ambient construction. For reconstruction only at the new generic points, require schematic density of those restrictions in each full pulled-back global center. Step 12 proves that reducedness of all full pulled-back centers is a sufficient condition, using the existing maximal-dominance lemma. No center is silently reduced. Do not assert invariance of r under arbitrary flat maps. This is faithful to Temkin's pushforward operations and to Stacks 081I; it distinguishes the extra generic-point replacement from those operations. The parent lem-per-codimension-resolution-improvement uses regular base changes: these have reduced pullbacks of reduced centers, so this correction does not rule out its use; obtaining those regular-pullback hypotheses remains the parent's responsibility. No target or chapter/unit statement is edited.

The old source description also mislocated schematic-closure pushforward: in the v2 PDF it is section 2.2.6 and Lemma 2.2.1, not section 2.2.7. Corrected the source description and blueprint place. Preserved the inherited ancestor and via chain.

## Search and duplicate audit

Read the latest blueprint's perverse unit and lem-per-artin-gabber-affine-curve proof Step 3, plus the fixed chapter/unit records and the parent codimension-resolution-improvement. This is auxiliary ordinary blowup geometry on the recorded regular-purity branch. It changes no chapter route and invokes no SGA source.

Searched the entire DAG for schematic closure/image, flat image pullback, reduced blowups, local schemes, generic support and strict transforms, and ran blueprint_refs.py search for schematic closure, schematic, pro-open, localization, blowup, scheme-theoretic image and reduced blowup. Reused lem-sfb-scheme-image-flat-base-change, lem-trf-reduced-scheme-image, lem-per-reduced-noetherian-blowup-geometry, lem-per-flat-maximal-dominance-base-change and the existing Nagata/localization/component nodes. There is no new-node candidate to compare or search. No theorem was restated as a new node, no clause was moved to a new node, and no elementary topology or induction was made a node.

The item's historical searches are preserved. Current msearch.py searches in searches.jsonl were actually run. For the item, normalization and spreading-out signatures do not mention the prescribed ordered center ideals or extend arbitrary finite blowup towers. Flatness/base-change declarations do not give a schematic-closure tower either. Loogle on schemeTheoreticImage and Mathlib grep for schematicClosure|schemeTheoreticImage|blow.?up.*(closure|local) gave no match. A second phrasing searched unique pro-open extensions and merging. Some exploratory Loogle queries reported unknown identifiers; these are not evidence for a leaf. The additional exploratory searches generated no new nodes and are not presented as successful matches.

## Not duplicates

No new nodes. All generic geometry inputs are existing nodes and are cited directly. In particular the general reduced blowup input and the general schematic-image flat-base-change input were already present.

## Review by Q130

I read delivery-errors B--E in full and checked the mathematical statements rather than just the dependency names. I read Stacks morphisms.tex 01R8 (lemma-quasi-compact-scheme-theoretic-image), 056B (lemma-scheme-theoretic-image-reduced), 081I (lemma-flat-base-change-scheme-theoretic-image), the proper-composition proof 01W3; divisors.tex 0805 (lemma-flat-base-change-blowing-up), 0808 (lemma-blow-up-reduced-scheme), 080E (lemma-strict-transform); and the online Temkin places above. The locally archived Stacks text and the existing DAG statements justify the twelve-step assembly. I also read the live statement of every dependency in citations.json, including the corrected current blueprint statement of strict-transform-is-blowup and the defining data behind the short blowup-flat-base-change comparison statement. The project's image-kernel proof at SchemeTheoreticallyDominant.lean:196 and strict-transform theorem at StrictTransformBlowup.lean:100 confirm that these are genuinely the general interfaces used here.

Step 1 uses localization-flatness and flat-base-change for exactly their stated flatness conclusions. It writes out the monomorphism and quasi-compactness checks; finite components are not assumed for a non-Noetherian source. Localization and quotient rings remain Noetherian by extending contracted ideals, so the local centers and their finite coproduct really have the needed quasi-compactness. The base case and preserved induction hypotheses are explicit.

Step 2 takes the coherent kernel ideal and injective image restriction from the image-ideal node, and reduced schematic image from the reduced-image node. The only extra algebra is finite generation of ideals/submodules over Noetherian rings, written explicitly against the definitions of Noetherian and coherent; no flatness or arbitrary-base-change reducedness is used.

Step 3 uses flat base change of schematic images, not just a definition of flatness. The base-changed source is computed: off-diagonal summands are empty by incomparability, and the diagonal is the actual closed center because the local-base map is a monomorphism. The closed-immersion image node identifies its schematic image. This proves equality of ideals, not just equality of sets.

Step 4 uses the exact flat-blowup comparison for the known flat local-base maps, the existing reduced-Noetherian blowup lemma for all later ambients, and the properness/composition statements to keep the projection to X proper. Coherence supplies the finite-type ideal hypothesis. This is a finite induction retaining every synchronized empty stage.

Step 5 uses only the finite-component, sober-scheme, and image-support statements it cites. It describes the finitely many irreducible closures of the local-center generic points. These give the actual generic images, so neither codimension nor density is guessed from a set-theoretic support inclusion.

Step 6 uses universal closedness only to make the image of the closed center closed. Both inclusions in its equality with the union of point closures are written out. Pure codimension uses exactly the stipulated common local-ring dimension r. Schematic density comes from the injective kernel-image map and the established equality with the union of local centers, so it does not mistake topological density for schematic density.

Step 7 proves nowhere-density by contradiction using component cover, sobriety, finiteness and the localizations. A component of the ambient contained in the global center would be a component of that center, whose generic image is one of S; restricting to that local base gives a component in the local center. Removing the other finitely many components gives the prohibited open subset. No assumption that X is irreducible, regular, catenary or finite dimensional enters.

Step 8 uses only the scheme-image kernel characterization to prove uniqueness of this specific construction, and does not claim arbitrary extensions are unique. It explicitly requires any comparison through auxiliary spreads to have these same schematic closures. This avoids using a lemma's proof as an unstated interface.

Step 9 takes exactly the stated strict-transform/blowup isomorphism, with the correct ambient ideal and its extension to the closed subscheme. The ambient center lies in the current strict transform because its source maps factor through it; the affine kernel calculation proves the subscheme factorization. I did not infer a scheme factorization from mere pointwise support. The next strict transform remains closed by its construction.

Step 10 checks the quasi-compact-source and flat-target hypotheses of 081I, and then uses flat blowup comparison stage by stage. It retains pulled-back nilpotents and does not substitute generic-local centers. The ambient assertion uses the same center ideal equality and the existing strict-transform isomorphism.

Step 11 handles the newly added schematic-density hypothesis through the kernel equality it actually means. This is an elementary consequence of image ideals and then induction; it makes the limitation reviewable rather than silently weakening the original flat claim.

Step 12 uses the existing flat-maximal-dominance statement for C->Z and Z'->Z, where Z is the reduced image and Z'=Z times_X X'. Step 5 checks the maximal-dominance hypothesis. The active members of S stay separate from the inactive ones under flat pullback: a generic point over an active s cannot lie in the pullback closure of a different member, by incomparability. Hence the relevant generic images belong to S'. Reducedness of C' is an explicit additional assumption in this sufficient criterion. The map from its finitely many local restrictions is quasi-compact and quasi-separated because its source is Noetherian. The reduced-dense-image node therefore applies exactly with its stated hypotheses. This is where reducedness is needed, and the counterexample shows why it cannot be omitted.

Small cases: empty S gives empty centers and identity stages; a zero-length tower gives P; some local centers empty do not contribute a global component; all empty centers give the empty global center; Cartier centers can give identity blowup morphisms but their nonempty ideals must be retained; a nonintegral ambient is covered by the component argument; a nonseparated ambient M is allowed because the ambient step only uses closed immersion and strict transform. Nonreduced flat pullback is handled by full ideals rather than a false reducedness assertion. The explicit counterexample even retains reducedness of X'. No new unsplit node has a hidden proof, and no non-elementary proof step exceeds 2,000 characters (the maximum is below 1,100).

## Unfinished work

None for this split. No Lean file or repository file was written and no compiler, Lake or local DAG/preflight checker was run. The archival Temkin PDF remains WANTED. Independent maintainer mathematical review still applies to this delivery.
