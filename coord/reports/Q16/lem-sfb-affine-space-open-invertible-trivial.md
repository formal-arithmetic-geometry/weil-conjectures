## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-affine-space-open-invertible-trivial.json: item split in four steps, preserving its statement and statement dependencies. Mathlib searches find related ring-Picard and affine results, but no theorem for arbitrary open subschemes.
- citations.json: nine step/node entries, each quoting the cited statement verbatim.
- No new nodes, no Mathlib leaves added, no Lean files written or compiled.

## Attachments

None. Searched the live WeilConjectures source by the blueprint tag and invertible/UFD/Picard/open terminology. PicardAffine.lean proves triviality on affine opens with factorial section rings; LocalizationAwayRigidity.lean proves equality of fibre restrictions in a family. Neither states the item for an arbitrary possibly nonaffine open. The existing whole-affine-space node has a Sheaf declaration, but that is only the whole-space case, not this item.

## Wanted

None. All mathematical sources used here are in the literature collection.

## What was wrong or incomplete

The item was statement-only. Its statement agrees with Divisors Tag 0BDA, including arbitrary opens and arbitrary fields; no statement correction is needed. The Noetherian branch of the source suffices because the number of variables is finite. The source's later non-Noetherian argument is unnecessary here. In particular, one cannot simply infer the item from the algebraic Picard-group theorem by taking sections on a nonaffine open.

The inherited blueprint chain has no imported ancestor: blueprint_refs.py ancestor returns None. Its existing from.node=null, precise from.place and via chain were retained. Read the current latest chapter and unit texts and direct-images proof (3). This split supplies the already requested line-bundle input to the normal-variety affine-parameter Picard argument and follows the inherited route. No unit/chapter record is changed. Whole-blueprint searches by UFD, Noetherian polynomial, invertible/open and Picard/affine find no equivalent imported theorem.

## Unfinished

None in this one-level split. The non-elementary inputs already have nodes, so this delivery introduces no further unsplit work.

## Not duplicates

No new nodes. The existing whole-affine-space result lem-sfb-affine-space-invertible-trivial is used as a proper special case, after extending the given line bundle to the ambient space. It does not already cover this item's nonaffine opens. The other DAG nodes citing 0BDA concern products, projective bundles, group varieties, or this item's parent; none replaces the arbitrary-open assertion.

## Review by Q16

I read Divisors lemma-open-subscheme-UFD (0BDA), especially its Noetherian-case paragraph, and lemma-extend-invertible-module (0BD9). I also read Algebra lemma-polynomial-ring-UFD (0BC1) and lemma-Noetherian-permanence (00FN), checking their tag mapping. No new nodes need separate source reviews. This is precisely the source's extension-to-Spec argument, specialized to the finite-variable field case.

For step 1 I opened every cited node. def-weil-pbc-noetherian-ring defines Noetherian by finitely generated ideals; the proof writes out why a field has this property. lem-weil-pbc-finite-type-algebra-noetherian explicitly allows a finite polynomial presentation modulo an ideal, so the identity presentation with zero ideal applies. pqf-def-locnoeth defines the affine-cover criterion, which the whole spectrum satisfies. lem-sfb-polynomial-field-ufd states factoriality for every field and every n, including zero. Thus the step does not confuse a Noetherian topological spectrum with a Noetherian ring.

For step 2 I opened lem-weil-pbc-affine-open-stalk-localization and used its clause (c), which actually identifies the local ring with the localization at the corresponding prime. I opened lem-sfb-ufd-prime-localizations: its statement supplies both the domain and unique-factorization property without a Noetherian hypothesis. Applied to the UFD from step 1, it proves the needed hypothesis at all complement points. These are Mathlib leaves and generic algebra/scheme tools, rather than an alternate unit route.

For step 3 I opened lem-sfb-invertible-extension-factorial-complement. It gives an invertible extension and a restriction isomorphism for a locally Noetherian scheme with UFD local rings outside the open. It explicitly imposes no density, integrality, separatedness or uniqueness. Steps 1 and 2 verify exactly its hypotheses. Hence this citation genuinely covers the possibly nonaffine or empty V; I did not use a construction hidden in that node's proof.

For step 4 I opened lem-sfb-affine-space-invertible-trivial. Its statement gives the sheaf isomorphism for the whole Spec of the same polynomial ring, so it applies to the extension, not to V. def-weil-open-immersion identifies the structure sheaf on an open with the restriction of the ambient one. The inverse maps are explicitly restricted and composed with the extension isomorphism; no unproved gluing or sections-to-sheaf comparison is hidden here.

I tested V empty, V=X, n=0, finite fields, and the nonaffine punctured affine plane. Empty V causes no obstruction to the extension statement or restricted isomorphism. The punctured plane illustrates why affineness of V must not be inserted. No algebraic closure, positive dimension, rational point, or density hypothesis is used. All proof steps are below 2000 characters, and the total is below 3000; every non-elementary input is a cited statement. I checked B--E against these files: no new-node relabelling, missing hypotheses, unrecorded searches, off-route theorem, or false dependency. The nine citations quote statements in full without adapting their wording.

I ran fresh LeanFinder, Loogle, LeanSearch and grep searches through msearch.py, including a second semantic phrasing, and read the returned ring-Picard/free-locus/affine candidates. PicardGroup.lean:478--552 and :883--887 concern algebraic modules and do not immediately give the arbitrary-open sheaf statement. The inherited searches are retained verbatim, and fresh searches are copied from searches.jsonl with their actual results. No compiler, Lake, repository git command, SGA source, or external download was used.
