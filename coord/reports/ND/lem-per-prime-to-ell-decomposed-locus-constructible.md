## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-prime-to-ell-decomposed-locus-constructible.json`: statement, split into six proof steps; no Mathlib match for the item.
- `citations.json`: 29 step/node citations, each quoting the cited statement verbatim.

New nodes: 0. New Mathlib leaves: 0. All supporting results already have DAG nodes.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint tag, `decomposed`, `residueDegree`, and prime-to-ell terminology found no declaration stating this locus. A sorry declaration would not have qualified.

## WANTED

None. The source PDF and the Stacks sources needed for this split are present.

## Problems found and changes

The item was statement-only. I read ILO, *Travaux de Gabber*, Expose II, Proposition 2.2.2, printed pp. 26--27 (including the surrounding definitions and Corollary 2.2.4). The conclusion is ind-constructibility, not necessarily constructibility by a finite union. The statement already correctly says ind-constructible and imposes no quasi-compactness or separation on the etale morphism. I preserved it and its statement dependencies.

The source abbreviates three parts of the argument: reducing at an arbitrary point to its integral closed closure; making a selected generic field factor finite; and obtaining a prime-to-ell point from a fibre whose total degree is prime to ell. The delivery supplies those arguments. In particular, it never identifies the whole fibre with a single residue field away from the generic point. Its degree is the sum of its field-factor degrees.

The PDF prints the residue extension in the reverse order in Definition 2.2.1; the proof of Proposition 2.2.2 and the definition of decomposed coverings in 2.1.1 use the intended extension from the base residue field to the source residue field. The item already uses that intended direction, so no statement correction is needed.

## Searches and reuse

The existing 2026-10-19 Mathlib-search records are retained as historical records from the creation of this node. All appended 2026-10-24 searches were actually run using `batch2/msearch.py`; `searches.jsonl` records them. I read the returned declarations. The item was searched with LeanFinder in two formulations, LeanSearch, Loogle, and source grep. The first Loogle query used the deprecated name `AlgebraicGeometry.IsEtale`, which its service did not recognize; the second used the actual names `AlgebraicGeometry.Etale` and `AlgebraicGeometry.Scheme.Hom.residueDegree`, and returned zero hits. The grep's Chevalley theorem requires a quasi-compact morphism and says nothing about residue degrees; its source at `Mathlib/AlgebraicGeometry/Morphisms/FinitePresentation.lean:121` was read and does not attach this item. The generic finiteness search found the proper-neighbourhood theorem in `ZariskisMainTheorem.lean:406`, whose properness hypothesis does not hold here; I read it and reused the existing algebraic generic-finiteness node instead.

Before considering a generic-field spreading node I searched the entire DAG by its statement, generic/finite/etale terms, and Stacks tag 02ML. This found `lem-weil-pbc-minimal-prime-finite-type-algebra-finite-away`. Its statement supplies exactly finite localization of a finite type algebra with finite fibre over a minimal prime. There is no need for a new spreading lemma. Similarly the searches found the existing etale ring base-change, affine fibre-product, etale-over-field product, affine principal-open, and finite-flat rank nodes. The logged searches about arbitrary etale base change were exploratory: no such new node was created, because all applications here are affine and the existing ring base-change leaf suffices.

Whole-blueprint searches with `tools/blueprint_refs.py search` included `decomposed`, `constructible`, `generic finite`, `finite generic`, `generic branch`, `residue degree`, `residue-degree`, `prime-to`, and `etale base change`. None supplies this item's statement. I read the latest blueprint's chapter/unit and `lem-per-artin-gabber-affine-curve.proof.md`, especially Step 3, and preserved the recorded ancestor and alteration-cover chain. The three off-unit non-Mathlib statements are declared as generic tools in `split_report.tool_uses`: generic algebraic finiteness, fibre-product residue fields, and closed-immersion residue fields. They implement the ILO reduction below the node level; no unit or chapter route is changed.

## Not duplicates

No new nodes were created. Existing facts were cited rather than duplicated.

## Unfinished work

None in the stage-1 split. Supporting nodes remain in their existing states; this delivery neither re-splits them nor claims their proofs finished. Server dry-run and delivery outcomes are recorded below after they run.

## Review by ND

I checked the item against the actual proof of ILO II Proposition 2.2.2, printed pp. 26--27, and opened the statements of every cited DAG node. The elementary expansions follow that proof's integral-affine, finite-flat-rank route. There are no new statements requiring an additional source or small-case audit.

Step 1 uses `lem-a1-etale-open-restriction` for the compatible affine restriction, `def-weil-closed-immersion` for the quotient model of the closure, `lem-weil-pbc-fibre-product-affine-spectra` for the tensor algebra, and `lem-weil-pbc-etale-ring-base-change` for its etaleness. The residue-field isomorphism for the closed immersion, together with the separate fibre-product point and residue-field nodes, gives an actual point with the original residue field and degree. The point-only node would not suffice for that last assertion. The ring R is chosen from the given Noetherian affine cover, not from an arbitrary affine neighbourhood. Its quotient by the point's prime is a domain; its fraction field is the residue field of that point. Quotient Noetherianity is written out via generators and is not an unstated theorem input.

Step 2 uses the etale-over-field product statement, read against Stacks algebra.tex Tag 00U3, label `lemma-etale-over-field`. It applies because the affine generic fibre remains etale by the cited base-change theorem. It supplies finite separable fields and allows the empty product; here the chosen witness forces a nonempty product. The coordinate idempotent is represented as b/s by putting a finite tensor sum over a common denominator. Inverting b retains exactly the chosen factor, so the generic fibre has exactly one prime. This is an explicit fraction computation, not a black-box spreading theorem. The principal-open statement, including its clause (b), identifies the new affine ring as B_b; the open restriction and affine etale criterion ensure it is finitely presented over A. I read Tag 02ML, algebra.tex label `lemma-generically-finite`: its hypotheses are finite type, a minimal prime, and finitely many primes over that prime. They all hold for A -> B_b at (0). The result supplies a nonzero a and a finite module after localization. There is no properness or global separatedness assumption in that statement.

Step 3 applies the finite-flat rank node exactly to a finite, flat, locally finitely presented morphism, which is the definition of finite locally free used in the DAG. I read Stacks morphisms.tex Tag 02KB, label `lemma-finite-flat`, and the finite-locally-free rank discussion. The generic rank equals the original witness degree because Step 2 retained a single field factor. Local constancy gives a neighbourhood of that same generic point; it does not assert that residue-field degrees themselves are locally constant. The fibre algebras and their dimensions are justified by the affine fibre-product statement and by the rank node's explicit fibre-dimension formula.

Step 4 again uses the etale-over-field product theorem. A basis in each coordinate proves dimension additivity directly. Divisibility of every summand would imply divisibility of their sum; therefore one residue extension has prime-to-ell degree. The fibre-product residue-field theorem and the closed-immersion theorem identify this with a genuine point of the original Y over the original X. Open restriction preserves stalks by the definition of open immersion. These cited statements supply isomorphisms of the relevant residue fields, not an assumed preservation under arbitrary field extensions. In particular no false assertion that every factor has prime-to-ell degree is used.

Step 5 is elementary subspace topology: an open subset of the closure of a point inside an open affine is locally closed in X. Each chosen neighbourhood contains the point that initiated the construction. Their union is exactly D; this proves the conclusion without a hidden Noetherian-induction or constructible-image lemma. Only affine neighbourhoods of individual points of Y were used, so an infinite or nonseparated source is permitted.

Step 6 uses precisely the statement that an open subscheme of a Noetherian scheme is quasi-compact, and the explicit subbase in `def-weil-pbc-constructible-topology`. A finite intersection of Zariski opens and their closed complements is locally closed; arbitrary unions give exactly the claimed patch opens. This is elementary from those two cited statements. I did not substitute Zariski openness for constructible-topology openness.

I checked empty X, empty Y and empty D: the conclusion is the empty union and no generic point is chosen. For X the spectrum of a field, the construction is just selection of one finite separable field factor. Nonreduced X is handled by the quotient R/p, with residue-field preservation explicitly cited. A split fibre of degree d can have several factors, including factors of ell-divisible degree; the sum argument covers that case. No invertibility of ell on X is used. For ell equal to a residue characteristic the etale field extensions are still finite separable and the same divisibility argument applies. I checked every step is below 2000 characters and hides no separate standard comparison or spreading claim. I corrected the tempting shortcut from prime-to-ell total rank to one-field fibres by using the explicit sum-of-degrees argument.

The B--E checklist therefore produces no new statement-only, duplicate, self-restating, missing-citation, unsupported-hypothesis, or circular-dependency issue. `citations.json` covers each use and every quotation was checked as a substring of its node's statement. The server's `review_split` check passed with zero new nodes before the full dry run.
