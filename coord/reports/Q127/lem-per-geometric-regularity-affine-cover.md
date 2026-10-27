## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-geometric-regularity-affine-cover.json`: statement item, now split into six steps. No Mathlib match for the criterion.
- No new nodes and no new Mathlib leaves. Every mathematical tool already has a DAG node.
- `citations.json`: one entry for each of the 19 step/node citations, with verbatim full statements checked against the live files.
- `searches.jsonl`: command-generated Mathlib search records. The sandbox preparation script reconstructs the item without changing the repository.

## Attachments

None. Searches for the blueprint id and for geometric regularity / affine-cover regularity in `lean/WeilConjectures/` found no project declaration stating the three equivalent conditions. The existing ring-theoretic geometric-regularity declarations supply supporting facts, not an attachment of this scheme criterion. No sorry declaration was treated as a completed proof.

## Literature wanted

None. All sources used are available locally.

## Problems and changes

The item had a correct statement and an empty proof. Its statement, hypotheses, statement dependencies, source and inherited provenance are retained. In particular the assertion is about every finite extension, not just purely inseparable extensions. I filled the missing argument from Stacks Varieties Tag 038V and explicitly used the existing Algebra Tag 0381 theorem to bridge from the purely inseparable algebra definition to arbitrary finite extensions. No separation, finite type, global Noetherianity, or nonemptiness hypothesis was added.

The newest blueprint's `lem-per-artin-gabber-affine-curve` is a perverse pushforward statement; it contains no explicit affine geometric-regularity lemma. The inherited provenance already identifies this as a supporting comparison far below that node, through the regular-morphism affine criterion. I preserved that ancestry and explained it in split_report, rather than claiming that the current blueprint explicitly states this item. Searches of the entire imported blueprint for “geometrically regular”, “geometric regularity”, and “regular”, and the whole DAG for the tags and affine/regularity terms, found no equivalent imported node. The actual source for this auxiliary comparison is 038V.

The only correction made during source checking was to my draft source reference: the affine tensor-product universal-property lemma is Tag 01I4, not 01IQ. Tag 01JQ is the affine-scheme fibre-product lemma; 01JR is its open-subscheme compatibility. The node's original statement needed no correction.

## Existing tools and duplicates

No new node is justified: the geometric-regularity field-extension theorem already exists as `lem-weil-pbc-geometrically-regular-finitely-generated-extensions`, and the general affine tensor base-change statement already exists as `lem-sbc-finite-affine-tensor-base-change`. Its one-summand instance suffices for this item. The regularity dictionary in step 2 is an explicit consequence of the definitions, the affine-stalk localization statement and affine-open Noetherianity; I did not create a second affine-cover regularity lemma. The direction (2) implies (3), tensor-factor symmetry, and the empty case are elementary assembly, not nodes.

## Not duplicates

No new-node/existing-node pairs: there are no new nodes.

## Review by Q127

I read Varieties `lemma-geometrically-regular` (038V), including the equivalence between finite purely inseparable testing, every affine open, and an affine cover. I also read Algebra `lemma-geometrically-regular` (0381), its proof and the preceding Noetherianity paragraph, Definition 0382, and `lemma-Noetherian-field-extension` (045I). For the scheme assembly I read Schemes `lemma-fibre-product-affines` (01JQ) and `lemma-open-fibre-product` (01JR), and Properties `lemma-locally-Noetherian` (01OW), `lemma-characterize-regular` (02IT) and `lemma-locally-regular` (02IU). These are sources for the item, not substitutes for DAG citations. No SGA route is used.

In step 1 I opened the statements of the affine-open Spec-points lemma, the affine-opens induced-ring-map square, the finite-affine tensor-base-change lemma, the fibre-product definition and the open-preimage fibre-product lemma. The first really supplies the canonical affine identification, the second identifies its structure map, the third permits arbitrary commutative base-change algebras and a one-term coproduct, and the last two identify this base change with the inverse-image open. I checked that the coproduct statement does not impose reducedness, finite type or Artinian hypotheses. Its statement only promises compatibility with the second projection; the proof uses no unstated first-projection formula. The equality of the iterated pullbacks is explicitly justified by their common universal property. The covering claim is just inverse image of a union.

In step 2 I read the entire definition of regular scheme: it explicitly states both the affine-neighbourhood definition and the equivalent locally Noetherian/regular-stalk criterion. The locally Noetherian definition record explicitly includes inheritance by open subschemes. The affine-open Noetherianity lemma gives the required Noetherian ring, not merely a Noetherian underlying space. The affine-stalk localization lemma explicitly identifies the localizations at all prime ideals with the corresponding stalks. Thus the argument writes out why a regular scheme has regular affine coordinate rings and why an affine cover by regular rings proves regularity. There is no appeal to regularity being local without an argument.

In step 3 I checked Noetherianity of A before invoking its geometric-regularity definition. Every finite purely inseparable extension is among the finite extensions in (1), including the identity extension. Steps 1 and 2 then give the regular tensor ring. I opened the algebra tensor-pushout universal-property statement: exchanging its two inclusion maps produces tensor symmetry and exchanging them again is its inverse by uniqueness. This is the only tensor comparison needed; no non-elementary assertion is hidden in “transport”. The definition of geometric regularity really uses precisely these purely inseparable tests.

Step 4 uses the affine-opens-basis statement, which explicitly provides an affine neighbourhood of each point in any open. Taking all affine opens covers Z and requires neither quasi-compactness nor a finite cover. No existence-of-cover theorem with stronger hypotheses is used.

In step 5 I checked the exact statement of the finitely-generated-extension theorem, not only its title or proof. It explicitly yields Noetherianity and regularity of K tensor A for every finitely generated extension and names finite extensions as examples. Its assumptions are a Noetherian geometrically regular algebra, exactly supplied by each hypothesis in (3). The cover from step 1 and the regular-affine-neighbourhood definition then prove scheme regularity. I deliberately restrict this assembly to finite extensions as the item requires; I do not need an arbitrary-extension Noetherianity assertion. This is the only substantial algebra input to the reverse implication and is a pre-existing node, not a renamed clause of this item.

For step 6 I checked the empty scheme, empty covering and zero-coordinate-ring cases directly: base change of an empty cover is empty; a zero ring has no primes and its tensor ring is zero. The pointwise regularity and Noetherianity tests therefore give exactly the allowed empty case. Further small-case checks were Spec k (all tensors are fields) and Spec(k[epsilon]/(epsilon^2)) (the identity extension already fails all three tests). Over an imperfect field of characteristic p, Spec(k(a^(1/p))) with a not in k^p fails the purely inseparable tensor test although the original ring is a field; this confirms that the proof has not silently replaced geometric regularity by ordinary regularity. No intersection of arbitrary affine opens is assumed affine.

I read the live statement of every cited node and generated citations.json only from those verbatim full statements. The first dry run required longer quotations for four citations; I replaced every excerpt with the full statement to expose all the hypotheses and conclusions used. I checked B--E of delivery-errors against the files: no new unsplit proof, no hidden new notions, no duplicate or item-clause nodes, no uncited substantive algebra claim, no use of a cited node's proof in place of its statement, no strengthened hypotheses, and no unsupported identification. Every proof step is below 2000 characters (maximum 1188); there is no long step concealing a separate lemma. The five off-unit statement tools are declared in split_report.tool_uses: they are generic algebra and scheme tools supporting the inherited route, not replacements for the perverse unit's proof. No unit record is changed because this item is not its key statement.

I ran the required Mathlib search command for LeanFinder, Loogle, grep and LeanSearch, and read every result. A second LeanFinder phrasing returned geometric reducedness and smoothness, not geometric regularity of general locally Noetherian schemes. I inspected the relevant Noetherian scheme definitions and the geometric-reducedness class in the installed source; these do not state the present equivalence. The five command-generated records are appended verbatim in tool/query identity to the retained historical searches of the item, with their actual hit names and no-match verdicts. No unavailable service is called an empty successful search.

## Unfinished work

No mathematical part of the item remains open. Independent maintainer review is still required after delivery.
