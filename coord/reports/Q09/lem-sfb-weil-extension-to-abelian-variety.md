# Stage-1 delivery: lem-sfb-weil-extension-to-abelian-variety

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-weil-extension-to-abelian-variety.json`: existing statement, now split into five proof steps. Statement and statement dependencies unchanged. Retained existing source, provenance, searches and blueprint chain; appended the actual sandbox searches.
- `dag/nodes/sec-six-functors-basics/lem-sfb-group-rational-divisorial-indeterminacy.json`: new statement-only lemma, unsplit, no Mathlib match. A nonempty indeterminacy locus of a map to a smooth connected group is divisorial. This does not assert extension to an abelian variety.
- `citations.json`: one verbatim statement quote for every citation in every item step.
- `searches.jsonl`: retained earlier searches and the new msearch output. `write_split.py` is a sandbox-only construction helper.

There is one new node and zero new Mathlib leaves. No Lean was written and no compiler, Lake or build tool was run.

## Attachments

None. Searches by blueprint id, extension terminology, rational-map terminology and abelian-variety terminology in the read project's WeilConjectures source found no declaration proving this item. The rational Tate module and algebraic-group rational representation hits are different notions. In particular rational-map representation in Mathlib is not the extension theorem.

## WANTED

None. Both Milne PDFs and the Stacks sources used here are already in the repository.

## Issues and corrections

No statement dispute or statement correction. The old item had no proof. The source's properness and group-target hypotheses must both be used; extending a rational map to an arbitrary proper target on the same smooth source would be false (the inverse of a surface blowup is the standard counterexample). The imported smooth-normal curve node has a dimension restriction and is not adequate for this arbitrary-dimensional source: the delivery uses `lem-trf-smooth-geometrically-normal`, whose statement explicitly covers all smooth schemes over fields, and declares it as a generic tool use.

The earlier searches survive in the sandbox. There were no old node files, report, dry run or delivery to preserve. The blueprint ancestor command returns `None`; the item already has `blueprint.from.node = null` and the recorded prerequisite chain. The new node retains that ancestor and adds the item at the beginning of `via`, with the exact Milne 8.17 place. The current blueprint is read from `literature/blueprint/latest/`: the direct-image unit proof is unchanged, and this auxiliary argument lies below its existing alteration/abelian multiple-retraction prerequisite chain. No chapter or unit record was edited.

## Not duplicates

The new node carries no Stacks tag; its source is Milne 8.17 and Lemma 3.3. Full-DAG and blueprint searches for rational maps, group varieties, indeterminacy, maximal domains, and prime divisors found no statement of the new group-target assertion.

- lem-sfb-group-rational-divisorial-indeterminacy vs lem-sfb-weil-extension-to-abelian-variety: the new node permits nonproper group targets and describes a possibly nonempty divisorial complement; it does not assert existence or uniqueness of a global extension.
- lem-sfb-group-rational-divisorial-indeterminacy vs lem-sfb-rational-map-extension-valuation-point: that node gives an extension near one valuation-ring stalk for a proper target, and makes no group-target or divisorial-indeterminacy assertion.
- lem-sfb-group-rational-divisorial-indeterminacy vs lem-sfb-valuation-stalk-proper-target-extension: that node assumes every stalk is a valuation ring and the target is proper; it does not describe indeterminacy on an arbitrary-dimensional smooth variety.
- lem-sfb-group-rational-divisorial-indeterminacy vs cor-nagata-conrad-proper-target-extension: that statement changes the source by an admissible blowup and has a proper target, with no divisorial-locus conclusion on the original source.
- lem-sfb-group-rational-divisorial-indeterminacy vs lem-sfb-normal-modification-codimension-one: that node concerns the isomorphism locus of a supplied proper birational morphism, not the domain of a rational map to a nonproper group.

I initially considered a new normal-source/proper-target codimension-two lemma, then found the existing valuation-point extension and normal-local-DVR nodes and used them directly in step 3. No redundant lemma was created for that combination or for gluing maximal representatives: the existing scheme-morphism gluing and relative equality nodes supply the latter in step 2.

## Review by Q09

I read Milne Algebraic Groups, printed pp.151–152, assertions 8.16–8.18, and Milne Abelian Varieties, Chapter I, printed pp.16–18, Theorems 3.1–3.2 and Lemma 3.3 with its difference-map proof. The first text states exactly the normal/proper versus smooth/group comparison the item uses; the second explains the local-DVR properness argument and the divisorial indeterminacy of a group-valued map. The new node is the latter lemma alone, stated with all fields, schemes, finiteness, smoothness, connectedness and separatedness introduced. Its definition of D is the union of actual extensions of the original f; gluing and separated equality identify this with the source's maximal rational-map domain. Its statement contains no proof sketch, proof dependencies or hidden appeal to the item. The local-ring formula explicitly defines the codimension-one condition, avoiding any change in the meaning of pure codimension.

For step 1 I opened `lem-trf-smooth-geometrically-normal`, `def-weil-regular-scheme`, the finite-type and integral-scheme definitions, the abelian-variety definition and the proper-morphism definition. The smooth-geometric-normal statement really gives regularity and normal domain stalks for the identity extension k/k, without a dimension hypothesis. Regularity explicitly includes local Noetherianity and Noetherian local rings; finite type over the affine point gives quasi-compactness. The abelian definition supplies a smooth connected proper group scheme, and properness explicitly includes separatedness and finite type. Thus neither a normality hypothesis nor a group or properness hypothesis is invented. I also read Stacks varieties.tex, Tags 056S and 056T (smooth regular/geometrically normal), against these uses.

For step 2 I opened the exact statements of `lem-sfb-relative-separated-dominant-ext`, `lem-weil-pbc-scheme-morphism-gluing` and `def-pc-reduced-scheme`. Every V contains U, so U is dense in each intersection; those intersections are reduced because their stalks are unchanged. The equality node applies relatively over Spec k, which is all that is needed, and gives equality of the two scheme maps on the whole intersection. The gluing statement permits the full set-indexed open family, gives a morphism on its union, and includes uniqueness on an open cover. Applying that uniqueness to the structure-map composites proves that the glued map is over k. I read Stacks Tag 0A1Y, lemma-rational-map-from-reduced-to-separated, including its overlap equalizer argument and its relative clause; Tag 01JB is the scheme gluing input. No unmentioned maximal-representative theorem is used.

For step 3 I opened `lem-sc-normal-dim1-dvr`, `def-sc-discrete-valuation-ring` and `lem-sfb-rational-map-extension-valuation-point`. The first says precisely that a one-dimensional Noetherian normal local domain is a DVR; the definition records the equivalence with a valuation ring, so the next node's stalk hypothesis is met. I read Stacks algebra.tex, Tag 00PD, lemma-characterize-dvr, including the valuation-ring equivalence, and morphisms.tex, Tag 0BX7, lemma-extend-across, statement and proof. The existing extension node requires integral Noetherian X, proper Y over S and dense U, and returns an open containing BOTH U and x with an extension of the given f. All these hypotheses were verified, and its exact output places x in the union D. I do not use the all-stalks-valuation theorem, which would be inapplicable to a general higher-dimensional smooth X.

For step 4 I checked the new node against Milne 8.17 and Chapter I Lemma 3.3. B meets the smooth connected separated finite-type group conditions from step 1. The definition of D in the new statement is literally the union used in step 2. If its complement is nonempty, the node supplies at least one generic point outside D whose local ring has dimension one, directly contradicting step 3. The contradiction, rather than a new lemma restating extension to B, carries the theorem's existence argument. Step 5 uses only the already opened relative dense-image equality node: reduced X, separated B/k, the inclusion U into X and equality of the restrictions are precisely its hypotheses. This proves uniqueness of k-morphisms as stated.

I checked the new statement on dimension zero (a dense open of an integral zero-dimensional variety is the whole variety), on U=X, on constant maps, and on nonproper targets. For G=G_a and f=1/t on A^1 minus the origin, the indeterminacy locus is the single codimension-one origin; the new node correctly allows it. For a trivial group, every f extends and the first alternative holds. In the item, B of dimension zero is allowed and no positive-dimensionality assumption is used. Arbitrary characteristic, imperfect fields, and smooth integral sources not assumed geometrically integral retain exactly the hypotheses of Milne 8.16–8.18; the argument does not choose k-rational points on X or add an algebraic-closedness assumption.

Against delivery-errors B–E: the sole new node is self-contained, statement-only and searched in Mathlib with two semantic phrasings, LeanSearch, Loogle and source grep. The hits were read: RationalMap.domain and toPartialMap construct the maximal domain and its representative, not its codimension; OrderOfVanishing merely uses codimension-one points. There is no match or Mathlib-leaf claim. The blueprint/DAG/source searches above rule out duplicates; all actual search records are taken unchanged from searches.jsonl. Every non-elementary step lists the node stating its input; citations.json quotes those statements verbatim. No proof of a dependency is used as its interface. Step 2 spells out compatibility and the relative structure map, step 3 verifies the local hypotheses, step 4 gives the actual contradiction, and step 5 gives the relative uniqueness test. No proof step exceeds 2000 characters, no inline argument hides an additional lemma, no SGA source is used, and the split never changes source by a blowup.

## Unfinished work

The single new group-indeterminacy lemma remains unsplit, as required for a one-level delivery. Nothing else in the assigned stage-1 split remains unfinished. The server dry run and final push are recorded by the delivery command.
