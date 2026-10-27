# Stage-1 report: lem-trf-nodal-stalk-completion-reduction

1. Files written:
- dag/nodes/sec-trace-formula/lem-trf-nodal-stalk-completion-reduction.json: item, split into five steps using existing completion and fibre nodes.
- dag/nodes/sec-trace-formula/lem-trf-locally-finite-type-stalk-essentially-finite-type.json: statement, Mathlib leaf; AlgebraicGeometry.LocallyOfFiniteType.stalkMap, Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean:102.
- citations.json: a verbatim statement quote for each of the thirteen proof-step citations.

2. Attachments: none. Searched WeilConjectures for the exact blueprint tag and for completed-stalk, completion/flatness and essentially-finite-type stalk terminology. The project has generic completion lemmas, but no declaration stating every clause of this item. No Lean file was written or compiled.

3. WANTED: none.

4. Issues found: the item had no proof. Its TeX commands were doubled in decoded JSON; normalized these escapes only, preserving the mathematical statement, all hypotheses, and conclusions. Its blueprint ancestry is historical: the latest lem-trf-local-term-locality proof uses contracting correspondences and no longer mentions nodal local equations. This does not make the assigned local-algebra lemma false; this delivery proves it on its recorded Stacks route and does not substitute nodal geometry into the current unit proof. Unit and chapter records are unchanged.

5. Unfinished: no mathematical step of the item is left unaccounted for; the existing cited nodes retain their own stage states. Independent review and acceptance remain the maintainer's responsibility.

## Review by Q69

I read Stacks curves.tex, Tag 0CBX (lemma-formal-local-structure-nodal-family), the entire first proof paragraph. I checked its invoked flat-completion theorem directly in more-algebra.tex, Tag 0C4G (lemma-flat-completion), and the local fibre formula in schemes.tex, Tag 0HA1 (lemma-local-ring-fibre). I read algebra.tex at Tags 00FN (Noetherian permanence), 0316 (Noetherian completion), 05GI (units and radical of a completion), 05GG (completeness and reduction of completion), and 00MA (exactness/tensor formula for finite modules). These are the sources behind the existing nodes, whose complete statements I opened before citing them. The new node uses the affine criterion in morphisms.tex Tag 01T2 and the exact Mathlib stalk declaration at lines 102–108. I also read Mathlib's EssentialFiniteness definition: it means a localization of a finite-type algebra, so this match requires no new equivalence theorem.

Step 1 uses the locally ringed-space morphism definition for locality and the definition of flatness at the given point for flatness; it never assumes f is flat away from that point. The new stalk leaf gives a localization of a finite-type A0-algebra. The finite-type algebra Noetherian lemma and the localization Noetherian lemma say precisely that these two successive rings are Noetherian. No neighbourhood of s is assumed Noetherian, so the argument does not silently replace the stalk hypothesis with local Noetherianity of S.

Step 2 uses the completion-Noetherian lemma on both now Noetherian stalks. The local-completion-local-ring statement provides exactly the maximal ideals and residue identifications, including their canonical maps. The Noetherian definition supplies finite generation required by completion-mod-ideal; that statement explicitly gives completeness with respect to the extended ideal. The residue-field isomorphism hypothesis is used only to identify both resulting residue fields with k.

Step 3 invokes flat-completion on a local flat homomorphism between Noetherian local rings, all checked in step 1. Its statement supplies the actual coordinatewise map and flatness. Locality of that map is written out using generators of the extended maximal ideal, not inferred from flatness. The residue comparison is its first quotient coordinate.

Step 4 uses the scheme-fibre-stalk-quotient statement, which gives both the surjective map and its kernel, not merely an abstract ring isomorphism. Locality follows from the locally ringed morphism definition; combined with surjectivity this identifies the image of the maximal ideal with the target maximal ideal. The local-completion-quotient statement then applies with source B0, target D, kernel J, and ideal the maximal ideal of B0. Its statement includes the surjective coordinate map, its exact kernel JB, and the commuting completion square.

Step 5 is the elementary assembly: extension of the same generating ideal twice gives JB = mB. The equality of coefficient actions is checked on representatives a in A0 of every class of k; the quotient-coordinate formula is explicitly given and commutes with transitions. Thus the comparison is a k-algebra isomorphism for the actual fibre coefficient structure, and its compatibility is not assumed from an unspecified isomorphism. This introduces no independent comparison theorem.

For small cases I checked the identity morphism, a field base, the smooth affine line at a rational point, and a nodal fibre k[x,y]/(xy) at its origin. Over a field m is zero, so the formula reduces to the completion of the fibre stalk itself, not to the uncompleted fibre. For the identity morphism the fibre completion is k and B/mB = k. Nonclosed points and non-Noetherian neighbourhoods introduce no extra hypothesis because only stalk essential finite type is used. The new leaf allows arbitrary points and no flatness, Noetherianity, separatedness or residue condition; its exact Mathlib theorem has the same scope.

I checked delivery-errors B–E: the new node has a self-contained statement and no proof, all its notions have definition dependencies, all search queries were actually run and their hits read, the leaf has a verified source line, and the blueprint search found no imported node with the same stalk assertion. I searched the whole DAG by essential-finite-type/stalk concepts, by declaration, and by source tag. The existing fibre and completed-base-change nodes require different hypotheses and do not state this generic input. None of the new content restates a clause of the item: the one new leaf is a general finite-type stalk fact used with two existing Noetherian permanence results. Every non-elementary step cites the exact statements it needs; citations.json records these verbatim. All five steps are below 2000 characters, with no hidden long-step lemma. Generic off-unit tools are declared in split_report.tool_uses.

## Not duplicates
- lem-trf-locally-finite-type-stalk-essentially-finite-type vs lemma-nagata-finite-type-to-separated-target: cancellation of finite type for composites, not essential finite type of stalk maps.
- lem-trf-locally-finite-type-stalk-essentially-finite-type vs lem-sf-hom-comparison-affine-inputs: finite affine coverings and flat coefficient complex models, not stalk ring maps.
- lem-trf-locally-finite-type-stalk-essentially-finite-type vs lem-trf-unramified-fibres-affine-differentials: affine covers and vanishing fibre differentials under unramified-fibre assumptions, not arbitrary stalk essential finite type.
- lem-trf-locally-finite-type-stalk-essentially-finite-type vs lem-pc-affine-finite-type-algebra: global sections of an affine finite-type scheme over a field, not local rings over an arbitrary base stalk.
- lem-trf-locally-finite-type-stalk-essentially-finite-type vs lem-weil-pbc-lft-affine-pairs: finite type for rings of affine open pairs, not essential finite type after localization at both points.
- lem-trf-locally-finite-type-stalk-essentially-finite-type vs lem-weil-pbc-lqf-locally-finite-type: local quasi-finiteness implies local finite type, not the induced maps on local rings.
- lem-trf-locally-finite-type-stalk-essentially-finite-type vs lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs: quasi-finiteness at an isolated fibre point in an affine chart, not general stalk essential finite type.
- lem-trf-locally-finite-type-stalk-essentially-finite-type vs lem-weil-pbc-lft-pointwise-criterion: finite-type affine neighbourhood criterion, not the local-ring conclusion.
- lem-trf-locally-finite-type-stalk-essentially-finite-type vs lem-weil-pbc-lft-over-field-isolated-point-residue-finite: finite residue extension at an isolated point over a field, not a stalk algebra over an arbitrary target.
- lem-trf-locally-finite-type-stalk-essentially-finite-type vs lem-weil-pbc-affine-base-piece-tensor-comparison: simultaneous affine tensor presentation of a supplied base change, not essential finite type of any stalk map.
- lem-trf-locally-finite-type-stalk-essentially-finite-type vs lem-weil-pbc-qc-open-immersion-finite-type: finite type of quasi-compact open immersions, not the generic stalk conclusion.
