Files written:

- `dag/nodes/sec-picard-framework/lem-pc-coherent-hi.json`: repaired the five-step Tag 02O5/02O6 proof.
- `dag/nodes/sec-picard-framework/lem-pc-chow-relative-ample.json`: new statement-only relative ampleness fact; Mathlib no match.
- `citations.json`: verbatim citations for every node used by every step.

Attachments:

- None. The slopmaster2 higher-direct-image declaration rests on sorry-backed declarations.

WANTED:

- None.

What was wrong and changed:

- The returned step 2 cited Tag 01YM, whose stronger criterion requires an unverified ideal-submodule condition and hypotheses (0)-(2). It now cites the existing fully stated devissage node and explicitly verifies the relevant closure conditions.
- The returned step 3 used a Leray edge-map node that did not state derived composition. It now cites derived direct-image composition, the two twist vanishings, the projectivity of the Chow immersion, and relative ampleness of the pulled-back O(1).
- The returned step 4 used a global cohomology edge node for a sheaf-level identity. It now cites affine higher-direct-image vanishing, derived composition, and coherent pushforward along the closed immersion.
- Step 5 records proper-implies-separated and the quasi-coherent affine-base hypotheses before applying the finite-section result.

## Review by G1

I reread the item source in `coherent.tex` (Tags 02O5, 02O6, 01XJ), the Chow source (Tag 0200), and every cited DAG statement. For step 1, properness supplies the quasi-compact and quasi-separated hypotheses required by finite-support vanishing. For step 2, affine Noetherian reduction and finite type make X Noetherian; the new 01YI statement supplies exactly the criterion, while the coherent kernel/cokernel/extension node supplies condition (1). For step 3, Chow supplies the proper surjection and dense-open isomorphism; the two new Chow nodes discharge closedness/projectivity and relative ampleness, and derived composition combines the twist vanishings. For step 4, the affine-morphism, composition, and closed-immersion nodes give the sheaf-level higher-image comparison and coherence, with the 01YI criterion concluding devissage. For step 5, properness gives separatedness and the affine-base comparison applies to the quasi-coherent higher images; coherent finite type then gives finite A-modules. Every citation quote was copied verbatim into `citations.json`, and all new statements were checked for small and degenerate cases before the dry run.

## Not duplicates

The former `lem-pc-devissage-01yi` node was removed: its statement did not match Tag 01YI and duplicated the existing devissage node.
lem-pc-relative-kill-by-twisting vs lem-weil-pbc-coherent-serre-vanishing: the existing 02O1 node is the affine-base statement about global cohomology; the new node is the relative higher-direct-image vanishing needed over arbitrary Noetherian bases.
lem-pc-chow-relative-ample vs lem-pc-relative-kill-by-twisting: the existing twisting node assumes relative ampleness and proves vanishing; the new node supplies ampleness of the pulled-back O(1) from the Chow immersion.

## Second reading by G1

I checked Tags 02O5 and 02O6 in `coherent.tex`, Tag 0200 in the Chow section, and Tag 01VJ in `morphisms.tex`. The item statement agrees with the two Stacks conclusions, including local/global vanishing and affine finiteness. Each proof step was checked against the cited node statements and hypotheses. Step 2 now uses the existing higher-rank devissage node; step 3 checks relative ampleness for both pi and g'; step 4 checks affine pushforward, composition, coherence, and the generic stalk; step 5 checks separatedness, quasi-coherence, and finite sections.

The former `lem-pc-devissage-01yi` node was removed because it did not match Tag 01YI and duplicated an existing node. Step 2 and step 4 citations were redirected, and the Chow ampleness node was tightened to state the induced closed immersion over Z and relative ampleness for both morphisms. Zero sheaves, a field base, the empty scheme, and degrees zero/one were checked.
