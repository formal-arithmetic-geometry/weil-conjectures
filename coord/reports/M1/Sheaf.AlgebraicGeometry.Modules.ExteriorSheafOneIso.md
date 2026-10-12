## What changed

Completed `AlgebraicGeometry.Scheme.Modules.exteriorSheaf_one_iso` in
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheafOneIso`, preserving its signature and imports.
Constructed the presheaf isomorphism with `PresheafOfModules.isoMk` and the sectionwise
`exteriorPower.oneEquiv`. Naturality is proved by expressing every exterior-degree-one
section as the singleton wedge given by `oneEquiv.symm`, applying the chosen restriction's
characterization, and evaluating the singleton wedge. Sheafification sends this isomorphism
to an isomorphism; composition with the sheafification adjunction counit gives the result.
The counit is explicitly interpreted in `SheafOfModules` to resolve the scheme-category
interface. The larger heartbeat allowance covers naturality elaboration across these
interfaces; the clean local compile takes about 24 seconds.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.Modules.exteriorSheaf_one_iso`
(node `lem-sc-smooth-proper-curve-dualizing-exterior-one`): 1 of 1 local sorries removed.
No sorry remains in the delivered module, and no new sorry is introduced.
The proof uses the existing `exteriorSheafRestriction_existsUnique` theorem and the
restriction-law proof used by `exteriorSheafPresheaf`; their existing sorries in the imported
`ExteriorSheaf` module remain separate work items, as intended by stage 3.

## No longer needed

None: no import is removed, and no node or module in the stated proof dependencies is
bypassed. The existing node's proof and dependencies describe the implemented route.
The general spanning argument is unnecessary in degree one: `oneEquiv.symm.surjective`
expresses each section as a singleton wedge directly. No separate spanning lemma or
additional module is imported. `exteriorSheaf_zero_iso` is not used by this proof, but its
module remains necessary for the exterior-sheaf definitions.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement discrepancy found. The planned route works with the existing
interfaces. Loogle and LeanFinder found the sectionwise equivalences; repository and
Mathlib searches found no pre-existing sheaf-level identification to apply instead.
The local clone does not contain the literature files at the source paths named by the
node; the proof implements the node's supplied argument using the Mathlib signatures read
locally. No source-dependent new statement is introduced.


## Second reading by M1

1. PASS: compared the only delivered Lean module with the repository using `diff -u`.
   The existing theorem signature and docstring are byte for byte unchanged; the only
   changes are its proof and a local heartbeat setting/comment. No definitions or
   visible imports changed, and no change record is required.
2. PASS: independently compiled the module with `lcompile.py` (25.7 seconds), without
   errors or warnings. Read the full proof and checked the file for forbidden trust
   mechanisms and local sorries: none occur. A scratch copy with `#print axioms
   AlgebraicGeometry.Scheme.Modules.exteriorSheaf_one_iso` compiled (26.5 seconds)
   and reported exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The last is inherited from the already-open exterior restriction existence and
   presheaf-law theorems in `ExteriorSheaf`, not introduced by this delivery.
3. PASS: no statement is split off and there are no new declarations or nodes.
   Independently searched the library with exterior-sheaf and degree-one variants,
   queried Loogle for `PresheafOfModules.isoMk`, and read Mathlib's constructor and
   degree-one equivalence. No existing sheaf-level theorem provides a shorter route.
   The argument also works for the zero module and empty scheme: the degree-one
   equivalence and counit impose no nonzero, rank, smoothness, or nonempty hypothesis.
4. PASS: the proof starts at the target, uses Mathlib's sectionwise equivalence and
   isomorphism constructor, and establishes naturality directly from the existing
   restriction characterization. In degree one every element is a singleton wedge,
   so no general spanning lemma is needed. The sole public import is required by the
   signature's `exteriorSheaf`; there are no proof-only public imports. The old
   `proof_deps` contains only `def-sc-sheaf-exterior-power`, still used. Thus
   `No longer needed: None` is complete. Read `sk-thm-picard-duality.json`; its
   `realized` entries and unit route are unchanged, and no unit is bypassed.
5. PASS: read the item's node and the imported definitions. Its proof plan describes
   exactly the sectionwise identification, restriction compatibility, sheafification,
   and counit composition used in Lean; `proof_deps` and `proof_origin` agree.
   No metadata correction or new node is needed.

Second reading changed only this report: added the independent review evidence above.
The Lean proof was correct and is delivered unchanged from the first worker.
