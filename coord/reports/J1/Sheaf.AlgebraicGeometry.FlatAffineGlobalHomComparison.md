## What changed

The original three declarations and their signatures are unchanged.
The retained AffineMorphismHomOutOfPerfect import becomes `import all` solely to reuse
its private, proved naturality helper; all imports added for the reduction are proof imports. The main theorem
mixedAffineGlobalHomBaseChangeMap_isIso is reduced to sheaf tensor base change and two
narrower compatibility obligations. The library's proved private baseChangeMap_naturality helper transports base
change along the perfect tensor-Hom isomorphism; the sections mate then factors the
specified scalar transpose into isomorphisms. Reusing this existing helper avoids re-elaborating the expanded derived-adjunction choices.
All original public imports remain.

New modules: FlatPullbackTorIndependent, MixedPerfectInternalHomPullbackIsIso, and
MixedAffineSectionsBaseChangeMate. FlatPullbackTorIndependent is proved by the flat stalk
criterion, Tor symmetry, and projective-resolution homology. The latter two state the
remaining compatibility obligations, with sources and complete proofs in words. Their
planned proof dependencies are imported with plain proof imports.

## Proved and sorry left

Closed original hole: AlgebraicGeometry.mixedAffineGlobalHomBaseChangeMap_isIso
(lem-sc-flat-affine-global-hom-comparison). The main module contains no sorry. This is a
DECOMPOSITION: one original hole closed, two new holes added, net holes closed minus added
is -1; it is not an independent sorry-free proof of the theorem's dependency closure.
The existing proved baseChangeMap_naturality helper is reused through
`import all Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect`. No new naturality
obligation is introduced.

Additional proved theorem: AlgebraicGeometry.flat_pullback_torIndependent
(lem-sc-flat-pullback-tor-independent), with no sorry.

Every remaining delivery hole:

- AlgebraicGeometry.exists_mixedAffineSectionsBaseChangeMate
  (lem-sc-mixed-affine-sections-base-change-mate). This requires only quasi-coherence of
  Rf_*E and identifies two mates for arbitrary E,L,m; it does not assert invertibility of
  sheaf base change, assume flatness, or assume perfectness.
- AlgebraicGeometry.mixedPerfect_internalHom_pullback_isIso
  (lem-sc-mixed-perfect-internal-hom-pullback-isIso). This concerns solely sheaf internal
  Hom and arbitrary morphisms, with no global sections or scalar extension.

Both new holes are public theorems with proofs exactly `by sorry`, each in its own module.
They are strictly separate parts of the argument. Empty schemes and zero objects satisfy
both statements; the perfect source permits arbitrary unbounded target complexes.

## No longer needed

None. The original AffineMorphismHomOutOfPerfect proof import is retained as `import all`
for its already proved naturality helper. Its equal-universe affine Hom theorem is not
applied, but the module remains needed. No original public import or DAG dependency is
pruned. The original mixed comparison modules are used through the comparison definitions.

The unit sk-thm-picard-duality has no realized statement or step nodes; this change bypasses
no realized unit statement or proof step.

## Where the brief, the DAG or earlier work was wrong

The earlier attempts were blocked by missing tracked sources MixedGlobalExtension,
MixedGlobalSectionsDirectImageIso, and MixedHomTensorPullbackIso, although the final
saved reduction compiled against cached artifacts. The source inventory now contains
these modules and the assigned item again. The delivery is checked against that restored
baseline; no missing baseline source was recreated and no tool was modified.

The initial DAG route hides the independent-universe sections transport and normalized
mate identity. The existing affine Hom theorem and PerfectInternalHomPullbackIsIso require
module and sheaf localization universes to agree, whereas this item's signature makes them
independent. The two compatibility obligations expose the missing parts without changing
that signature. The original theorem is proved from named existing statements even where
their transitive proofs still contain sorry, as required in stage 3.

## New nodes

lem-sc-flat-pullback-tor-independent: proved flatness implies stalkwise Tor independence.
Uses lem-weil-pbc-tor-symmetry to resolve the other stalk and tensor with the flat stalk.

lem-sc-mixed-perfect-internal-hom-pullback-isIso: perfect-source evaluation-mate pullback
invertibility in sheaf derived categories without a module localization choice.

lem-sc-mixed-affine-sections-base-change-mate: affine sections compatibility of the scalar
and sheaf mates for independent localization universes, without invertibility assumptions.

The existing main node's proof, proof_deps, and proof_origin follow the reduction.
No interface change, change record, or forced adaptation is needed.

## Second reading by J1

1. Compared every delivered module with the repository. The main module is the only
   existing file; its three declaration signatures, definition bodies, public imports,
   universe binders and section instances are byte for byte unchanged. All added
   imports are proof imports. No interface change or change record is required. PASS.
2. Compiled the four delivered files in import order through lcompile.py: no errors
   or warnings. The only literal sorries are the two public compatibility theorems
   listed above, each exactly `by sorry`. No forbidden declaration or hollow
   definition occurs. Existential witnesses are eliminated within proofs, not used
   to define arbitrary public data. Explicit #print axioms checks on a scratch copy show only propext,
   Classical.choice, Quot.sound and (for the comparisons and open compatibility
   theorems) sorryAx. flat_pullback_torIndependent uses only the three permitted
   axioms. Delivery preflight also checks every declaration.
3. Checked each split-off statement against the cited Stacks sources (0AA7, 08I3,
   0FPC, 08HY, 0D5T) and its node. The internal-Hom claim is the dualizable-source
   evaluation mate for arbitrary targets; the sections claim is an identity for all
   mates, without asserting base-change invertibility. Neither restates the main
   theorem. Zero objects, empty schemes, identity morphisms and nonflat g introduce
   no missing condition. Independently searched with leanfinder, loogle and rg;
   the equal-universe affine theorem and internal-Hom theorem are not applicable
   replacements. Sources and complete natural-language arguments are present. PASS.
4. The reduction uses Tor-independent tensor base change, naturality, and the mate
   identity to factor the actual scalar transpose into isomorphisms. Reviewed the
   existing flat-Tor proof degree by degree, including the transported right stalk
   action and the n+1/n+2 indexing. All original imports and dependencies remain
   required; no node/module is pruned. The unit sk-thm-picard-duality has empty
   realized statement and step lists; no realized route is bypassed. PASS.
5. Checked node statement records against each Lean signature, sources, creation
   fields, blueprint provenance, proof steps and dependency unions. Repaired the
   main node's omitted original mixed comparison dependencies and its directly used
   scheme internal-Hom adjunction dependency and recorded fresh
   searches on all three new nodes. Added plain imports of the stated planned
   dependencies to the two open modules. Corrected the new source records to cite
   algebra.tex for Tor symmetry and cohomology.tex for internal Hom. PASS after repairs.

Changes in this reading are dependency metadata, missing planned proof imports,
source records and independent search records. The original proof is retained.
A bounded attempt to close mixedPerfect_internalHom_pullback_isIso using the
existing source's monoidal_adjunct_isIso reached its final categorical application,
but the last-green cached module still has the older sorried theorem and lacks that
helper. The attempt remains only in scratchpad; no duplicate helper or unverified
proof is delivered. The delivery remains a decomposition (one original hole closed,
two added), not a net reduction of holes or a sorry-free dependency closure.

Sources read: [Stacks 0AA7](https://stacks.math.columbia.edu/tag/0AA7),
[08I3](https://stacks.math.columbia.edu/tag/08I3),
[0FPC](https://stacks.math.columbia.edu/tag/0FPC),
[08HY](https://stacks.math.columbia.edu/tag/08HY),
[0D5T](https://stacks.math.columbia.edu/tag/0D5T),
[00M3](https://stacks.math.columbia.edu/tag/00M3),
[08IB](https://stacks.math.columbia.edu/tag/08IB).

Final validation: all four delivered modules compiled without warnings; the first
dry run passed (CODEX, due to new nodes/modules). The final metadata correction
adds the directly used internal-Hom adjunction to the main node dependency union.
