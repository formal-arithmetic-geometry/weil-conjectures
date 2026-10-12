## What changed

Reduced `AlgebraicGeometry.Etale.integralGeometricFibreSections` without changing its
signature, visibility, definitions, or existing docstring. The module now proves pointed
refinement naturality of the explicitly specified iterated pullback lift, and then of
`geometricFibreSectionRestriction`. These are private, fully proved helpers. The universal
property `Point.presheafFiberDesc` constructs the module homomorphism, and its coprojection
equation proves the required formula on every pointed neighbourhood, not just affine ones.
There is no use of exchange invertibility or of an arbitrarily chosen witness to construct
data.

Two new modules isolate independent local geometric tasks. `IntegralFibreSectionLocalLift`
states existence of a neighbourhood section lifting a given fibre section.
`IntegralFibreSectionLocalZero` states that a section restricting to zero becomes zero on a
pointed refinement of its original neighbourhood. The parent proves surjectivity using the
first, and injectivity using the second, the kernel criterion, representation of stalk
elements, and the pointed colimit transition equation. The concrete ModuleCat criterion
then proves invertibility. Thus the assembly, including linearity and the entire germ
formula, is complete Lean; the two local geometric tasks remain open.

The parent imports the two new proof modules and Mathlib's module filtered-colimit API.
The four former proof imports moved to the two new modules, which also import the existing
canonical module/set inverse-image comparison and strict-henselization local-structure
theorem. The node's proof and proof dependencies
now describe the actual colimit assembly. No unit statement or unit proof step is bypassed;
`sk-lem-universal-datum.realized` has no additional route constraint on this node.

All three modules compiled together in dependency order with the required local launcher,
with no errors or non-sorry warnings. The new statements were checked against the Stacks
strict-henselization, henselian restriction, and separably closed field-extension arguments.
The final delivery dry run also checks their signatures, node records, and axiom probes.

## Proved and sorry left

One original hole closed:
`AlgebraicGeometry.Etale.integralGeometricFibreSections`
(`lem-sbc-integral-geometric-fibre-sections`). There are no remaining sorries in the item.

Two new holes added, each the entire proof of its named public theorem:

- `AlgebraicGeometry.Etale.integralFibreSection_localLift`, node
  `lem-sbc-integral-fibre-section-local-lift`, in
  `Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLift`.
- `AlgebraicGeometry.Etale.integralFibreSection_localZero`, node
  `lem-sbc-integral-fibre-section-local-zero`, in
  `Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero`.

This is a decomposition, not a completed geometric comparison proof: one hole closed and
two added, hence delivery-local net minus one. Each new theorem proves only one direction
of the local section argument. Neither asserts a stalk isomorphism, constructs the parent
map, or includes its universal germ formula.

## No longer needed

The parent no longer directly imports:

- `Sheaf.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization`, node
  `lem-weil-pbc-sets-pushforward-stalk-strict-henselization`;
- `Sheaf.RingTheory.IntegralOverHenselianPair`, node
  `lem-weil-pbc-integral-over-henselian-pair`;
- `Sheaf.AlgebraicGeometry.EtaleSectionsBaseFieldExtension`, node
  `lem-weil-pbc-sections-base-field-extension`;
- `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero`, node
  `lemma-weil-pbc-etale-degree-zero`.

These are moved dependencies, not pruned modules: both new geometric tasks still need them,
and their proof dependencies and imports retain them. No original DAG node or module is
claimed to leave the targets' import closure. Pruned: none. The existing public imports
are retained unchanged.

## Where the brief, the DAG or earlier work was wrong

No disputed mathematical statement or forced adaptation. The existing proof dependencies
are insufficient for a short literal application: the strict-henselization comparison is
set-valued and its formula uses the small affine representative category; this item needs
module coefficients and a formula on every pointed neighbourhood. The set field-extension
comparison has the same coefficient mismatch. The new nodes explicitly record use of the
existing canonical module/set inverse-image comparison and its unit compatibility, and
the proved strict-henselization local-structure theorem for the chosen ring colimit.

Mathlib searches found no direct local lifting/vanishing theorem. LeanSearch returned an
Internal Server Error; LeanFinder, Loogle, source grep, DAG search, and blueprint searches
were still used. The literature files omitted from this read-only clone were read from the
existing local literature mirror, including the actual proofs of henselian degree-zero
restriction, integral henselian-pair permanence, and field-extension invariance.

Edge cases: an empty fibre has only its zero section, so local lifting uses zero; integrality
makes the image closed, permitting local vanishing after shrinking away from the image.
For the identity morphism the tasks are the usual representation/equality criteria for a
geometric stalk. A zero coefficient ring has zero section modules. Arbitrary geometric
point extensions are covered by Tag 0A3I without an algebraicity hypothesis. No finite-type,
properness of the integral morphism, or torsion hypothesis has been added.

## New nodes

`lem-sbc-integral-fibre-section-local-lift` records the surjectivity part of the
strict-henselization/henselian/field-extension argument. A fibre section lifts through the
two section comparisons and is represented at a pointed neighbourhood by Tag 03Q9.
Its module is `Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLift`.

`lem-sbc-integral-fibre-section-local-zero` records the injectivity part plus the pointed
filtered-colimit equality criterion: zero fibre restriction forces the strict-henselization
section to vanish, and hence forces the original section to vanish after refinement.
Its module is `Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero`.

Both nodes carry a complete source-based proof, searches, exact Lean signature, and the
parent's chapter, unit, and blueprint ancestry. No change record is needed: existing public
interfaces and public imports are unchanged, and no existing module other than the item is
adapted.

## Second reading by S1

1. Compared the whole item module against the repository version with `diff`, and
   checked the existing declaration signatures using the delivery parser. Verdict:
   the existing theorem signature and public imports are unchanged, byte for byte;
   no definition or existing docstring changes, and no change record is required.
   The two other delivered modules are new, not adaptations of existing modules.

2. Read both naturality proofs and the colimit assembly. The two pullback extensionality
   arguments establish compatibility of the explicitly constructed lift, and unit
   naturality establishes the cocone equation. The coprojection equation supplies
   the formula on every pointed neighbourhood. Kernel detection uses a refinement
   killing the representative, and local lifting supplies surjectivity. Verdict:
   correct conditional proof. All three files compile with lcompile.py in dependency
   order. Scratch-copy `#print axioms` for the parent and both local theorems reports
   only propext, Classical.choice, Quot.sound and sorryAx. Exactly two sorries remain,
   in the two reported named public theorems; there are no hollow definitions or
   forbidden declarations. The parent is not claimed to be axiom-clean or a net proof.

3. Read the local theorem signatures, their full proof docstrings and nodes, and the
   statements of all their imported comparison theorems. Independently checked
   [Tag 09XK](https://stacks.math.columbia.edu/tag/09XK),
   [Tag 09ZH](https://stacks.math.columbia.edu/tag/09ZH),
   [Tag 0A3I](https://stacks.math.columbia.edu/tag/0A3I), and
   [Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9).
   Integrality supplies an affine pullback over the strict henselization, and
   henselian restriction followed by field-extension restriction is bijective on
   sections. Section continuity gives existence of a representative and detection
   of zero after a pointed refinement. The unit formulas identify these restrictions
   with the map actually used by the parent. Verdict: both statements are true,
   needed, and strictly parts of the argument, not restatements of the isomorphism
   with its germ formula. Checked empty fibres, zero coefficients, the identity
   morphism, and arbitrary (including transcendental) extensions of the separably
   closed residue field. Independent LeanFinder search for henselian-pair integral
   algebra specialization, Loogle search for the stalk equality criterion, and
   source rg searches for henselian sections and local lift/zero detection found no
   direct replacement. The existing henselian and set-valued section comparisons
   remain the appropriate ingredients; closing either geometric hole is not a
   short application of a theorem already stated with these objects and maps.

4. Verdict: the parent follows the shortest available colimit assembly, with all
   proof-only imports written as plain imports. Its four former proof dependencies
   move to both local geometric modules and remain in the import closure; none is
   falsely counted as pruned. The No longer needed section lists all four old
   proof dependencies. Checked sk-lem-universal-datum.realized: its statement list
   and single step list are empty, so this change bypasses no recorded realization.
   No unit record or chapter route changes.

5. Compared the old and new parent proof_deps with the actual applications in Lean;
   they are precisely the local zero and local lift nodes. Checked both new nodes'
   source, proof steps and their union of proof_deps, searches, creation record,
   blueprint ancestry, chapter, unit, and Lean records. Verdict: the DAG agrees
   with the delivered decomposition and records the dependencies still needed
   to prove the two geometric tasks.

Second reading changed only documentation and metadata: added this review and stored
both new nodes' Lean signatures verbatim, with their actual line breaks. No Lean proof,
statement, definition, import, or mathematical route needed repair. Holes closed: the
one original parent hole; holes added: the two reported local theorem holes. This remains
one decomposition with delivery-local net minus one, and no pruned modules.
