## What changed

Replaced the sorry in `AlgebraicGeometry.etaleSetStagePresheaf_locallySurjective` by a
complete Lean proof from finite local representatives and eventual matching. The public
signature and its existing docstring are unchanged. The argument follows the existing
unit route and the finite-cover existence argument of Stacks Sites 0A35, with the affine
étale presentation of 0EYL (the geometric input to 09YQ).

The proof obtains a finite affine covering family at a stage, transports that exact
family to a later stage where it is compatible, and glues by the stage sheaf axiom.
Naturality and separatedness of the continuous pushforward of the limit sheaf identify
the glued image with the prescribed limit section. The iterated-pullback isomorphism
then identifies this map with `etaleSetSectionComparison`. The supplied Arrow equality
transports both endpoints to the arbitrary cocone. Finally `colimit.ι_desc` makes the
coprojection of the representative a preimage in the presheaf colimit.

Added `EtaleSetSheafComparison`, an actual construction of the sheaf-level comparison,
and two theorem modules, one per remaining geometric step. The comparison uses the
existing uniquely unit-characterized composition isomorphism, whose theorem is proved;
it chooses no arbitrary object from an unproved existence statement.

Validation: all four modules compile together through `lcompile.py --all`, without
warnings. The required `deliver3.py --no-push` dry run passed the axiom probes and
preflight; only the second reader’s section remains, as expected. The generic sheaf gluing lemma, the endpoint-transport lemma, the global
representative assembly, and the colimit assembly have complete proofs. Edge cases
checked: n = 0, empty test objects, identical overlap indices, and sheaves with no
sections. Neither new theorem asserts the existence of a section on an empty object
of G. Affineness of the finite covering objects is explicitly required in matching
descent, so their overlaps admit finite affine refinements. An arbitrary finite list
of possibly non-quasi-compact étale objects would not justify that step.

## Proved and sorry left

Closed: `AlgebraicGeometry.etaleSetStagePresheaf_locallySurjective`
(node `lem-weil-pbc-sets-stage-presheaf-locally-surjective`). No sorry remains in the
item's module, including its private helpers.

Added and left with exactly `:= by sorry`:

- `AlgebraicGeometry.etaleSet_finiteLocalStageRepresentatives`
  (`lem-weil-pbc-sets-finite-local-stage-representatives`). This produces a finite
  affine stage cover and individual representatives; it asserts no matching.
- `AlgebraicGeometry.etaleSet_eventualLocalStageMatching`
  (`lem-weil-pbc-sets-eventual-local-stage-matching`). Given such a family, this
  makes the exact base-changed family compatible at a later stage; it asserts no
  global stage section and no presheaf-colimit surjectivity.

This is a decomposition: one upper hole closed, two strictly smaller holes added;
net holes closed minus added is -1 before any later pruning or lower proofs. The
sheaf gluing and categorical assembly are proved here, not moved into either hole.

## No longer needed

Removed the original direct proof imports:

- `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`;
- `Sheaf.AlgebraicGeometry.AffineEtaleInverseImageComparison`;
- `Sheaf.CategoryTheory.ColimitSites`;
- the redundant direct import `Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`
  (still reached through the public section-comparison module).

The first two geometric statements remain inputs to the new lower nodes' proof
plans, rather than being used to pretend a direct application proves this item.
The generic inverse-image section-colimit formula of `ColimitSites` is not used
by the new local-representative/matching route; its category/site construction may
still be reached through the affine site presentation. No claim is made that any
of these modules is now globally unreachable.

Removed all six old direct proof-dependency edges from the item:
`lem-weil-pbc-affine-etale-site-colimit`,
`lem-weil-pbc-sets-affine-etale-inverse-image-comparison`,
`lem-weil-pbc-affine-etale-site-topos`, `lem-weil-pbc-colimit-of-sites`,
`lem-weil-pbc-sets-etale-inverse-image-composition-units`, and
`lem-weil-pbc-presheaf-colimits-sectionwise`. The affine site
presentation, affine inverse-image comparison, affine-site restriction equivalence,
and inverse-image composition units remain below the new nodes as needed. The
`lem-weil-pbc-colimit-of-sites` section formula and
`lem-weil-pbc-presheaf-colimits-sectionwise` are not used by the item's Lean assembly.
The last step uses only the universal property `colimit.ι_desc`, without computing
the presheaf colimit sectionwise. No public import was removed or privatized.

## Where the brief, the DAG or earlier work was wrong

The original plan's generic `ColimitSites` theorem is for Cat.{u,u} and Type u,
whereas the affine-site presentation is in Cat.{u,u+1} and these sheaves take values
in Type (u+1). It cannot be applied directly. The present reduction avoids that
universe transport by separating concrete finite local representatives and eventual
matching from the formal sheaf assembly.

The existing `EtaleSetSectionFiniteMatching`, `EtaleSetSectionPairMatchingEventually`,
and `EtaleSetSectionLiftLocalFamily` are not usable lower lemmas: their imports already
reach this item. `import_direction.py may` rejects importing the first two from the
item. Their fixed-base objects also differ from the stage cover objects needed here.
The new matching theorem works on the stage cover and transports its exact family.

The object's equality hypothesis and diagram-map equations are redundant for this
surjectivity proof: the supplied cocone-leg Arrow equalities already identify both
section-type endpoints. They remain in the signature unchanged.

The local checkout has no Stacks source at the conventional literature path; the
source was read at the Stacks pages for 0A35 and 09YQ. Searches were performed with
msearch: LeanFinder returned structure-sheaf continuity hits, Loogle found the generic
local-surjectivity criterion, and grep found no exact new declaration. LeanSearch
returned Internal Server Error and is recorded as unavailable, not as no match.
Blueprint searches for finite local stage sections, matching sections, and inverse
image units found no exact blueprint node.

## New nodes

`def-weil-pbc-sets-sheaf-comparison`, in
`lean/Sheaf/AlgebraicGeometry/EtaleSetSheafComparison.lean`, constructs the existing
unit-and-composition map before evaluation and fibre-product transport. Its definition
contains no sorry and agrees definitionally with the part of the existing section
comparison before the last restriction.

`lem-weil-pbc-sets-finite-local-stage-representatives`, in
`lean/Sheaf/AlgebraicGeometry/EtaleSetFiniteLocalStageRepresentatives.lean`, isolates
local representation and finite object/arrow/cover descent, without matching.

`lem-weil-pbc-sets-eventual-local-stage-matching`, in
`lean/Sheaf/AlgebraicGeometry/EtaleSetEventualLocalStageMatching.lean`, isolates eventual
matching of the exact finite base-changed family, without sheaf amalgamation.

No existing interface changed, no forced adaptation was made, and no change record
is needed. The item's copied node now records these two geometric steps and the
proved gluing/coprojection assembly.

## Second reading by Q2

1. Interface preservation: PASS. Read the diff of the only pre-existing delivered
   module against the repository. The existing theorem signature and docstring are
   byte-for-byte unchanged; no existing definition or target changed. The other
   three modules are new. All existing public imports are retained. No change
   record or adaptation is needed.
2. Proof and trust: PASS as a decomposition. All four modules compile locally
   through lcompile.py --all without warnings. Read the gluing, endpoint transport,
   global-representative assembly, and colimit assembly proofs. Exactly the two
   reported public theorem bodies contain sorry. No definition contains a hole;
   no axiom, unsafe, opaque, implemented_by, or extern occurs. Explicit axiom
   probes of the private helpers, the target, the comparison construction, and
   the composition-units theorem check the permitted standard axioms and sorryAx
   only. The first two private helpers use no sorryAx. The constructed comparison
   chooses only the uniquely unit-characterized composition isomorphism, never
   an arbitrary section from an unproved existence assertion.
3. Split statements: PASS. Read both statements, their source proofs, and their
   nodes. Local representation omits matching; eventual matching fixes a given
   finite affine family and omits amalgamation. Neither restates the item.
   Checked the empty cover, empty test scheme, singleton/identical overlap indices,
   identity refinement, and arbitrary sheaves: the empty-cover sheaf axiom supplies
   the unique section on the empty object. Affine domains and affine Y make overlaps
   affine; there is no illicit finiteness assumption on an arbitrary etale object.
   Independently read Stacks 0A35, 0EYL, and 09YQ online. Searched with different
   words using msearch LeanFinder, Loogle, grep, and rg on the library. LeanFinder
   returned scheme object/arrow descent, not either arbitrary-sheaf statement;
   Loogle did not resolve the current compatible-family identifier; grep found
   general sheaf APIs. Existing finite matching and eventual-equality declarations
   depend on this item and are circular here. No usable duplicate or few-minute
   proof of either geometric hole was found.
4. Route and pruning: PASS. The new proof really glues a matching family and
   computes the cocone comparison using colimit.ι_desc. Every import of the four
   files supports its signature, construction, or proof. The six old direct DAG
   edges are accounted for in No longer needed; geometric units remain in the
   lower proof plans, while the sectionwise presheaf-colimit formula is bypassed.
   Checked dag/units/sk-thm-iff.json and its realized statement/step node: none is
   removed or bypassed by this below-unit decomposition. The net hole count is
   -1 (one closed, two added), not a completed geometric proof. No whole module
   is certified globally pruned.
5. DAG agreement: PASS after metadata repair. Read all four delivered nodes.
   The item's proof steps and dependency union match its two geometric applications,
   comparison construction, sheaf assembly, and colimit assembly. New nodes carry
   sources, proofs, searches, provenance, blueprint ancestry, chapter/unit, and Lean
   records. Replaced the abbreviated signatures in all three new Lean records by
   the exact multiline declaration signatures from the delivered source, using
   the delivery parser convention that omits the noncomputable modifier. Existing node fields outside stage-3 ownership
   are unchanged.

Second reading changed only the three new node signatures and this report: added
an omitted redundant removed import, enumerated all six removed dependency edges,
and recorded the independent review. Lean proofs and statements required no repair.
The delivery closes AlgebraicGeometry.etaleSetStagePresheaf_locallySurjective by
reduction and adds the two named geometric holes listed above.
