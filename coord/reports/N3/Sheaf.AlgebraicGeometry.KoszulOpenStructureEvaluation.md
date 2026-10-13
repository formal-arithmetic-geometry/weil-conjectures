## What changed

Reduced `AlgebraicGeometry.koszulOpen_structure_evaluation` without changing its
signature, visibility, universes or hypotheses. The main proof specializes a
natural evaluation on an arbitrary open and composes its unit normalization with
the exponent-one normalization.

Added `KoszulOpenSectionsUnit`, with concrete definitions for the extended single
structure complex, the termwise tilde-to-sections unit, its ordinary homology
class and its image under the ordinary-to-derived sections comparison. All data
are constructed explicitly; no witness is chosen from an unproved existence
statement.

Added `KoszulOpenAugmentationCechUnit`, isolating the ordinary Cech homology
calculation. Added `KoszulOpenExponentOneUnit`, which transports this ordinary
calculation to the derived normalization using the proved chain-class
naturality theorem. Its private compatibility lemma proves that ordinary Cech
augmentation followed by the derived Cech comparison is the derived-sections
unit, using the comparison's K-injective-resolution equation.

## Proved and sorry left

Original hole closed by decomposition:
`AlgebraicGeometry.koszulOpen_structure_evaluation`
(`lem-sc-koszul-open-structure-evaluation`), 1 of 1 original holes.

The delivery adds exactly two holes:

- `AlgebraicGeometry.derivedOpenStructure_evaluation_unit`
  (`lem-sc-derived-open-structure-sections-unit`): general open evaluation,
  normalized at the concrete ordinary-to-derived unit; independent of the
  Koszul/Cech class calculation.
- `AlgebraicGeometry.koszulOpen_augmentation_cech_unit`
  (`lem-sc-koszul-open-augmentation-cech-unit`): equality of ordinary Cech
  homology classes; requires no derived-category instances, evaluation family,
  naturality claim or inverse augmentation.

`AlgebraicGeometry.koszulOpen_exponent_one_unit`
(`lem-sc-koszul-open-exponent-one-unit`) is proved from the ordinary cycle
statement and existing chain-class naturality. The private
`cechAugmentation_sections_unit` is proved, not left with a hole.

This is a decomposition, not a sorry-free proof: one original hole is closed
and two strictly smaller independent obligations are added. The local hole
count therefore increases by one. The canonical definitions contain no sorry.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.DerivedStructureSheafHomHypercohomology` from the item;
it is retained in `KoszulOpenSectionsUnit` as the general comparison ingredient.
The original public import of `KoszulOpenHomChainRepresentatives` stays because
the original statement uses its definitions.

The old direct proof dependencies no longer used by the item's proof are
`lem-pc-derived-structure-sheaf-hom-hypercohomology`,
`def-sc-koszul-open-system`, `def-sc-koszul-cech-comparison-construction`, and
`lem-sc-koszul-open-hom-chain-representatives`. They remain statement dependencies
or are used by the new intermediate modules; none is globally pruned.

No existing dependency module is claimed globally pruned. The Koszul system,
Cech comparison and chain-class definitions remain necessary, now through the
smaller ordinary-cycle and derived-normalization statements. The unit's
`realized` record has no statement or step realized by this item; its route is
unchanged.

## Where the brief, the DAG or earlier work was wrong

The general structure-sheaf Hom/hypercohomology theorem exposes an existential
natural family but no normalization formula. Its statement alone does not
justify that an arbitrarily selected family evaluates the structure identity
to the prescribed Cech class. The new general-open obligation explicitly
retains evaluation of the identity as the concrete sections unit; its docstring
explains the cycle construction needed for that normalization.

The signed fraction formula and the Cech-to-derived resolution comparison are
available separately, but their compatibility with the structure unit was not
a named interface. The private compatibility proof now handles the derived
comparison, leaving just the ordinary cycle calculation.

Edge cases checked from the constructions: empty U and r=0 give zero Hom and
sections groups; zero f_j gives an empty principal open, so localized
cancellation remains valid; the zero ring gives zero modules throughout. At
p=q=0 the sign is +1. No nontriviality, quasi-coherence or boundedness assumption
was added. The two chosen localization universes are compared by their canonical
isos. Searches used Lean Finder, Loogle, grep on both library roots and the DAG,
and blueprint searches for evaluation at one, augmented identity and Koszul.
LeanSearch returned Internal Server Error; no mathematical verdict was inferred.
The relevant official Stacks pages 09M1, 06Z0, 08D1 and 08DC were read.

## New nodes

`lem-sc-derived-open-structure-sections-unit` records the normalized evaluation
on any open and the concrete unit constructions in `KoszulOpenSectionsUnit`.
Its new hole is the first independent part of the original argument.

`lem-sc-koszul-open-augmentation-cech-unit` records the ordinary exponent-one
augmentation calculation in `KoszulOpenAugmentationCechUnit`. Its new hole is
strictly below the original derived normalization and has no derived hypotheses.

`lem-sc-koszul-open-exponent-one-unit` records the proved passage from ordinary
Cech homology to the derived normalization in `KoszulOpenExponentOneUnit`.
All three inherit the item's chapter, unit and blueprint ancestor. No existing
statement or definition interface is changed, and no change record is needed.


## Second reading by N3

1. Compared the item with the repository version using a file diff. Its existing
   signature, universes, visibility and hypotheses are byte-for-byte unchanged;
   only its proof and a plain proof import change. The other three modules are
   new. No target or existing definition changes, and no change record is needed.
2. Read all four modules. The two reported named public theorems are the only
   source holes; no definition contains a hole or chooses arbitrary data from an
   unproved existence statement. The private comparison proof uses the defining
   resolution equation, cancels genuine isomorphisms, and then uses naturality.
   All four modules compiled in the sequential dry run, which passed preflight.
   An explicit scratch-copy #print axioms check compiled successfully: every new
   definition uses only propext, Classical.choice and Quot.sound; the four named
   theorems additionally use sorryAx, exactly as expected for the two open
   obligations and the results depending on them. The temporary copy was removed.
3. Read both split statements and their complete docstring arguments. They are
   independent proper parts of the original argument, not renamed restatements:
   general-open normalized evaluation has no Koszul cycle, and the ordinary Cech
   equality has no derived evaluation. Checked empty opens, r=0, zero generators,
   the zero ring, and the singleton sign. Read Stacks 09M1, 08D1 and 08DC against
   the constructions. Independent searches used `unitHomEquiv`, cohomology as
   morphisms from the structure sheaf, and `"toOpen", "homology"`; they found
   ordinary unit evaluation and single-complex homology ingredients, but no
   complete normalized open evaluation or augmentation/Cech unit theorem.
   The DQCoheratorAdjunction cycle/sections comparison is private and does not
   expose either required normalization. Neither hole has a short existing proof.
4. Verified the actual reduction and its chain-class-naturality transport, and
   checked imports against the public signatures and concrete definition bodies.
   The item retains its original public import. All four original direct proof
   dependencies are now explicitly accounted for under No longer needed; they
   remain needed transitively or in signatures, so no global pruning is claimed.
   sk-thm-picard-duality has empty realized statement and step lists; no unit
   route is bypassed. Verdict: a decomposition, closing one hole and adding two,
   rather than a net reduction in holes.
5. Compared each node's Lean signature and proof steps with its module. The
   original node uses exactly the two new intermediate results. The exponent-one
   node records the proved comparison/naturality calculation; the other nodes
   record the two open obligations. New nodes have sources, searches, ancestry,
   chapter/unit, created and lean records. No existing statement field changes.

Second reading changed report bookkeeping only: explicitly listed the old direct
proof dependencies and documented these checks. No correct Lean proof was rewritten.
