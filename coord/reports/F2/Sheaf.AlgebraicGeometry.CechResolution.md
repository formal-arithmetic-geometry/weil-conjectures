## What changed

Replaced the sorry in `AlgebraicGeometry.cech_resolution_derived_direct_image` by a
complete Lean proof from two narrower intermediate statements. Its signature and
existing docstring are unchanged. Added the modules
`Sheaf.AlgebraicGeometry.CechSheafResolution` and
`Sheaf.AlgebraicGeometry.AffineOpenPushforwardAcyclic`, each with one public named
statement, a source, a complete proof in words, and its own DAG node.

The main proof obtains the exact sheaf resolution, proves each finite nonempty
intersection affine, applies the single-affine-open acyclicity statement, and uses
Mathlib's closure of an object property under finite products to obtain termwise
acyclicity. This includes an empty product. The single-object derived homology
comparison converts classical right acyclicity to the exact higher-direct-image
vanishing in the original statement.

The private helper `derived_iso_of_acyclic_resolution` is fully proved: extend the
resolution by zero to integer degrees; acyclicity survives extension; the bounded-below
derived unit is invertible; bounded-below/unbounded compatibility and the quotient
factorizations give the derived-category isomorphism. Extending the augmentation and
using the single-complex extension isomorphism gives precisely the required source
object. The argument uses the full Čech complex, without a bounded-above assumption.

Added proof imports of `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology`,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`,
`Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`, and the two new
modules. Updated the original node's proof, proof_deps and proof_origin. No existing
public interface or target statement changes, no forced adaptations, and no definition
chooses data from an unproved existence theorem.

## Proved and sorry left

Closed: `AlgebraicGeometry.cech_resolution_derived_direct_image`
(node `lem-pc-cech-resolution`), one of one original holes. The private helper
`derived_iso_of_acyclic_resolution`, finite-product assembly, higher-image comparison,
and the proof combining the two intermediate statements all compile with no sorry.

Added and still sorry:

- `AlgebraicGeometry.exists_cech_sheaf_resolution`
  (node `lem-pc-cech-sheaf-resolution`): construction, sectionwise identifications,
  augmentation, term isomorphisms, and local exactness only; no derived image or
  acyclicity assertion. It works for any open cover and any module sheaf.
- `AlgebraicGeometry.affine_open_pushforward_rightAcyclic`
  (node `lem-pc-affine-open-pushforward-acyclic`): classical acyclicity of direct image
  from one affine open only; no cover, complex, resolution or final isomorphism.

This is a decomposition: one original hole closed and two strictly smaller holes
added, not a net sorry reduction. The item has no remaining sorry. Edge cases checked
mathematically: zero modules, empty affine opens, empty cover of the empty scheme,
empty finite products, singleton covers, and repeated tuples. In particular, the
full singleton Čech complex has nonzero terms in arbitrarily high degrees.

## No longer needed

Removed the original proof imports:

- `Sheaf.CategoryTheory.FiniteAcyclicResolution`
- `Sheaf.CategoryTheory.GrothendieckComposablePair`
- `Sheaf.CategoryTheory.GrothendieckSpectralSequence`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism`

The finite acyclic-resolution node `lem-pc-derived-acyclic-resolution` and its module
`Sheaf.CategoryTheory.FiniteAcyclicResolution` are not needed anywhere in this route.
The general bounded-below acyclic-unit argument replaces that node.

The composable-pair, spectral-sequence and affine-morphism-vanishing nodes remain
planned dependencies of the new single-affine-open statement; removing their direct
imports from the item is not a claim that those nodes are globally obsolete. The
ringed-site resolution node remains needed through the public scheme-derived-image
infrastructure. The affine-intersection node also remains needed by the main proof.
No unit statement or realized proof step is bypassed: the unit record
`sk-thm-picard-semicon` has no binding realized nodes for this auxiliary item.

All original public imports are retained. A redundant experimental proof import of
`Mathlib.Algebra.Homology.Embedding.ExtendHomology` was removed; it is already public
through the source-library PlusSingle module. New statement modules import only the
modules needed by their signatures. The second reader removed the redundant direct
public import `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian` from
`CechSheafResolution`; it is already publicly imported by the module-sheaf module.

## Where the brief, the DAG or earlier work was wrong

The original node's last step described the alternating finite complex and asserted
vanishing above the number of opens. The Lean statement specifies the full Čech
complex, indexed by all tuples including repeats, so that assertion does not apply
to its D. The delivered argument uses a bounded-below acyclic complex instead and
requires no finite-length assertion. The target signature itself is unchanged.

Also, the planned `FiniteAcyclicResolution` declaration provides cohomology
isomorphisms, not the derived-category isomorphism requested here. The latter is
proved in Lean from the invertible bounded-below unit and unbounded compatibility.

The blueprint source file named by the existing node is not present in this local
read-only checkout. The full original node proof and all planned dependency
signatures were read; the two new proof sketches expand those recorded paragraphs.
LeanSearch returned Internal Server Error for both new statements, recorded as
unavailable. LeanFinder, Loogle, library rg, the recorded Mathlib grep search, and
blueprint searches found no existing statement supplying either missing part.

A transient full-filesystem error truncated the working copy during development;
the original source was restored from the repository, the proof was rewritten, and
all delivered files were subsequently compiled together. Repository source was
never edited directly.

## New nodes

`lem-pc-cech-sheaf-resolution` in
`dag/nodes/sec-picard-framework/lem-pc-cech-sheaf-resolution.json` realizes the
construction and local-exactness part of the original proof paragraph 1, in the new
`CechSheafResolution` module. It is strictly independent of the morphism f and its
acyclicity and derived-image conclusions.

`lem-pc-affine-open-pushforward-acyclic` in
`dag/nodes/sec-picard-framework/lem-pc-affine-open-pushforward-acyclic.json` realizes
paragraphs 2-3 for a single affine open, in the new `AffineOpenPushforwardAcyclic`
module. Finite products and the final comparison are proved in the item, not moved
to this hole. Neither new node duplicates a whole original statement.

## Second reading by F2

1. **Interfaces: PASS.** Compared every delivered module with the repository. The only
   existing module changed is CechResolution; its existing theorem signature and
   docstring are byte-for-byte unchanged. The two other modules are new. There are
   no definition changes, no changed hypotheses or conclusions, and no change records
   or forced adaptations are needed.
2. **Proof and kernel checks: PASS.** Compiled all three modules using lcompile.py in
   import order, without errors or warnings. Only the two reported public named
   intermediate theorems contain sorry, each as its entire proof. No forbidden
   declaration or hollow definition is present. Scratch copies with #print axioms
   checked the main theorem, its private derived-category helper, and both new
   theorems: only propext, Classical.choice, Quot.sound and sorryAx occur. The helper
   has no sorryAx. The main theorem remains conditional on the two reported holes
   and already-open infrastructure; this is a decomposition, not a net proof gain.
3. **Split statements: PASS.** Read both statements, proof docstrings and nodes.
   The first asserts only construction and local exactness of the augmented sheaf
   complex; the second only acyclicity of one affine-open direct image. Neither
   restates the original derived-image theorem. Checked zero sheaves, empty affine
   opens, an empty cover of the empty scheme, singleton covers, repeated tuples,
   and arbitrary covers for the construction. Local insertion is valid on every
   open contained in a cover member, without commuting infinite products with
   stalks. Affine-open acyclicity uses separatedness to make the inclusion affine
   and exact restriction to make its direct image preserve injectives. Repeated
   searches with LeanFinder (open-immersion/composite acyclicity and insertion
   contraction queries), Loogle (rightAcyclic and cechComplexFunctor), and rg on
   Mathlib, both library roots and the related resolution modules found no exact
   duplicate or immediately applicable shorter theorem. Closing either remaining
   statement requires substantial construction or composition infrastructure.
4. **Route and pruning: PASS.** Read the bounded-below unit theorem and compatibility
   source, the original finite-resolution declaration, all original proof-dependency
   declarations, and dag/units/sk-thm-picard-semicon.json. The main proof genuinely
   assembles the resolution, affine intersections, finite products (including the
   empty product), positive-degree homology comparison and derived-category iso.
   It does not assume the full repeated-index complex is bounded above. The unit's
   realized statement and step arrays are empty; no assigned unit realization is
   removed. All four removed old proof dependencies are accounted for:
   lem-pc-derived-acyclic-resolution is replaced by the proved bounded-below helper;
   lem-pc-affine-morphism-hi, def-sp-composite-acyclicity and thm-sp-grothendieck move
   into the planned proof of lem-pc-affine-open-pushforward-acyclic, so are not claimed
   globally obsolete. The ringed-site node remains through public infrastructure.
   Tested removal of EnoughInjectives: compilation fails, so retained it.
5. **DAG: PASS.** Compared the existing node JSON: only proof, proof_deps and
   proof_origin changed. Verified the new nodes' statements and normalized Lean
   signatures against their modules; sources, complete proof steps, dependency
   unions, searches, creation records, blueprint ancestry, chapter and unit are
   present. The existing node describes the actual bounded-below argument. The
   acyclic-unit theorem is a proved tool in the Leray-acyclicity implementation,
   and the homology/compatibility modules supply the remaining comparisons.

Changed on second reading: removed the redundant direct public Abelian import
from CechSheafResolution and expanded this report's explicit dependency accounting
and verification evidence. No mathematical statement or proof was rewritten.
