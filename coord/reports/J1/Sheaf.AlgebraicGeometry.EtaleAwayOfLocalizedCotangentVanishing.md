## What changed

Proved `AlgebraicGeometry.exists_etale_away_of_localized_cotangent_vanishing` in
`Sheaf.AlgebraicGeometry.EtaleAwayOfLocalizedCotangentVanishing` without changing its
signature. The second reader changed the proof-only Etale.Locus import to a plain import. The localized vanishing hypotheses give membership in
Mathlib's étale locus, `Algebra.exists_etale_of_isEtaleAt` gives an étale principal
localization, and `HasRingHomProperty.Spec_iff` with `RingHom.etale_algebraMap` gives the
scheme conclusion. Updated the item's DAG proof to this shorter route. No new modules,
statements, or nodes were needed.

Read Mathlib Etale/Locus.lean, RingTheory/Support.lean, RingHom/Etale.lean,
and AlgebraicGeometry/Morphisms/{Etale,RingHomProperties}.lean. LeanFinder and Loogle
confirmed the two locus lemmas; local searches checked the signatures and the existing
cotangent-criterion node. The proof compiles cleanly with the prescribed local compiler.
The item's node is absent from the unit's `realized` statement and step lists, so this
change only prunes below the unit route.

## Proved and sorry left

Proved `AlgebraicGeometry.exists_etale_away_of_localized_cotangent_vanishing`
(node `lem-weil-pbc-etale-near-prime-naive-cotangent-vanishing`). One of one original
sorries closed. No sorry remains in the item or is added elsewhere. All proof dependencies
are Mathlib declarations, with no project sorry used.

## No longer needed

No imports removed. Mathlib.RingTheory.Etale.Locus is now a plain proof import;
Mathlib.AlgebraicGeometry.Morphisms.Etale remains public for the statement.
The retained public import supplies all statement vocabulary without Etale.Locus.
Change record: coord/changes/EtaleAwayOfLocalizedCotangentVanishing-proof-import.md. The following original proof-only dependencies are no longer
needed by this item (their definitions may still occur in its statement dependencies):

- `lem-weil-pbc-smooth-at-prime-naive-cotangent-criterion`
  (Mathlib.RingTheory.Smooth.Locus)
- `lem-weil-pbc-kahler-differentials-localization`
  (Mathlib.RingTheory.Etale.Kaehler)
- `lem-weil-pbc-smooth-ring-map-principal-localization`
  (Mathlib.RingTheory.Smooth.Basic)
- `def-weil-pbc-smooth-ring-map`
- `def-weil-pbc-kahler-differentials`
- `def-weil-affine-spectrum`
- `def-weil-etale-morphism`

The Mathlib modules listed remain available transitively; no independent Sheaf statement
module for these lemmas is imported or needed here. The affine étale criterion is retained.
The existing Mathlib leaf `lem-sc-etale-at-prime-formally-etale-cotangent-criterion` is used
as a generic tool: its statement is precisely the vanishing-to-IsEtaleAt step for any
commutative algebra, with no abelian-variety assumptions.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original node's searches already recorded the complete
short Mathlib chain, although its proof still followed the longer smoothness/localization
plan. That chain suffices directly. The existing declaration docstring records the original
plan and is preserved; the DAG proof and this report describe the implemented route.


## Second reading by J1

1. Compared the only delivered module with the repository using diff: the entire
   declaration signature is byte for byte unchanged; no definition or new declaration
   is introduced. The only additional repair is import visibility, recorded below.
2. The module compiles without errors or warnings through lcompile.py. A scratch copy
   with `#print axioms AlgebraicGeometry.exists_etale_away_of_localized_cotangent_vanishing`
   reports exactly propext, Classical.choice, Quot.sound. No sorry or forbidden construct
   remains. Both localized vanishing assumptions are used, in the correct order for
   the support intersection (differentials first, H1 second). FinitePresentation is
   supplied to exists_etale_of_isEtaleAt; primality gives h outside q.
3. No split-off statement or new node exists, so there are no new small-case claims or
   docstring holes to validate. Independently read Etale/Locus.lean:59-110,
   Support.lean:45-57, RingHom/Etale.lean:28-38, and RingHomProperties.lean:360-364.
   Loogle confirmed exists_etale_of_isEtaleAt with exactly the required hypotheses;
   rg on both project roots found no shorter declaration of this localized conclusion.
4. The three-step Mathlib route is direct and sound. The original seven dependencies
   absent from the new proof_deps are all listed under No longer needed. Read the unit
   sk-thm-p1 realized lists: this item is neither a statement nor a step carrier, and
   using the generic Mathlib cotangent criterion from the other unit does not bypass
   the unit route. Tested import visibility in a scratch copy: Etale.Locus can be plain
   because no symbol specific to that module occurs in the signature. Both direct
   importers already import this item privately, and the cotangent-criterion importer
   independently publicly imports Etale.Locus, so no downstream adaptation is needed.
5. Read the delivered node and both retained Mathlib leaf nodes. The support criterion,
   principal localization existence, and affine Spec criterion agree with the actual
   Lean applications; proof_deps equals the union of uses and proof_origin names the
   implementation sources. The Mathlib existence application is explicitly recorded
   in the elementary step, without adding a duplicate node.

Changed only Etale.Locus from public to plain import, corrected the report's claim that
both imports were statement imports, and added the import change record. The proof and
node were otherwise right and remain unchanged. One original hole closed, zero added;
this is a proof, not a decomposition. The existing docstring describes the older valid
plan; the node and report document the shorter implemented proof.
