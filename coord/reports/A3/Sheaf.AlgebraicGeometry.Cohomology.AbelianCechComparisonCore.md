## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_abelianCechComparison_core` with its
signature and visibility unchanged. Added a proof-only import of the new module
`Sheaf.AlgebraicGeometry.Cohomology.AbelianResolutionSectionsIso`, and a proof-only
Mathlib injective-resolution import (needed for the chosen resolution). Private, proved helpers construct the induced
section and total maps and verify both augmentation squares. The proof uses the
homotopy equivalence from an arbitrary resolution to the chosen one, and cancels
the resulting invertible total-homology map.

The new public theorem `AlgebraicGeometry.Scheme.Modules.exists_abelianResolutionSectionsIso`
is also completely proved. It explicitly identifies the constant-integer Hom complex
with section complexes, then applies Mathlib's homology and Ext equivalences. Its
cocycle formula is proved by transporting cycles and homology projections. No data
is chosen from an unproved existence theorem; no definition has a hole.

Updated the core node's proof, proof_deps and proof_origin to this actual route.
No existing statements, definitions, universes or target declarations changed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.exists_abelianCechComparison_core`
(node `new-abelian-cech-comparison-core`).

Also proved the new helper:
`AlgebraicGeometry.Scheme.Modules.exists_abelianResolutionSectionsIso`
(node `new-abelian-resolution-sections-iso`).

No sorry remains in either delivered module. Holes closed: 1. Holes added: 0.
This is a proof, not a decomposition into new holes. Compilation and declaration
axiom checks are performed by the delivery dry run.

## No longer needed

None. The original public construction import remains necessary for the unchanged
statement and the actual augmentation definitions. The node originally had only
that proof dependency; no original node or module is bypassed. The new helper uses
the source library's `WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap`
through a proof-only import, and neither delivered file has unused imports.

## Where the brief, the DAG or earlier work was wrong

No statement or source error found. The initial node hid the substantial
Hom-complex/section-complex identification under its construction-definition
citation. This delivery proves that identification explicitly, in the new helper,
instead of treating it as an available lemma. Resolution independence is proved
using the reverse lift J -> I and the section functor's preservation of homotopy
equivalences; it does not need a second Ext identification for J.

Checked degree zero (no incoming boundaries), zero sheaves, empty spaces and empty
index families: the helper assumes no cover and the core uses only the supplied
alpha quasi-isomorphisms. The unit `sk-thm-picard-rr` has empty realized statement
and step lists, so no unit realization is bypassed.

Searches: LeanFinder and Loogle returned the existing Ext cocycle APIs; Mathlib grep
found these APIs and no section-homology comparison. LeanSearch returned an internal
server error and is recorded as unavailable. Repository searches found the broader
terminal-resolution comparison for sheafified free representables, whose signature
is not this constant-sheaf cocycle formula. Whole-blueprint searches for injective
resolution/global sections and cohomology/sections found no exact match. Read
Stacks Tag 01EQ and Mathlib's Injective/Ext, HomComplexSingle,
HomComplexCohomology, ExtendHomology and the source library's ExtendMap.

## New nodes

`new-abelian-resolution-sections-iso`, in
`dag/nodes/sec-picard-framework/new-abelian-resolution-sections-iso.json`, records
the completely proved isomorphism between resolution section homology and Ext,
with its exact cocycle formula. It is independent of Cech covers, alpha and beta,
and is strictly the first part of the original argument. Its source, full proof,
actual search records and verbatim Lean signature are included. No change record
is required, since no existing interface changed.

## Second reading by A3

1. **Interface preserved — pass.** Diffed the core module against the repository.
   The full existing theorem signature, including universes, hypothesis hα,
   existential conclusion and comparison predicate, is byte-identical. Its
   visibility stays public. The only new declarations in that module are private
   proved helpers. No definition or statement used by targets is changed, and no
   forced adaptation or change record is needed.
2. **Proof and trust — pass.** Read both delivered modules completely and compiled
   them in import order with lcompile.py: helper 21.2 s, core 4.2 s, no warnings.
   Neither module contains sorry, axiom, unsafe, opaque, implemented_by or extern.
   The helper's printed axioms are exactly propext, Classical.choice, Quot.sound;
   the core prints exactly the same three axioms, and the delivery probe
   accepted all private declarations too.
   sectionHomEquiv and homSectionsComplexIso explicitly construct their data;
   the chosen resolution comes from Mathlib's proved existence machinery, and e
   is obtained from the completely proved helper, not an unproved existence claim.
3. **New statement — pass; no split-off holes.** Checked the helper's node and
   docstring against its Lean: arbitrary scheme X, abelian sheaf F, arbitrary
   injective resolution I, every natural degree q, and every compatible a and z.
   Read Stacks Tag 01EQ (Lemma 20.11.2): its beta/inverse-alpha construction uses
   resolution-section cohomology; here the stronger no-cover formulation is valid
   because quasi-isomorphism of alpha is supplied as an explicit hypothesis.
   The Hom/section equivalence sends a to its adjoint evaluated at 1; differential
   compatibility uses δ_fromSingleMk, and the extended complex's cycles and
   homology projections give exactly extMk's defining representative. Checked
   q=0: extension supplies zero negative degree and no extra boundary; zero
   sheaves and empty schemes need no nonemptiness, and an empty cover enters only
   the conditional hα. This is strictly the section/Ext part of the argument.
   Fresh LeanFinder query used “cohomology of a sheaf computed by applying global
   sections ... canonical cocycle isomorphism”; Loogle checked homotopyEquiv;
   Mathlib grep checked homAddEquiv/homology and uliftZMultiplesAddEquiv. None
   gives the complete helper. Repository searches additionally found
   abelianCechExtSectionIso_exists: it is still sorry and supplies only chosen
   representatives for each Ext class, not the formula for every compatible
   representative needed here. SheafPullbackResolution.extSectionsIso is for the
   small etale site and chosen resolution; the terminal-resolution evaluation
   theorem gives successor degrees and endomorphism naturality, not this formula.
4. **Route and pruning — pass.** The proof first constructs the quotient on one
   resolution. For J, Mathlib homotopyEquiv J I gives a lift of the identity;
   sections preserve its homotopy equivalence. alpha_naturality checks restriction
   naturality explicitly, beta_naturality uses the augmentation identity, and hα
   plus invertibility of the section map makes the total map invertible. The
   transported cocycle has unchanged Ext class by extMk_comp_mk₀, and cancellation
   proves the predicate on J. The new helper is proved, so this does not move a
   hole into an imported statement. The original proof_deps consisted solely of
   def-pc-abelian-cech-comparison-construction, still used; none is pruned. Tested
   removing the direct Resolution import: compilation failed at injectiveResolution,
   so restored it. The helper's ExtendMap import provides mapExtendIso. Public
   imports supply the unchanged/new signatures; proof-only imports stay plain.
   Read sk-thm-picard-rr's realized fields: statement [] and steps [[]]; the
   section/Ext identification and augmented-double-complex route are retained.
5. **DAG/Lean agreement — pass.** Compared both recorded lean.statement strings
   with the files verbatim; both match. In each node proof_deps equals the union
   of proof-step uses. The core cites the proved new helper and the unchanged
   construction node; its resolution direction J -> I matches the code. The new
   node's source, complete three-step proof, actual search records, creation data,
   blueprint ancestor/via/place, chapter, unit and Lean record are present. Only
   proof, proof_deps and proof_origin differ in the existing node.

Second reading changed the core node's ambiguous “followed by its inverse” to
“followed by the inverse of H^q(alpha_I)” so the DAG cannot be read as inverting
beta. Removed duplicate blank lines in both Lean modules and clarified the needed
resolution import in this report. No proof repair or statement change was needed.
The final dry run returned OK: both modules compile and preflight passes.
Review class: CODEX (adds a proved public helper, its module and node).
