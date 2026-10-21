## What changed

Proved CategoryTheory.ExactDerivedPasting.exact_derived_transformation_pasting without
changing its signature or any existing definition. Private helpers construct the word
factorization, establish its empty-word and composition formulas, normalize cells, and
prove the normalization for all eleven expression constructors by induction. The final
proof uses localization uniqueness and the existing derived natural-isomorphism API.

Added the proof-only import Sheaf.CategoryTheory.DerivedCategory.ExactRestrictionComposition
for its proved cochain identity-comparison formula. Removed the redundant public import
Sheaf.CategoryTheory.ExactDerivedComposition; the retained source ExactFunctor import
already supplies the prescribed compositor and its component normalization.
Updated the existing DAG proof and dependencies to match the formal argument.
Import cleanup record: coord/changes/F6-exact-derived-pasting-imports.md.

## Proved and sorry left

Closed one hole:
CategoryTheory.ExactDerivedPasting.exact_derived_transformation_pasting
(lem-sp-exact-derived-transformation-pasting).

Added zero holes; zero sorries remain in the delivered module. No split statements or
new public declarations. The remote single-file compile passed in 9.4 seconds;
#print axioms reported exactly propext, Classical.choice and Quot.sound.
The proof treats empty words, both directions of structural
cells, both whiskerings, and arbitrary noninvertible generating transformations. The
Finite I hypothesis and every existing signature are retained verbatim.

## No longer needed

Removed the redundant direct public import Sheaf.CategoryTheory.ExactDerivedComposition.
Its existence-and-uniqueness theorem is not needed as an extra Lean dependency: the
prescribed compositor already has a proved component-normalization lemma in the source
library. The DAG dependency on the normalized compositor remains, since that mathematical
construction is used by Word.comparison and wordFactors_comp. No node or module is
withdrawn, and no upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The planned argument works with the existing declarations.
The structural cases can use the binary word-factorization formula directly; no separate
coherence theorem or extra induction on words is needed. Invertibility follows directly
from the existing Localization.liftNatIso-based mapDerivedCategoryNatIso construction.
The generic cochain identity-comparison formula was already proved in
lem-pur-exact-restriction-composition and is reused rather than restated.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
