## What changed

Proved `SheafOfModules.exists_localizedSiteTensorRestriction` with its original signature
and docstring. The comparison is constructed using the module sheafification adjunction,
proved invertible by local bijectivity of the two sheafification units, and composed with
the sectionwise identity identification of tensor presheaves. Private helpers establish
its naturality and pure-tensor formula; the final proof inverts this specific comparison.
No definitions or signatures visible to consumers change. The private isomorphism
lemma is registered only locally inside the module namespace.

Change record: `coord/changes/C4-localized-site-tensor-proof-scopes.md` documents
the proof sections and local commands conservatively classified as interface changes.

Replaced the proof import `Mathlib.CategoryTheory.Sites.CoverLifting` by
`Mathlib.CategoryTheory.Sites.PreservesLocallyBijective`. Removed the unused proof import
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, which had been added
to the current source after the retained proof was written. The other imports are retained
for their existing statements or for module sheafification. Updated the item's node proof,
proof dependencies and proof origin to describe this direct specialized comparison.

## Proved and sorry left

Closed the original single hole:
`SheafOfModules.exists_localizedSiteTensorRestriction`
(node `lem-sfb-localized-site-tensor-restriction`).

Holes added: zero. Holes left in the delivered module: zero. No split-offs.
Validation: the resumed single-file `lcompile.py` check passed cleanly in 20.5 seconds;
the original theorem signature is textually unchanged and every Lean line is at most
100 characters.
The proof uses the existing tensor constructions and their pre-existing proof dependencies;
this does not assert that all transitive dependencies in the library are already sorry-free.

## No longer needed

Removed the direct proof imports `Mathlib.CategoryTheory.Sites.CoverLifting` and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`. The latter provides
cochain monoidal instances that this proof does not use; the tensor presheaf and
sheaf constructions used here are already exposed by `SiteTensorFunctoriality`.
The general slice-sheafification comparison node
`lem-cbc-sieve-slice-sheafification` is no longer a proof dependency of this item:
its needed specialization is proved here directly under the original hypotheses, using
module sheafification and preservation of local bijectivity. No Sheaf or WeilConjectures
module is withdrawn. The other three planned proof dependencies are all used.

## Where the brief, the DAG or earlier work was wrong

The retained sandbox had two unfinished helper statements asserting naturality and the
pure-tensor formula for an arbitrary family of isomorphisms. Such a family need not obey
either normalization or naturality (already a sign automorphism can violate normalization).
Those helpers had never been delivered and are removed. Their replacements are proved
private lemmas for the constructed comparison, with no additional assumptions.

The mathematical node statement and its unit route require no correction. The direct
module-adjunction construction also avoids transporting an abelian action afterwards:
linearity is part of the morphism constructed by the module adjunction from the beginning.

The previous delivery attempt stopped at a temporary-worktree checkout timeout. On
resumption no delivery process for this item remained active; the required dry run was
restarted with the retained sandbox. The proof compiles against the current server baseline. The first resumed preflight
requested a change record for added proof-scope commands; this delivery includes it
and replaces the private global instance with a local registration of a proved lemma.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
