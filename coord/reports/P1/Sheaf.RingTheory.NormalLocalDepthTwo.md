## What changed

Proved `IsLocalRing.depth_two_of_normal` in
`lean/Sheaf/RingTheory/NormalLocalDepthTwo.lean`, with its original signature unchanged.
The proof follows Stacks Tag 031S and the existing Kollár dichotomy. A fully proved
private helper, `finite_extension_surjective`, constructs the fraction-field algebra
map by clearing one fixed denominator and applies integral closedness. Its numerators
are uniquely determined by the injective structure map; no data is taken from an
unproved existence theorem. Added proof-only Mathlib imports for Artinian modules and
Krull dimension of fields. Updated the existing node's proof and dependencies.

Searches: Lean Finder returned dimension-one/Dedekind results but no depth-two theorem;
Loogle returned `IsIntegrallyClosed.algebraMap_eq_of_integral`, used in the proof;
Mathlib grep found no normal-depth theorem. Repository searches found the existing
Kollár dichotomy and nonzerodivisor theorem. Checked the published Stacks Tag 031S text.

## Proved and sorry left

Closed the single hole in `IsLocalRing.depth_two_of_normal`
(node `lem-weil-pbc-normal-local-depth-two`). The private helper is also completely
proved. No `sorry` remains in the delivered module; no holes were added or split off.
This is a proof from existing declarations, including the existing Kollár dichotomy,
whose downstream holes are outside this delivery.

The module compiles without warnings through `lcompile.py`. The dimension-zero and
one cases are explicitly contradicted. The denominator argument works for any nonzero
regular denominator, including a unit; nontriviality of the extension is used to
exclude a zero regular element, and injectivity makes each chosen numerator unique.

## No longer needed

`lem-weil-pbc-artinian-local-unique-prime` is no longer needed by this proof: Mathlib's
`IsArtinianRing.isField_of_isDomain` and `ringKrullDim_eq_zero_of_isField` exclude the
Artinian case directly. Removed this node from the item's proof dependencies.
No original module import was removed; both existing Sheaf proof imports are used.
`lem-weil-pbc-finite-algebra-is-integral` remains a dependency: its Mathlib leaf
explicitly records the elementwise `IsIntegral.of_finite` used here.
The trial import `Mathlib.RingTheory.IntegralClosure.Algebra.Basic` was removed because
its required declarations are already exposed by the existing integrally-closed import.
No additional Sheaf module or lower planned argument was introduced.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement or unusable dependency was found. The original Artinian
unique-prime detour was unnecessary in the domain case. The public statement and all
public imports are unchanged, and the unit's route is preserved.

## Second reading by P1

1. Compared the sole delivered module with the repository version. The existing theorem
   signature and docstring are byte for byte unchanged, as is the node statement. The
   only additions are a private proved helper, two proof-only imports, and the proof.
   No statement or definition change requires a change record. Verdict: pass.
2. Compiled the module without warnings through `lcompile.py`, and compiled a scratch
   copy with `#print axioms` for both declarations. The helper uses only `propext`,
   `Classical.choice`, and `Quot.sound`; the main theorem also uses `sorryAx` from
   existing imported open declarations. No sorry remains here, no forbidden declaration
   was introduced, and there is no hollow definition. Verdict: pass.
3. No statement was split off and no hole was added. Reviewed the fully proved helper:
   a nonzero regular denominator and injectivity uniquely determine every numerator;
   the explicit algebra map preserves products and is injective. Unit denominators
   work, and a zero denominator is excluded. Repeated Lean Finder and Loogle searches
   with finite-birational-extension queries and searched the repository and Mathlib;
   no duplicate that removes this construction was found. Verdict: pass.
4. Checked the top-down dichotomy argument, its dimension-zero and dimension-one
   contradictions, and the `sk-thm-p1` unit's `realized` statement and steps. This
   auxiliary node changes none of those steps. Both existing Sheaf proof imports are
   used, and both added Mathlib imports are proof-only. The sole removed old dependency,
   the Artinian unique-prime lemma, is listed above. Verdict: pass.
5. Compared the node with the proof. Its `proof`, `proof_deps`, and `proof_origin` match
   the Lean argument. The finite-integrality dependency remains valid: its Mathlib
   match explicitly includes the `IsIntegral.of_finite` used here. No new node is needed
   for a private fully proved implementation helper. Verdict: pass.

Changed only this report: added the second reading and clarified the retained
finite-integrality Mathlib dependency. The Lean proof and node required no repair.
