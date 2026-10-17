## What changed

Rebased the returned affine pushforward sections proof onto the synced source and repaired
its removed dependency in the same delivery. Restored the full proof of
`formalFunctions_affine_restriction_dictionary`, importing its private helpers directly
from their new upstream modules and explicitly proving quasi-coherence under restriction.
Restored the retained complete proof of `formalFunctions_affine_pushforward_sections`.
Both modules compile together against the current library. Public statements and definitions
are unchanged. The restored dictionary `lean` attachment and proof text match the repair.

Change record: `coord/changes/A3-formal-functions-dictionary-upstream-private-imports.md`.
The independent second reading below covers the repaired dictionary and the item together.
It removes the dictionary's unused public import of
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`; no proof needed changing.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.formalFunctions_affine_pushforward_sections`
(node `lem-weil-pbc-formal-functions-affine-pushforward-sections`).
Also restored the fully proved
`AlgebraicGeometry.formalFunctions_affine_restriction_dictionary`
(node `lem-weil-pbc-formal-functions-affine-restriction-dictionary`), removed by the sync.
Zero `sorry`s remain in either delivered module. Zero holes added; zero split-offs.
The proof still uses the library's stated dependencies, as intended by stage 3.

## No longer needed

Replaced the two proof-only wrapper imports in the dictionary:
`Sheaf.AlgebraicGeometry.TorsionControlledFormalRestriction` and
`Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`.
Their upstream modules supply the same helpers and are used directly.
Also removed the unused public import
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits` from the dictionary. The pushforward
item retains its own direct import for evaluation preserving limits.
No dependency node or mathematical step is pruned; the unit route stays unchanged.
Every old `proof_deps` entry remains used, including the upstream restriction helpers
recorded under their existing nodes. No module leaves the target import closure here.

## Where the brief, the DAG or earlier work was wrong

An earlier retry recovered the returned proof from commit `5340804d4`. This session
retained that work, compared both files with current main, and compiled the pair with
`lcompile.py --all`. The earlier delivery
relied on a compiled dictionary whose source declaration was commented out. This repair
restores and compiles that source dependency; it no longer relies on a stale compiled name.
The sync also removed the node's `lean` attachment, which this repair restores unchanged.

## Forced adaptations

The dictionary module is currently unclaimed (H2 has a return entry, not a live claim).
It is restored as a necessary dependency repair. The original item error on the synced
source was `Unknown identifier formalFunctions_affine_restriction_dictionary`.
Uncommenting the dictionary's original proof produced `failed to synthesize instance`
for quasi-coherence of the restriction, unknown `Scheme.Modules.finiteType_restrict`,
and unknown `restrictionCompletionIso`. The only substantive proof edits are the two
proof-only upstream imports and the explicit `isQuasicoherent_restrictFunctor` application.
Its original theorem signature and visibility are identical. The change record lists
all downstream modules and their interface checks. No module held by another group is changed.


## Second reading by A3

1. Compared both complete module diffs with the shared repository. The pushforward
   theorem changes only its proof. The dictionary restores the commented theorem with
   its byte-identical signature and visibility; both private helper signatures are also
   byte-identical. Its other changes are the two direct proof-only `import all` lines,
   the explicit quasi-coherence restriction lemma, and removal of one unused import.
   No target, definition body, hypothesis, conclusion, or scalar action changed. The
   dictionary restoration and downstream interface checks have the change record above.
   Verdict: pass.

2. Compiled the pair in import order with `lcompile.py --all`. In separate scratch
   copies, appended `#print axioms` for both public theorems and for the dictionary's
   `affine_restriction_appTop` and `affineRestrictionSectionsIso`. All four show exactly
   `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`. Repeated these checks
   after removing the unused import. Neither delivered file contains a `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by`, or `extern`. The section comparison is built
   explicitly from presheaf restriction maps; no arbitrary witness is chosen to define
   data. Verdict: pass; the item closes one hole, with no added holes.

3. There are no new or split-off statements. The restored dictionary is the original
   finite-level statement, not a restatement of formal functions: it does not assert a
   completion or limit isomorphism. Checked the zero ideal (constant system), unit ideal
   (zero quotients), zero module and empty affine open. The positive index n+1 and the
   direction of both quotient comparison maps agree in all these cases. Its source
   docstring and existing node remain in place. Verdict: pass; zero split-offs.

4. Read Stacks `coherent.tex`, `theorem-formal-functions` (02OC) and
   `lemma-inverse-systems-push-pull` (088B), especially its affine M and M_n calculation.
   Read `globalSections_formal_functions`, the upstream `finiteType_restrict`, and
   `restrictionQuotientIso`, its projection equation and `restrictionCompletionIso`.
   The proof takes the direct route: apply the finite-level dictionary and degree-zero
   formal functions, transport the quotient map through a and b, and transport completion
   and the limit. The hθ proof uses hθ₀ followed by hb; the last equation uses preservation
   of the limit, the natural-isomorphism limit equation and completion congruence.
   The dictionary supplies properness by base change, restricted coherence using local
   Noetherianity and finite type, the ideal equality by affine extensionality, and the
   explicit section and quotient comparisons. No completion theorem is used circularly
   in that dictionary. Searched both Lean roots for an existing affine pushforward
   formal-functions statement; the only direct consumer is
   `formalCompletion_pushforward_limit_app_bijective`, so there is no upstream replacement
   to apply. The remaining explicit imports supply objects in the signatures or the
   proof's restriction, completion and limit constructions. Removed the unused dictionary
   sheaf-limit import and compiled again. Read `dag/units/sk-thm-p1.json`: its realized
   statement and four step lists stay intact, and this affine reduction bypasses none of
   them. `No longer needed` lists all removed imports; no old proof dependency is unused.
   Verdict: pass.

5. Read both nodes and the Lean declarations of each proof dependency. The pushforward
   node's three existing steps describe the proof exactly and its two `proof_deps` are
   used. The dictionary's revised steps name the actual upstream private helpers,
   explicit quasi-coherence restriction, ideal transport and naturality calculation.
   Its four `proof_deps` remain used, with the restriction helper declarations recorded
   in the proof text under their existing owning nodes. `proof_origin` agrees with the
   source just read. Its restored `lean` attachment equals `lean_before_upsync_e47`
   exactly. Only the permitted `lean` and `proof` fields differ from the repository;
   no new nodes need stage-3 metadata. Verdict: pass.

Second-reading changes: removed the unused public dictionary import of
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`, documented that removal in the report
and change record, and added this independent review. The proofs were retained.
