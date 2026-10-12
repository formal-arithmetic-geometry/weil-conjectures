## What changed

Repair of return X-35c09, C1: added `lem-weil-pbc-sheafification-exact` to the
adjunction node’s first proof-step `uses` and `proof_deps`. Replaced that step’s
text with the reviewer’s prescribed direct-sum, monomorphism, sheafification,
and exactness argument. This repairs the missing non-elementary citation;
the Lean statements and proofs are unchanged.

Repair of return X-bbb80, C1: added `lem-weil-pbc-right-adjoint-preserves-kinjective` to the target node’s proof-step `uses` and `proof_deps`. This records the non-elementary `Adjunction.preservesKInjectiveComplexes` dependency already used by the Lean proof.

Repair of return X-53d80: removed the unused public import
`Mathlib.Algebra.Category.Grp.FilteredColimits` from the intermediate module.
Corrected the new node statement and corresponding Lean docstring to specify
additivity of localized restriction, matching the unchanged Lean conclusion.

Added the intermediate module `Sheaf.Algebra.Homology.LocalizedRestrictionAdjunction` containing `CategoryTheory.localized_restriction_adjunction`, and used it to prove `isKInjective_restrict_localized`. The proof installs the exactness and additivity instances, applies `Adjunction.preservesKInjectiveComplexes`, and extracts the induced K-injectivity result. The module compiles with `lcompile.py`.

## Proved and sorry left

Closed the original hole `CategoryTheory.isKInjective_restrict_localized`.
Added one strictly lower intermediate hole, `CategoryTheory.localized_restriction_adjunction`, recorded in node `lem-pur-kinjective-restrict-localized-adjunction`.

## No longer needed

Second reading also removed the unused public import
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian` from the new adjunction module.

Removed the unused import `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact` from the target module. Also removed the unused public import `Mathlib.Algebra.Category.Grp.FilteredColimits`
from `Sheaf.Algebra.Homology.LocalizedRestrictionAdjunction`.
The old proof dependency `lem-pur-site-restriction-module-adjunction-exact` and its module
`Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact` are no longer used by this proof.
The other old dependency, `lem-weil-pbc-right-adjoint-preserves-kinjective`, remains used.
The derived-functor composition import remains available for the K-injective criterion.

## Where the brief, the DAG or earlier work was wrong

The DAG proof dependency `localizedModule_adjunction_exact` requires small-site and precoverage hypotheses absent from this theorem. I therefore stated the needed general-site adjunction as a separate intermediate theorem rather than applying that narrower result.

## New nodes

Change record: `coord/changes/localized-restriction-adjunction.md`.

`lem-pur-kinjective-restrict-localized-adjunction` is the exact additive extension-by-zero adjunction needed by the parent proof, now stated in the new module `Sheaf.Algebra.Homology.LocalizedRestrictionAdjunction`.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered module against the repository version. The target declaration signature is byte-for-byte unchanged; only the proof and the added named intermediate theorem differ.
2. Compiled the module with `lcompile.py`; it compiles successfully. The only remaining `sorry` is the named theorem `CategoryTheory.localized_restriction_adjunction`, and no forbidden declarations or hollow definitions were introduced.
3. Reviewed the split-off statement and its node. The theorem is a strictly lower exact additive adjunction statement with a source and proof description, and is needed by the parent proof; it does not restate the target.
4. Checked the proof route and imports. The proof uses the new adjunction and the K-injective preservation theorem. Removed the unused narrow `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact` import and updated the target DAG proof dependencies accordingly.
5. Confirmed the unit route is retained: the target is still proved through an exact extension-by-zero adjunction and right-adjoint preservation of K-injectivity. The intermediate theorem remains the sole open hole.

Changed the target proof dependency record and removed the unused import; no target statement or definition was changed.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered target module with the repository version. The target declaration signature is unchanged; the proof and its import set are the only target-module changes.
2. Compiled both delivered modules with `lcompile.py --all`; both compile. The only remaining `sorry` is the named intermediate theorem `CategoryTheory.localized_restriction_adjunction`, and no forbidden declarations or hollow definitions were introduced.
3. Reviewed the split-off theorem and its node. It is a strictly lower exact additive adjunction statement with a source and proof description, and is needed by the parent proof rather than restating the target.
4. Audited the route and imports. The parent uses the new adjunction and `Adjunction.preservesKInjectiveComplexes`; the unused narrow `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact` import was removed. The target node proof dependencies now match the written route.
5. Confirmed the unit route: the proof still proceeds through exact extension by zero and right-adjoint preservation of K-injectivity. The intermediate theorem is the sole open hole.

Changed the target proof dependency record, moved the intermediate theorem to its own module, and removed the unused import; no target statement or definition changed. The new module is documented by `coord/changes/localized-restriction-adjunction.md`.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered target module with the repository version. The target declaration
   signature is byte-for-byte unchanged; the only interface addition is the separately
   documented intermediate theorem and its module.
2. Compiled both delivered modules with `lcompile.py --all`. They compile without errors.
   The sole remaining `sorry` is the named theorem
   `CategoryTheory.localized_restriction_adjunction`; no forbidden declarations or hollow
   definitions occur. Both declarations report exactly `propext`, `Classical.choice`, `Quot.sound`, and
   `sorryAx`, the last arising from the open intermediate theorem.
3. Checked the split-off statement and node. The adjunction/exactness/additivity assertion is
   strictly lower than the target, has a source and a proof description, and is required by the
   target proof. It does not restate the target or weaken it.
4. Audited the written proof and imports. The target invokes the intermediate adjunction,
   installs its exactness and additivity instances, and applies the K-injective preservation
   theorem. The obsolete narrow adjunction import is removed, and the intermediate module's
   unused filtered-colimits import is removed; the DAG proof dependencies match this route.
5. Confirmed the unit route is retained: restriction is handled through an exact additive
   extension-by-zero left adjoint and right-adjoint preservation of K-injectivity. No target
   statement or definition was changed.

I changed only the report during this second reading; no Lean proof or declaration required
repair.

Second-reader searches used “sheaf module localization slice site exact left adjoint”,
`SheafOfModules.overFunctor`, and “extension by zero left adjoint restriction modules”.
The hits include module sheafification adjunctions and the restriction functor itself, but
no general-site exact localized adjunction. The existing localized adjunction node has
additional precoverage/smallness assumptions. The unit has empty realized steps, so no
realized unit step is bypassed. This is a one-hole-for-one-hole decomposition, net zero.

For edge cases, on a terminal category the slice restriction and its left adjoint are
identity functors; for the zero ring both module categories are zero categories. For a
category with no arrows from V to U, the presheaf extension has zero sections at V.
These cases agree with the asserted adjunction and finite-limit/finite-colimit properties.
The intermediate is only an existential proposition used inside a proof; it introduces
no definition selecting arbitrary data from that existence theorem.
The cited source was checked directly at https://stacks.math.columbia.edu/tag/08FI:
it identifies the exact left adjoint as the reason restriction preserves K-injectivity.


## Earlier second reading (a previous round; superseded)

1. Compared both delivered modules with the repository. The existing target signature and
   docstring are byte-for-byte unchanged; there is no changed definition. The new intermediate
   declaration is documented in `coord/changes/localized-restriction-adjunction.md`. Verdict: pass.
2. Recompiled both files with `lcompile.py --all`, then compiled a scratch copy with
   `#print axioms` for both declarations. Both compile; both use exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The sole direct hole is the named theorem
   `CategoryTheory.localized_restriction_adjunction`; no forbidden commands or hollow
   definitions occur. Verdict: pass as a decomposition, not a completed proof.
3. Checked the lower statement against Stacks Tag 08FI and the direct-sum/sheafification
   argument. The arrow index lies in universe v, so the prescribed module universe max(u,v)
   supports the construction. Terminal-site and zero-ring cases agree with the assertion;
   absence of arrows into U gives zero sections before sheafification. The existential is
   eliminated only inside a proposition proof and selects no public data. Fresh leanfinder
   search for “module sheaf functor from slice site left adjoint exact”, loogle search for
   `SheafOfModules.overFunctor`, and grep for extension-by-zero/restriction found no matching
   proved general-site exact adjunction. The existing project lemma needs extra smallness,
   commutative-ring and precoverage hypotheses. Verdict: true, strictly lower, needed.
4. Read the proof from the target downward: it installs the exactness and additivity
   instances and applies `Adjunction.preservesKInjectiveComplexes`. Proof-only project imports
   are plain imports. The obsolete narrow dependency is explicitly listed above as pruned.
   The unit `sk-def-sf-operations` has empty realized statement/steps records; the prescribed
   exact-adjunction route is retained. Verdict: pass.
5. Compared both node records with the Lean declarations. The parent proof dependencies
   are precisely the new adjunction node and the right-adjoint K-injectivity node; the lower
   node has its source, natural-language proof, searches, creation/blueprint fields and
   verbatim Lean signature. Verdict: pass.

Changed the report only: added this current second reading and explicitly named the removed
old proof dependency. One original hole is closed and one strictly lower hole added: net zero.
No Lean statement, definition, or proof needed repair. The intermediate hole requires the
full general-site extension-by-zero construction and is not a short missing tactic proof.


## Second reading by N3

1. Compared each delivered module with the repository. The parent theorem's signature
   and existing docstring are byte-for-byte unchanged. The new module has no repository
   counterpart and is covered by its change record. No existing definition changed. Pass.
2. Compiled both modules with lcompile.py --all, then a scratch copy with #print axioms
   for both declarations. Both compile without errors; both report propext,
   Classical.choice, Quot.sound and sorryAx. The only direct hole is the named theorem
   CategoryTheory.localized_restriction_adjunction. No forbidden declarations or hollow
   definitions occur. Pass as a decomposition: one original hole closed, one lower hole
   added, net zero; the target still depends on sorryAx.
3. Checked the lower assertion against Stacks Tags 08FI, 03DI and 03DJ. The sectionwise
   direct-sum construction gives the adjunction; preservation of monomorphisms and
   right exactness give exactness. Terminal-category and zero-ring cases agree; no arrows
   V to U means a zero presheaf section before sheafification. Universe max(u,v) contains
   both the arrow index and section modules. The existential is eliminated only in a
   proposition proof; no definition chooses arbitrary data. Fresh leanfinder search for
   “exact left adjoint module sheaves slice category arbitrary Grothendieck topology”,
   loogle search for SheafOfModules.overFunctor, and source grep found no matching proved
   exact general-site adjunction. Mathlib's pullback adjunction supplies adjointness but
   does not supply the exactness of this localized left adjoint. The existing project
   adjunction has extra precoverage and commutative-ring hypotheses. Pass: true, needed,
   and strictly lower than K-injectivity preservation; not a restatement.
4. Read downward from the parent: the exact adjunction supplies the instances needed by
   Adjunction.preservesKInjectiveComplexes, followed by isKInjective_map. The left-adjoint
   instance is needed for zero-morphism preservation during additivity synthesis.
   Removed the new module's unused public Abelian import and recompiled. Its remaining
   public import supports its signature. The parent's FilteredColimits import supports
   abelian instances in the existing K-injectivity signature. All old proof dependencies
   no longer used are listed in No longer needed. The unit sk-def-sf-operations has empty
   realized statement/steps; the exact-adjunction route is retained. Pass.
5. Checked both DAG nodes, proof dependencies, proof origin and verbatim Lean signatures.
   The parent records the lower adjunction and right-adjoint preservation; the lower node
   records the non-elementary sheafification exactness dependency and required creation,
   source, search and blueprint fields. Pass.

Changed the new intermediate theorem's docstring to give the full adjunction and
monomorphism/right-exactness argument, removed its unused public Abelian import, and
made the change record's New section contain the verbatim signature. No Lean statement,
definition or proof was changed. The intermediate construction cannot be closed by a
short tactic repair, so its named hole remains. This delivery is a decomposition.
