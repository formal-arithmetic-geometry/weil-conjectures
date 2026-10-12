## What changed

In `Sheaf.Algebra.Homology.RhomIntoKInjectiveLocal`, proved
`CategoryTheory.module_overFunctor_preservesZero` by extensionality on sections.
Reduced `CategoryTheory.rhom_into_kinjective_local` to two separate, strictly smaller
intermediate results, in the new modules `KInjectiveRestrictLocalized` and
`LocalizedHomComplexHomotopy`. The existing declarations and their signatures are unchanged.
The latter intermediate statement has neither a derived-category nor a K-injectivity
hypothesis: it computes only homotopy morphisms from Hom-complex sections.
The former intermediate statement says only that restriction preserves K-injectivity.

The actual combining proof installs K-injectivity on the restricted target, obtains the
cocycle and homology equivalences, applies Mathlib's
`CochainComplex.IsKInjective.Qh_map_bijective`, and composes equivalences. It transports
endpoints with `DerivedCategory.quotientCompQhIso`; naturality and the inverse/hom
identity prove that the resulting map sends every cocycle class to `Q.map (e z)`.
The component formula of the original theorem is preserved verbatim.

Only proof imports were replaced: added the two new modules and
`Mathlib.Algebra.Homology.DerivedCategory.KInjective`. No public import was added.
Updated the existing node's proof, proof_deps, and proof_origin to the actual combination.
No definition or target statement changes, no adaptation records, and no new data choices.
Single-file compilation is through lcompile.py, with a scoped heartbeat allowance for
elaboration of the long Hom-complex comparison; the wall-clock limit is unchanged.

## Proved and sorry left

Original holes closed: 2.

- `CategoryTheory.module_overFunctor_preservesZero`: proved directly, with no remaining
  sorry in its proof (node `lem-pur-rhom-into-kinjective-local`).
- `CategoryTheory.rhom_into_kinjective_local`: its proof is complete from the two new
  intermediate theorems and Mathlib (node `lem-pur-rhom-into-kinjective-local`). This is
  a decomposition, not a claim that the full derived-Hom dependency chain is proved.

New holes added: 2, each a named public theorem with proof exactly `:= by sorry`.

- `CategoryTheory.isKInjective_restrict_localized`, node
  `lem-pur-kinjective-restrict-localized`, module
  `Sheaf.Algebra.Homology.KInjectiveRestrictLocalized`.
- `CategoryTheory.localizedHomComplex_homotopy`, node
  `lem-pur-localized-hom-complex-homotopy`, module
  `Sheaf.Algebra.Homology.LocalizedHomComplexHomotopy`.

No sorry remains in the item's module. Source-level closed-minus-added is zero, before
any closure/pruning census. Existing imported holes such as `homComplex_exists` were
neither changed nor counted as new. The two new statements were checked on zero
complexes, unbounded complexes, and arbitrary localized objects. Restriction preservation
requires neither pullbacks nor smallness. The degree-minus-one sign is (-1)^(-1) = -1,
so its boundary formula is the null-homotopy formula, not its negative.

## No longer needed

Removed direct proof imports:

- `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.

Their declarations are not used by the item's combining proof. Correspondingly,
`lem-pur-site-restriction-module-adjunction-exact` and
`lem-weil-pbc-right-adjoint-preserves-kinjective` cease to be direct proof dependencies
of the item. They remain conceptual proof dependencies of the new restriction lemma;
this delivery does not claim to prune their mathematics from the entire graph.
`def-pur-hom-complex` remains a statement dependency and is used through the new
Hom-complex comparison. `lem-weil-pbc-kinjective-hom-derived` is retained and used
through its Mathlib match. There are no bypassed unit statements or steps: the unit's
realized.statement and realized.steps are both empty. The global import census must
judge whether another target path still reaches either removed module.

## Where the brief, the DAG or earlier work was wrong

The natural-language module-adjunction node applies to an arbitrary ringed site, but
`SheafOfModules.localizedModule_adjunction_exact` in its recorded Lean module assumes
`SmallCategory C` and a precoverage satisfying HasPullbacks, as well as the displayed
precoverage stability hypotheses. The present item assumes arbitrary Category.{v} C
and GrothendieckTopology C, with no pullbacks. Thus its recorded Lean declaration
cannot directly perform DAG step 1. Using J.toPrecoverage does not provide missing
pullbacks or reconcile arbitrary category universes. The new restriction lemma exposes
exactly the needed general-site conclusion; its proof plan explains the general exact
extension-by-zero argument, and the mismatch is also recorded in its node.

DAG step 2, marked elementary, suppresses the nontrivial quotient comparison between
chosen categorical homology of a section complex and Mathlib's homotopy-category arrows.
The new Hom-complex node states that comparison and its compatibility on representatives,
without importing any derived category. The upper proof then performs the actual
localization step, rather than moving the original derived comparison to a new name.

Read Stacks online sources Tag 0A94 (Lemma 21.34.6), Tag 08FI (Lemma 21.20.1), and
Tag 0A8Y (Equation the project server). Searches of blueprint nodes by Hom complex, restriction
K-injective, 08FI, and 0A8Y produced no duplicate of either new intermediate statement.
The nearby ringed-space open-restriction theorem has a different domain. Mathlib
LeanFinder found the abstract CochainComplex HomComplex quotient equivalence, but not
this sheaf-section identification. Both required LeanSearch requests returned HTTP 500;
they are recorded as unavailable, not as negative search results. The successful
LeanFinder/Loogle/grep requests are recorded in searches.jsonl and the new nodes.

## New nodes

`lem-pur-kinjective-restrict-localized`, in
`dag/nodes/sec-smooth-purity/lem-pur-kinjective-restrict-localized.json`, states only
restriction preservation of K-injectivity (Stacks 08FI), independently of L, Hom-complex
sections, or a derived-category realization. Its module is
`lean/Sheaf/Algebra/Homology/KInjectiveRestrictLocalized.lean`.

`lem-pur-localized-hom-complex-homotopy`, in
`dag/nodes/sec-smooth-purity/lem-pur-localized-hom-complex-homotopy.json`, states the
cocycle and quotient identifications of Stacks 0A8Y, for arbitrary pairs of complexes.
Its module is `lean/Sheaf/Algebra/Homology/LocalizedHomComplexHomotopy.lean`.
Both nodes inherit the item's chapter and unit and trace to the original derived
internal-Hom ancestor. There are no change records.

## Second reading by S2

1. I compared the delivered item module with the repository version. The two existing
declaration signatures (`module_overFunctor_preservesZero` and
`rhom_into_kinjective_local`) are byte-for-byte unchanged; only proof imports, proof bodies,
and the heartbeat annotation changed. The two added modules introduce the split statements
listed above. Verdict: unchanged target and existing signatures.

2. I compiled all three modules together with `python3 /home/ubuntu/weil-launcher/lcompile.py
--all`. They compile cleanly in import order. A source scan finds no `axiom`, `unsafe`,
`opaque`, `implemented_by`, or `extern`; the only remaining `sorry`s are the two named
split-off public theorems, each with a source, proof docstring, and matching node. Verdict:
proof files pass the local gate. A scratch import module with `#print axioms`
confirmed that the zero-morphism theorem uses only `propext`, `Classical.choice`,
and `Quot.sound`; the item and two split statements add only the expected `sorryAx`.

3. I checked the two split statements against Stacks Tags 08FI and 0A8Y. The first is
exactly restriction of a K-injective complex to the slice, with the explicit zero-morphism
parameter needed by the Lean functor. The second is the degree-zero cocycle and homology
identification, including its representative formula, and has no K-injectivity or derived
category hypothesis. Both are strictly smaller than the item and remain meaningful for zero
and unbounded complexes. LeanFinder, Loogle, and repository grep found only abstract
HomComplex/K-injective results, with no duplicate sheaf-localized statements. Verdict: true,
needed, and not restatements.

4. I traced the combining proof: it obtains restricted K-injectivity, applies the Hom-complex
comparison, applies `CochainComplex.IsKInjective.Qh_map_bijective`, and transports through
`DerivedCategory.quotientCompQhIso`; the final naturality rewrite proves the required
component formula. The unit `sk-def-sf-operations` has no realized statement or steps, so no
unit route is bypassed. Removed proof-only imports and DAG proof dependencies are listed in
`## No longer needed`. Verdict: proof dependencies agree with the Lean route.

5. I checked the report, node records, searches, and declaration documentation. The
intermediate theorem docstrings give complete natural-language arguments and edge-case
checks, and both node records identify their source, proof steps, Lean declaration, and
proof dependencies. Verdict: records and documentation are consistent.

I changed only this report: corrected the description of `homComplex_exists` as a proved
imported construction and added this second-reading audit.
