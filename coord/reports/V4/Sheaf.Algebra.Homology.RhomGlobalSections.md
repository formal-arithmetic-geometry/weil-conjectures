## What changed

Repaired and completed the earlier sandbox proof of
`CategoryTheory.rhom_global_sections` in
`Sheaf.Algebra.Homology.RhomGlobalSections`, without changing its signature or
its existing docstring. The proof compares functorial K-injective representatives,
proves the naturality of the additive homotopy-to-derived equivalence, and descends
that comparison through the product localization. Universe lifts place the two
abelian-group-valued functors in a common universe and are removed in the final
additive equivalences.

The complex-level hypercohomology calculation is isolated in the new module
`Sheaf.Algebra.Homology.HomComplexHypercohomology`. It is strictly intermediate:
its source objects are cochain complexes, its conclusion uses homotopy-category
morphisms, it has no derived internal Hom and needs no resolution transformation.
The main proof supplies the K-injective replacement, localization, comparison with
derived morphisms, descent and naturality for arbitrary derived morphisms.

The parent node's proof and dependencies now follow this Lean proof. Added proof
imports: `Sheaf.Algebra.Homology.HomComplexHypercohomology` and
`Mathlib.Algebra.Homology.DerivedCategory.KInjective`.

## Proved and sorry left

Closed the original hole `CategoryTheory.rhom_global_sections`
(node `lem-pur-rhom-global-sections`): its entire combining proof is written in Lean.
No `sorry` remains in the item's module.

Added one hole, `CategoryTheory.homComplex_hypercohomology`
(node `lem-pur-hom-complex-hypercohomology`), whose whole proof is `:= by sorry`.
Its source and full argument, including naturality and the extension from K-flat
sources to arbitrary sources, are in its docstring and node. Zero sources and
zero targets give zero groups; unbounded complexes use products. An arbitrary
functor I with K-injective values suffices; no natural resolution map is needed
for this complex-level statement.

This delivery is a decomposition: one original hole closed and one strictly
intermediate hole added, net zero holes, not a complete axiom-free proof of the
transitive theorem.

## No longer needed

Removed the following direct proof imports from the item:

- `Sheaf.Algebra.Homology.HomComplex`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Homology.KFlatResolution`
- `Sheaf.Algebra.Homology.KInjectiveHomComplex`
- `Sheaf.Algebra.Homology.QuasiIsoHomComplexMap`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`

The Hom-complex interface is available through the public statement imports.
K-flat resolutions, K-injectivity of Hom from K-flat sources, and Hom-complex
quasi-isomorphism invariance belong to the remaining intermediate calculation:
`def-pc-kflat-complex`, `lem-pc-kflat-resolution`,
`lem-pur-hom-kflat-into-kinjective`, and `lem-pur-rhom-well-defined` are removed
from the parent's direct proof dependencies and retained below the new node.
They are not globally unnecessary. The fifth removed parent dependency is
`def-pur-hom-complex`; its statement import and the new node retain it. The Grothendieck property and canonical
functorial K-injective replacement use existing proved source declarations;
the stronger separator/termwise-injective resolution theorem is not applied.

No global module pruning is asserted. No unit route is bypassed: the ambient
six-operations unit has no proof steps or realized statement nodes; the same
K-flat/K-injective calculation from the parent is retained below the new node.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt had two compiler failures in the naturality calculation,
no new DAG node for its proposed intermediate theorem, and no report. Those
are repaired here. The localization part is a real argument, rather than a
renaming of the original hole.

The local Stacks TeX source is absent. The online primary sources were read at
https://stacks.math.columbia.edu/tag/08JA,
https://stacks.math.columbia.edu/tag/0A95 and
https://stacks.math.columbia.edu/tag/0A96. Their K-flat/K-injective route is kept.
LeanSearch returned an Internal Server Error; this unavailability is recorded
without a mathematical verdict. LeanFinder, Loogle, source grep, and blueprint
search supplied the other checks.

## New nodes

`lem-pur-hom-complex-hypercohomology`, at
`dag/nodes/sec-smooth-purity/lem-pur-hom-complex-hypercohomology.json`, states the
natural additive complex-level comparison proved by the K-flat calculation,
global-cochain identification, and transport along surjective K-flat roofs.
Its module is `lean/Sheaf/Algebra/Homology/HomComplexHypercohomology.lean`.
The later homotopy-to-derived and product-localization steps are proved in
the parent and are absent from this intermediate statement.

No interface change or forced adaptation; no change record is needed.


## Second reading by V4

1. Compared every delivered existing module with the repository using `diff`.
   The complete signature of `CategoryTheory.rhom_global_sections` and its
   docstring are byte-for-byte unchanged. No definitions or other existing
   declarations changed. The only extra module is the declared new theorem.
   Verdict: unchanged interface; no change record required.
2. Compiled both modules in import order with `lcompile.py --all`; both pass.
   Read the full combining proof, including inverse-resolution naturality,
   homotopy-to-derived additive bijection, product-localization descent, and
   removal of universe lifts. There is one named sorry, exactly
   `CategoryTheory.homComplex_hypercohomology`, and no prohibited declarations
   or sorry in a definition. The explicit scratch-copy axiom inspection and
   delivery axiom probe are recorded below. Choices in this proof select
   additive comparison isomorphisms and use their inverse and naturality;
   they do not define a new object from arbitrary unproved existence data.
   Verdict: a valid conditional proof/decomposition, not a transitive
   axiom-free proof.
3. Read the new statement, its complete docstring, its node, and the cited
   existing declarations. Checked Stacks Tags 08JA, 0A95, 0A96, and 06YS
   directly. For zero source or zero target both groups vanish; arbitrary
   K-injective targets need no resolution transformation; products permit
   unbounded complexes. Pullbacks of termwise epimorphic quasi-isomorphisms
   remain such because their kernels are acyclic. Resolving these pullbacks
   gives common K-flat roofs, so the naturality/independence argument works.
   Fresh LeanFinder, Loogle, wrapper grep and repository `rg` searches found
   only external Hom cohomology, local-section comparisons, and the separate
   right-derived computation. None supplies this global additive natural
   comparison. This hole excludes the resolution transformation, comparison
   to derived morphisms and localization descent proved in the parent, so
   it is strictly intermediate rather than a restatement. Verdict: true,
   needed decomposition; not closable in a few-minute proof pass.
4. The parent uses the shortest available generic homotopy-to-derived and
   localization APIs. Its proof-only imports are private to the module;
   public imports supply its existing signature. All five removed direct
   parent proof dependencies are accounted for above: K-flatness,
   K-flat resolution, Hom-complex construction, K-injectivity of Hom and
   Hom quasi-isomorphism invariance. They remain below the new node or in
   statement imports, so no global module pruning is claimed. Read the unit
   `sk-def-sf-operations`: its `steps` and both `realized` lists are empty.
   Its ambient six-operation route is not bypassed. Verdict: route retained.
5. Checked both node proof steps, their dependency unions and origins against
   the written Lean and documented remaining argument. The new node has the
   required source, searches, creation, blueprint, chapter/unit and Lean
   fields. Updated its Lean statement to the actual multiline signature.
   Verdict: nodes agree with the proof and remaining hole.

Repairs: added private proof-plan imports to the new intermediate module
(`KFlatResolution`, `KInjectiveHomComplex`, `QuasiIsoHomComplexMap`,
`HomComplexGlobalCochains`, `HomComplexProjections`, and Mathlib
`DerivedCategory.KInjective`), because its DAG names those inputs and a
future worker must receive them. Completed the removed-dependency list,
recorded fresh searches, and made the new node signature verbatim.
No mathematical statement, definition or correct combining proof was rewritten.

Axiom check: a scratch copy compiled successfully and `#print axioms` for
both declarations printed exactly `[propext, sorryAx, Classical.choice,
Quot.sound]`. The scratch copy was removed before delivery.
