## What changed

Replaced the `sorry` in `AlgebraicGeometry.projectionMate_affineChart_transport`
with a proof combining three separate parts. The existing
`exists_derivedProjectionMate_openRestriction_comparison` supplies the local
adjunction, tensor comparison, objects and arrow isomorphism on the actual
inverse-image open. The new `projectionMate_schemeIso_transport` supplies an
arrow comparison across the given commuting scheme-isomorphism square. The
proof transfers invertibility through both arrow isomorphisms, applies the
exact functor's derived homology comparison in each degree, and reflects
invertibility through `Scheme.Modules.overEquiv`.

Added proof-only imports of
`Sheaf.AlgebraicGeometry.DerivedProjectionMateOpenRestrictionComparison`,
`Sheaf.AlgebraicGeometry.ProjectionMateSchemeIsoTransport`, and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
The new module publicly imports the three definition modules its statement
uses and Mathlib's arrow category. The parent node's proof and dependencies
now follow the implemented reduction. No existing signature, definition,
public import or visibility changed. No forced adaptations or change records.

The local Lean compilation validates the reduction. Final validation is the
`deliver3.py --no-push` dry run, including its compilation and axiom probe.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.projectionMate_affineChart_transport`
(node `lem-pc-projection-mate-affine-chart-transport`). Its body has no `sorry`.

Added one hole, exactly `:= by sorry`, in a new module:
`AlgebraicGeometry.projectionMate_schemeIso_transport`
(node `lem-pc-projection-mate-scheme-iso-transport`).
This is a decomposition, not a completed axiom-free proof of chart transport:
one upper hole closed and one strictly separate scheme-isomorphism comparison
hole added. The existing open-restriction comparison remains an imported
proof dependency with its own existing hole; it was not duplicated or edited.

The new statement concerns arbitrary commuting squares of scheme
isomorphisms. It has no ambient open, restriction functor, homology map,
affineness, compactness or quasi-separatedness in its conclusion. It returns
a derived equivalence and an arrow isomorphism, rather than restating the
parent implication. The Lean proof independently combines it with the
existing open comparison and proves the passage to restricted homology.

## No longer needed

No original imports were removed: all five public imports are used by the
unchanged statement. The original file had no proof-dependency imports.

The parent no longer directly needs these planned nodes/modules:

- `lem-pc-derived-open-restriction-qcoh-iff` /
  `Sheaf.AlgebraicGeometry.DerivedOpenRestrictionQCoh`: the existing open
  comparison already supplies quasi-coherent local objects.
- `lem-pc-scheme-iso-derived-localizations` /
  `Sheaf.AlgebraicGeometry.SchemeIsoDerivedLocalizations`: standard local
  derived categories are already available, and this theorem only supplies
  localization instances, not functorial tensor or mate transport.
- `lem-pc-derived-localization-tensor-comparison` /
  `Sheaf.AlgebraicGeometry.DerivedLocalizationTensorComparison`: its
  objectwise tensor comparison alone is not a natural comparison for a
  commuting square of schemes; the new scheme-isomorphism comparison
  incorporates the required natural functor transport instead.
- `def-pc-derived-category`, `def-pc-scheme-derived-tensor-structure`,
  `def-pc-derived-pullback`, `def-pc-derived-direct-image` as direct proof
  dependencies of the parent. They remain statement dependencies and are
  still needed by the new comparison. Their definition modules are not
  globally pruned.

These are pruning claims for this argument only; unrelated target paths may
still reach these modules. The open comparison is retained. The parent now
also explicitly cites `def-pc-derived-open-restriction-maps` for the exact
restriction used in the homology step.

## Where the brief, the DAG or earlier work was wrong

The original DAG step 2 contained a whole Lean docstring in place of a
numbered mathematical step. More substantively, its stated dependencies do
not provide the natural comparison it needs. The localization-instance
existence theorem supplies no tensor/pullback/direct-image equivalences;
the localization tensor comparison is objectwise and supplies no scheme
square or projection-mate equation. The new node isolates precisely the
scheme-isomorphism transport part, rather than silently extracting stronger
claims from these declarations.

The literature tex files and imported blueprint files are absent in this
clone. Read the source online at https://stacks.math.columbia.edu/tag/08EU:
its first sentence is the affine-local reduction being implemented. The
existing scheme-isomorphism modules cite 08EB, but that tag actually concerns
perfection on affine schemes, not an explicit mate transport theorem. The
new node cites 08EU and labels the expanded comparison construction as an
agent argument; it does not cite 08EB as an exact match.

The new statement was checked on identity chart isomorphisms, zero input
objects, empty schemes, unbounded complexes, independent localization
universes, and arbitrary supplied p,t. Identity isomorphisms reduce to the
localization equivalences and their unit/counit comparisons. Empty schemes
and zero objects require no nonemptiness assertion. Arbitrary p,t are
conjugated with their own units, counits and inverse tensor comparison; no
canonical normalization or coherence hypothesis is added. Independent
universes are handled by the equivalences of the two chosen localizations.
No arbitrary witness is used in a definition. The unit's own statement and
realized steps are not bypassed or changed.

Searches used the provided msearch wrapper: LeanFinder found only underived
scheme tensor/conjugation ingredients; Loogle found the five
`CategoryTheory.conjugateIsoEquiv` declarations; grep found no matching
derived scheme mate transport; LeanSearch returned HTTP 500 and is recorded
as unavailable. Local searches covered both Lean roots. Blueprint searches
for projection mate found no match, and the broader isomorphism search was
also inspected. No existing node was found with the new comparison's full
statement. Its blueprint ancestry is inherited from the parent node's
recorded finite-duality Hom-chain comparison step.

## New nodes

`lem-pc-projection-mate-scheme-iso-transport`, stated in
`lean/Sheaf/AlgebraicGeometry/ProjectionMateSchemeIsoTransport.lean`, isolates
the isomorphism-square comparison between two supplied derived projection
mates. The declaration and node carry the source, the explicit equivalence,
adjunction/tensor transport construction, and the arrow-square proof in
words. Future work can prove it independently of any ambient open or
restricted homology. The node records the actual searches, chapter, unit,
blueprint ancestry and verbatim Lean signature. No new definitions or change
records were added.

## Second reading by T3

1. **Interface preservation: pass.** Read both delivered modules and diffed the
   existing chart module against the repository. Its declaration signature,
   docstring, universes, assumptions, public imports and visibility are unchanged.
   The only changes are three proof-only imports, scoped elaboration options,
   and the proof body. Compared the parent JSON field by field: only `proof`,
   `proof_deps` and `proof_origin` differ. There are no definition changes or
   forced adaptations. Restored the original single space before `:=` so the
   complete signature prefix is byte-for-byte identical.

2. **Kernel/proof checks: pass as a decomposition.** Compiled both modules in
   import order with `lcompile.py --all`. Independently compiled scratch copies
   with `#print axioms` for both declarations: each reports precisely `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The only delivered `sorry` is
   the new named theorem `projectionMate_schemeIso_transport`; there are no
   definitions, prohibited declarations, or hidden proof holes in this delivery.
   Read the open-restriction comparison statement: its arrow goes from the
   restricted original mate to the local mate. Thus `a.hom` is used in the
   reverse direction for invertibility; `b.hom` goes from the transported chart
   mate to the local mate and is used forward. The homology natural isomorphism
   gives exactly restriction of the original homology map, and `overEquiv`
   reflects its invertibility. This closes one body and adds one body: net zero
   holes, not an axiom-free proof of the chart theorem.

3. **Split statement: pass.** Read Tag 08EU online, including the affine-local
   first sentence of its proof; it motivates the reduction, rather than stating
   the new comparison verbatim. Read `exists_scheme_iso_derived_equivalence` and
   `scheme_iso_derived_inverse_preserves_qcoh`: the first supplies equivalences
   with termwise pushforward comparisons for independent universes, and the
   second supplies precisely quasi-coherence of inverse-transported objects.
   The remaining construction is the new theorem's documented agent argument.
   The four schemes, two derived universes, commuting equation, arbitrary p,t,
   and quasi-coherent M,L in its node agree with its Lean signature. Its arrow
   isomorphism contains no projection-formula invertibility assumption.
   Conjugating the supplied t, rather than replacing it with a canonical t,
   handles noncanonical tensor comparisons; conjugating p handles noncanonical
   units and counits. Identity scheme isomorphisms give transport between the
   chosen localizations; zero objects and empty schemes require no extra
   hypothesis. No boundedness is used. The statement isolates scheme transport;
   open restriction and passage to every restricted homology map remain actual
   separate steps in the parent. It is not the parent under another name.

   Independently searched using LeanFinder for "derived monoidal equivalence
   conjugates projection formula adjunction counit", and Loogle for
   `"homEquiv", "tensor"`; these return monoidal-equivalence identities and
   rigid-category adjunctions, not the scheme comparison. Searched both local
   Lean roots and upstream CategoryTheory. Read
   `CategoryTheory.Adjunction.rightAdjointProjectionMap_mate` in
   `WeilConjectures/CategoryTheory/Adjunction/ProjectionMapCompat.lean` and the
   comparison results in `ProjectionMapMate.lean`: useful for the final
   categorical calculation, but they assume the tensor/pullback comparisons
   and compatibility equations that must still be constructed. Consequently
   they do not close the new hole in a few minutes or duplicate its statement.
   Fixed doubled TeX backslashes in the new node's prose statement; its
   mathematical content and Lean signature are unchanged.

4. **Route and pruning: pass.** All five original public imports occur in the
   unchanged statement; each added private import supplies a used declaration.
   The new module's public imports supply its tensor, pullback, direct image
   and arrow-category statement. Compared every old `proof_deps` entry with
   the report: the open comparison is retained and all seven removed direct
   dependencies (four definitions and three lemmas) are listed under
   `No longer needed`. None is claimed globally unreachable. Read
   `dag/units/sk-thm-picard-duality.json`: its existing `realized.statement`
   and sole `realized.steps` entry are empty; this delivery changes neither
   them nor a unit statement or step. The recorded finite-duality Hom-chain
   projection-formula route still passes through the affine-chart reduction.

5. **DAG agreement: pass.** The parent node's four steps match the two comparison
   calls, invertibility transfer, and exact homology/over-equivalence argument.
   The new node has its source, complete construction in the declaration
   docstring, proof plan, dependency union, agent proof origin, search records,
   group/item/date, chapter/unit, inherited blueprint ancestry and verbatim
   Lean signature. No data is selected from this new existence statement in a
   definition: its witnesses are eliminated only inside the parent's proof.

Second reading changed only signature-delimiter whitespace, TeX escaping in the
new node, and this report. The proof reduction itself needed no repair. Scratch
axiom-probe copies were removed before the delivery dry run.
