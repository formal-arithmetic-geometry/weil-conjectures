## What changed

Proved `AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_zero_of_isSepClosed`
with its signature and public imports unchanged. The proof uses terminal-section epimorphism
preservation from the existing `WeilConjectures.AlgebraicGeometry.Sites.PointCohomology`
instance, transfers it to global sections, derives exactness using Mathlib, and applies the
existing exact-functor comparison with degree-zero single objects. Positive-degree homology
then vanishes. Updated the declaration's proof description and its DAG proof to this route.

Added a node attaching the already proved terminal-section instance; no Lean module or theorem
is duplicated. No definition, instance, existing statement, or downstream module was changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_zero_of_isSepClosed`
(node `lem-sf-separably-closed-torsion-cd`). Added 0 holes; split off 0 theorems; 0 holes remain
in the delivered module. The new node references the already proved
`AlgebraicGeometry.Scheme.preservesEpimorphisms_sheafSections_of_isSepClosed`.

The remote compiler accepted the proof. `#print axioms` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`. The temporary print command was removed.
The proof covers arbitrary abelian sheaves, including locally torsion sheaves without a uniform
annihilator, and separably closed fields in arbitrary characteristic, including imperfect fields.
The positive-degree hypothesis excludes q=0, as required; zero sheaves are included.

## No longer needed

Removed proof imports:
- `Sheaf.AlgebraicGeometry.AbelianSheavesGModules`;
- `Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants`;
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek` (already publicly provided by
  `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`).

Second reading also removed the proposed proof-only import
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory`: its
comparison is already publicly available through `CohomologicalDimension` and `LowerShriek`.
A scratch copy without this import compiled cleanly.

The proof no longer needs nodes `lem-exc-abelian-sheaves-gmodules` and
`lem-exc-field-sections-stalk-invariants`; their two old top-level `tool_uses` entries are
withdrawn. No construction of a separable closure, algebraic closure, Galois action, abelian
Galois equivalence, or section/stalk invariant comparison is needed by this proof. The modules
remain available for other users; no whole-project unreachability is claimed. The two definition
nodes for cohomology and its torsion bound remain required. The unit has no realized nodes in
its statement or steps, and the unit's exactness-to-vanishing argument is preserved.

## Where the brief, the DAG or earlier work was wrong

The original route was mathematically valid but unnecessary: the existing source library
already proves the terminal-section epimorphism-preservation instance using split covers.
It therefore avoids constructing and comparing Galois equivalences. The Ext-valued vanishing
theorem `subsingleton_H_of_isSepClosed` was not used: this delivery proves vanishing for the
ordinary derived-section cohomology appearing in the assigned statement.

## New nodes

`lem-sf-separably-closed-sections-preserve-epi` records the existing proved instance
`AlgebraicGeometry.Scheme.preservesEpimorphisms_sheafSections_of_isSepClosed` in
`WeilConjectures.AlgebraicGeometry.Sites.PointCohomology`. This is only a degree-zero
lifting statement, strictly smaller than the assigned higher-cohomology vanishing, and has no
open proof. Its source is Stacks Tag 03QO specialized to a separably closed field. The direct
proof follows split coverings and local surjectivity. Searched Mathlib with LeanSearch,
LeanFinder/Loogle, and grep; searched the DAG and blueprint for this preservation statement.
No duplicate node with this exact statement was found. No change record is necessary because
no existing interface changed.

## Second reading by F1

1. **Visible interface: PASS.** Compared the sole delivered Lean module with the shared
   repository using `diff` and a byte comparison of the declaration header and public imports.
   The sole existing theorem has exactly the same binders, hypotheses, conclusion, universe,
   visibility and public imports. There are no new Lean declarations or definitions, no
   downstream adaptations and no statement changes requiring a change record.
2. **Proof and axioms: PASS.** Independently compiled the delivered file through `lcompile.py`
   without errors or warnings. Compiled a scratch copy with `#print axioms` for
   `AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_zero_of_isSepClosed`:
   exactly `propext`, `Classical.choice`, `Quot.sound`. Checked the full proof and the source
   definitions of `HasTorsionEtaleCohomologicalDimensionLE`, ordinary `Etale.cohomology`, and
   the exact-functor single-object comparison. The homology isomorphism has the correct
   direction for transporting zero. No sorry, forbidden construct, or data choice is added.
3. **Split statements and searches: PASS.** There are no split-off holes or new Lean
   statements. Read the existing terminal-sections instance and its local-surjectivity and
   split-cover proof in `PointCohomology`. Its new DAG attachment describes that actual
   degree-zero result, not a renamed higher-vanishing theorem. Independently searched with
   LeanFinder for exact-functor higher vanishing, grep for the kernel/epi exactness results,
   and `rg` across `lean/Sheaf`, the relevant source modules, and DAG declarations. The
   existing Ext-valued `subsingleton_H_of_isSepClosed` and ordinary right-derived-functor
   vanishing do not directly state this total-derived-section result. No duplicate attachment
   to the terminal-sections instance was found. Checked arbitrary sheaves (including locally
   torsion sheaves without a uniform annihilator), zero sheaves, positive degree q=1, and
   separably closed imperfect fields. Degree zero is correctly excluded.
4. **Route and pruning: PASS.** The proof uses the existing split-cover instance, Mathlib
   exactness, and the existing exact total-derived-functor comparison. The remaining new proof import,
   `PointCohomology`, supplies the terminal object and epimorphism instance and is private.
   The exact derived-functor comparison is already provided by the retained public imports;
   removed its redundant direct proof import after a clean scratch compilation. The three removed imports and
   both discarded old proof-dependency nodes are listed above. Read the unit record and its
   blueprint section: its field-bound step is preserved; the Galois-equivalence route occurs
   below the unit level. No realized node or unit-level step is bypassed, and no global
   unreachability claim is made for the removed imports.
5. **DAG agreement: PASS.** Compared the original node with its delivered version: only
   `proof`, `proof_deps`, `proof_origin` and withdrawal of the two obsolete `tool_uses` entries
   change. The proof-dependency lists equal the union of their steps' uses and all dependency
   ids exist. The new node attaches the unchanged proved instance in the correct chapter and
   unit, with its source, complete proof, searches, creation record and blueprint ancestry.
   Checked its source against the local Stacks strictly henselian exactness lemma.

Second-reading changes: removed the redundant direct proof import of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory` and
added this review record. The proof body needed no repair. The existing-instance attachment
correctly omits `lean.file`, since no source file is delivered for that declaration. Closed 1 original hole,
added 0 holes, split off 0; this is a proof, not a decomposition.
