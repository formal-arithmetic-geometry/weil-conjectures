## What changed

Removed the false noetherian-only instance
`AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible` from the item module. It asserted
triangulated closure for arbitrary coefficient ring objects, a claim already marked
STATEMENT-DISPUTED in the file and refuted by the square-zero-ring counterexample in the change
record. The fully proved conditional instance
`AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible_of_serre` is retained verbatim,
including its priority, name, closure hypotheses and proof. The module docstring now links to that
retained declaration. No existing definition or target signature changes. The item imports are
unchanged. Added three fully proved unconditional object-property instances in the item: isomorphism
invariance, zero membership and stability under all integer shifts. These facts do not require
coefficient-dependent Serre closure.

Added the proved coefficient-specific instance in
`Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated`. It derives triangulation for
`Profinite.padicIntegersRingObj ℓ E` from the existing integral Serre theorem, using the norm
induced from the fixed algebraic closure. The two valuation-ring/coefficient-ring definitions agree
definitionally. The unclaimed consumer
`WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization` imports this module publicly
because its rationalization signatures require the integral triangulated structure; its existing
signatures, definitions, proof terms and visibility are unchanged. Its docstring now identifies the
actual coefficient-dependent justification.

Change record: coord/changes/C4-retire-false-noetherian-constructible-triangulation.md. It lists
every module returned by tools/downstream.py with its current holder.

## Proved and sorry left

Validation: the repaired item compiles in 3.8 seconds, the new integral coefficient instance in 4.8
seconds, and the adapted rationalization module in 26.9 seconds without warnings. Eight direct
importers compile against the repaired module. Two checks have independent baseline import failures:
Derived.BoundedConstructible cannot find
WeilConjectures.Mathlib.CategoryTheory.Monoidal.Subcategory.olean (the same failure was reproduced
without the sandbox overlay), and the umbrella WeilConjectures cannot find
WeilConjectures.Algebra.Category.ModuleCat.Presheaf.TopologicalPullback.olean. Those sources are not
changed to work around missing published artifacts. The bounded six-functor source contains no use
of triangulated closure; its operations are restrictions of ambient functors to the unchanged full
subcategories.

Current baseline: one hole, in `AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible`.
This false statement is retired, not proved. Thus zero of one original holes were proved; one false
holed declaration was removed; zero holes were added; zero holes remain in the item and the new
module. The adapted EllAdicRationalization module retains its two pre-existing holes unchanged:
`AlgebraicGeometry.ProEtale.boundedConstructible_derivedExtendScalars_obj` and
`AlgebraicGeometry.ProEtale.isLocalization_boundedConstructibleExtendScalars`. No new hole is hidden
in a definition or helper. This is a statement repair, not a decomposition.

The retained conditional instance, `mem_boundedConstructible_iff`, and the three private helpers
remain completely proved. New proved declarations:
`AlgebraicGeometry.ProEtale.isClosedUnderIsomorphisms_boundedConstructible`,
`AlgebraicGeometry.ProEtale.containsZero_boundedConstructible`,
`AlgebraicGeometry.ProEtale.isStableUnderShift_boundedConstructible`, and
`AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible_padicIntegers`. The latter uses the
existing integral Serre theorem rather than adding an obligation. The conditional instance's axiom
check reports exactly `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

The false unrestricted noetherian-only assertion
`AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible` is removed. No imports or
dependency modules are removed. The existing DAG node
`prop-weil-pbc-module-bounded-constructible-triangulated` retains exactly the same conditional
statement and proof dependencies; its lean record now also names the three unconditional API
instances, and a fourth proof step explains these closures independently of triangulated closure.
Its tool `prop-constructible-derived-subcategory` remains needed through the existing general
homology-property theorem. No unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: noetherianity of X alone does not make constructible R-modules closed under
kernels for arbitrary R. Over a separably closed point take the constant discrete ring B = k ⊕ V
with V infinite-dimensional and square-zero. For nonzero e in V, multiplication by (0,e) between
rank-one free B-modules has kernel V. The B-action on V factors through k, so it is not finitely
generated. Its constant sheaf is not locally finitely presented, as a local presentation would give
a finite presentation on the geometric fiber. The cone therefore has nonconstructible cohomology
although the two endpoints are bounded constructible. The change record gives the complete
calculation.

The final noetherian-only sentence of the current blueprint unit `sk-def-sfb-bounded-constructible`
has the same arbitrary-coefficient error. The displayed square-zero example establishes the
mathematical defect; the chapter and proper-base-change unit route are unchanged. The integral
specialization needed by rationalization remains valid by its coefficient-dependent Serre theorem.

The earlier B4 repair established the correct conditional instance. The current base restored the
false noetherian-only instance alongside it; its removal is the repair here. The source scan finds
no explicit consumer of the retired name, but compiling direct importers reveals that
EllAdicRationalization implicitly used it for the integral triangulated structure. This is repaired
using the correct existing integral closures, not by retaining an inconsistent global instance. The
explicit consumer of the conditional instance is Sheaf.Paper.CondensedFiniteModelProofAPI, which
constructs all three closure instances. All category/property definitions remain unchanged.

Searches run through msearch.py: Lean Finder on bounded derived homology in a weak Serre class
(eight generic derived/triangulated hits); Loogle on IsTriangulated and homology (no hits); grep on
homologyProperty_isTriangulated (no Mathlib hits). The project already provides the needed generic
theorem in WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty, used by the
retained proof; no false arbitrary-coefficient Serre statement was added.

## Forced adaptations

`WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization` is unclaimed. Its original
source fails against the repaired item at original lines 155, 163, 167 and 173. The first failure
was:

```text
failed to synthesize instance of type class
HasZeroObject (BoundedConstructible
  (condensedRingObj (Profinite.padicIntegersRingObj ℓ ↥↑E) X))
```

After the unconditional zero/shift API was supplied, the remaining failure was:

```text
failed to synthesize instance of type class
Pretriangulated (BoundedConstructible
  (condensedRingObj (Profinite.padicIntegersRingObj ℓ ↥↑E) X))
```

Its added public import is `Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated`; the other
changed lines are only its explanation of the integral triangulated structure. The imported, fully
proved instance provides precisely that structure under the original finite-field and noetherian
hypotheses. No existing declaration signature or visibility was changed.

## New nodes

`lem-weil-pbc-padic-integers-bounded-triangulated` records the new module's proved
integral-coefficient corollary. Its proof identifies the coefficient definitions, applies
`lem-weil-pbc-integral-constructible-serre`, and then uses the unchanged conditional triangulation
theorem. Searches run through msearch.py include LeanSearch, Lean Finder, Loogle and grep; they find
generic triangulated infrastructure, with no coefficient-specific match. A full blueprint search for
bounded constructible categories found the generic claim in `sk-def-sfb-bounded-constructible` and
the integral rationalization use in `def-sfb-rationalization-equivalence`; neither provides this
specialized coefficient proof. The new lemma is the integral special case of that blueprint claim,
established from the actual integral Serre theorem. The ancestor tool gives no ancestor for the old
generic repair node, so the new record identifies this explicit current-blueprint sentence. Empty X
and zero complexes are included: the closure theorem and the intersection argument impose no
nonempty-base or nonzero-object condition. No residue characteristic restriction on X is introduced.
No new sorry is left.

Change record: coord/changes/C4-retire-false-noetherian-constructible-triangulation.md.


## Second reading by C4

1. **Visible declarations: pass, with the declared retirement.** I compared all three
   delivered modules with the shared repository. Every retained existing signature and
   proof body is unchanged, including the conditional instance's priority and hypotheses.
   No existing definition changes. The only removed declaration is the false
   `AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible`, explicitly recorded
   in `coord/changes/C4-retire-false-noetherian-constructible-triangulation.md`; its hole
   is retired, not proved. The square-zero-ring calculation correctly refutes it.
   EllAdicRationalization retains all existing signatures, definitions and proof bodies.
2. **Proofs and axioms: pass.** I independently compiled all three delivered files without
   warnings. Scratch copies with `#print axioms` checked `boundedConstructible`,
   `mem_boundedConstructible_iff`, the three new unconditional closures, the retained
   conditional triangulation instance and the new integral-coefficient instance: each
   uses only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   The only two direct holes in the delivered files are the unchanged rationalization
   consumer's named holes listed above. No forbidden declaration or hollow definition
   was introduced. I compiled the original rationalization consumer against the changed
   dependencies and reproduced its missing `Pretriangulated` errors at original lines
   155, 163, 166/167 and 173. Rebuilding both original source modules in a separate
   scratch sandbox makes the original consumer compile; the published compiled baseline
   alone has older missing-zero/shift errors. This source-to-source counterfactual confirms
   the adaptation. Its new public import is needed by its signatures.
3. **New statements and edge cases: pass.** No statement is split off with a hole. The new
   coefficient-specific instance is fully proved from the existing integral Serre theorem
   and the conditional triangulation theorem; its norm transport is definitional and
   introduces no new hypothesis. The unconditional closures also include zero complexes
   and empty schemes. I repeated Lean Finder, Loogle and grep searches using different
   wording (cohomology in a Serre class; shift invariance of homology properties), and
   searched both project roots. The hits supply generic infrastructure already used;
   they do not duplicate the coefficient-specific statement. Sources, proof docstrings
   and the new node are present.
4. **Route, imports and pruning: pass.** The proof uses the existing generic
   homology-property theorem and the existing integral Serre theorem directly. The new
   module's Serre import is proof-only; its public imports provide its statement's types
   and coefficient definitions. The consumer's public import supplies an instance needed
   in its public signatures. No old proof dependency or import becomes unused, and no
   module is pruned. I read both relevant unit records: their realized steps are not
   bypassed. The false arbitrary-coefficient sentence in
   `sk-def-sfb-bounded-constructible` is explicitly disputed in the report and change
   record. The maintainer should relay that established unit error to `coord/HUMAN.md`;
   this delivery does not edit the fixed unit record or any target.
5. **DAG agreement: pass.** The existing node keeps its conditional statement and its
   original `proof_deps`, with the three additional unconditional closures recorded in
   its Lean declarations and proof. The new node's declaration and verbatim signature
   match its module; its proof steps identify exactly the integral coefficient comparison,
   integral Serre closure, and conditional triangulation used by the Lean proof. Its
   required creation, source, blueprint, chapter, unit and search fields are present.

Second-reading changes: removed three accidental blank lines from the adapted consumer,
and corrected the report's indented Forced adaptations heading. No mathematical proof,
statement, definition or import needed repair. Counts remain zero of one original holes
proved, one false holed declaration retired, zero holes added, zero split off, and no
modules pruned. The four new proved closure instances are additional API, not four
original holes closed.
