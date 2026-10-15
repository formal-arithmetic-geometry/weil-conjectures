## What changed

The item module preserves all existing signatures and public imports. Its pushforward
continuity proof now applies a comparison on one affine weakly contractible target
object and proves the sheaf-theoretic passage from those comparisons to an isomorphism.
The private detector proves injectivity by separation, constructs local lifts on the
covering family, applies the locally bijective criterion, and reflects the resulting
isomorphism through `Mod.forget`.

Both shift `colimMap` statements are proved using commutation with shifts of the
localization and right derived functor, the standard cohomology shift isomorphism,
and naturality of `condensedContinuityComparison`. Their shifted cocones are proved
colimiting before applying `isIso_colimMap_ι`. No new hypercover proof is used for shifts.

The representative statement is proved directly from its supplied leg equation and
its supplied continuity assumptions. Whisker the representative isomorphisms with
homology, compare the universal colimit maps on every leg, and cancel the invertible
diagram and homology-colimit comparisons. The existing exact-colimit homology instance
in `WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits` supplies the latter.
A source node attaches that already-proved instance; it adds no Lean hole.

New proof imports are the local-comparison module, `Mathlib.CategoryTheory.Sites.LocallyBijective`,
`Mathlib.Algebra.Category.Grp.EpiMono`, the source `DegreewiseLimits` module, and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`.
The geometric calculation's planned imports are moved into the local-comparison module.
The four existing node copies record these final routes. No definitions or existing
statements are changed and no forced adaptation is needed.

## Proved and sorry left

Three original holes have complete categorical proofs, using the original unshifted
continuity declarations where their statements require them:

- `AlgebraicGeometry.ProEtale.condensed_qcqs_pushforward_continuity_shift_colimMap`.
- `AlgebraicGeometry.ProEtale.condensed_qcqs_globalSections_continuity_shift_colimMap`.
- `AlgebraicGeometry.ProEtale.condensedContinuityComparison_representatives_homology`.

The fourth original hole,
`AlgebraicGeometry.ProEtale.condensed_qcqs_pushforward_continuity`, is a decomposition
into a strictly local comparison and the fully proved sheaf detection step. It is not
reported as an independent completed geometric continuity proof.

One original hole remains unchanged in the item:
`AlgebraicGeometry.ProEtale.condensed_qcqs_globalSections_continuity`
(blueprint `lem-weil-pbc-condensed-qcqs-pushforward-continuity`). It still needs the
bounded-below hypercover computation for derived global sections of internal modules.

One new hole remains:
`AlgebraicGeometry.ProEtale.condensed_qcqs_pushforward_local_comparison`, in
`lean/Sheaf/Paper/CondensedQcqsPushforwardLocalComparison.lean`, with node
`lem-weil-pbc-condensed-qcqs-pushforward-local-comparison`. It needs the geometric
calculation at a single affine weakly contractible target object, including the
internal-module / sectionwise-ringed-module bridge and naturality of the hypercover
comparison for the original truncated cocone. The statement is strictly local:
it concludes invertibility of one component of the underlying abelian-sheaf map;
it does not conclude invertibility of the module-sheaf map. No arbitrary witness is
chosen from a sorried existence theorem and no definition contains a hole.

The axiom probe against the sandbox build confirms the representative theorem
uses only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The
pushforward theorem and shift theorems additionally use `sorryAx` from the pending
geometric comparisons; no other axiom occurs. These are stage-3 reductions, not
claims that all geometric dependencies are proved.

Thus four of five original holes are removed, one hole is added, and the total number
of holes in the delivered Lean files drops from five to two. This is three completed
formal compatibility proofs plus one geometric decomposition, with net three holes closed.

## No longer needed

The item module no longer directly imports:

- `Sheaf.AlgebraicGeometry.ProEtaleOperations`.
- `Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian`.
- `Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover`.
- `Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits`.
- `Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution`.
- `Mathlib.Algebra.Category.ModuleCat.AB`.
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`.
- `Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction`.

The first eight imports remain in the pending local calculation's module as its
planned dependencies; moving them does not prune them from the geometric argument.
`ProEtaleOperationsCanonicalAdjunction` is removed outright: neither the completed
proofs nor the local statement need it. No claim is made that it is unused elsewhere
in the library's target closure.

The representative node no longer uses the geometric continuity theorem as a proof
dependency. Its original dependency on
`lem-weil-pbc-condensed-qcqs-pushforward-continuity` is replaced by the already-proved
exact-colimit homology source node. The common comparison definitions remain statement
dependencies. All affine hypercover, evaluation, injective-resolution, and qcqs
geometry nodes are unnecessary for the representative argument itself. They remain
needed by the two unproved geometric calculations, so none is globally withdrawn.
The shift nodes keep the unshifted comparison as a dependency, but need no independent
signed hypercover totalization or shifted acyclicity calculation.

## Where the brief, the DAG or earlier work was wrong

The former shift/representative node plans unnecessarily repeated the hypercover
calculation. The source-library exact-colimit homology instance is an existing proved
instance; it is attached as `src-weil-homology-preserves-exact-colimits` rather than
reproved locally. The shift assertions follow from the existing shift APIs and comparison
naturality; the representative assertion follows from its hypothesis and exact
filtered colimits, with a real proof of equality of the universal comparison maps.

The geometric DAG imports do not yet provide an immediately applicable internal-module
hypercover theorem. `hypercover_computes_boundedBelow_complex` and
`affine_weaklyContractible_evaluation_colimits` use `SheafOfModules` over a sheaf of
commutative rings, whereas this item's coefficients are internal `Mod` objects over
`condensedRingObj Λ X`. A comparison of these coefficient presentations is needed;
the declarations are usable after that comparison, but cannot simply be applied to
these terms by definitional equality. The coproduct theorems were also inspected:
their rational-algebra hypotheses do not apply to the unrestricted Λ of this item.
This is an interface gap, not a disputed mathematical statement.

The session pursued this bridge in `scratchpad/RingObject.lean` (outside the delivered
Lean root). It compiles without holes and constructs section rings, modules and their
maps, the forward module-sheaf functor, a full presheaf functor, the inverse presheaf
construction and its round-trip isomorphism, the reverse sheaf functor through monoidal
sheafification, and its natural underlying-sheaf comparison. It does not yet construct
the module-compatible sheaf round-trip isomorphisms or transport the derived hypercover
comparison. The scratch file is intentionally not imported or delivered as a library
module: those constructions are not yet used by a completed proof. It is available in
this sandbox for the second reader. `scratchpad/WeakEvaluation.lean` separately proves
exact evaluation for underlying abelian sheaves at a weakly contractible object.

Edge cases checked for the new local statement are an empty inverse image W, empty
effective total diagonals below a, the zero coefficient ring, and arbitrary integral
q and a. The covering-basis detector handles arbitrary site objects, rather than
assuming their intersections themselves are affine weakly contractible.

## New nodes

`lem-weil-pbc-condensed-qcqs-pushforward-local-comparison` isolates the original
proof's sectionwise calculation (steps 1–5). It is a true, strictly local part of the
original argument; the original theorem is recovered by the separately proved sheaf
criterion and reflection through the forgetful functor. It is the only new hole.

`src-weil-homology-preserves-exact-colimits` attaches the existing source-library
instance
`HomologicalComplex.instPreservesColimitsOfShapeHomologyFunctorOfHasExactColimitsOfShape_weilConjectures`.
A local `#synth` verifies the attachment. No new module or proof obligation is created
for this node. There are no change records because no interface is changed.


## Second reading by D4

1. **Existing interfaces: pass.** Read the complete diff against the read-only
repository. Parsed all 13 existing declarations and compared their original signature
text byte for byte, including every hypothesis, universe and conclusion. All match;
all existing definition bodies and public imports also match. Only the new local
comparison theorem is public and new. No target or dependent module is adapted.

2. **Proofs and axioms: pass with the documented holes.** Independently compiled both
modules with `lcompile.py --all` (12.9 and 39.5 seconds). Read the detector's separation
and local-lifting arguments, the shift transport and colimiting-cocone argument, and
the representative comparison identity on every leg. A scratch copy of the delivered
module, compiled against the sandbox `.lbuild`, prints only `propext`,
`Classical.choice`, and `Quot.sound` for both representative declarations. Pushforward,
global sections, and their shift colimMap declarations also use `sorryAx`, as expected
from the remaining geometric holes. The log is `scratchpad/second-reading-axioms.log`.
The older `scratchpad/Probe.lean` does not select the sandbox outputs when invoked on
its own, so it is not the evidence used for this verdict. No forbidden declaration
or hole in data is present. The only two literal holes are precisely the named global
sections and local comparison theorems listed above.

3. **Split statement, source and duplication: pass.** Read Lemma 5.3(1) and its proof
on page 14 of the arXiv PDF (printed page 13). Its evaluation at a weakly contractible
affine V and the qcqs hypercover computation support exactly the new local comparison.
Checked its fixed-object conclusion, underlying group map, good-truncation legs and
all hypotheses against its node. Empty W, the zero ring and degrees below a cause no
exception: the section groups or relevant diagonals are zero. The new theorem supplies
one component, while the item proves the passage to an isomorphism of sheaves and then
module objects; this is a genuine decomposition, not a renamed sheaf-level conclusion.
Repeated LeanFinder, Loogle and grep searches with different wording through
`msearch.py`, and searched both library roots by concept. Results give no competing
sectionwise internal-module theorem; the presheaf Kan-extension result in
`CategoryTheory.Pro.PresheafColimit` has different hypotheses and no derived sheaf
comparison. The existing `DegreewiseLimits` homology instance is correctly reused.
The remaining internal-module / ringed-module bridge needs substantial work; the
scratch constructions do not yet supply an exact equivalence or derived comparison,
so neither remaining geometric hole can be closed by those constructions alone.

4. **Shortest route, imports and unit route: pass.** The shift arguments use Q's and
the derived functor's shift commutation rather than another geometric calculation.
The representative argument needs only its supplied comparison hypotheses and exact
colimits. Checked every removed direct import against `## No longer needed`; geometric
imports remain planned dependencies of the local calculation, and the canonical
adjunction import is removed outright. No claim of global pruning is made. Read
`dag/units/sk-thm-properbasechange.json`: its statement and three realized steps are
unchanged and none is bypassed by these formal compatibility reductions.

5. **Nodes and Lean: pass.** Read all six delivered node files. Existing node edits
are confined to `proof`, `proof_deps` and `proof_origin`; every dependency list equals
the union of its proof-step uses. The main node distinguishes the proved detector
from the still-pending global calculation. Both new nodes have source, searches,
creation, blueprint and Lean attachments. The local theorem's recorded signature
matches its Lean declaration; the other new node attaches the already-proved exact
colimit homology instance and introduces no hole.

Changed during second reading: corrected the two shift theorem proof docstrings to
describe the categorical transport and colimiting-cocone proof actually written;
completed the representative homology docstring with the exact-colimit comparison
and cancellation step. No signature, definition, import or proof term changed.
The initial delivery dry run passed; final dry-run and delivery validation follow.
