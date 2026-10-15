## What changed

Proved thirteen of the fourteen original holes in `lean/Sheaf/Paper/ProfinitePointPullback.lean`.
Added private, proved normalization and coherence helpers; all existing signatures,
visibility, definitions and source docstrings are unchanged. Updated the node's proof,
proof dependencies and proof origin to the implemented route. The proper-base-change
unit's realized statement and steps are preserved. The conservative scope-command
check is documented in `coord/changes/ProfinitePointPullback-proof-scope.md`; no
mathematical interface changes and no forced adaptations are involved.

Repair for the returned duplicate-declaration finding: the nine generic derived-category coherence
lemmas are now provided by `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`,
their generic dependency. They were removed from the incompatible pro-etale
`RestrictScalars` module and from this item; the finite-coefficient pro-etale imports remain intact.
The item compiles together with both adapted source modules.

Added proof-only imports:

- `WeilConjectures.CategoryTheory.Monoidal.Conjugate`
- `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`
- `WeilConjectures.CategoryTheory.Sites.MonObj`

## Proved and sorry left

Closed original holes (not decompositions):

- `AlgebraicGeometry.ProEtale.profinite_point_pullback`
- `AlgebraicGeometry.ProEtale.profinite_point_pullback_coefficient_coherence`
- `AlgebraicGeometry.ProEtale.profinite_point_pullback_abelian_coherence`
- `AlgebraicGeometry.ProEtale.existsUnique_profinitePointModuleDirectImageIdentity`
- `AlgebraicGeometry.ProEtale.profinite_point_pullback_module_coherence`
- `AlgebraicGeometry.ProEtale.profinitePoint_isMonoidal_upperStarComp`
- `AlgebraicGeometry.ProEtale.profinitePoint_isMonoidal_upperStarId`
- `AlgebraicGeometry.ProEtale.profinite_point_pullback_ring_coherence`
- `AlgebraicGeometry.ProEtale.profinite_point_pullback_abelianderived_coherence`
- `AlgebraicGeometry.ProEtale.profinite_point_pullback_modulederived_coherence`
- `AlgebraicGeometry.ProEtale.profinite_point_pullback_ring_comparison`

- `AlgebraicGeometry.ProEtale.profinite_point_pullback_module_square`

- `AlgebraicGeometry.ProEtale.profinite_point_pullback_set_coherence`

Original hole left, belonging to `lem-weil-pbc-profinite-point-pullback`:

- `AlgebraicGeometry.ProEtale.profinite_point_pullback_module_comparison`

No holes added, no split-offs and no new modules. The item closes thirteen textual holes;
twelve of those theorems are axiom-free beyond the three permitted axioms.
`profinite_point_pullback_module_square` is proved relative to the original, still-open
`profinite_point_pullback_module_comparison` and therefore additionally uses `sorryAx`. The proved declarations reuse existing
library inputs, including inputs whose own proofs remain open; this does not assert that
the full target import closure is axiom-free. Local compilation succeeds without warnings (15.6 seconds after the final set coherence proof).
The delivery dry run passes with the independent second reading reserved for the next worker.

The module comparison still needs compatibility of the scalar-extension identification
with the specified module adjunction and its canonical composition mate. A useful next
step is to show that the forgetful comparison is the mate of the strict direct-image /
forgetful square. The relevant APIs are `Adjunction.mapModAdjunction_unit_app_hom`,
`Mod.extendScalarsIsoComapInv`, and the unit equation for `Adjunction.leftAdjointUniq`.
Exactness itself already follows from existing instances. The module square is proved
from the original comparison theorem by raw-morphism cancellation; no replacement hole
was added.

The set coherence proof is complete. Its component normalization initially exceeded the
kernel budget, with repeated `Functor.obj`, `pullback`, `limit` and
`WidePullbackShape.wideCospan` reductions. Changing abbreviations, removing the identity
associator, and a unique-component characterization were tested only in scratch copies.
The final repair proves the comparison's hom equation at the natural-transformation
level and then takes components. This compiles quickly with the original definitions.
Similarly, the module square avoids `Iso.app` and `Functor.mapIso` intermediates and
proves the diagram directly on raw morphisms. No experimental definition change or
new module is included in the delivery.

## No longer needed

Removed all ten original direct proof-only imports:

- `Mathlib.CategoryTheory.Adjunction.CompositionIso`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Sheaf.Paper.ProfiniteTestObjectFunctor`
- `Sheaf.CategoryTheory.SiteMorphismComposition`
- `Sheaf.CategoryTheory.SiteInverseImageTensor`
- `Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects`
- `Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage`

Second reading additionally removed two redundant proof-only imports added by the first
worker, after testing each removal and their joint removal by compilation:

- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy`
- `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types`

Their APIs remain available through existing imports. The three retained added imports
were each tested for removal; each removal fails on a declaration the proof uses.

Pruned these proof-dependency nodes from this item's route:

- `lem-weil-pbc-profinite-test-object-functor`
- `lem-weil-pbc-left-exact-site-inverse-image-tensor`
- `lem-weil-pbc-site-morphism-composition`
- `lem-sc-left-adjoint-composition-iso-associativity`
- `lem-weil-pbc-adjunction-lifts-group-ring-objects`
- `lem-weil-pbc-sheaf-algebraic-structures-objects`

Their specialized statement modules are not invoked by the proofs. Redundant direct
Mathlib imports were removed while retaining the corresponding mate/localization DAG
inputs where the proofs use those APIs transitively. Public definition imports remain;
this report does not claim that a module is globally unreachable from every other target.

## Where the brief, the DAG or earlier work was wrong

The original plan required more generic intermediate statements than necessary. Concrete
source-library direct-image coherence and the mate API give a shorter route. For derived
coherence, the exact-functor/localization API suffices without new derived existence lemmas.
No false statement or incorrect definition was found. No statement or definition was changed.


## Forced adaptations

- `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate` (unclaimed): the
  original dependency lacked the generic coherence declarations, while importing
  `WeilConjectures.SixFunctors.ProEtale.Derived.RestrictScalars` into this finite-coefficient
  module failed with `environment already contains
  AlgebraicGeometry.ProEtale.«term(_)_*[_]»` because the two coefficient APIs define the same
  notation. The unclaimed-module change moves the generic `Factors`, `Coherence`, and `Whisker`
  sections into this generic module; declarations and signatures are unchanged. See
  `coord/changes/DerivedCategoryCoherenceRelocation.md`.
- `WeilConjectures.SixFunctors.ProEtale.Derived.RestrictScalars` (unclaimed): the original file
  contained the same generic sections. They are removed there because the declarations now live in
  `MapDerivedCategoryMate`; its pro-etale restriction-scalar declarations are unchanged.
  The second reader compiled the original against the changed dependency and reproduced
  nine duplicate-declaration errors, starting at line 103. The adapted file compiles.

## Earlier second reading (a previous round; superseded)

1. **Signatures and accidental changes.** Compared the delivered module with the repository
version declaration by declaration. Existing public signatures, definitions, visibility and
target statements are unchanged; the sole intentional open declaration remains
`profinite_point_pullback_module_comparison`. Verdict: pass.

2. **Proof and soundness.** Compiled the delivered module with `lcompile.py`; it is clean,
contains one named `sorry` in the original theorem, and contains no `axiom`, `unsafe`,
`opaque`, `extern`, `implemented_by` or hollow definition. The proved declarations use only
the permitted library assumptions transitively. Verdict: pass, with the documented original
hole still open.

3. **Split statements and searches.** No split-off theorem or new module was added. Existing
private helpers are proved and are not interface statements. The recorded Mathlib searches
were checked in `searches.jsonl`; no duplicate library theorem was introduced. Verdict: pass.

4. **Shortest route and pruning.** Checked the proof from the targets downward, including the
unit route in `sk-thm-properbasechange`; the realized unit statements and steps remain intact.
The report lists all removed proof-only imports and pruned proof-dependency nodes. Verdict:
pass.

5. **DAG agreement.** Checked that the node's `proof`, `proof_deps` and `proof_origin` describe
the implemented route, and that the remaining theorem is recorded as the original split hole.
Verdict: pass.

Changed during second reading: added this review section only. No Lean declarations, node
statements, definitions or change records required repair.


## Second reading by B4

1. **Signatures and accidental changes — pass.** Read the full item and both upstream
   diffs. Compared every existing signature byte for byte and every definition body:
   none changes. The nine relocated generic lemmas, including their variable blocks,
   statements, docstrings and proofs, are byte-identical to the original `Factors`,
   `Coherence` and `Whisker` sections of `RestrictScalars`. Their public visibility and
   names remain available to old users through its existing public import. Neither
   upstream module is claimed. No target statement or mathematical definition changes.
2. **Proof and soundness — pass with one original hole.** Compiled all three modules
   in dependency order with `lcompile.py`: 6.7 s, 16.6 s and 10.9 s. Compiled the main
   module again after pruning imports (14.9 s). Appended `#print axioms` to scratch
   copies of each delivered module. Every public constant uses only `propext`,
   `Classical.choice` and `Quot.sound`, except the original open module comparison and
   its proved square consequence, which also use `sorryAx`. There is exactly one textual
   `sorry`, the whole proof of the original named comparison theorem, with its source,
   full proof docstring and existing DAG node. No forbidden declaration or hollow data
   definition occurs. The identity is selected from an explicitly proved unique
   specification of its underlying map. Reproduced the nine errors from compiling the
   unchanged `RestrictScalars` against the changed generic dependency, then checked the
   adapted file and the unchanged consumer `RawFixedDerivedComparisonNaturality` compile.
3. **Split statements and searches — pass.** No new hole, split-off statement or module.
   All private helpers are proved. Searched the existing library by scalar-extension,
   direct-image monoidality and derived composition/whiskering terminology; the nine
   generic coherence lemmas already exist and are reused by relocation, not duplicated.
   The independent LeanFinder query "coherence of composition and identity isomorphisms
   for exact functors induced on derived categories" returned the existing factorization
   API and unrelated bounded derived results, no shorter complete replacement. Checked
   identity arrows and equality transports by their explicit reflexivity reductions;
   square statements require only commutativity, with no hidden cartesian hypothesis.
4. **Top-down route and pruning — pass after import repair.** Read RefactorInstruction
   lem:XS, prop:pX, eq:triangle and thm:alpha (lines 496–545 and 720–775). The implemented
   route uses the concrete source functors, faithful forgetful functors, adjunction mates
   and derived localization. The exact ordinary comparisons are retained, including
   their units, associativity and specified common-composite square comparison. The
   unchanged `sk-thm-properbasechange` realized statement and all three realized steps
   remain in place; none of the six removed proof dependencies realizes those steps.
   Confirmed `## No longer needed` lists all six old proof dependencies removed and all
   ten old direct proof imports. Tested all five added imports; removed the two redundant
   ones, and checked their joint removal compiles. The other three are necessary.
5. **DAG agreement — pass.** The only changed node fields are `proof`, `proof_deps` and
   `proof_origin`; their steps describe the direct-image/mate, faithful ring/module,
   exact-functor derived and set normalization proofs actually written. The remaining
   original module comparison and its use in the square proof are expressly recorded.
   There are no new nodes requiring statement or source validation.

Changed during this second reading: removed the redundant `CoherenceLegacy` and
`GrothendieckAxioms.Types` proof imports; corrected the report's axiom accounting and
relocation explanation; corrected the scope record's obsolete section list; added the
complete relocation change record with the counterfactual compiler evidence. No theorem
proof, existing signature, definition or node statement was changed.
