## What changed

Closed `AlgebraicGeometry.Scheme.Modules.isZero_moduleCohomology_restrict_of_cech_basis`
in `Sheaf.AlgebraicGeometry.ModuleCechVanishingBasis` without changing its signature or
visibility. The proof follows Stacks 01EW's injective-cokernel induction, using the completed
all-coverings proof in `ModuleCechVanishingCriterion` as a model, without importing that
criterion. Cofinality produces the covering predicate needed by 01EU; comparison isomorphisms
handle arbitrary chosen Cech fibre products. Their universal properties identify the opens
with finite intersections, so section surjectivity on B suffices for degreewise short
exactness. Exact restriction and injectivity transport through `overEquiv`; the long exact
sequence proves degree one and the inductive step.

Added proof imports `Mathlib.Algebra.Homology.ShortComplex.Ab` and
`Mathlib.Algebra.Category.Grp.EpiMono`. Removed two proof imports below. Updated the node's
proof and dependencies to record the exact module-cohomology definition, ringed-space enough
injectives, and Mathlib degree-zero isomorphism. No public interface changes or adaptations.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.isZero_moduleCohomology_restrict_of_cech_basis`
(node `lem-weil-pbc-module-cech-vanishing-basis`). No sorry remains in the delivered module;
no new hole or module was added. This is a proof from existing declarations, not a decomposition.

## No longer needed

Removed proof imports:
- `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor`, node
  `lem-weil-pbc-right-derived-universal-delta-functor`: Mathlib's
  `Functor.rightDerivedZeroIsoSelf` suffices, recorded by `lem-sp-derived-well-defined`.
- `Sheaf.Paper.PQFCohomology`, node `pqf-def-cohomology`: the definition
  `RingedSpace.moduleCohomology` and the existing long exact sequence suffice; no comparison
  with derived direct images is used.

Also removed `def-pc-scheme` from the old `proof_deps`: the open subscheme and its
module category are already available from the unchanged public scheme-module import;
no separate scheme-construction proof is invoked. This is a DAG dependency removal,
not another removed import.

All other original imports remain needed. No unit statement or realized step was bypassed.
The two pruned nodes remain statement references where already present; only proof dependencies
were changed. Other targets may still reach these modules.

## Where the brief, the DAG or earlier work was wrong

No false statement or plan step found. The existing all-coverings proof's global presheaf
surjectivity must not be used here: the hypotheses give surjectivity only on B. The delivery
instead checks short exactness of each Cech degree using its intersection opens. The topology
basis hypothesis itself is unnecessary in the dimension-shifting argument once cofinality and
intersection membership are supplied; its original binder is preserved. A declaration-local
unused-variable linter option handles this without changing the interface.

Source read: Stacks `cohomology.tex`, `lemma-cech-vanish-basis` (01EW), lines 1696–1770,
from the existing local literature copy under `/home/ubuntu/work-bp/sheaf/literature/`.
Searches through leanfinder, loogle, grep and both library roots found the completed 01EV
and etale 03F9 arguments, but no direct specialization proving the basis version.

Verification on resumption (2026-10-13): the saved module compiled cleanly through
`lcompile.py` in 12.2 seconds. The required `deliver3.py K4
Sheaf.AlgebraicGeometry.ModuleCechVanishingBasis --no-push` printed OK: compilation and
preflight pass, with the independent second reading still reserved for the second reader.
The earlier `import_cycles.refuse_missing` import failure no longer occurs. No tool was
edited or bypassed, and nothing was pushed.


## Second reading by K4

1. **Interface: pass.** Diffed the sole delivered Lean module against the repository.
   The existing theorem signature is byte-for-byte identical, including `hB`, universes,
   cofinality, intersection hypotheses, conclusion and visibility. No definition or
   public import changed; there are no change records or forced adaptations.
2. **Proof: pass.** Independently compiled the module with `lcompile.py` (10.5 seconds,
   no errors or warnings). Scanned the delivered source: no `sorry`, forbidden axiom,
   unsafe/opaque declaration or implementation override. A scratch copy with
   `#print axioms AlgebraicGeometry.Scheme.Modules.isZero_moduleCohomology_restrict_of_cech_basis`
   compiled (11.7 seconds) and reported only `propext`, `Classical.choice`, `Quot.sound`
   and `sorryAx` from existing open dependencies. This closes the local named hole,
   without claiming that its entire dependency closure is already proved.
3. **Split statements: pass (none).** No new declaration, node, module or hole was
   introduced. Read the section-surjectivity, injective-Cech-acyclicity, restriction,
   Cech-comparison and module-cohomology APIs used by the proof. The comparison
   isomorphism is fixed by product projections; the proof constructs no data from an
   arbitrary unproved existence statement. Empty covers and empty opens cause no
   exception: degreewise products over an empty index are zero, and the section
   theorem includes the empty open. Degree one is handled separately, and all
   intersections used in the successor case are indexed by nonempty `Fin (n + 1)`.
4. **Route and pruning: pass after report correction.** Read Stacks 01EW in the local
   source, compared with 01EV's module proof and the upstream abelian-sheaf criterion,
   and searched independently with leanfinder, loogle and grep using derived-sections,
   acyclic-cover and cofinal-cover terminology. No applicable shorter module-valued
   theorem was found. The proof uses Mathlib's degree-zero isomorphism directly and
   checks surjectivity only on basis intersections. Each retained import supplies
   statement types or a used proof API; proof-only imports are plain imports. Read
   `dag/units/sk-thm-p1.json`: none of its realized statement/step nodes is bypassed
   by this below-unit argument. The old-minus-new dependency set has three nodes;
   the original report listed two and omitted `def-pc-scheme`.
5. **DAG: pass.** Diffed the node: only `proof`, `proof_deps` and `proof_origin` changed.
   Checked that `proof_deps` is exactly the union of the proof steps' `uses`. Its
   nine steps match cofinal section surjectivity, identification of chosen fibres
   with intersections, degreewise short exactness, quotient acyclicity, transport
   of restriction through `overEquiv`, and the two dimension-shifting cases. Source,
   statement, Lean record, chapter and unit remain unchanged.

**Second-reader changes:** completed `## No longer needed` with the missing
`def-pc-scheme` dependency removal and added this independent review. No Lean proof
or node repair was necessary. Holes closed: the one original declaration listed above;
holes added: none; split off: none.
