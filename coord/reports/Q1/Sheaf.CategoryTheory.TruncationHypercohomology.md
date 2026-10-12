## What changed

Proved `CategoryTheory.exists_truncationHypercohomology` without changing its signature.
Constructed the exact couple from exactness of its raw maps, proved the specified natural
E2 comparison by whiskering the single-functor, shift, and ordinary derived-functor
isomorphisms, and combined the quadrant, sharp bounds, and canonical abutment clauses.
Added four argument-part modules. `truncation_quadrant_vanishing` and
`halfPlane_sharp_bounds` are fully proved. The latter derives support, boundedness,
zero differentials, sharp cycle/boundary constancy, regularity and completeness.
No statement or definition of an existing declaration was changed.

## Proved and sorry left

Proved: `CategoryTheory.exists_truncationHypercohomology` (thm-sp-truncation-e2),
`CategoryTheory.truncation_quadrant_vanishing` (lem-sp-truncation-quadrant-vanishing),
and `CategoryTheory.halfPlane_sharp_bounds` (lem-sp-half-plane-sharp-bounds).
Two public whole-proof sorries remain in the new modules:

- `CategoryTheory.truncation_raw_exact` (lem-sp-truncation-raw-exact).
- `CategoryTheory.truncation_canonical_abutment` (lem-sp-truncation-canonical-abutment).

The item's module contains no sorry. Its proof still depends on open library statements,
as intended for stage 3. Local compilation of all five modules passes.

## No longer needed

Removed these proof-only imports from the item's module:

- `Sheaf.CategoryTheory.DerivedCategory.ShiftIdentification`
- `Sheaf.CategoryTheory.DerivedCoupleExact`
- `Sheaf.CategoryTheory.ExactCouple`
- `Sheaf.CategoryTheory.Filtration`
- `Sheaf.CategoryTheory.HalfPlaneConvergence`
- `Sheaf.CategoryTheory.RightDerivedFunctorTruncationIso`
- `Sheaf.CategoryTheory.TruncationCoupleExact`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`

The ShiftIdentification module is unnecessary for this proof: its E2 comparison is
constructed directly from proved source-library natural isomorphisms. The
TruncationCoupleExact module is unnecessary for this proof: it fixes standard derived
category instances, whereas the raw exactness interface must work for the instances
in this theorem. The existing exact-couple and filtration definition modules remain
transitively required. HalfPlaneConvergence remains required by HalfPlaneSharpBounds.
DerivedCoupleExact, RightDerivedFunctorTruncationIso, and the triangulated derived-functor
module remain in the proof plan for the canonical abutment part; they are not globally
pruned. No unit statement or realized step is bypassed.

The complete list removed from the main node's old `proof_deps` is:

- `lem-sp-truncation-couple-exact`: replaced by arbitrary-instance raw exactness.
- `lem-sp-shift-identification`: replaced by the source natural isomorphisms.
- `lem-weil-pbc-derived-functor-negative-vanishing`: replaced in the vanishing part by
  `Functor.isGE_rightDerivedFunctor_obj_singleFunctor` from PlusCompatibility.
- `lem-weil-pbc-truncation-cohomology`: still used through the vanishing lemma's
  Mathlib truncation-cohomology proof.
- `lem-sp-derived-couple-exact`, `thm-sp-half-plane-convergence`,
  `lem-weil-pbc-derived-direct-image-triangulated`, and
  `lem-weil-pbc-derived-functor-truncation-iso`: retained through the argument-part nodes.
- `def-sp-convergence`, `def-sp-filtration`, and `def-sp-image-filtration`:
  retained in the interfaces and argument-part nodes.

Thus only the truncation-couple-exact and shift-identification helper nodes are
unneeded on this proof route; negative vanishing is also bypassed here, although
its module remains needed for triangulatedness. This is pruning of this route,
not a claim that other target routes no longer reach these nodes.

## Where the brief, the DAG or earlier work was wrong

`truncationCouple_exact` refers to `truncationCouple`, which internally chooses
`HasDerivedCategory.standard`. The theorem under work allows arbitrary instances and
universes. Applying that lemma directly does not establish exactness of the specified
raw maps for those instances. The new raw exactness lemma makes this missing interface
explicit and includes the type-zero target-index transport of g.

`halfPlaneConvergence` does not expose the exact cycle/boundary stabilization equations,
canonical j and c maps, or the specified lambda/lift/psi equations required here. Its
abstract comparison alone cannot fill the canonical abutment clauses. The new interfaces
isolate these genuine parts, rather than restating the entire theorem.

LeanSearch was unavailable (Internal Server Error) for every attempted query; recorded
as unavailable, without an absence verdict. LeanFinder and source grep were used.
WANTED: literature/stacks-project/homology.tex, Tags 011R, 011T, 0BDU, 0BDV, 012F,
012U; literature/stacks-project/derived.tex, Tags 08J5, 05SE, 05TC, for the new nodes.
These local literature files are absent; the proof descriptions refine the existing
blueprint steps and are marked agent-written.

## New nodes

`lem-sp-truncation-raw-exact`: raw-map exactness for arbitrary derived-category
instances, including the type-zero g transport; TruncationRawExact.lean. Open.

`lem-sp-truncation-quadrant-vanishing`: initial D/E support; proved using homology
conservativity, truncation cohomology, derived single-object support and the bridge;
TruncationQuadrantVanishing.lean.

`lem-sp-half-plane-sharp-bounds`: sharp page/cycle/boundary bounds and completeness;
proved from halfPlaneConvergence, page subquotients and cycle/boundary recursion;
HalfPlaneSharpBounds.lean.

`lem-sp-truncation-canonical-abutment`: canonical abutment witnesses and their map
equations, strictly the final filtration and convergence part of the theorem;
TruncationCanonicalAbutment.lean. Open. No change records: no existing interfaces changed. Proof-only imports in the two
open modules retain the dependencies of their stated proof plans.


## Second reading by Q1

1. Compared every delivered module with the repository. Only the main module exists
   there; its existing theorem signature is byte for byte unchanged, and its public
   imports and existing definitions are unchanged. All four new modules have matching
   nodes. No change record is needed. Verdict: pass.
2. Compiled all five modules in import order through lcompile.py. Checked the two
   whole-proof sorries against the report and scanned for forbidden declarations and
   hollow definitions. A scratch copy printed the axioms of all five public theorems:
   only propext, Classical.choice, Quot.sound, and sorryAx. The last is transitive
   through the explicitly open statements, including existing library statements;
   these are reductions, not claims of axiom-free closure. Verdict: pass.
3. Read each new interface and its word proof. Raw exactness is only the three
   short complexes, not the original theorem; canonical abutment assumes the already
   constructed exact couple and support, and supplies only the final filtration and
   convergence part. Neither restates the complete item. Checked the zero-complex
   case, a single object under an exact functor, negative first indices, q<a, p=0,
   and n<a (where fullness and zero force the abutment to be zero). The stabilized
   page is clamped at 2, and the stronger graded-map bound makes u<=-1. New searches
   using distinguished-triangle exact sequences and eventual-constant colimits found
   Mathlib building blocks, not these entire interfaces. Read the actual source
   definitions and the existing half-plane and truncation-isomorphism interfaces.
   Raw exactness still requires bridge/index transport; canonical abutment still
   requires the specified maps and their equations, so neither closes by one existing
   lemma in a few minutes. Checked Stacks
   [05TC](https://stacks.math.columbia.edu/tag/05TC) and
   [011T](https://stacks.math.columbia.edu/tag/011T). Verdict: pass.
4. Read the proof from the target down: exact-couple construction, the definitional
   natural E2 component comparison, vanishing, sharp bounds, and final abutment.
   Removed the redundant Mathlib.Exact proof import. Tested removal of
   EnoughInjectives, but restored it because its instance is required by the
   vanishing proof. Retained proof-plan imports in open modules. Completed the old-proof-dependency pruning
   list, distinguishing removed direct dependencies from retained argument-part
   dependencies. Read dag/units/sk-thm-properbasechange.json: none of its statement
   or realized step nodes is replaced or bypassed. Verdict: pass.
5. Checked every new node's Lean signature record against its declaration, required
   fields, and proof_deps against the union of proof-step uses. Corrected the vanishing
   node to cite PlusCompatibility's single-object negative support rather than the
   bypassed general negative-vanishing theorem. The main node follows the four proof
   parts actually assembled; the open nodes record their remaining proof plans.
   Verdict: pass after metadata repair.

Second reading changed: corrected the raw-exactness word proof's triangle indexing
(and its node); corrected the vanishing node's proof dependencies; added private
proof-plan imports to the two open modules; removed the redundant Mathlib.Exact proof import;
completed the pruning report. No existing or new theorem signature changed, and no
Lean proof term needed repair. Local compilation and axiom checks passed; final
server compilation and preflight are checked by deliver3.py.
