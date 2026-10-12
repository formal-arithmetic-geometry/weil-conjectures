## What changed

Replaced the rejected two-lemma attempt with a four-step decomposition of the original
seven-step Stacks 087W argument. The existing statement, universes, public imports and
docstring of `AlgebraicGeometry.coherentFormalModules_affine` are preserved. Its proof now
extracts a finite completed-module limit functor L and its projections, obtains the two
natural isomorphisms for the canonical quotient functor Q, and constructs E with
`CategoryTheory.Equivalence.mk`. That constructor keeps L and Q unchanged while adjusting
the unit to satisfy the triangle law. The projections and their four assertions therefore
have exactly the required types, and the inverse identification follows by `Iso.refl`.

Added four modules, each with one named public theorem, a source, a complete proof in
words, and its own DAG node:

- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffineLimit`: the limit functor, finite
  generation, cone naturality, projection kernels, and completed scalar action (original
  steps 1 and 3--5). It asserts no equivalence or inverse functor.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffineQuotient`: coherence of the fixed
  quotient system (parts of steps 2 and 6). Also defines
  `coherentFormalModules_affine_quotientFunctor` using `ObjectProperty.lift` of the
  existing restriction/tilde/formalCompletionFunctor composite. All object and morphism
  data come from this real construction; the unproved theorem supplies only membership
  in the coherent full subcategory. No arbitrary witness is chosen in a definition.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffineComplete`: finite-module
  completeness gives Q followed by L naturally isomorphic to identity (step 6).
  Its hypotheses use only the limiting cones, naturality and scalar equation.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffineReconstruction`: the surjective
  ideal-power projection kernels give L followed by Q naturally isomorphic to identity
  (steps 2, 5 and 7). It needs only naturality and the projection quotient assertions.

Updated the original node's proof, proof_deps and proof_origin to this actual assembly.
The new nodes cite the lower ingredients of the original proof; none cites the original
node as a statement or proof dependency. The original unit sk-thm-p1 and every one of
its realized statements and steps stay unchanged.

## Proved and sorry left

The local hole in `AlgebraicGeometry.coherentFormalModules_affine` is closed by a complete
Lean proof FROM the four named intermediate statements. This is a decomposition, not a
sorry-free proof of Stacks 087W. One original hole is closed and four holes are added;
the arithmetic is -3 before any ledger calculation, and no net progress is claimed.
There is no remaining sorry in the item's module.

Every added hole is exactly `:= by sorry` in one public named theorem:

- `AlgebraicGeometry.coherentFormalModules_affine_limit`
  (`lem-weil-pbc-coherent-formal-modules-affine-limit`).
- `AlgebraicGeometry.coherentFormalModules_affine_quotient_coherent`
  (`lem-weil-pbc-coherent-formal-modules-affine-quotient`).
- `AlgebraicGeometry.coherentFormalModules_affine_complete`
  (`lem-weil-pbc-coherent-formal-modules-affine-complete`).
- `AlgebraicGeometry.coherentFormalModules_affine_reconstruction`
  (`lem-weil-pbc-coherent-formal-modules-affine-reconstruction`).

The quotient functor definition contains no sorry; its data are the existing quotient
construction with a proposition-valued membership proof. The equivalence assembly
contains no anonymous, nested or private hole. Existing downstream unproved ingredients,
including `CategoryTheory.tower_limit_exact_surjective_kernels` and
`AlgebraicGeometry.Scheme.Modules.ideal_times_quasiCoherent_affine_sections`, are retained
as the lower work of the appropriate new nodes.

All five delivered modules compile through lcompile.py. Separate scratch compilation
verified the module first-isomorphism comparison with its quotient projection equation,
and `AdicCompletion.isAdicComplete_self` for the extended ideal; these are the concrete
algebraic tools used in the reconstruction and completeness proof descriptions.

## No longer needed

Removed these direct proof imports from the item's module and placed them in the
intermediate modules whose proofs require them:

- `Sheaf.Algebra.Category.ModuleCat.TowerLimitExactSurjectiveKernels`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`.
- `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`.
- `Sheaf.RingTheory.AdicCompletionNoetherian`.
- `Sheaf.RingTheory.FiniteModuleComplete`.
- `Sheaf.RingTheory.NakayamaNilpotent`.

None of these modules or their nodes is pruned from the transitive argument. The new
lower items still need the original proof ingredients. Thus the list of existing nodes
and modules no longer needed is **none**. The rejected AffineCore and AffineInverse files
and nodes remain only in scratchpad/rejected-first-reading and are not delivered or
imported; those were never landed.

## Where the brief, the DAG or earlier work was wrong

The rejected `coherentFormalModules_affine_inverse` asserted the canonical inverse
identification for an arbitrary equivalence E. It is false for A = k × k and I = 0 after
composing the ordinary affine equivalence with the factor-swap autoequivalence. The
proposed AffineCore and AffineInverse nodes also cited the original theorem circularly.
Neither statement is reused. This report replaces the earlier rejection report, including
its old second-reading section; the next independent reader must write a fresh reading.

The new split gives the two inverse identities for the fixed canonical Q, and the
completeness statement characterizes L through limiting cones and completed scalar
compatibility. In the factor-swap example such scalar-compatible limiting projections
cannot exist for a twisted L. Reconstruction is a statement about the underlying
A-module quotients and does not need scalar compatibility or a preexisting equivalence.

Edge cases checked in ordinary mathematics: I = 0 gives towers of isomorphisms and the
usual finite-module/affine correspondence; I = top makes the completion and every
positive-level formal module zero; zero modules give zero cones, and n = 0 means the
first positive quotient, with kernel I times the module. These cases satisfy all four
new statements. This is mathematical checking of the hypotheses, not a claim that
compiling with sorry verifies truth.

Read Stacks coherent.tex, lemma-inverse-systems-affine, lines 6272--6310, from the available
local literature mirror. LeanSearch currently returns Internal Server Error, recorded
as unavailable for each query. LeanFinder, Loogle and Mathlib source grep were run and
recorded through msearch.py for the new nodes. Searches found the algebraic ingredients,
but no ready-made formal-system equivalence or canonical quotient reconstruction.

## New nodes

`lem-weil-pbc-coherent-formal-modules-affine-limit`: original steps 1 and 3--5, plus the
componentwise scalar and morphism construction. Strictly the forward functor and its
projection properties, with no equivalence assertion.

`lem-weil-pbc-coherent-formal-modules-affine-quotient`: original steps 2 and 6, the
membership theorem for the existing canonical quotient system; also records the actual
lifted functor definition in its Lean declarations.

`lem-weil-pbc-coherent-formal-modules-affine-complete`: original step 6, the finite-module
inverse identity using Noetherianity and completeness, then uniqueness of limiting cones
and completed scalar compatibility.

`lem-weil-pbc-coherent-formal-modules-affine-reconstruction`: original steps 2, 5 and 7,
the formal-system inverse identity using the first isomorphism theorem, affine
quotient/tilde comparison, and naturality checked after quotient projections.

No existing definition or statement changes, forced adaptations, or change records.

## Second reading by D2

1. **Interfaces: PASS.** Compared each delivered module with the repository: only
   CoherentFormalModulesAffine already exists. Its complete theorem signature,
   universes, visibility, docstring and three public imports are byte-for-byte unchanged.
   Its diff consists of private proof imports and the proof body. There are no adapted
   existing modules, existing definition changes or change records.
2. **Lean proof and data: PASS as a decomposition.** Independently compiled all five
   modules in import order through lcompile.py, without errors or warnings. A scratch
   copy with explicit #print axioms for the original theorem, all four new theorems
   and quotientFunctor reports only propext, Classical.choice, Quot.sound and sorryAx.
   Exactly the four reported named public intermediate theorems contain sorry; there
   are no forbidden declarations or holes in definitions. Inspected ObjectProperty.lift:
   quotientFunctor's object and morphism data are the existing canonical quotient
   composite, and the missing theorem supplies only a proposition. The existential L
   is eliminated inside a theorem proof, not used to define an arbitrary public object.
3. **Intermediate statements: PASS.** Read all four signatures and complete docstring
   arguments against the source proof of lemma-inverse-systems-affine in the available
   Stacks coherent.tex mirror (lines 6272--6310). Limit constructs only the forward
   functor and projections. Quotient establishes membership for a fixed construction.
   Complete and Reconstruction prove separate natural inverse identities, with exactly
   the cone/scalar or quotient hypotheses their arguments need. None merely renames
   the entire equivalence assertion. Checked I=0, I=top, zero modules, level n=0 and
   A=k x k with a factor-swap twist: completed scalar compatibility prevents the false
   twisted completeness claim. Independently searched with different queries using
   msearch.py LeanFinder, Loogle and grep, plus rg on Sheaf and upstream sources.
   Found AdicCompletion.ofLinearEquiv and finite-module completion/tensor ingredients,
   but no theorem supplying any whole new sheaf-system statement. The existing
   formalCompletionSystem_coherent requires a coherent input; restricted finite
   completed modules need not be finite over A, so it does not close Quotient directly.
   None of these four holes can be closed by a short application of the found results.
4. **Route and pruning: PASS.** The main proof assembles the two natural isomorphisms
   with Equivalence.mk, which preserves both functors. Its final Iso.refl therefore
   proves precisely the canonical inverse identification. Proof-only new imports are
   private; public imports serve signatures or the actual quotient definition. The
   old seven proof modules remain below the new lemmas for their documented arguments.
   All old direct proof dependencies are replaced by the four intermediate nodes;
   their mathematical ingredients remain in the transitive route. No existing module
   is claimed pruned. Inspected sk-thm-p1.realized; no unit statement or realized step
   is bypassed or edited. One original hole closed and four added is decomposition
   with raw net -3, not a sorry-free proof or a claim of ledger progress.
5. **DAG consistency: PASS.** The original node changes only proof, proof_deps and
   proof_origin. For every delivered node, proof_deps equals the union of step uses.
   Each new node has source, proof_origin, statement dependencies, recorded searches,
   creation record, blueprint ancestry, matching unit/chapter and Lean record; each
   recorded theorem signature occurs literally in its Lean file. The top node records
   exactly the construction and assembly in the Lean proof. No new node depends on
   the original theorem, so the new route is not circular.

Second-reading changes: added this independent review and verification evidence only.
Added the private proof import
Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections to Complete:
its node and docstring explicitly use the affine quotient comparison, and Quotient
imports that module privately, so it does not export this proof ingredient to Complete.
No statement, definition or proof body changed. Removed the temporary axiom-probe copy.
