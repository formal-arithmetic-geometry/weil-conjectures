## What changed

The target module's theorem now has a complete Lean proof. It first obtains a bounded finite
projective complex model for the prescribed scalar-restricted cohomology module. It proves
coherence of the valuation ring: each finitely generated ideal is principal; the zero ideal is
finitely presented, and a nonzero principal ideal has a singleton basis. It applies the existing
`CochainComplex.finitePresentation_homology_of_coherent` and transfers finite presentation
through the model's A-linear isomorphism with `Module.FinitePresentation.of_equiv`.

The geometric model is split into the new module
`Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric`. Its statement works over an arbitrary
commutative affine base ring, so it isolates the geometric input from valuation-ring coherence.
It states existence of a complex only within a theorem; no definition chooses an arbitrary
witness. The target signature and all public imports are unchanged. The target DAG proof and
proof dependencies now match this argument.

Both delivered modules compile with the required wrapper. The independent second reading
and its subsequent validation are recorded below.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.finitePresentation_moduleCohomology_of_valuationRing`
(node `lem-sc-valuation-proper-coherent-higher-direct-images`).

Added one hole:
`AlgebraicGeometry.Scheme.Modules.exists_finiteProjectiveComplex_model_moduleCohomology`
(node `lem-sc-valuation-proper-coherent-higher-direct-images-perfectness`).
Its proof is exactly `by sorry` in its own module, with the source and complete argument in its
docstring. No holes remain in the target module. This is a decomposition with one hole closed
and one added, not a claim of net hole reduction or of a sorry-free target. The existing
`CochainComplex.finitePresentation_homology_of_coherent` is used as a stated dependency.

Edge cases checked mathematically: the zero ideal is handled explicitly in Lean; rank-zero
coefficients, empty X, and degrees outside the model bounds use zero modules/complexes. The
new model theorem allows the zero base ring, when Spec A and hence X are empty. For positive
rank and arbitrary q, relative flatness follows from flatness of f and local free presentations.
The model does not assert that its homology is projective or free.

## No longer needed

Removed these direct proof imports from the target module:

- `Sheaf.AlgebraicGeometry.LeraySpectralSequence`
- `Sheaf.AlgebraicGeometry.PerfectComplex`
- `Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange`
- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech`

The old dependency `def-amb-finite-locally-free-module` is also no longer a direct proof
dependency of the parent: its public import remains required for the statement and the new
geometric-model node uses it.

Their corresponding nodes (`pqf-lem-leray`, `def-pc-perfect-complex`,
`lem-pc-rf-perfect-base-change`, `def-pc-derived-direct-image`, and
`lem-pc-affine-vanishing`) are no longer direct proof dependencies of the target node. They
remain needed by the new geometric model node, and its module retains their proof imports
(`PerfectComplex` is already public through `PerfectDirectImageBaseChange`). The second
reader removed the redundant target proof import `Mathlib.LinearAlgebra.FreeModule.Basic`
and replaced the new module's unused finite-presentation import by the smaller
`Mathlib.RingTheory.Finiteness.Projective` needed for the model's term properties. Thus no module is
claimed to be pruned from the targets' entire import closure.

## Where the brief, the DAG or earlier work was wrong

The existing plan's coherence argument can be proved directly with Mathlib's valuation-ring
Bezout instance, principal ideal basis construction, and finite-projective finite-presentation
lemma; it needs no new coherence hole. The affine perfect-complex description applies over any
commutative ring, so the geometric model need not assume a valuation ring or use the closed
point of its local spectrum. This preserves the perfect-direct-image, affine-model and Leray
route below the cube unit, whose recorded statement and step are unchanged.

The original Leray declaration forgets scalar actions to abelian groups. An additive
isomorphism alone is insufficient for the target's finite presentation over A. The new model
statement explicitly requires an A-linear isomorphism, and its proof in words explains the
module-valued resolution/edge comparison needed to establish that scalar compatibility.

The referenced Stacks source files are not present in this clone's literature directory.
The relevant statements were checked on the official Stacks pages:
[0B91](https://stacks.math.columbia.edu/tag/0B91),
[08EB](https://stacks.math.columbia.edu/tag/08EB),
[0EX8](https://stacks.math.columbia.edu/tag/0EX8), and
[0EWV](https://stacks.math.columbia.edu/tag/0EWV).
LeanSearch returned Internal Server Error; that search is recorded as unavailable. LeanFinder,
Loogle and Mathlib source searches provided no exact geometric-model theorem.

## New nodes

`lem-sc-valuation-proper-coherent-higher-direct-images-perfectness` states the bounded finite
projective A-module complex model and its A-linear cohomology comparison. It is strictly the
geometric part of the argument: it neither assumes valuation-ring coherence nor asserts finite
presentation of the homology. Its docstring and DAG proof follow 0B91(2), 08EB, affine vanishing,
and the module-valued Leray edge map. The parent uses the model with the already stated coherent
complex cohomology theorem and a proved coherence argument. No interface changes, adaptations,
or change records are needed.

## Second reading by J2

1. **Unchanged interface: PASS.** Read the full repository/sandbox diff. The existing theorem
   `finitePresentation_moduleCohomology_of_valuationRing` has a byte-identical signature,
   including CommRing, IsDomain, ValuationRing, properness, flatness, local finite presentation,
   constant rank d, every natural q, and the precise scalar restriction through
   `GammaSpecIso.inv` followed by `f.appTop`. All its public imports are identical. There are
   no changed definitions, other existing declarations, or forced adaptations. Parsed the
   existing node diff: only `proof`, `proof_deps`, and `proof_origin` change.
2. **Proof and trust: PASS as a decomposition.** Compiled both files in import order with
   `lcompile.py --all`, then compiled a scratch module printing axioms for both declarations.
   Each lists only propext, Classical.choice, Quot.sound, and the expected sorryAx. The sole
   delivery hole is the new named geometric model theorem; the imported coherent-complex
   theorem is also still open in the baseline. No forbidden declarations or hollow data occur.
   Read the ideal proof: valuation gives Bezout; the bottom ideal is subsingleton; for a
   nonzero ideal the principal generator is nonzero, giving the singleton basis; finite free
   implies finite projective and finite presentation. The final equivalence is in ModuleCat A,
   so `of_equiv e.symm.toLinearEquiv` transfers precisely the required module property.
3. **Split-off statement: PASS after citation repair.** Read Stacks 0B91(2), 08EB and the
   general-case proof of 0EX8 on their official pages. Proper plus locally finite presentation
   gives finite presentation; finite locally free F is finitely presented and quasi-coherent,
   and flat f makes it relatively flat. No noetherian or valuation assumption is needed for
   perfectness. A perfect quasi-coherent object on an affine scheme has a bounded finite
   projective ring-complex model. The comparison must be A-linear: forgetting to abelian groups
   in `exists_leray_spectralSequence` would not suffice. Expanded the docstring and node to
   explain module-valued sections, acyclicity of pushforward injectives, the sectionwise
   identity on the resolution complex, and scalar restriction. Checked empty X, d=0, zero A
   (then X is empty), q=0 and q outside model bounds. The model is strictly the geometric
   input; it makes no finite-presentation assertion about homology over a noncoherent ring.
   No arbitrary witness is used to define data.

   Independently searched LeanFinder for "derived global sections perfect complex proper flat
   finitely presented sheaf", Loogle for `"CochainComplex", "Module.Projective"`, and Mathlib
   grep for `bounded.*projective|projective.*complex.*model|moduleCohomology.*homology` using
   `msearch.py`; no exact theorem. Also searched the repository and upstream Lean sources.
   Read `ProperFlatBoundedPresentationModel`, `ProperFlatAffineCechPerfectModel` and
   `AffinePerfectFlatModelReplacement`: they give sheaf-complex models or higher-direct-image
   comparisons, not this scalar-restricted moduleCohomology model. Read
   `PerfectAffineBoundedProjective`: this is the exact existing affine-model input, now cited
   and imported instead of attributing the global affine conclusion to a definition alone.
   Closing the remaining resolution/edge comparison is not a few-minute specialization of
   those statements; kept the one properly documented geometric hole.
4. **Top-down route and pruning: PASS.** The target now uses the geometric model and the
   existing coherent-complex cohomology statement, with coherence proved directly in Lean.
   Its old dependencies are all accounted for under No longer needed, including the
   finite-locally-free definition dependency. The five removed geometric imports remain in
   the new model's route, so there is no claim of a module pruned from the full target closure.
   Removed `FreeModule.Basic` from the target and narrowed the new module's public algebra
   import. All proof-only imports are plain `import`. Read `sk-prop-av-cube.json`: its fixed
   cube statement and seven-factor cancellation step are untouched; its pre-existing empty
   `realized` entries are not rewritten by this delivery. The node still serves the same
   valuation-ring cohomology input to the cube route.
5. **DAG agreement: PASS after repair.** Parent step 1 is the model theorem; step 2 is exactly
   the ideal/coherent-homology/linear-equivalence reduction. Its proof_deps are those two
   nodes. The new node matches every binder and clause of the Lean statement, has the source,
   complete word proof, chapter/unit, blueprint ancestry, actual searches, creation record
   and verbatim Lean record. Added the existing affine bounded-projective node and the
   pushforward-injective module-acyclicity node to its proof and proof_deps, with their plain
   proof imports. No new duplicate statement was introduced by the second reader.

Changes: corrected the global affine-model citation and the scalar-linear comparison proof
in the new node/docstring, added their existing dependency imports, added the missing module
blueprint marker, removed the redundant FreeModule.Basic import, narrowed the new algebra
import, and completed the pruning report. No theorem signature or definition changed.
The hole accounting remains one original hole closed, one new hole added: a decomposition,
with zero net reduction claimed.
