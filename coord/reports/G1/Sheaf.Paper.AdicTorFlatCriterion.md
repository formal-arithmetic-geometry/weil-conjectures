## What changed

Restored the quarantined `Sheaf.Paper.AdicTorFlatCriterion` source, retaining the original theorem signature and all its public imports. Its proof now combines an explicit local DVR torsion normal form with fully proved categorical glue: nilpotent epimorphisms have zero domain, sectionwise free sheaves are flat, and flatness descends along finite stratum covers. The descent proof identifies tensor kernels after exact module inverse image and uses the existing noetherian zero-object detection theorem. Five private helpers are fully proved.

Added `Sheaf.Paper.AdicCohomologyTorsionNormalForm`, isolating the independent elementary-divisor and periodic-resolution calculation for arbitrary K, without any Tor-vanishing assumption. Its sole theorem remains a hole. This packet therefore decomposes the item; it does not establish the entire criterion from the three permitted axioms alone.

Completed three existing holes of the unclaimed `Sheaf.Paper.ProEtaleCanonicalTensorPullback`: preadditivity comes from the proved independent-universe sheaf tensor; ordinary-comparison naturality is the chosen comparison's characterization; the total comparison is invertible by the existing coproduct-preserving left-adjoint theorem.

## Proved and sorry left

Closed original item hole:

- `AlgebraicGeometry.Scheme.pbc_adic_tor_implies_flat_cohomology` (node `lem-weil-pbc-adic-tor-implies-flat-cohomology`): complete Lean proof from the new normal-form theorem and existing declarations; one original hole removed, one retained result below. This is a decomposition, not a net closure of the criterion.

Closed existing dependency holes, with signatures unchanged:

- `AlgebraicGeometry.Scheme.proEtaleTensorPreadditive`.
- `AlgebraicGeometry.Scheme.proEtaleOrdinaryTensorPullback_naturality`.
- `AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotal_isIso`.

These three are attached to `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`. The dependency originally had five holes; two remain untouched:

- `AlgebraicGeometry.Scheme.proEtaleOrdinaryTensorPullback_existsUnique`.
- `AlgebraicGeometry.Scheme.proEtaleCanonicalTensorPullback`.

New hole:

- `AlgebraicGeometry.Scheme.pbc_adic_cohomology_torsion_normal_form`, node `lem-weil-pbc-adic-cohomology-torsion-normal-form`: the geometric perfect-model coefficient transport, DVR block decomposition, and comparison of its explicit periodic quotient resolution with the ambient Tor functor remain to be formalized. Its complete source proof is in the module docstring and node. This is an independent structural result, assuming neither the conclusion nor the hypothesis of the criterion. In particular it has no Tor-vanishing hypothesis and produces a finite-free/torsion decomposition for every bounded constructible complete complex, plus a specific Tor quotient.

Counts across the three delivered modules: four preexisting holes removed, one new hole added; three holes remain, two preexisting and one new. The item itself has zero holes, originally one. The five private helpers have zero holes. No definition contains a hole, and no existential witness is turned into definitional data.

Validation: each delivered module compiles through the remote single-file compiler. The proof covers zero torsion, zero rank, empty charts and empty schemes without introducing a nonemptiness assumption. The nilpotent argument works even with exponent zero. The quotient convention is index n = exponent n+1; only Tor degree one at cutoff q-1 is used.

## No longer needed

No existing module is withdrawn, and no global module pruning is claimed. The item retains its original public imports. Redundant proof imports removed after compilation: `Mathlib.RingTheory.Flat.EquationalCriterion`, `Mathlib.LinearAlgebra.FreeModule.Basic`, `Mathlib.Algebra.Homology.ShortComplex.ExactFunctor`, and `Mathlib.RingTheory.Nilpotent.Defs` (their APIs are supplied by the remaining imports).

The direct item proof no longer needs a nonzero residue-field sheaf or preservation of flatness in the forward direction. It instead uses a nilpotent epimorphism and proves only the descent direction needed here. The DVR and perfect-realization dependencies remain mathematical work of the new normal-form node, not globally pruned work. The obsolete direct `tool_uses` entries removed from the item node are:

- `lem-pc-bounded-above-flat-kflat-site`.
- `lem-pc-sheaf-modules-tensor-closed`.
- `lem-weil-l-adic-extension-integers-dvr`.
- `lem-weil-pbc-completed-constant-sheaf-reduction`.
- `lem-weil-pbc-constant-module-section-properties`.
- `lem-weil-pbc-integral-stratified-perfect-characterization`.
- `lem-weil-pbc-proetale-immersion-limit-preservation`.
- `lem-weil-pbc-ringed-pullback-preserves-kflat`.
- `lem-weil-pbc-ringed-topoi-module-pullback-tensor`.
- `lem-weil-pbc-site-derived-tensor-descent`.
- `lem-weil-proetale-weakly-etale-localization`.

## Where the brief, the DAG or earlier work was wrong

The archived item source is a restoration assignment, not a withdrawn lemma. Its parent continues to need the declaration; no withdrawal was attempted.

Step 3 of the previous node says that the integral stratified-perfect characterization has exactly these hypotheses. Its current quarantined interface actually takes `E : Type u`, the lifted `pbcIntegralDatum`, and a global unit hypothesis, while this criterion takes `E : Type (u+1)`, the actual unlifted `pbcPadicCoefficientDatum`, and stalkwise invertibility. It cannot be applied directly as written. The new node explicitly records the required coefficient transport rather than treating this mismatch as definitional equality.

The supplied Smith normal form is a matrix/submodule theorem, not a bounded-complex block decomposition. Similarly the constant-realization theorem supplies reduction comparisons, not the specific periodic Tor projection. Those are genuine steps of the retained structural result; this delivery does not claim that importing these declarations alone closes them.

The previous plan discarded empty charts and proved a residue sheaf nonzero. The nilpotent epimorphism argument avoids that separate nonzero calculation and includes empty charts uniformly.

## New nodes

`lem-weil-pbc-adic-cohomology-torsion-normal-form` records exactly the local elementary-divisor/Tor-obstruction portion of the original source proof, in a new module with one public theorem. Its statement does not repackage the all-level Tor hypothesis: it has no vanishing hypothesis and exhibits data before vanishing is imposed. Blueprint searches for “Smith normal form”, “consecutive”, and “nilpotent cohomology” found no duplicate: the two matches for “consecutive” were an exact couple and normalized towers, neither this result. The required LeanSearch, Loogle/LeanFinder and source-grep search kinds are recorded. LeanSearch returned split-short-complex constructions and ModuleCat.free_shortExact, not a DVR complex normal form.

The original item's node now records the actual nilpotent, equational-criterion and kernel-descent proof, with proof dependencies updated. The unit route is preserved (`sk-rem-rest` has no separate realized step bypassed).

Change record: `coord/changes/G1-adic-tor-tensor-proof-completions.md` documents the three proof completions in the unclaimed tensor dependency. No existing public statement or definition changes meaning.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
