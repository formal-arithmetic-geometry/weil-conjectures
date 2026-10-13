## What changed

Proved the existing declaration `CochainComplex.boundedProjective_restriction_torAmplitude`
with its signature and visibility unchanged. Added private, fully proved helper
`CochainComplex.single_torAmplitude_of_Tor`: extend a projective resolution into degrees
n-j, prove it K-flat, compute the derived tensor, and identify its homology with Tor'.

Added `Sheaf.Algebra.Homology.BoundedComplexTermAmplitude`, whose theorem
`CochainComplex.bounded_torAmplitude_of_single_terms` is proved by finite induction on
stupid truncations. Both the single-term base case and the empty interval case are proved.
Extension closure of the canonical t-structure supplies the induction step after tensoring.
A K-flat representative of the test module supplies the shift comparison and triangulatedness,
so the proof retains the original arbitrary derived-category universe w.

Added `Sheaf.Algebra.Homology.ProjectiveRestrictionTorBound`, stating the strictly smaller
algebraic step needed for the projective terms. The main proof applies that step termwise,
uses the proved Tor calculation to obtain amplitude [t-d,t], widens to [r-d,s], and applies
the proved bounded induction. The new imports in the original module are proof-only.
Its existing public imports are preserved. Updated the original DAG proof and dependencies.

All three delivered modules compile cleanly through lcompile.py. Searches included the
upstream flat-model and homotopy-devissage files, Mathlib, all Sheaf modules, and imported
blueprint nodes. LeanSearch returned an HTTP internal-server error, recorded as unavailable;
LeanFinder and source search provided component results. Stacks 066H and 066K were read online.
No finite generation, interval-ordering, or derived-universe restriction was added.

## Proved and sorry left

Closed the one original hole:
`CochainComplex.boundedProjective_restriction_torAmplitude`
(node `lem-pc-bounded-projective-restriction-tor-amplitude`). Its proof is a decomposition,
not a complete axiom-free proof: one lower hole was added.

New proved theorem: `CochainComplex.bounded_torAmplitude_of_single_terms`
(node `lem-pc-bounded-complex-term-amplitude`). Its private induction helper is also proved.
The original module's private `CochainComplex.single_torAmplitude_of_Tor` is proved.

The only sorry in the delivered files is
`ModuleCat.projective_restriction_tor_bound`
(node `lem-pc-projective-restriction-tor-bound`). It is a public named theorem with its entire
proof `:= by sorry`, a complete source proof in words, and its own module and DAG node.
It concerns one module and Tor only: no complexes, derived categories, support bounds,
filtrations, or totalization occur in its statement. The source argument is valid for
infinite free modules. The existing finiteProjective_tor_acyclic theorem cannot replace it:
that theorem assumes a finite split-free presentation and tests only algebra coefficients.
No axioms or hollow definitions were added. Net direct-hole count is zero (one closed,
one added); the spectral-sequence branch is unnecessary for this item.

## No longer needed

The previous proof dependencies `thm-sp-spectral-object-yields` and
`lem-pc-module-bounded-flat-kflat` are removed from this item's DAG proof dependencies.
Their modules `Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence` and
`Sheaf.Algebra.Homology.BoundedFlatKFlat` are not imported or used by the delivered proof.
No assertion is made that other targets cease to reach these modules.

The entire planned bounded-filtration spectral-sequence argument is replaced by the proved
finite stupid-truncation induction. No first-page calculation, convergence theorem,
exact-couple construction, or finite-filtration graded-piece argument is needed here.
The K-flat calculation instead uses the proved upstream
`CochainComplex.kFlat_of_isStrictlyLE_of_flat` directly.

No original import was removed: those imports also expose the existing statement's API.
The trial direct import of DerivedCategory.Monoidal.Shift in the new induction module was
removed after checking that HasMonoidalDerivedCategory already makes the required tools
available. The final main module needs FlatModel, ExtendMap and Flat.ModuleCat for its proof.
No trial ordered-case or empty-case restatement was retained or delivered.

## Where the brief, the DAG or earlier work was wrong

The planned spectral sequence is not necessary. Stacks Tag 066H proves the bounded-complex
step by induction on stupid truncations; this delivery writes that induction in Lean.
The existing generic homotopy devissage theorem assumes shift-stability of the object
property, which a fixed Tor-amplitude interval does not satisfy. The new private induction
uses extension closure only and tests single complexes in their actual degree.

The upstream global derived tensor shift/triangulated instances tie the Grothendieck
universe to the derived-category universe. Applying them directly would fail for the
original arbitrary w. The representative-dependent commShiftTensorRightQhObj and
isTriangulated_tensorRightQhObj tools avoid that issue without any interface change.

Edge cases checked: empty [r,s], a=b for the generic induction, empty [a,b] with zero terms,
d=0, zero modules and rings, and infinite projective modules. The Lean induction handles
empty support by proving the whole complex zero. All unit-level statements and steps
remain untouched; this is a route change below the unit level.

## New nodes

`lem-pc-bounded-complex-term-amplitude` is the common-interval, actual-degree formulation
of Stacks 066H. Its module is fully proved and imposes no projectivity or Tor-dimension
hypothesis. Its induction also handles both pairs of endpoints without ordering.

`lem-pc-projective-restriction-tor-bound` is the single-module Tor step below Stacks 066K.
Projectivity realizes the module as a retract of an arbitrary free module; Tor of that
restricted free module is a direct sum of the regular-module Tor groups, so the bound
passes to the retract. The node names the existing Tor-symmetry declaration for resolving
the test module. This is the only new unfinished statement and is strictly a part of the
argument. No statement/interface change records or forced adaptations are needed.

## Second reading by K3

1. I compared the delivered modules with the repository versions. Existing declaration
signatures and visibility are unchanged; the only additions are proof imports, private
helpers, and the two separately named split/proved modules recorded above. No target or
existing public statement was weakened.

2. I compiled all three sandbox modules with `lcompile.py --all`. They compile without
errors or warnings. The only remaining `sorry` is the named public theorem
`ModuleCat.projective_restriction_tor_bound`; no definition contains `sorry`, and no
forbidden declarations or axioms were added.

3. I checked the new split statement against the projective-retract/direct-sum Tor
argument and its Stacks sources. It is strictly smaller than the target (one module and
one Tor degree bound), has no finiteness hypothesis, and the node, source, docstring, and
Lean signature agree. The bounded-complex theorem is fully proved and handles empty
intervals and zero terms.

4. I reviewed the proof downward for shorter library routes and verified that the
projective-resolution calculation, K-flat comparison, and stupid-truncation induction
use existing declarations. The spectral-sequence and bounded-flat dependencies are no
longer imported or used, as listed above; imports retained by the statements remain.

5. I checked the DAG proof and `proof_deps` against the Lean proof and confirmed that the
unit route remains realized through the bounded-complex and projective-restriction steps.
The new nodes carry their Lean records and proof origins.

I changed only this report section; no Lean proof or statement required repair after the
independent reading.
