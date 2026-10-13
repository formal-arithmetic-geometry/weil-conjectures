## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.Modules.dual_free_quotient_embedding`
with a proof from local retractions of the transpose. The theorem signature and all
public imports stay identical. Added the proof-only import
`Sheaf.AlgebraicGeometry.Modules.DualMapLocalRetraction`, together with
`WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent`,
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel`, and
`Mathlib.Algebra.Homology.ShortComplex.ShortExact` for the proved cokernel and
pullback arguments.

The private helpers prove composition of mapped split monomorphisms, finite local
freeness of the cokernel of a split inclusion, gluing this cokernel property, and
monicity of arbitrary pullbacks of a locally split inclusion. The affine cokernel
argument uses a genuine split short complex: its evaluated quotient is a finite
projective retract of the middle module. No construction chooses data from the
new unproved theorem; its local retractions are used only inside proposition proofs.

Read Stacks Project Tag 0EKP at https://stacks.math.columbia.edu/tag/0EKP,
proof of (2) to (3). The local finite-basis splitting expands the omitted details
of the dual-surjection construction. The unit route is kept; this node is not
listed as a unit statement or step in `dag/units/sk-prop-input-spreading.json`.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.dual_free_quotient_embedding`
(node `new-sbc-quasi-affine-embedding-pullback`). Its module contains no sorry.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.exists_local_retraction_dualMap_of_epi`
in `Sheaf.AlgebraicGeometry.Modules.DualMapLocalRetraction`
(node `lem-sbc-dual-map-local-retraction`). This is a decomposition, with one upper
hole closed and one strictly partial lower hole added, not a net hole reduction.
The lower statement has no bidual/free comparison, global monicity, cokernel
conclusion, or pullback conclusion. All these remaining parts of the original
argument are proved in the delivered module.

The new statement is true without quasi-coherence of its source: lift the finite
basis locally through the epimorphism, intersect the finitely many neighbourhoods,
and transpose the resulting section. Rank zero uses the unique map from zero;
the empty scheme has no points. Varying rank is allowed because the basis is chosen
separately near each point. The proved cokernel argument requires no constant
rank and no Noetherian assumption, and the proved pullback argument allows every
g, including non-flat morphisms.

## No longer needed

No existing imports were removed; the original module had only its public Dual
import. No original proof-dependency nodes were pruned: its list was empty.

The separate construction of a finite projective kernel of beta and its further
trivialization is unnecessary for the delivered proof. Finite projectivity of the
cokernel is established directly from the local split inclusion. The fixed-rank
`LocalSplittingFiniteFree` and `LocallySplitShortComplexHomology` modules inspected
during the search are not imported: their rank hypotheses are unnecessary.

## Where the brief, the DAG or earlier work was wrong

The original node's two non-elementary proof steps had no stated dependencies.
The one new node isolates local transposition and splitting; the cokernel and
pullback steps are now actual Lean proofs.

`tools/blueprint_refs.py ancestor new-sbc-quasi-affine-embedding-pullback`
returned None because the existing created.item chain records a module rather
than a node id. The new node's blueprint reference follows the explicit parent
`new-sbc-quasi-affine-locally-free-embedding` reference to
`sbc-thm-spreading-finite-etale-galois`; the original blueprint fields were not edited.

LeanSearch returned an Internal Server Error, recorded as unavailable. LeanFinder,
Loogle and source grep searches ran; none returned the local transpose/retraction
statement. Existing local splitting results assume fixed ranks and a locally free
kernel, so they cannot establish the needed splitting here without circularity.

## New nodes

`lem-sbc-dual-map-local-retraction`, stated in
`lean/Sheaf/AlgebraicGeometry/Modules/DualMapLocalRetraction.lean`, isolates the
finite-basis local splitting and compatibility of the transpose with open
restriction. It generalizes the source of the quotient to an arbitrary sheaf,
and retains precisely the local retraction needed by the upper proof. Its
source, complete proof in words, actual search records, edge cases, and Lean
signature are recorded in the new node. No statement or definition was changed,
and no change record or forced adaptation is required.

## Second reading by K4

1. Compared both delivered modules with the repository versions. Existing declaration
signatures and definitions are unchanged; the added declaration is recorded by its new node.
Verdict: pass.

2. Compiled `DualMapLocalRetraction.lean` and inspected the target proof for forbidden
constructs. The upper theorem has no `sorry`; the sole remaining `sorry` is the named,
documented split-off theorem. Verdict: pass, subject to the delivery preflight build.

3. Checked the split-off statement against the local finite-basis argument and edge cases
(rank zero and empty schemes). It is strictly weaker than the upper target and introduces
no hollow definition. Verdict: pass.

4. The proof uses the local retraction node, affine finite-projective sections, and open
restriction/pullback lemmas; unused candidate modules were not imported. The unit route and
existing imports remain intact. Verdict: pass.

5. The target node proof now follows the Lean proof, while the new node records the split
theorem and its dependencies. Verdict: pass.

Changed only the report by adding this review record; no further code repair was needed.
