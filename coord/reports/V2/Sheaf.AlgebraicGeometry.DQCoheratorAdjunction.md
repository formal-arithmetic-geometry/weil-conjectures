## What changed

Filled all four original theorem proofs in Sheaf.AlgebraicGeometry.DQCoheratorAdjunction,
with every public signature and public import unchanged. The detection theorem is moved
below the proved structure-sheaf and comparison lemmas so it can use them.

The adjunction proof uses schemeDerivedQCoh_compactlyGenerated, the ambient coproduct
and closure theorems in DerivedQCohDirectSumsAux, and the existing locally-small Brown
Hom representability theorem. This handles arbitrary supplied Hom universe w while the
coproduct and compact-generation universe remains u. The locally-small instance comes
from the source library's Grothendieck/K-injective-resolution machinery.

The shifted structure sheaf is proved from Mathlib single-functor cohomology and the
source library's quasi-coherent unit and arbitrary-sum results. The zero-cohomology case
uses the empty sum, without assuming a nonempty scheme or family.

The global-sections computation is built explicitly from unitHomEquiv, a natural
Hom-complex isomorphism, homology classes, Qh_map_bijective, localization comparisons,
and the additive shift adjunction. Its naturality proves detection using the supplied
adjunction and IsIso hypothesis. All private helpers are fully proved. The generic
postcomposition/LeftHomologyMapData helpers follow the already proved private helpers
in EtaleSheafHExtDerivedComparison; that unrelated module is not imported.

Updated the existing node's proof, proof_deps and proof_origin to this implemented route.
No new module, node, interface, or forced adaptation is needed. The local heartbeat
increase on the naturality helper is for unfolding the composite localization and shift
Hom equivalence; the complete module compiles within the single-file time limit.

## Proved and sorry left

Closed all four original holes, all attached to lem-pc-dq-coherator-adjunction:

- AlgebraicGeometry.exists_dqCoheratorAdjunction
- AlgebraicGeometry.dqCoherator_detects_globalSections
- AlgebraicGeometry.structureSheaf_shift_is_derivedQCoh
- AlgebraicGeometry.globalSections_homology_equiv_structureSheaf_shift

No sorry remains in this module. No sorry was added anywhere. This is four closed
holes and zero split-off holes; the existing dependencies retain their own proof status.
The final pruned module compiles without errors or warnings using lcompile.py.

## No longer needed

Removed these direct proof imports:

- Sheaf.AlgebraicGeometry.DerivedAmbientDirectSums
- Sheaf.AlgebraicGeometry.DerivedQCohDirectSums
- Sheaf.AlgebraicGeometry.GlobalDerivedHom
- Sheaf.AlgebraicGeometry.Modules.QuasicoherentBinarySum
- Sheaf.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections
- Sheaf.CategoryTheory.BrownRepresentabilityRightAdjoint

The first two are supplied transitively by the existing compact-generation/ambient
coproduct-closure machinery; their mathematical results remain needed there. The Brown
right-adjoint result remains a dependency of BrownRepresentabilityHomLocallySmall.
Consequently those three nodes are replaced as direct proof dependencies, not claimed
to be globally unreachable.
Their exact identifiers are lem-pc-derived-qcoh-direct-sums,
lem-pc-derived-ambient-direct-sums, and lem-pc-brown-representability-right-adjoint.

The binary-sum and filtered-colimit route is unnecessary: the already proved arbitrary
quasi-coherent coproduct theorem replaces it, including the empty sum.
lem-weil-pbc-quasi-coherent-module-direct-sum and
lem-weil-pbc-quasi-coherent-module-colimit-affine-sections are no longer direct dependencies.
The construction of RΓ via a separate derived functor and derived internal Hom in
GlobalDerivedHom is unnecessary for the theorem's complex-valued conclusion;
def-pc-global-derived-rhom is removed from the direct proof dependencies. Other target
branches may still need these modules. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The mathematical route is correct. Its original list did not mention the already proved
ambient coproduct/closure and locally-small Brown helpers. The common-universe Brown
statement cannot be applied directly for an arbitrary Hom universe w from merely
u-indexed coproducts; the existing locally-small version resolves this without changing
any hypothesis.

The original Nonempty additive-equivalence statement alone does not encode naturality,
so it would not suffice by itself to prove detection. This delivery constructs the
comparison and proves its naturality in private lemmas, rather than introducing a
stronger unproved comparison statement. Existing docstrings are kept verbatim;
the node and this report record the refined proof route.

## Second reading by V2

1. **Visible changes and signatures.** Compared the delivered module and node with the
repository versions. Existing public theorem signatures are byte-for-byte unchanged;
the module changes only proof bodies and proof-only imports, and the node changes only
its implemented proof route and dependencies. Verdict: pass.

2. **Compilation and proof soundness.** Compiled the sandbox with
`python3 /home/ubuntu/weil-launcher/lcompile.py --all`; it compiled successfully. Searched
the delivered Lean and node files for `sorry`, `axiom`, `unsafe`, `opaque`, `extern`,
`implemented_by`, and `debug.skipKernelTC`; none occur. Verdict: pass.
The delivery dry run also passed its axiom probe and preflight for every declaration.

3. **Split statements and mathematical strength.** No theorem was split off and no new
public statement or definition was added. The four original target holes are proved
directly, with the empty coproduct case handled explicitly. Verdict: pass.

4. **Shortest route and pruning.** The proof uses the existing locally-small Brown
representability criterion, compact-generation/ambient coproduct closure, and explicit
Hom-complex naturality. The six removed proof-only imports and their superseded direct
dependencies are recorded above; the unit route and realized steps remain represented
by the node. Verdict: pass.

5. **DAG agreement.** The node proof steps, `proof_deps`, and `proof_origin` match the
implemented declarations and imports. Every dependency named by the node exists in the
repository DAG. Verdict: pass.

I added this second-reading section and spelled out the three superseded direct
dependency node identifiers in the pruning report. No Lean code, declarations, or DAG
statements were changed during review.
