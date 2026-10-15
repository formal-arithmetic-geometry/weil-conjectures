## What changed

Proved three of the four existing declarations in `Sheaf.Paper.CondensedFlatCoefficientCalculus`,
with their statements unchanged. Added private, fully proved helpers for continuous basis
coordinates, transport of finite free internal modules, and coherence of the specified
scalar-change comparisons. These helpers construct their data explicitly; no data is
chosen from an unproved existence assertion.

Finite freeness is constructed first on continuous-function presheaves, then transported
through sheafification and the existing inverse image from the point. Exactness, scalar
adjunctions, and the comparison between exact and left-derived functors use the existing
source APIs. The general transport and shift lemmas for canonical comparison coherence are proved;
the original concrete coherence theorem remains open.
Tensor preserves the colimit already supplied in the statement.

The general coherence helpers are retained as proved private lemmas for the remaining
original obligation. The full candidate specialization is saved in
`scratchpad/FullCoherenceCandidate.txt` for the second reader. Earlier versions of this
candidate passed standalone checking (51.5 seconds without warnings), but every tested
artifact-producing compile exceeded 60 seconds. It is therefore not counted as a closed
hole. The remaining work is to simplify the resolution and shift interface enough to
compile that specialization with artifacts. No file or proof was split to evade the limit.

Updated the existing node's proof, proof_deps and proof_origin to this route. No target,
existing theorem signature, or coefficient definition changed. Proof imports were added
for adjunction composition, exact derived shifts, derived comparison naturality, automatic
continuity, monoidal functor categories, and mapMod. Removed the imports listed below.
The public-import pruning is recorded in
`coord/changes/CondensedFlatCoefficientCalculus-proof-imports.md`; it requires no adaptation.
The delivered module compiled with artifacts in 54.9 seconds without warnings; the
unchanged direct importer `Sheaf.Paper.CondensedQbarExchangeEquality` then compiled
against those artifacts in 27.1 seconds, also without warnings.

## Proved and sorry left

Closed these three original holes:

- `AlgebraicGeometry.ProEtale.condensedFiniteCoefficientCalculus`.
- `AlgebraicGeometry.ProEtale.condensedAlgClCoefficientCalculus`.
- `AlgebraicGeometry.ProEtale.condensedCoefficientTensorColimit`.

Holes closed: 3. Holes added: 0. Split-offs: 0. The one original sorry left is
`AlgebraicGeometry.ProEtale.condensedCoefficientCoherence`, associated with
`lem-weil-pbc-condensed-flat-coefficient-calculus`. All private helpers are proved.

The first two proofs use existing source flatness instances
`AlgebraicGeometry.ProEtale.CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap`
and
`AlgebraicGeometry.ProEtale.CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl`
in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`.
Those source proofs still contain sorry and remain downstream obligations; this delivery
closes the three item holes from existing source declarations, as stage 3 requires.

## No longer needed

Removed these imports (including three unnecessary public imports):

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`.
- `Sheaf.CategoryTheory.RingedSiteModules`.
- `Sheaf.Algebra.Homology.FilteredColimitsTensor`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed`.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`.
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`.
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse`.
- `Sheaf.Paper.ProfinitePointPullback`.

The updated proof does not need these previous direct proof dependencies:

- `def-pur-sheaf-tensor-product`.
- `def-weil-pbc-condensed-e-module-category`.
- `def-weil-presheaf-modules-sheafification`.
- `lem-pc-module-filtered-colimits-tensor`.
- `lem-pc-sheaf-modules-tensor-closed`.
- `lem-weil-pbc-exact-functor-derived-factorization`.
- `lem-weil-pbc-exact-functor-derived-functor`.
- `lem-weil-pbc-finite-dimensional-linear-homeomorphism`.
- `lem-weil-pbc-left-adjoint-preserves-colimits`.
- `lem-weil-pbc-localization-universal-property`.
- `lem-weil-pbc-module-sheaves-colimits-forgetful`.
- `lem-weil-pbc-profinite-point-pullback`.
- `lem-weil-pbc-ringed-topoi-module-adjunction`.
- `lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact`.

These are pruned from this node's route; another target may still need them independently.
In particular the tensor-colimit conclusion does not require constructing the coefficient
colimit, proving filtered exactness, or an additional filtered-complex tensor theorem.
The separate profinite-point pullback proposition and ringed-site module API are not used:
the source internal module functors already provide the needed constructions.

## Where the brief, the DAG or earlier work was wrong

The old DAG planned much more than the actual four Lean statements require. The colimit
cocone is a hypothesis of the tensor clause, so its preservation follows for any diagram
from the existing closed module tensor structure. Flatness and the derived adjunction are
already named source declarations; their remaining source holes are not obstacles to
proving this item from them. Automatic continuity of the individual basis coordinates
suffices; a separate topological linear-equivalence theorem is unnecessary.

Importing `WeilConjectures.SixFunctors.ProEtale.Derived.RestrictScalars` directly conflicts
with the already imported finite-coefficient UpperLowerStar notation. A concurrently landed
change relocates its generic derived coherence declarations to MapDerivedCategoryMate,
but those declarations were not yet present in the local green compiled library when
checked. The compiled library subsequently refreshed. The final proof imports the relocated generic
API directly from MapDerivedCategoryMate, and the temporary duplicate private proofs were
removed. No adaptation of another group's module was needed.

## Second reading by A4

1. **Signatures and accidental changes.** Compared the delivered module with the repository
version. The four existing theorem statements are byte-for-byte unchanged; only proof bodies,
proof-only imports, private helpers, and the existing node's proof metadata changed. Verdict: pass.

2. **Proof checks.** Compiled the module with `lcompile.py` and compiled all sandbox modules;
both completed without errors or warnings. The only remaining `sorry` is the named theorem
`AlgebraicGeometry.ProEtale.condensedCoefficientCoherence`; no definitions contain `sorry`, and
no forbidden declarations occur. Verdict: pass.

3. **Statements and split-offs.** No new public theorem or split-off node was added. The three
closed declarations use existing source APIs and preserve their original statements. The
remaining coherence theorem retains its original statement and its documented source. Verdict:
pass.

4. **Route and pruning.** The proofs use the finite-free, exact scalar-change, derived
adjunction, triangulation, shift, and tensor-colimit APIs needed by the item. Removed imports
and obsolete proof dependencies are listed in `## No longer needed` and the import change
record. The unit route remains represented by the existing item node. Verdict: pass.

5. **DAG agreement.** Checked the item's node against the Lean proof: its proof steps,
`proof_deps`, and `proof_origin` describe the finite-free construction, scalar-change APIs,
derived comparison, shift compatibility, and tensor-colimit preservation actually used. No new
node is required. Verdict: pass.

Changed during second reading: added this review section only; no Lean declarations or DAG
statements were changed.
