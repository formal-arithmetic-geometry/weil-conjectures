## What changed

Replaced the sole sorry in
AlgebraicGeometry.Scheme.relativeTensor_stalk_localModel_homology_iso with a complete
composition of a global K-flat stalk computation and an exact local-model comparison.
The original declaration, universes, hypotheses and conclusion are unchanged. Added two
proof-only imports and updated its node's proof, proof_deps and proof_origin.

Added RelativeTensorGlobalLocalStalkDerivedIso and proved
AlgebraicGeometry.Scheme.relativeTensor_global_local_stalk_derived_iso. This is the full
local-model part of the original argument, not an assumed comparison: the Lean proof
uses the existing open restriction stalk extension theorem, the invertible
extension/restriction adjunction unit along the open immersion stalk map, and
Scheme.Modules.overFunctorEquiv to construct a complex comparison. It then applies
exact derived functors and their mapDerivedCategoryFactors isomorphisms to eL.

Added RelativeTensorStalkGlobalHomology with the remaining global computation. Unlike
the original statement this has no V, L, eL, hy or derived category of sheaves: it
computes the tensor using the scalar-restricted global stalk of K. The original proof
tensors the independently proved local comparison with M[0], takes derived homology,
forgets scalars, and composes the resulting isomorphism in every degree.

All three modules compile individually through lcompile.py; the sandbox compiles in
import order with --all. No source repository files were edited, and no push was made.

## Proved and sorry left

Closed the original hole:
AlgebraicGeometry.Scheme.relativeTensor_stalk_localModel_homology_iso
(lem-pc-relative-tensor-stalk-local-model-homology).

Also proved the new theorem
AlgebraicGeometry.Scheme.relativeTensor_global_local_stalk_derived_iso
(lem-pc-relative-tensor-global-local-stalk-derived-iso), with no sorry in its proof.

Added one remaining hole:
AlgebraicGeometry.Scheme.relativeTensor_stalk_global_homology_iso
(lem-pc-relative-tensor-stalk-global-homology), in its own new module. This is a
decomposition, not a complete proof of the original theorem: one upper hole closed
and one strictly smaller lower hole added. The global computation requires the
inverse-image stalk scalar compatibility and the K-flat derived tensor comparison;
it cannot be supplied by the purely local comparison proved here.

Edge cases checked mathematically: when F is zero the transported module is zero;
when K is acyclic the K-flat representative is acyclic and tensor homology is zero.
No restriction on degrees enters either comparison. An empty X has no point y;
when V is empty the hypothesis hy is impossible. The local comparison uses only
the actual stalk map of V.ι, so zero stalk rings require no extra hypothesis.
No definition or other data was introduced using a sorry theorem; existential
isomorphisms and the module witness are eliminated only within theorem proofs.

## No longer needed

No existing imports were removed and no previously reachable module is claimed
pruned. The original seven proof dependencies are redistributed, not eliminated:
OpenModuleStalkFunctor is used in the proved local comparison; KFlatResolution,
KFlatStalkCriterion, KFlatTensorQuasiIso, InverseImageStalkScalarTransport,
StalkTensorComplex and ModuleStalkExact remain in the global computation's plan.
The parent node now depends directly on the two new comparison nodes.

The new local comparison does not import KFlat, TensorPullback, HasMonoidalDerivedCategory,
FlatResolution, Single or Sheaves.Abelian. Its scalar exactness and scheme-module
instances are supplied by ChangeOfRingsExact and GrothendieckAbelian.Sheaf. The global
comparison uses ModuleStalkFunctor in place of OpenModuleStalkFunctor. These are
minimized new-module imports, not pruning of existing reachable modules.

## Where the brief, the DAG or earlier work was wrong

No statement error or departure from the unit route was found. The unit's realized
statement and step lists do not attach this node; the argument remains below its
existing finite Tor verification route.

The original proof dependencies supply the ingredients but not a ready-made relative
stalk derived tensor comparison. InverseImageStalkScalarTransport is stated for
inverse-image modules from Y, whereas K is an arbitrary O_X-complex restricted to the
inverse-image ring sheaf. The remaining global node records the additional germ
compatibility and derived tensor bridge explicitly. The open restriction comparison
needed by the local part was already available as
lem-pc-open-restriction-stalk-extension-iso and was used rather than restated.

## New nodes

lem-pc-relative-tensor-global-local-stalk-derived-iso:
lean/Sheaf/AlgebraicGeometry/RelativeTensorGlobalLocalStalkDerivedIso.lean.
An independently proved derived comparison of the scalar-restricted global stalk
with the chosen open local model, without K-flat or tensor hypotheses.

lem-pc-relative-tensor-stalk-global-homology:
lean/Sheaf/AlgebraicGeometry/RelativeTensorStalkGlobalHomology.lean.
The remaining named global K-flat computation, independent of any local model,
with its source and a complete proof in words in the declaration docstring.

No change record is needed: no existing statement, definition, visibility, public
import or instance was changed, and there are no forced consumer adaptations.

## Second reading by K1

1. Compared the delivered local-model module with the repository version. The
   target declaration has the same signature byte for byte; only proof imports and
   proof text changed. The two added modules are new declarations with matching DAG
   nodes.

2. Compiled all three delivered modules individually with `lcompile.py`; all pass.
   The only remaining `sorry` is the named decomposition theorem
   `relativeTensor_stalk_global_homology_iso`; no definitions contain `sorry`, and
   no forbidden declarations were introduced. The proved local comparison uses only
   the permitted classical axioms.

3. Checked the two split statements against their signatures and docstrings. They
   are true reductions: the local comparison is independent of tensor hypotheses,
   and the global homology theorem is strictly simpler than the original target.
   Their DAG nodes include sources, proof steps, dependencies and searches.

4. The proof follows the unit route: the original target factors through the global
   stalk computation and the exact local-model comparison. No shorter existing
   library theorem was found, and no imports were removed because each is used by
   the corresponding proof or public signature.

5. DAG `proof`, `proof_deps`, and `proof_origin` agree with the Lean proof and the
   report lists the one remaining lower hole. No statement or definition was changed.

Second reading changed only this report; the first worker’s Lean proofs and DAG
nodes required no repairs. Independent axiom probes report only propext,
Classical.choice and Quot.sound for the local comparison, and additionally sorryAx
for the original target and the named global computation, as expected. Searches
for exact open restriction derived comparisons, mapDerivedCategoryFactors and
scalar restriction stalks found component results, including Mathlib
Scheme.Modules.restrictStalkNatIso used by the existing dependency, but no
replacement for the global computation.
