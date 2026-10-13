## What changed

The signature and visibility of the assigned theorem are unchanged. Its proof now combines two strictly intermediate statements with two fully proved private helpers. The helper `directImage_isGE` proves preservation of the specified lower cohomological bound using bounded-below right-derived compatibility. The helper `tensor_vanishes_of_isZero` constructs a K-flat witness and transports homology along the tensor comparison.

New modules: `Sheaf.AlgebraicGeometry.RelativeTorPullbackTensorLowerBound` and `Sheaf.AlgebraicGeometry.ProperSupportDerivedProjectionFormula`. These isolate respectively the relative-Tor bound on X (without any support or coherence hypotheses) and the proper-support projection isomorphism (without any Tor hypothesis). Both parts follow the two displayed equalities in Stacks Tag 08EV, checked at https://stacks.math.columbia.edu/tag/08EV and https://stacks.math.columbia.edu/tag/08EU because the literature files are not present on this machine.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.exists_schemeDerivedDirectImage_tensor_lower_bound` (node `lem-pc-proper-direct-image-tensor-lower-bound`), by decomposition into two strictly intermediate statements; not claimed as a sorry-free proof of the entire argument.

Added holes:
- `AlgebraicGeometry.Scheme.exists_relativeTor_pullback_tensor_lower_bound`, node `lem-pc-relative-tor-pullback-tensor-lower-bound`.
- `AlgebraicGeometry.Scheme.nonempty_properSupport_derivedProjection_iso`, node `lem-pc-proper-support-derived-projection-formula`.

There are no remaining sorries in the assigned module and none in the private helpers. One original hole closed, two holes added: net minus one. The new statements pass the zero-object/zero-module cases; the relative bound does not require flatness of f and uses all modules over the inverse-image ring, as the definition requires. The projection claim keeps proper-support and quasi-coherence assumptions and does not assert projection for arbitrary non-quasi-coherent F or unrestricted non-qc f.

## No longer needed

Removed direct proof imports:
- `Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat` (node `lem-pc-bounded-above-flat-kflat`).
- `Sheaf.Algebra.Homology.BoundedFlatReplacement` (node `lem-pc-kflat-bounded-flat-replacement`).
- `Sheaf.Algebra.Homology.KFlatPullback` (node `lem-pc-kflat-pullback-preservation`).
- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian` (node `pqf-lem-coherent-ft-locnoeth`).
- `Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh` (node `lem-pc-derived-pullback-tensor-qcoh`).
- `Sheaf.AlgebraicGeometry.DirectImageQCSupportReduction` (node `lem-pc-direct-image-qc-support-reduction`).
- `Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback` (node `lem-pc-flat-complex-derived-pullback`).

The old proof dependency `lem-pc-projection-formula` is also no longer used directly by
the assigned theorem; it remains in the projection helper's mathematical plan. Its recorded
module `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections` was not a direct
import of the original assigned module, so this is a DAG dependency change, not an import
removal. The two old definition dependencies `def-pc-derived-direct-image` and
`def-pc-derived-tensor-cohomology-vanishes` remain used by the theorem and its proved bridge;
their public imports remain. They are interface dependencies, not pruned mathematical inputs.

Second reading removed the redundant proof-only import
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`, already
publicly available through `RightDerivedFunctor.PlusCompatibility` and its `PlusSingle`
import. The EnoughInjectives import was tested and retained: removing it prevents synthesis
of `EnoughInjectives` in `directImage_isGE`.

These dependencies are moved to the new nodes' planned proofs, not declared mathematically unnecessary. No module is claimed globally pruned; all original public imports remain and no unit route is bypassed (the unit record has no realized node bindings here).

## Where the brief, the DAG or earlier work was wrong

The projection formula node records the general derived statement, but its Lean declaration `nonempty_higherDirectImage_tensorObj_pullback_iso` only concerns ordinary higher direct images and invertible modules. It cannot provide the derived projection formula for an arbitrary quasi-coherent module. The new proper-support projection statement supplies the missing part while preserving the existing unit route.

The support-reduction theorem requires derived categories of every scheme at the same universe; the assigned theorem only assumes derived categories of X and S. The new projection statement explicitly isolates transport from auxiliary localizations on the restricted open to the fixed localizations on X and S.

The finite-Tor definition bounds restricted scalars but the plan contains no theorem relating that bound to E tensor Lf*F. The other new statement isolates precisely this change-of-rings comparison. No signature, definition, or public import was changed; no forced adaptations.

## New nodes

`lem-pc-relative-tor-pullback-tensor-lower-bound` states only the uniform bound on X and uses no geometric hypotheses. Its module and node include the K-flat inverse-image/change-of-rings argument of Tag 08EV and Cohomology Lemma 20.27.4.

`lem-pc-proper-support-derived-projection-formula` states the support-reduced projection isomorphism for arbitrary quasi-coherent module coefficients; no Tor bound is assumed. Its proof combines support reduction, the derived projection formula on the qcqs restricted open, and the supported-open comparison for the tensor input. No change records are necessary.


## Second reading by J2

1. **Interface comparison — pass.** Read the repository and all three sandbox modules,
   and compared the assigned file with `diff -u`. The existing theorem's complete signature,
   docstring, namespace, and public imports are byte-for-byte unchanged. The only changes
   there are proof-only imports and proved private helpers followed by the new proof.
   There are no changed definitions, forced adaptations, or undeclared interface changes.
   The existing node differs only in `proof`, `proof_deps`, and `proof_origin`.

2. **Kernel and holes — pass as a decomposition.** Compiled all three modules in import
   order with `lcompile.py --all`. An appended scratch-copy axiom probe showed precisely
   `propext`, `Classical.choice`, and `Quot.sound` for both private helpers; the main theorem
   and the two new statements additionally use `sorryAx`, as expected for the two explicit
   imported holes. There is no `sorry` in the assigned module or in data, and no forbidden
   axiom, unsafe declaration, opaque declaration, external implementation, or kernel bypass.
   The K-flat witness in the bridge is chosen inside a proof, from the proved resolution
   theorem, and does not introduce a definition with arbitrary data.
   Exactly one original hole is closed syntactically and two holes are added: this is a
   decomposition with net minus one, not a complete proof of the original mathematics.

3. **Split statements — pass.** Read Stacks [08EV](https://stacks.math.columbia.edu/tag/08EV),
   [08EU](https://stacks.math.columbia.edu/tag/08EU), and
   [08DE, Lemma 20.27.4](https://stacks.math.columbia.edu/tag/08DE), and the definitions of
   finite relative Tor dimension, derived pullback, and the recorded derived tensor.
   The relative-Tor statement is the second equality of 08EV followed by its uniform Tor
   interval: it needs no quasi-coherence assumption on F or flatness assumption on f.
   Its docstring resolves F in nonpositive degrees, computes change of rings, and uses
   the chosen restricted-scalars K-flat resolution. The projection statement uses only
   bounded coherent proper support and quasi-coherent F, with no Tor hypothesis. Its
   docstring gives the finite closed union T, a quasi-compact open U, the qcqs projection
   formula there, and the supported-open comparison also for the tensor input. Although
   that input can be unbounded below, its restriction off T is zero; clause (2) of
   `supported_open_pushforward` does not require perfectness or boundedness. Thus neither
   new statement merely renames the assigned conclusion: one bounds an object on X,
   the other supplies a geometric isomorphism without a Tor assumption.
   Checked E=0, F=0, empty X, and f=id: zero tensor gives zero cohomology, the empty support
   allows U empty, and the identity case is the usual Tor bound and identity projection.
   Both statements have named holes, source/docstring arguments, and matching new nodes.
   Independently searched with msearch LeanFinder (derived tensor associativity/restriction
   of scalars), Loogle (`"projection"`), and grep (restrictScalars/tensor/projectionFormula),
   then searched lean/Sheaf and upstream WeilConjectures using Tor, lower-bound, and
   projection terminology. The hits give module-level tensor comparisons, categorical
   bounds, or projection results requiring stronger properness/adjunction data, not either
   new statement. In particular `exists_tensorRestrictExtend_module_natural` is only the
   underived module comparison, and `exists_rightAdjointTensorComparison_projection` needs
   a proper morphism and additional adjunction/monoidal data. The recorded original
   `nonempty_higherDirectImage_tensorObj_pullback_iso` only handles invertible coefficients.
   No split statement can be closed by a direct application of these hits.

4. **Route and pruning — pass after reporting repair.** Read the original dependencies
   and `dag/units/sk-thm-picard-duality.json`; its realized statement and step bindings are
   empty, so the two displayed-equality reductions preserve the unit route. The main
   proof first takes the uniform bound on X, then applies the projection isomorphism and
   the fully proved right-derived lower-bound helper, then converts vanishing to the
   original K-flat predicate. This last conversion uses the existing K-flat comparison,
   rather than adding a new hole. All new proof imports are plain imports. Removed one
   redundant proof import and retained EnoughInjectives after a failed removal test.
   Completed `No longer needed` with the omitted old projection dependency and clarified
   that the two definition dependencies remain used. No global pruning is claimed.

5. **DAG agreement — pass.** The assigned node's first step cites the relative bound;
   its second cites the projection isomorphism, K-flat resolution and K-flat comparison,
   exactly as the Lean proof does. Its proof_deps is their union. Each new node has its
   own statement, source, proof steps and dependency union, proof_origin, actual search
   records (including unavailable LeanSearch), status, creation/item/group/date, blueprint
   ancestry, chapter/unit and verbatim Lean signature. Read the cited support-reduction,
   supported-open and projection interfaces; the report explicitly records the projection
   interface mismatch and the localization-universe transport that their completion needs.
   No node statement was weakened to facilitate the Lean reduction.

Changes by this reader: removed the redundant RightDerivedFunctorPlus proof import;
completed the old-dependency accounting in `No longer needed`; added this independent
review. The mathematical proof and the two new statements were retained.
