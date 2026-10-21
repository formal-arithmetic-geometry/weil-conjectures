## What changed

Filled both remaining proofs in `Sheaf.Paper.ConstantRealizationDerivedScalarExtension`.
All existing public signatures, public imports, definitions and instances are preserved.
The ordinary sheafification/tensor comparison and the chosen independently sized derived
adjunctions remain the same constructions.

The comparison is proved invertible using flat-term K-flat representatives. Its representative
square is proved by transposing under the scalar adjunction, using the ordinary unit identity
and exact-derived-functor factorization. Its unit compatibility follows directly from its mate
definition. Tower compatibility is proved formally from coherent restriction comparisons and
the unit normalization of `leftAdjointUniq`, without an additional tensor model.

Added four fully proved supporting modules: `FlatTermKFlatFunctor`, `ConstantModuleFlat`,
`ConstantModuleKFlat`, and `ExactRightDerivedAdjointKFlatRepresentative`. The first proves
preservation using flat resolutions, flat cycles of acyclic K-flat complexes, good truncations,
integer-indexed colimits and cones. The next two apply the local relation criterion and
colimit preservation to the actual constant module functor on an arbitrary site. The last
identifies the canonical cochain-unit transpose with an invertible derived counit, retaining
independent category and localization universes. Private proof imports expose existing
same-universe flat-resolution and change-of-rings invariance helpers; no interface is changed.

Updated the item's proof route and added four DAG nodes matching those supporting results.
No source-library file is modified and no existing module is withdrawn.

Validation: the four supporting modules compile. The complete main proof elaborates within
44 seconds. Explicit `#print axioms` checks of both original theorems report exactly
`propext`, `Classical.choice`, and `Quot.sound`; the supporting flatness, constant K-flatness
and adjoint-transpose theorems have the same axiom set. Diagnostic commands were removed
before delivery. The first delivery attempt hit the 60-second compile limit and pushed
nothing. Chosen adjoints are now kept locally irreducible in the universal-property proofs,
and the representative theorem applications supply their functors explicitly. A second delivery attempt also timed out. Keeping `Functor.leftAdjoint` itself locally
irreducible avoids repeatedly reducing the chosen-adjoint construction. With this final
optimization, a full `--all` compile, including the main module artifact, succeeds in
39.0 seconds for the main module without warnings. The delivery tool performs the final compile and preflight checks.

## Proved and sorry left

Closed the two original holes:

- `CategoryTheory.ConstantScalarRealization.constantRealizationDerivedScalarExtension`.
- `CategoryTheory.ConstantScalarRealization.constantRealizationDerivedScalarExtension_transitivity`.

The new public results are also completely proved:

- `CategoryTheory.Functor.kFlat_map_of_flat_terms`.
- `CategoryTheory.isFlatOnSite_constantModule`.
- `CategoryTheory.isKFlat_constantModule`.
- `CategoryTheory.Adjunction.isIso_cochainTranspose_of_kFlat`.

Holes closed: 2 of 2. Holes added: 0. Holes left in the delivery: 0. No unproved theorem
is split off. Imported project declarations retain their existing proof status.

## No longer needed

Removed these private imports from the item:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`.
- `Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral` (already supplied by the public base).
- `Sheaf.Paper.KFlatRingedToposPullback`.

The ordinary import of `KFlatResolutionIndependentCoefficients` is replaced by `import all`
for its existing private functorial-flat-resolution and exact-colimit interfaces.
`DerivedModuleScalarAdjunction` likewise becomes `import all` for its existing ordinary-module
flat-resolution construction. These are private proof imports, not new public dependencies.

Removed the following planned proof dependencies from this node:

- `lem-weil-pbc-ringed-pullback-preserves-kflat`: direct flatness and colimit arguments replace
  construction of a geometric morphism to the point site and its ringed pullback.
- `lem-weil-pbc-site-derived-tensor-descent`: the existing exact-square factorization and a
  flat-term K-flat representative prove invertibility of the already defined natural mate.
- `lem-pur-kflat-change-of-rings`: tower coherence follows from adjunction unit identities.
- `lem-sfb-successive-derived-quotient-normalization`: the actual transitivity maps are already
  normalized by `leftAdjointUniq`, whose unit identity proves their compatibility directly.

Removed obsolete `tool_uses` approvals for `lem-weil-pbc-ringed-pullback-preserves-kflat`,
`lem-weil-pbc-site-derived-tensor-descent`, and `lem-pur-kflat-change-of-rings`, preserving
all other entries and their order. None of these nodes or modules is globally withdrawn;
other consumers may still need them. Statement dependencies are unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement was found false. The original geometric-morphism route and successive tensor
normalization are unnecessary for this proof. The existing specialized cochain-counit result
uses common successor universes and injective-resolution assumptions; it does not directly
serve the independently sized localizations in this item's unchanged statements. The new
exact-right-adjoint version removes those unnecessary hypotheses using Mathlib's derived
adjunction and absolute K-flat derivability.

Edge cases are covered by the proofs themselves: the finite relation argument allows zero
relations, the topology may have empty covers, the site need not have a terminal object or
enough points, the complexes are unbounded, and the ring maps may be nonflat or have zero
codomain. No finiteness hypothesis or equality between localization universes is introduced.
The unit record `sk-lem-integral-models` has no realized steps imposing the pruned route.

## New nodes

`lem-sfb-flat-term-kflat-functor` records the proved generic flat-term K-flat preservation
result, with the resolution/cone/truncation proof and the actual Mathlib searches.

`lem-sfb-constant-module-flat` records the proved local finite-relation argument for flat
constant module sheaves, without a terminal object or enough points.

`lem-sfb-constant-module-kflat` records colimit preservation and the application of the generic
preservation theorem to constant realization, including the independent coefficient API.

`lem-sfb-exact-right-adjoint-kflat-representative` records the proved normalized representative
transpose theorem with independent localization universes and its derived-adjunction proof.

All four are in `dag/nodes/sec-six-functors-basics/`, attached below the existing constant
realization node and to its existing unit. The static preflight requires a record for added `open` and local `attribute` commands:
`coord/changes/constant-realization-proof-elaboration.md` documents their proof-only scope,
the unchanged interface, and the direct consumers. The private naturality helper also receives definitionally identical explicit universe
annotations, documented in the same record; its implicit version caused another compile
timeout. No existing public interface or data construction changes. LeanSearch searches were added separately from LeanFinder/Loogle to satisfy the
three-kind search policy, after the first server preflight identified this metadata omission.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
