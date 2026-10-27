## What changed

Filled `AlgebraicGeometry.Scheme.ambTateRootProjectionReduction` by the four-step
DAG route. The public definitions, structure fields, and theorem signature are
unchanged. Private proved helpers identify the scalar maps, apply scalar-extension
associativity, normalize the finite root comparison, prove the power-transition
formula, and transport the specified pullback maps and their coherence.

The proof imports `RootTowerFiniteTensor`, `AmbRootTowerPullbackCoherence`, and
`ScalarExtensionDualTowerCore`. The coefficient algebra on the quotient is the
actual integral-coefficient map followed by the quotient map. `ULift` reconciles
the finite-tensor theorem's coefficient universe with the prescribed coefficient
sheaf. The normalized isomorphisms chosen from the existing theorem are unique:
pure scalar-extension tensors determine their forward maps, and an isomorphism's
forward map determines its inverse. No data is chosen from mere existence.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.ambTateRootProjectionReduction`
(node `lem-amb-tate-root-projection-reduction`). Zero holes added; zero split off.
No `sorry` remains in the delivered module. The actual module compiled cleanly
with `lcompile.py` in 36.9 seconds after the final scope adjustment, without warnings. The two existing root-tower theorems
are used as the declared proof dependencies, and are not changed by this packet.

## No longer needed

Removed direct proof imports:

- `Mathlib.CategoryTheory.Sites.EpiMono`
- `Mathlib.CategoryTheory.Sites.LocallySurjective`
- `Sheaf.CategoryTheory.TorsionSheafConstantModule`
- `Sheaf.Paper.PurTwistRootTransitions`
- `Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover`
- `Sheaf.Paper.RingedTopoiTensorSections`
- `Sheaf.AlgebraicGeometry.RootsOfUnityInverseImageIso`
- `Sheaf.CategoryTheory.SiteInverseImageTensor`
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`

Removed the following obsolete direct tool approvals from the parent node:

- `lem-pur-twist-root-transitions`
- `lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective`
- `lem-weil-pbc-site-sheaf-sets-epi-locally-surjective`
- `lem-weil-pbc-proetale-affine-wcontractible-covering-family`
- `lem-pur-torsion-sheaf-constant-module`
- `lem-pur-roots-of-unity-inverse-image-iso`
- `lem-weil-pbc-left-exact-site-inverse-image-tensor`
- `lem-weil-pbc-ringed-topoi-module-pullback-tensor`
- `lem-pe-constant-left-module-inverse-image`

The old direct tool uses for Kummer transitions, local-surjectivity criteria,
weakly contractible covers, torsion-module linearity, finite-root inverse image,
inverse-image tensors, module-pullback tensors, and constant coefficient pullback
are no longer steps proved in this parent. They belong to its already-stated
two root-tower dependencies. This does not withdraw any upstream declaration or
claim those dependencies can be deleted from the library. The general tensor
section-calculus node `def-weil-pbc-ringed-tensor-section-calculus` is replaced as a direct proof dependency by the proved
scalar-extension tower API, which supplies associativity, pure-tensor formulas,
naturality, and determination of maps. The root-limit, coefficient-twist, and
sheaf-tensor definition nodes remain statement dependencies; their separate direct
proof-dependency entries are unnecessary after using the normalized APIs. No module
is withdrawn, and no claim is made that the ten removed direct imports all leave
the targets' transitive import closure.

## Where the brief, the DAG or earlier work was wrong

The Lean docstring retained the original nine-step proof, while the current DAG
already assigns root lifting/kernel/tensor inversion and pullback coherence to
two separate declared dependencies. This proof follows that four-step DAG route.
The finite tensor theorem accepts coefficient types in the larger universe,
whereas the pullback theorem accepts the original coefficient universe and lifts
the constant rings internally. Applying the former to `ULift A` and transporting
along equality of the explicit scalar maps resolves this interface difference.

No statement repair, new node, source-library edit, or forced adaptation is needed.
Preflight requested a proof-scope change record; see
`coord/changes/B8-amb-tate-root-proof-scope.md`. The three added helper instances
are explicitly private and local, and all added irreducibility attributes are local.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
