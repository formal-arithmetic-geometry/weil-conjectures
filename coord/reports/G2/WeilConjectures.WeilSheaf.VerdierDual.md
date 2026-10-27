## What changed

The source module retains every existing declaration signature, attribute, public import,
and definition body. The existing lisse sheaf biduality declaration is placed before the
WeilComplex namespace so that the tensor-Hom proof can use it. The new `open ... in`
commands apply only to private proof helpers; the reopened namespace and its variables
retain the original theorem's parameters. These command changes do not add public
notation, instances, attributes, or a mathematical interface change.

`AlgebraicGeometry.WeilComplex.nonempty_tensorLisse_dual_iso_derivedHom` now applies sheaf
biduality, maps its isomorphism through the contravariant native internal-Hom bifunctor,
passes that natural isomorphism to right derived functors, and composes with the inverse
of the existing single-resolution comparison. The lower bound required by that comparison
is supplied by the boundedness of the given Weil complex.

`AlgebraicGeometry.WeilSheaf.nonempty_iso_dual_dual` is reduced to invertibility of the
underlying native adic bidual map. Its Frobenius-equivariance calculation is proved in the
private lemmas `bidual_evaluation_equivariance` and `bidual_frobenius`, using evaluation
compatibility for the sheaf and its dual,
lax monoidal naturality, symmetry, and injectivity of uncurrying. The resulting equivariant
morphism is invertible because inclusion and forgetting Frobenius reflect isomorphisms.

The only additional proof imports are `Sheaf.WeilSheaf.DerivedHomSingleResolution` and
`Sheaf.SixFunctors.AdicLisseBidualInvertible`. The latter is a new module containing the
underlying adic invertibility statement, without a Weil structure or a base field.

Validation: the final `lcompile.py --all` request compiled both delivered modules with
exit code 0 and no warnings. The compiler tool accepted both files under its separate
60-second Lean-runtime check; the displayed per-file duration also includes cache and
artifact setup. All temporary profiler options were removed. Existing signatures,
public imports, and non-theorem bodies were compared against the current source.

## Proved and sorry left

The original module contained seven holes. Two original holes are closed:

- `AlgebraicGeometry.WeilComplex.nonempty_tensorLisse_dual_iso_derivedHom`
  (`lem-sf-weil-lisse-internal-hom-tensor-dual`), proved from sheaf biduality and the
  existing single-resolution comparison.
- `AlgebraicGeometry.WeilSheaf.nonempty_iso_dual_dual`
  (`lem-sf-weil-lisse-biduality`), decomposed into underlying adic invertibility and a
  complete Frobenius-equivariance/reflection argument. This is a decomposition, not a
  complete proof of the underlying finite-free invertibility argument.

Five original holes remain unchanged:

- `AlgebraicGeometry.WeilComplex.isLeftAdjoint_derivedLowerShriek`
  (`thm-sf-weil-compact-direct-image-right-adjoint`).
- `AlgebraicGeometry.WeilComplex.nonempty_iso_verdierDual_rightOp_comp_verdierDual`
  (`lem-sf-weil-verdier-biduality`).
- `AlgebraicGeometry.WeilComplex.nonempty_upperShriek_obj_iso`
  (`lem-sf-weil-upper-shriek-verdier-conjugate`).
- `AlgebraicGeometry.WeilComplex.nonempty_verdierDual_derivedLowerShriek_iso`
  (`lem-sf-weil-verdier-exchange`).
- `AlgebraicGeometry.WeilComplex.nonempty_dualizingComplex_iso`
  (`lem-pur-weil-smooth-dualizing-complex`).

One hole is added:

- `AlgebraicGeometry.ProEtale.isIso_adicNativeBidual_of_isLisse`
  (`lem-sf-adic-lisse-bidual-invertible`). Its module contains exactly this one named
  theorem with `:= by sorry`, a source, and a complete natural-language proof.

The packet therefore closes two original holes and adds one underlying adic obligation:
five holes in the item and one in the new module. No definition contains a hole.

## No longer needed

No existing import or module is removed. The direct sectionwise reindexing argument
`lem-sf-reindexed-sheaf-bidual-equivariance` / `Sheaf.CategoryTheory.ReindexedSheafBidualEquivariance`
is no longer needed for the lisse Weil biduality proof: the native evaluation compatibility
already proves Frobenius equivariance. It is not imported.

`lem-sf-adic-module-slice-hom-comparison` and
`lem-sf-locally-free-sheaf-evaluation-biduality` are still needed for the new underlying
adic invertibility obligation. They move below that node; they are not globally pruned.
The tensor-Hom node now records its actual use of `lem-sf-weil-lisse-biduality` instead of
repeating the finite-free biduality calculation in its own proof plan. The existing
single-resolution node remains needed. All untouched declarations retain their existing
proof dependencies, and no unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The current blueprint path has `sec-six-functors-basics`, whereas the historical source
fields of the native nodes use `sec-six-functors`. The new source citations use the current
`literature/blueprint/latest` path. `blueprint_refs.py ancestor lem-sf-weil-lisse-biduality`
returns None; the new node records this explicitly and names the exact finite-projective
proof paragraph it serves.

The tensor-Hom plan did not list the existing lisse biduality theorem as a dependency even
though its first two steps reconstruct that theorem. The updated dependency is explicit.
There is no mathematical statement repair or forced downstream adaptation.

## New nodes

`lem-sf-adic-lisse-bidual-invertible` isolates the underlying native adic invertibility part
of lisse Weil biduality (the original node's first two steps). It applies on any scheme,
requires no Frobenius structure, and concerns the actual transpose of the identity,
not an arbitrarily chosen isomorphism. Its proof uses the existing native/slice comparison
and sectionwise locally free evaluation theorem, including the empty and zero-rank cases.
LeanSearch, LeanFinder, Mathlib/source grep, and the blueprint duplicate search were run.
Ordinary-module reflexivity and sectionwise sheaf biduality already exist; the native
comparison and locality bridge are the remaining work. There are no change records,
since no existing mathematical interface or definition was changed.

The broader blueprint search also found
`lem-proetale-finite-projective-dualizable`. Its declaration concerns `supportModules`
for a condensed ring in sheaves of abelian groups. The present native `AdicSheaf` is a
module object in sheaves of `WeilCoefficients` (lifted vector spaces); its internal Hom
and canonical transpose require a comparison before that theorem can apply. It is
therefore not a direct replacement for the native invertibility bridge.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
