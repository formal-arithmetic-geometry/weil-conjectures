## Worker report

The module `Sheaf.RingTheory.UniversalInjectiveFiniteTest` states
`LinearMap.universally_injective_tensor_iff`, with the sole proof `by sorry`.
It packages the node's general equivalence and its conditional Noetherian variant as
one conjunction. No definition, new node, dependency repair, or statement correction is needed.
Only `lean` changes in the item node copy. The recorded signature is verbatim from the file.

### Every hypothesis and clause

| Node text | Lean rendering |
| --- | --- |
| A commutative ring R | `{R : Type u} [CommRing R]` |
| R-modules M and N | `{M : Type v} {N : Type w}`, `[AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]` |
| An R-linear map u from M to N | `(f : M →ₗ[R] N)`; renaming the map changes no content |
| Every R-module Q | `∀ (Q : Type (max u v w t)) [AddCommGroup Q] [Module R Q], ...` |
| The canonical Q tensor M to Q tensor N map | `f.lTensor Q`, whose Mathlib definition is `TensorProduct.map LinearMap.id f` and sends `q ⊗ m` to `q ⊗ f m` |
| Universally injective, in the node's explicit meaning | `Function.Injective (f.lTensor Q)` for all the preceding Q |
| If and only if every finitely presented Q gives an injective tensor map | The first conjunct is `↔` with the same quantified Q and map, adding only `[Module.FinitePresentation R Q]` on its right side |
| If R is Noetherian | The second conjunct starts `IsNoetherianRing R → ...`; the first conjunct has no Noetherian hypothesis |
| Equivalent to requiring the test only for finite R-modules | The second conjunct is the same universal-injectivity predicate `↔` the predicate with `[Module.Finite R Q]` |
| Tensor products as in the cited definition | Mathlib's actual `TensorProduct` and `LinearMap.lTensor`; no private tensor construction or arbitrary comparison map |

Every universe is explicitly declared: `universe u v w t`. The independent universes of R,
M and N are retained. All test types live in `Type (max u v w t)`, so the test universe
contains the ring and both modules and cannot make the quantifier vacuous. The parameter t
allows arbitrarily large test modules. Types in lower universes have canonical lifted
representatives; tensor-map injectivity and finite generation/presentation are invariant
under these module isomorphisms. There is no nontriviality, flatness, finite generation,
injectivity, or finite presentation hypothesis on M, N, or f.

### Dependency declarations read and used

- `def-weil-pbc-module-tensor-product`: `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, `TensorProduct.mk`, and the bilinear universal
  property `TensorProduct.lift`/`TensorProduct.ext'` in
  `Mathlib.LinearAlgebra.TensorProduct.Basic`; the induced map is
  `LinearMap.lTensor` in `Mathlib.LinearAlgebra.TensorProduct.Map`.
  Its full definition and pure-tensor formula were read. This is the left-tensor
  orientation explicitly required by the item; the dependency's `rTensor` orientation
  is the same tensor construction with factors swapped.
- `def-weil-finitely-generated-module`: `Module.Finite` in
  `Mathlib.RingTheory.Finiteness.Defs`, defined by finite generation of the top submodule.
  Thus "finite module" is finite generation, without an assumption that the set is finite.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` and `isNoetherianRing_iff_ideal_fg` in
  `Mathlib.RingTheory.Noetherian.Defs`. Its docstring and definition identify precisely
  the condition that every ideal be finitely generated.
- `def-sc-finitely-presented-module`: `Module.FinitePresentation` in
  `Mathlib.Algebra.Module.FinitePresentation`. Its finite generators and finitely generated
  kernel, and `Module.FinitePresentation.exists_fin'`, give the node's finite free exact
  presentation. Its implication to `Module.Finite` is already an instance.

The statement dependencies use their recorded Mathlib declarations; no copies are made.
All four owning modules are public imports. For the stated proof dependencies, the imports
also expose tensor-colimit preservation (`CategoryTheory.Limits.isColimitOfPreserves` and
`CategoryTheory.ihom`'s left-adjoint tensor-right instance, with the `ModuleCat` closed
structure), and representatives/eventual equality
(`CategoryTheory.Limits.Concrete.isColimit_exists_rep`,
`CategoryTheory.Limits.Concrete.isColimit_rep_eq_iff_exists`, and
`ModuleCat.FilteredColimits.forget_preservesFilteredColimits`). Their full source signatures
were read. `Module.finitePresentation_of_finite` is in the already public finite-presentation
module. These proof-only imports are ordinary imports. The proof dependency
`lem-trf-module-directed-colimit-fp` has no `lean` or `mathlib_match` in the current DAG,
so there is no module for it to import yet; it is explicitly named in proof step 2 of
the docstring. It is not needed to type the statement and is not re-stated in this delivery.

The docstring contains all five DAG proof steps: restrict the tests; present an arbitrary
module as a directed colimit of finitely presented modules; tensor the canonical cocone;
chase a kernel representative to a later injective stage using eventual vanishing; and
identify finite and finitely presented modules only over a Noetherian ring. Stacks Algebra,
`theorem-universally-exact-criteria` (Tag 058K), including its preceding definition and
conditions (1) and (2), was read in the local source. Passing to a cokernel and using tensor
right exactness gives the map formulation; the DAG's direct colimit argument avoids needing
a short exact sequence in the statement. There is no source-wide omitted hypothesis.

### Edge cases checked before writing

- R the zero ring is allowed; its unital modules are zero, and both equivalences hold.
- Zero test modules, zero source, and identity maps satisfy both sides. No nonempty
  generating family, positive rank, or nontriviality assumption appears.
- Q equal to R detects any noninjective f, so injectivity need not be assumed separately.
- Multiplication by 2 on the integers is injective but fails the finitely presented
  test with Q = Z/2Z. The statement therefore does not confuse ordinary injectivity
  with universal injectivity.
- Finite generation is identified with finite presentation only inside the Noetherian
  implication. Over an arbitrary ring the first clause retains the stronger test predicate.
- Arbitrary additive groups with arbitrary compatible R-actions are quantified; no flatness
  condition on Q is added. The same test universe occurs on both sides of each equivalence.

### Searches made

All service searches used `msearch.py Q124 lem-trf-universal-injective-finite-test`.

- LeanFinder: "A linear map of modules is universally injective if and only if tensoring it
  with every finitely presented module is injective". Eight hits, all flatness characterizations
  or related flatness criteria, rather than the fixed-map assertion here.
- Loogle: `TensorProduct, Function.Injective, Module.FinitePresentation`. Three hits about
  freeness and lifting bases over local rings, none the required universal-injectivity test.
- Mathlib grep: `universallyInjective|universally_injective|PureMono|pure.*inject|finitePresentation.*[iI]nject`
  in `RingTheory`. One hit in `Mathlib/RingTheory/Ideal/Pure.lean`, about flatness of an ideal
  quotient, rather than this criterion.
- LeanSearch: "Universal injectivity of a fixed linear map can be tested by tensoring with
  finitely presented modules". Eight hits: flatness, faithful flatness, invertible tensor
  factors, and finitely generated submodule tests. None quantifies over finitely presented
  tensor factors for a fixed arbitrary map.
- `rg` in `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for the same
  universal-injectivity and finite-presentation terms found scheme-theoretic universal
  injectivity and different stalk/localization/residue criteria. The existing
  `UniversalInjectiveCheckStalks.lean` statement was read; it is a different local criterion.
- `rg` for the exact item id in `WeilConjectures` found nothing. The broader search for
  `universally_injective_tensor_iff|universal.*inject.*finite|finite.*test.*inject` in Mathlib,
  `WeilConjectures`, `lean/Sheaf`, and the upstream-name index found no existing declaration
  of this result and no collision with the selected declaration name.

The Q128 delivery in `coord/reports/Q128/lem-trf-universal-injective-finite-test.md` was read.
It is explicitly a stage-1 split, says that it ran no Lean compiler, and leaves the live node
without a `lean` record. Its merge does not supply the stage-2 statement requested here.

### Validation

The required `scompile.py` wrapper compiled both its sandbox view and
`Sheaf/RingTheory/UniversalInjectiveFiniteTest.lean` cleanly (7.0 seconds and 19.3 seconds
respectively). There were no errors or warnings. The file has no lines over 100 characters.
Only the node's `lean` field differs from the shared node. There are no statement disputes
or mathematical node faults.

## Second reading by Q124

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
