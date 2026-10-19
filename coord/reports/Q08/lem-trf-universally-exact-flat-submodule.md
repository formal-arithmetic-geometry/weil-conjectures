## Worker report

This repair supplies the missing stage-2 Lean module and item Lean record for
`lem-trf-universally-exact-flat-submodule`. The module
`Sheaf.TraceFormula.UniversallyExactFlatSubmodule` states
`Module.flat_submodule_of_universally_exact`; its proof is `sorry`, as required
for stage 2. No definition is introduced and no data is chosen by `sorry`.
The natural-language node statement, dependencies, source, proof, and metadata
are unchanged; only the node's `lean` field is added in the sandbox copy.

The theorem has the following exact rendering of the node's hypotheses and clauses.

* `R : Type u` with `[CommRing R]` is the commutative base ring.
* `M₁ : Type v`, `M₂ : Type w`, and `M₃ : Type z`, each with
  `[AddCommGroup]` and `[Module R]`, are the three modules. Their universes are
  independent, so zero modules and modules of different sizes are included.
* `f : M₁ →ₗ[R] M₂` and `g : M₂ →ₗ[R] M₃` are the two maps in the sequence.
  `hf : Function.Injective f`, `hg : Function.Surjective g`, and
  `hfg : LinearMap.ker g = LinearMap.range f` render the short exactness
  hypotheses `0 → M₁ → M₂ → M₃ → 0`.
* `h_exact` universally quantifies every test module
  `Q : Type (max u t)` with `[AddCommGroup Q]` and `[Module R Q]`. The three
  conjuncts are injectivity of `f.rTensor Q`, exactness
  `Function.Exact (f.rTensor Q) (g.rTensor Q)`, and surjectivity of
  `g.rTensor Q`. Thus tensoring with every such module preserves the stated
  short exact sequence. The test universe contains the ring universe, avoiding
  a vacuous family of tests.
* The typeclass conclusion `[Module.Flat R M₂]` is the recorded flatness of the
  middle module, and the theorem conclusion `Module.Flat R M₁` is flatness of
  the submodule. Flatness is the Mathlib declaration recorded by
  `def-weil-pbc-flat-ring-map`.

The proof docstring follows both proof steps in the node. First, for an arbitrary
injection `N → N'`, complete it with its cokernel `N''`; tensor the universally
exact sequence with `N`, `N'`, and `N''` to obtain the three exact rows, while
flatness of `M₂` makes `M₂ ⊗ N → M₂ ⊗ N'` injective. Second, if an element of
`M₁ ⊗ N` maps to zero in `M₁ ⊗ N'`, commutativity of the left square makes its
image in `M₂ ⊗ N` map to zero in `M₂ ⊗ N'`; middle-column injectivity makes that
image zero, and top-row injectivity makes the original element zero. This gives
injectivity for every injection and hence `Module.Flat R M₁`.

Dependency declarations read and used:

* The dependency `def-weil-pbc-flat-ring-map` is a Mathlib leaf. Its recorded
  declarations are `Module.Flat` in `Mathlib.RingTheory.Flat.Basic` and
  `RingHom.Flat` in `Mathlib.RingTheory.RingHom.Flat`; the theorem uses
  `Module.Flat` exactly. I read the full signatures and documentation for both.
* The dependency `def-weil-pbc-module-tensor-product` is a Mathlib leaf. Its
  recorded declarations are `TensorProduct` and `TensorProduct.lift` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs/Basic`, and the map used here is
  `LinearMap.rTensor` from `Mathlib.LinearAlgebra.TensorProduct.Map`. I read
  the universal-property and `rTensor` signatures and documentation.

Edge cases checked: the test-module index may be empty only in the impossible
case that its universe has no module instances, while the quantified type itself
is the full `Type (max u t)` as required; `M₁`, `M₂`, or `M₃` may be zero; `f`
may be the zero map when its injectivity permits that; and the sequence may be
split or have `R` the zero ring. No finite-generation, Noetherian, nonzero,
separation, or universe-equality assumption was added.

Searches made on 2026-10-18:

* `msearch.py Q08 lem-trf-universally-exact-flat-submodule leanfinder` for
  “universally exact short exact sequence flat middle module flat submodule”:
  only generic flatness and tensor exactness results; no exact theorem.
* `msearch.py ... loogle "Module.Flat, universally exact, submodule"`: no direct
  hit; `universally` was not a recognized identifier in the relevant search.
* `msearch.py ... grep "universally.exact|flat.*submodule|058P"` in Mathlib:
  no matching Stacks lemma or exact theorem.
* `rg` over `WeilConjectures/` and `lean/Sheaf/` for the item id,
  `universally exact`, and the proposed declaration name: no duplicate
  declaration. The nearby `Module.flat_of_universally_exact` theorem concerns
  the cokernel and is a different statement, so it was not reused.

The module compiled cleanly with the required wrapper:

`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q08 lem-trf-universally-exact-flat-submodule /home/ubuntu/weil-newtargets-stage2-sandbox/Q08/lem-trf-universally-exact-flat-submodule/lean/Sheaf/TraceFormula/UniversallyExactFlatSubmodule.lean`

Both sandbox and library compilation completed with exit code 0; the only
postponed proof is the expected `sorry` theorem warning, suppressed by the
module's `warn.sorry = false` option. `citations.json` records verbatim quotes
for every dependency use in both proof steps.

## Second reading by Q08

I independently reopened the node, the final module, both dependency records,
and the source location Tag 058P. The maps, injective/surjective/kernel-image
conditions, and all three tensor exactness conjuncts match the node's short
exact universally exact sequence. The conclusion uses the same Mathlib flatness
notion and only assumes flatness of `M₂`; it concludes flatness of `M₁`.
Universes permit arbitrary modules and the test type is `Type (max u t)`, so no
vacuity or hidden universe equality was introduced. The docstring contains the
node's two proof steps, and the node copy changes only `lean`. No mismatch was
found.
