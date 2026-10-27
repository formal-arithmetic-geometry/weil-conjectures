## Worker report

This delivery states `Algebra.fppfTensorModelSurjectivity` in
`Sheaf.RingTheory.FppfTensorModelSurjectivity`, with one postponed theorem proof.
The same module constructs the canonical `Algebra.fppfTensorModelMap` using Mathlib's
`Algebra.TensorProduct.productMap`. Its data is explicit, with no choice or postponed
well-definedness proof. This helper belongs to the item's own tensor-model map;
there is no new independent notion or new DAG node.

Source read: `literature/stacks-project/descent.tex`, Tag 0367,
`lemma-finite-type-local-source-fppf-algebra`, especially the final paragraph at
lines 4370–4387. The DAG item isolates its generic tensor-model argument; it does
not inherit the finite-presentation assumptions used to obtain such a model in
the source's preceding paragraph.

Hypotheses and objects, matched to the node:

- All six commutative rings are independent `Type uR`, `Type uC`, `Type uP`,
  `Type uA`, `Type uD`, `Type uB`, each with `CommRing`.
- `R → P → A → B` are `algebraMap R P`, `algebraMap P A`, and
  `algebraMap A B`. `Algebra R A`, `IsScalarTower R P A`, `Algebra R B`, and
  `IsScalarTower R A B` specify the induced coefficient structures, without
  imposing any further property on these maps.
- `C → P`, `C → D`, and `D → B` are the corresponding `algebraMap`s.
  `Algebra C A` and `IsScalarTower C P A` specify the node's induced `C`-structure
  on `A`. `Algebra C B` with `IsScalarTower C A B` and `IsScalarTower C D B`
  expresses exactly agreement of the two maps `C → B`. There is no map `R → C`
  and no compatibility assumption between `R` and `C` beyond those in the node.
  Every compatible diagram in the node supplies these structures, so this is
  an encoding of the stated diagram rather than a restriction on its rings.
- Faithful flatness is `[Module.FaithfullyFlat C D]`, as required by the project's
  faithful-flatness convention and the dependency's recorded declaration.
- `e : A ⊗[C] D ≃ₐ[A] B` gives precisely the isomorphism hypothesis.
  `he : ∀ a d, e (a ⊗ₜ[C] d) = algebraMap A B a * algebraMap D B d`
  identifies it with the induced map in the node. It is not an unconstrained
  tensor equivalence. Using an equivalence instead of a bijective algebra map
  merely packages its uniquely determined inverse.
- `n : ℕ`, `b : Fin n → B`, and `hb : Algebra.adjoin R (Set.range b) = ⊤`
  mean exactly that the listed `b_j` generate `B` over `R`.
- `Q` is written as `P ⊗[C] D` throughout, using Mathlib's tensor product and
  its left `P`-algebra structure. No arbitrary model or auxiliary `Q` is assumed.
- The definition `fppfTensorModelMap C P A D B` is the node's `q`: its defining
  term is `productMap ((toAlgHom C A B).comp (toAlgHom C P A))
  (toAlgHom C D B)`, hence its value at `p ⊗ d` is `f(φ(p))g(d)`.
  The maps `toAlgHom` use exactly the scalar towers already described.
- `z : Fin n → P ⊗[C] D` and `hz : ∀ j, fppfTensorModelMap ... (z j) = b j`
  are all the stipulated generator lifts, without an assumption on other elements.

Conclusion clauses, in order:

- `Module.FaithfullyFlat P (P ⊗[C] D)` means faithful flatness of the canonical
  left-factor map `p ↦ p ⊗ 1`, not of an arbitrary algebra structure.
- `Function.Surjective (fppfTensorModelMap C P A D B)` is surjectivity of `q`.
- The existential `θ : A ⊗[P] (P ⊗[C] D) ≃ₐ[A] B` is the required comparison.
  Its first conjunct is the exact forward formula
  `θ (a ⊗ (p ⊗ d)) = e ((a * algebraMap P A p) ⊗ d)`.
  Its second conjunct is the exact inverse formula
  `θ.symm (e (a ⊗ d)) = a ⊗ (1 ⊗ d)`.
  Its third conjunct quantifies over every `w : P ⊗[C] D` and states
  `θ (1 ⊗ w) = fppfTensorModelMap ... w`. This is the claimed identification
  of the base-change map with `q`, not merely agreement on the generator lifts.
- `Function.Surjective (algebraMap P A)` is surjectivity of `φ` itself.
- The final universal quantifiers `∀ (N : ℕ) (p : Fin N → P)` and implication
  from `Algebra.adjoin R (Set.range p) = ⊤` to
  `Algebra.adjoin R (Set.range (fun i ↦ algebraMap P A (p i))) = ⊤`
  state exactly the conditional assertion about images of the listed generators.
  They do not assume finite generation of `P` unconditionally.
- There is no finite-presentation, Noetherian, nonzero-ring, field, or
  characteristic hypothesis.

Dependency declarations used (full signatures and docstrings read in local Mathlib):

- `def-weil-pbc-faithfully-flat-ring-map`:
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`, `Module.FaithfullyFlat`.
  Also read `iff_exact_iff_lTensor_exact`, and the ring-map bridge in
  `Mathlib.RingTheory.RingHom.FaithfullyFlat` to confirm the exactness notion.
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`:
  `Mathlib.RingTheory.TensorProduct.Maps`, `Algebra.TensorProduct.productMap`
  and `productMap_apply_tmul`; `Mathlib.RingTheory.TensorProduct.Basic`,
  `instCommRing`, `tmul_mul_tmul`, `instAlgebra`, `includeLeft`, `includeRight`, `ext`.
- `def-weil-pbc-finite-type-algebra`:
  `Mathlib.RingTheory.FiniteType`, `RingHom.FiniteType` and `Algebra.FiniteType`.
  A specified generating family is expressed by the underlying `Algebra.adjoin`
  notion (definition read in `Mathlib.Algebra.Algebra.Subalgebra.Lattice`),
  retaining the actual generators instead of only the existential `FiniteType`.
- `def-weil-pbc-module-tensor-product`:
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, `TensorProduct` and `TensorProduct.mk`;
  the universal `TensorProduct.lift`/`ext'` in `.Basic` and `LinearMap.rTensor`
  in `.Map` were read as well. These are public transitive imports of
  `Mathlib.RingTheory.TensorProduct.Maps`.
- The proof-only nodes are already supplied by the public imports:
  `lem-weil-pbc-faithfully-flat-base-change` is `Module.FaithfullyFlat.instTensorProduct`
  in `.Flat.FaithfullyFlat.Basic`; `lem-weil-pbc-tensor-cancel-base-change` is
  `Algebra.TensorProduct.cancelBaseChange` in `.TensorProduct.Maps` (both pure-tensor
  formulas read); `lem-weil-pbc-module-tensor-comm` uses `TensorProduct.comm`,
  `comm_tmul`, `map_comp_comm_eq` in the linear tensor modules read above.
  Thus no additional proof-only module import is needed.

Edge cases checked before writing and in the second reading:

- `n = 0`: `Fin 0` allows the empty list; `hb` then says the coefficients alone
  generate `B`. Its elements lift through the coefficient map of `Q`, so the
  polynomial surjectivity argument still applies.
- `N = 0`: the last implication includes coefficient-generated `P`, and correctly
  gives coefficient-generated `A` by the surjectivity conclusion.
- Zero rings and zero tensor products: there is no `Nontrivial` assumption.
  Faithful flatness handles precisely the degeneracies allowed by the source;
  a zero `C` forces its unital algebras to be zero, so it is not a counterexample.
- No requirement that `R → P`, `C → P`, or `P → A` be injective or flat was
  introduced. In particular a genuine quotient `P → A` is covered.
- Arbitrary independent universes for all six rings are retained. No testing
  quantifier on a smaller universe or restriction to same-universe rings occurs.

Searches for existing declarations (2026-10-24, prescribed `msearch.py`, Q14/item):

- LeanSearch query `Tensor product cancel base change faithfully flat surjectivity
  and images of algebra generators`: 8 hits, including
  `Algebra.TensorProduct.cancelBaseChange`, `Module.FaithfullyFlat.instTensorProduct`,
  `Module.FaithfullyFlat.surjective_of_tensorProduct`, and
  `Algebra.Generators.baseChange`. These are component results; none states the
  full model criterion with arbitrary `e`, specified lifts, comparison and final
  generator images.
- LeanFinder query `Faithfully flat tensor model with lifts of algebra generators
  implies surjectivity of the original algebra map and a specified tensor comparison`:
  8 hits including `Module.FaithfullyFlat.surjective_of_tensorProduct`,
  `RingHom.FaithfullyFlat.codescendsAlong_surjective`,
  `Module.FaithfullyFlat.lTensor_surjective_iff_surjective`, and tensor inclusion
  surjectivity lemmas. None supplies the whole statement. The first and the
  codescent declaration were read in `.Flat.FaithfullyFlat.Descent`.
- Loogle query `Algebra.TensorProduct.cancelBaseChange,
  Algebra.TensorProduct.productMap, Module.FaithfullyFlat.surjective_of_tensorProduct`:
  0 hits (this combined query is supplementary to both semantic searches).
- Mathlib grep query `fppf.*tensor|tensor.*model|surjective_of_tensorProduct|cancelBaseChange`
  in `RingTheory`: 25 hits, mostly cancellation uses, plus unrelated smooth-algebra
  tensor models; no exact full criterion.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for `fppfTensorModel|fppf_tensor_model|lem-a1-fppf-tensor-model-surjectivity`:
  no existing declaration or attachment. Both final proposed full declaration
  names were also searched in Mathlib and both project source roots: no hits.
- Broader `rg` in both project RingTheory trees for
  `fppf|faithfully.*surject|surject.*faithfully` found the related
  `Sheaf.RingTheory.FiniteTypeFppfSourceDescent`, which was opened: it states only
  finite-type descent under a faithfully flat finitely presented source map,
  not this generic tensor-model criterion. Other hits concern spectrum
  surjectivity or module descent. No duplicate definition is needed.

Validation: `scompile.py Q14 lem-a1-fppf-tensor-model-surjectivity` compiled the
sandbox module and library-path module cleanly, at the default 60-second limit,
with no errors or warnings. Every universe and variable is explicitly bound;
the module has no local notation or instances, and its sole theorem proof is `sorry`.
No statement correction, dependency repair, or disputed statement was required.

## Second reading by Q14

Author's fresh self-check for this directly dispatched remote delivery; independent
review belongs to the maintainer, as specified in the dispatch brief.

Reopened the node and the delivered file and checked every hypothesis and conjunct
against the mapping above. In particular the algebra structures on `A` and `B`
are constrained by the stated paths, while there is no invented `R → C` map;
`he` fixes the given equivalence on every pure tensor. The comparison and its
inverse use `C` on the inner tensors and `P` on the outer tensors, exactly as
in the node. The all-elements compatibility is inside the same existential as
both comparison formulas, so a single `θ` satisfies all three. The last
conclusion is conditional on each supplied generating family of `P`, with `N = 0`
allowed. The canonical map helper constructs the product-map data directly and
is recorded among the item's declarations. No mismatch was found and no
hypothesis or conclusion was changed during this reading.
