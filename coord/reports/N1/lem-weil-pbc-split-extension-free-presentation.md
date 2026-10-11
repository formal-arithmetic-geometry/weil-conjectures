## Worker report

The module `Sheaf.LinearAlgebra.SplitExtensionFreePresentation` states
`LinearMap.exists_retraction_iff_relation_factors`, with only a `sorry` proof.
No definitions, dependency modules, new nodes, or statement corrections are needed.

Hypothesis and clause correspondence:

- The ring is `{R : Type u} [Ring R]`; no commutativity, Noetherianity, finiteness,
  locality, or ideal hypothesis is introduced into this elementary criterion.
- The four modules are `{N M F₀ F₁ : Type v}`, with explicitly bound
  `AddCommGroup` and `Module R` instances. The common ambient universe places no
  cardinality bound; the ring universe is independent.
- The injection is `(u : N →ₗ[R] M)` and `(hu : Function.Injective u)`.
- The quotient Q is literally `M ⧸ LinearMap.range u`, not a freely chosen
  module with an unspecified quotient identification. Its projection p is
  `(LinearMap.range u).mkQ`.
- The presentation arrows are `(d₁ : F₁ →ₗ[R] F₀)` and
  `(π : F₀ →ₗ[R] M ⧸ LinearMap.range u)`.
- `[Module.Free R F₀]` is exactly the freeness assumption, including infinite
  and empty bases. F₁ is not assumed free.
- `hexact` is `ComposableArrows.Exact` of the three-arrow diagram built by
  `ComposableArrows.mk₃ (ModuleCat.ofHom d₁) (ModuleCat.ofHom π) 0`.
  The final object is `ModuleCat.of R PUnit.{v + 1}`, the zero module.
  Exactness at F₀ is image d₁ = kernel π; exactness at Q is surjectivity of π.
  This includes the complex condition, without imposing injectivity of d₁.
- The lift is `(α : F₀ →ₗ[R] M)` with
  `hα : (LinearMap.range u).mkQ.comp α = π`, exactly p ∘ α = π.
- The given relation map is `(β : F₁ →ₗ[R] N)` with
  `hβ : u.comp β = α.comp d₁`. This is the node's description of β.
  Uniqueness follows from hu; existence follows from exactness and the quotient
  kernel, as in the node. Quantifying over the given β with this equation does
  not require extra data or choose a different relation map.
- A left inverse is precisely `∃ v : M →ₗ[R] N, v.comp u = LinearMap.id`.
- The equivalent condition is precisely
  `∃ γ : F₀ →ₗ[R] N, β = γ.comp d₁`. Both directions appear in the `↔`.

Dependency declarations read and used:

- `def-weil-pbc-free-module`: `Module.Free` in
  `Mathlib.LinearAlgebra.FreeModule.Basic` (class and basis docstring read).
- `def-weil-pbc-exact-sequence`: `CategoryTheory.ComposableArrows.Exact` in
  `Mathlib.Algebra.Homology.ExactSequence` (full structure and docstring read);
  its exactness fields use `CategoryTheory.ShortComplex.Exact`, whose full
  structure and docstring were also read.
- `ModuleCat.ofHom` and its signature in
  `Mathlib.Algebra.Category.ModuleCat.Basic` turn the same linear maps into
  categorical arrows; `Mathlib.Algebra.Category.ModuleCat.Abelian` supplies the
  abelian structure needed for module exactness.
- `Submodule.mkQ` in `Mathlib.LinearAlgebra.Quotient.Defs` is the existing
  quotient projection; its full definition and docstring were read.

Edge cases checked before writing: all zero modules (both sides hold); F₀ = 0
forces Q = 0 by exactness, so u is an isomorphism and β = 0; F₁ = 0 makes π an
isomorphism, and the lift supplies a split extension. Empty/infinite bases and
zero rings are permitted. Neither Noetherianity nor commutativity is needed in
the four-step proof. β is unique even for zero modules. The zero target PUnit
has a canonical module structure, so exactness at Q really tests surjectivity.
The freeness hypothesis is retained even though the given lift makes it
unnecessary for the equivalence.

Source checked: the local `literature/stacks-project/algebra.tex` is absent on
this machine. Read the primary source https://stacks.math.columbia.edu/tag/02HO,
proof of Lemma 10.74.1, the paragraph describing α, β, and the splitting criterion.
The source's surrounding completion theorem has additional hypotheses, but the
criterion's elementary proof in this node uses none of them. No node fault or
STATEMENT-DISPUTED issue was found.

Searches made:

- `msearch.py ... leansearch` query “injection of modules splits iff the induced
  map from relations of a free presentation of the cokernel factors through
  the presentation differential”: unavailable, HTTP Internal Server Error.
- `msearch.py ... leanfinder` query “An injection of modules splits if and only
  if the map from relations of a free presentation of its cokernel factors
  through the presentation differential”: eight hits, including
  `Module.finitePresentation_of_split_exact`,
  `Module.Presentation.CokernelData.ofSection`, `Module.Projective.iff_split`,
  and `Function.Exact.splitInjectiveEquiv`; none state this criterion.
  Read the signatures/docstrings of the split-exact finite-presentation result
  and splitInjectiveEquiv to check the closest candidates.
- `msearch.py ... loogle` query
  `Function.Exact, LinearMap.comp, Function.Injective`: twelve hits, including
  `Function.Exact.split_tfae`, `split_tfae'`, and snake/five-lemma results;
  no presentation criterion.
- `msearch.py ... grep` query
  `split.*presentation|presentation.*split|splitInjectiveEquiv` in `Algebra`:
  six hits, only finite-presentation preservation and splitInjectiveEquiv.
- `rg -n` with `split.*presentation|presentation.*split|split_extension|freePresentation`
  in the source `WeilConjectures` and project `lean/Sheaf`: only unrelated
  polynomial/separable-algebra and rank-one group splitting remarks.
- `rg -n` for the node id in the source `WeilConjectures`: no matches.

Validation: the first server compile succeeded with one whitespace warning on
`PUnit.{v+1}`; repaired to `PUnit.{v + 1}`. Final server compile passed cleanly in 1.3 seconds.
`deliver2.py N1 lem-weil-pbc-split-extension-free-presentation --no-push` printed
OK: compilation and preflight pass, except the independent second reading,
which the second reader supplies. Nothing pushed. No proofs have been written.

## Second reading by N1

Read the node copy, the full module, both statement dependency nodes and their
recorded Mathlib declarations independently. No new nodes, dependency modules,
or statement_change are present. The statement and module require no repair.

Source: read the primary Stacks page https://stacks.math.columbia.edu/tag/02HO
and fetched the Stacks algebra.tex into this item's scratchpad. Read lines
18142-18170, including the surrounding assumptions and the splitting criterion
at 18166-18168. The surrounding completion lemma assumes a Noetherian
commutative ring, finite modules and an ideal in the Jacobson radical; those
assumptions establish injectivity and the later completion argument. The
isolated elementary criterion in this node has a given injection, presentation
and lift. Its four-step proof works over every ring and requires none of the
completion assumptions. F1 need not be free and no F2 is needed for this
criterion. The node explicitly records this extraction; Lean matches it.

Objects, hypotheses and conclusions, checked individually (all PASS):

- Ring R: `{R : Type u} [Ring R]`, exactly the node's ring. No field,
  commutativity, Noetherianity, nontriviality or characteristic restriction.
- R-modules N, M, F0, F1: `{N M F₀ F₁ : Type v}` with each AddCommGroup and
  Module R instance bound explicitly. These are the node's four modules.
- Injection u: `(u : N →ₗ[R] M)` and `(hu : Function.Injective u)`.
- Quotient Q and projection p: `M ⧸ LinearMap.range u` and
  `(LinearMap.range u).mkQ`. Read Submodule.mkQ's actual definition: it is
  the quotient projection, with no independently chosen quotient data.
- Presentation maps: `(d₁ : F₁ →ₗ[R] F₀)` and
  `(π : F₀ →ₗ[R] M ⧸ LinearMap.range u)`.
- Exactness F1 → F0 → Q → 0: `hexact` is ComposableArrows.Exact of
  `ComposableArrows.mk₃ (ModuleCat.ofHom d₁) (ModuleCat.ofHom π) 0`.
  Read Exact's IsComplex parent and consecutive ShortComplex.Exact fields:
  only the positions F0 and Q are tested. Read ShortComplex.Exact and
  exact_iff_image_eq_kernel, and exact_iff_epi for a zero second arrow.
  Thus this means image d1 = kernel π and π surjective, with no unwanted
  injectivity of d1. `ModuleCat.of R PUnit.{v + 1}` is the zero target.
  Read ModuleCat.ofHom and the Ring-only ModuleCat.abelian instance.
- Freeness of F0: `[Module.Free R F₀]`, the recorded dependency declaration.
  Read the class's exists_basis field and free_iff_set; arbitrary bases are
  allowed. No freeness or finite generation is imposed on F1.
- Lift α: `(α : F₀ →ₗ[R] M)` with
  `hα : (LinearMap.range u).mkQ.comp α = π`, exactly p composed with α = π.
- Induced β: `(β : F₁ →ₗ[R] N)` with `hβ : u.comp β = α.comp d₁`.
  Its existence follows from π composed with d1 = 0 and ker p = range u;
  uniqueness follows from hu. Quantifying over β satisfying this equation
  expresses the specified unique map, with no stronger solvability assumption.
- Left inverse clause: `∃ v : M →ₗ[R] N, v.comp u = LinearMap.id`.
- Factorization clause: `∃ γ : F₀ →ₗ[R] N, β = γ.comp d₁`.
- Equivalence and quantifier order: the two clauses are linked by `↔`, after
  fixing all the presentation and lift data, exactly as in the node.

Edge cases: zero modules and the zero ring are permitted. An empty basis
means F0 = 0; exactness forces Q = 0 and u is an isomorphism, so both clauses
hold. If F1 = 0, π is an isomorphism and the given lift splits the extension.
Infinite bases are permitted, with no cardinality bound. All module carriers
share an arbitrary ambient universe v, independent of ring universe u;
heterogeneous carriers can be placed in a common larger universe. There is no
small-universe test-object quantifier. No schemes, n, or characteristic bound
occur, so their special cases impose no additional hypotheses.

Independent searches (different queries from the worker):

- LeanSearch: "module extension split exactly when lifted relations factor
  through the presentation map"; service unavailable (Internal Server Error),
  recorded as unavailable, with no verdict inferred.
- LeanFinder: "Obstruction to splitting a module extension from a presentation:
  the lifted relation homomorphism factors through its differential"; eight
  hits about Module.Presentation.ofExact and Relations.Solution desc. Read
  the actual Presentation.ofExact and IsPresentation.desc signatures and
  docstrings in Cokernel.lean and Basic.lean. They construct presentations
  or descend maps, and do not state this retraction equivalence.
- Loogle: `LinearMap.comp, LinearMap.range, Function.Injective`; six hits,
  including codRestrictOfInjective_comp and lequivProdOfRightSplitExact.
  Their returned signatures restrict a map to an image or build a product
  equivalence from an already split sequence; neither is this criterion.
- msearch grep: `retraction|relation.*factor|factor.*relation` in Algebra/Module;
  five SnakeLemma comments, no matching theorem.
- Direct rg with `retraction|relation.*factor|factor.*relation|extension.*split|
  split.*extension` on WeilConjectures and lean/Sheaf, and split/retraction
  on Mathlib/Algebra/Module/Presentation: no matching statement. Exact name
  and blueprint-id searches on WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json found no existing declaration.

H5-H9: no definitions or hollow data, one theorem with proof `by sorry`,
no proved helper, no local notation/private copy. Both docstrings name Tag
02HO and the blueprint id. The proof docstring renders all four node steps:
γ = v composed with α, surjectivity of Φ, ker Φ contained in ker Ψ,
and descent to the retraction. Dependency citations match. Every universe,
type, instance and map is bound. Node lean.statement is verbatim the theorem
signature. No mathematical mismatch found; only this independent review
section was added. Single-file server compilation and delivery preflight
are run after this reading.
