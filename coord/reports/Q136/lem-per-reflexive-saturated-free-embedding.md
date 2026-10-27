## Worker report

The module `Sheaf.RingTheory.ReflexiveSaturatedFreeEmbedding` states
`Module.isReflexive_iff_exists_exact_finite_free`, with `sorry` as its only proof.
It introduces no definitions or additional nodes. The node is changed only in `lean`.

Source checked: `literature/stacks-project/more-algebra.tex`, lines 5308–5330,
`lemma-characterize-reflexive` (Stacks Tag 0AV2). The statement there is precisely the
reflexivity/finite-free-embedding equivalence of this node. The full node proof was
read; its five steps are included in the theorem docstring. The converse follows the
bidual diagram chase in Tag 0EB8, using the two already landed helper statements.

The statement matches hypothesis by hypothesis and clause by clause:

- A commutative Noetherian integral domain is `(R : Type u) [CommRing R]
  [IsDomain R] [IsNoetherianRing R]`. Mathlib's domain includes nontriviality.
- The arbitrary finitely generated R-module is `(M : Type v) [AddCommGroup M]
  [Module R M] [Module.Finite R M]`; `v` is independent of `u`.
- The dual is Mathlib's `Module.Dual R M = M →ₗ[R] R`. Reflexivity is
  `Module.IsReflexive R M`, whose single field is bijectivity of `Module.Dual.eval R M`.
  Its defining evaluation identity is `Module.Dual.eval_apply`: evaluation at `m`
  sends `φ` to `φ m`. Bijectivity of this linear map is exactly being an isomorphism.
- The two directions are joined by `↔`; neither direction is omitted.
- The nonnegative integer rank is `∃ (r : ℕ)`; no positive-rank hypothesis is imposed.
- The module N is explicitly existential: `(N : Type (max u v))
  (_ : AddCommGroup N) (_ : Module R N)`.
- Its torsion freeness is `Module.IsTorsionFree R N`. By
  `Module.isTorsionFree_iff_smul_eq_zero` over a domain, this is exactly
  `a • n = 0 → a = 0 ∨ n = 0`, equivalently the node's nonzero-scalar condition.
- The finite free module of tuples R^r is `Fin r → R`, with the ordinary pointwise
  R-module structure. `Fin 0 → R` is the zero module.
- Both named R-linear arrows occur explicitly:
  `(i : M →ₗ[R] (Fin r → R))` and `(q : (Fin r → R) →ₗ[R] N)`.
- Left exactness is `Function.Injective i`; right exactness is
  `Function.Surjective q`. Middle exactness is `Function.Exact i q`, defined as
  `∀ y, q y = 0 ↔ y ∈ Set.range i`, precisely `ker q = im i`.
  This also forces the composition to vanish, with no extra clause required.

The universe of N excludes no existence case: a surjective q identifies N with the
quotient of `Fin r → R` by its kernel. Such a quotient is in `Type u`, and can be
lifted to `Type (max u v)` with its module structure and arrows. In the forward
construction one can directly lift the image of d, a submodule of `Fin m → R`.
Thus there is no smallness assumption on R or M and no restriction on the underlying
mathematical existence assertion about N.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` (and `isNoetherianRing_iff_ideal_fg` to check its meaning).
- `def-weil-finitely-generated-module`: `Mathlib.RingTheory.Finiteness.Defs`,
  `Module.Finite`, meaning `(⊤ : Submodule R M).FG`.
- The node itself introduces duals, reflexivity, torsion freeness and exactness inline;
  these use the existing Mathlib notions `Module.Dual`, `Module.IsReflexive`,
  `Module.IsTorsionFree`, and `Function.Exact`. They are not copied.

The proof imports retain all already stated proof dependencies:

- `lem-weil-pbc-noetherian-submodule-finite`: its Mathlib match `Submodule.FG.of_le`,
  in `Mathlib.RingTheory.Noetherian.Basic`.
- `lem-weil-pbc-module-hom-left-exact`: `LinearMap.exact_lcomp_of_exact_of_surjective`
  in `Mathlib.LinearAlgebra.LeftExact`, with `LinearMap.lcomp_injective_of_surjective`
  from its imported `Mathlib.LinearAlgebra.BilinearMap`; `LinearMap.piRing` in
  `Mathlib.LinearAlgebra.Pi` supplies the coordinate identification.
- `lem-per-torsion-free-bidual-injective`:
  `Sheaf.LinearAlgebra.Dual.TorsionFreeBidualInjective`,
  `Module.eval_injective_iff_isTorsionFree`.
- `lem-per-finite-injection-bidual-injective`:
  `Sheaf.RingTheory.FiniteInjectionBidualInjective`,
  `LinearMap.dualMap_dualMap_injective_of_injective_of_finite`.

Edge cases checked before writing: M = 0 permits r = 0 and N = 0; when r = 0,
injectivity and surjectivity force both M and N to be zero. For finite free M,
the identity embedding with zero quotient works. Over a field, every finite module
is reflexive and the same construction works. A nonzero torsion module such as
Z/2 cannot inject into a finite free Z-module and is not reflexive. For the ideal
(x,y) in k[x,y], the usual injection into R has torsion quotient and is not a
counterexample to the criterion: its bidual is R and the evaluation is not onto.
The zero ring is correctly excluded by the domain hypothesis. No characteristic
restriction or requirement that the short exact sequence split has been added.

Existing-declaration searches (all on 2026-10-24):

- `msearch.py ... leansearch "Over a Noetherian domain a finite module is reflexive
  precisely when it is a submodule of finite free with torsion free quotient"`:
  eight hits, including `Module.IsReflexive`, `Module.IsReflexive.of_finite_of_free`,
  `Module.IsReflexive.to_isTorsionFree`, the finite-projective instance, and PID
  freeness. None states the desired characterization for an arbitrary finite module
  over a Noetherian domain; the projective/free/PID hypotheses do not specialize to it.
- `msearch.py ... leanfinder "A finite module over a Noetherian domain is reflexive
  if and only if it embeds in a finite free module with torsion free quotient"`:
  eight hits, the same finite-free/projective reflexivity and PID results; no match.
- `msearch.py ... loogle "Module.IsReflexive"`: twelve hits, including reflexivity
  of a direct summand (`Module.IsReflexive.of_split`), the dual of a reflexive module,
  and the evaluation equivalence. The split-summand theorem requires a retraction;
  a torsion-free quotient is not assumed to split here. No exact match.
- `msearch.py ... grep "IsReflexive|reflexive" LinearAlgebra/Dual`: ten hits;
  read the full relevant signatures and docstrings in `Dual/Defs.lean:205–275`
  and `Dual/Lemmas.lean:251–275`. No embedding characterization.
- `rg -n "IsReflexive|reflexive"` in project `WeilConjectures` and `Sheaf`
  RingTheory/LinearAlgebra directories: the already landed bidual helpers and flat
  base change theorem, plus quotient duality over Artinian coefficient rings, do
  not state this equivalence. The source id grep under `lean/WeilConjectures` is empty.
- Full-tree `rg` for `isReflexive_iff_exists|saturated_free|
  ReflexiveSaturatedFreeEmbedding` in Mathlib, `lean/Sheaf`, `lean/WeilConjectures`,
  and `dag/lean_names_upstream.json`: no existing declaration or name collision.

The previous worker's stage-1 gate refusal is not a current blocker. The live node
is split and reviewed, has no `lean` record, and is explicitly in `coord/queue.tsv`
as a stage-2 item. The stage handoff in `coord/brief-stage2.md` section 0 authorizes
recording its statement without reopening its accepted split. There is no repair note.
No statement fault or disputed clause was found; no statement correction was needed.

Validation: prescribed `scompile.py Q136 lem-per-reflexive-saturated-free-embedding`
compiled the delivered module cleanly in both sandbox and library mode (1.1 s and
1.4 s respectively); no errors or warnings. `autoImplicit false` is set and both
universes are explicitly bound. No other theorem is introduced or proved.

## Second reading by Q136

A separate second pass by this worker read the original node, Stacks 0AV2, and the
finished Lean signature together; no other agent was started, as the dispatch brief
forbids that. The ring, finite module, canonical evaluation reflexivity, equivalence,
nonnegative rank, arbitrary quotient module with its module structure, torsion-free
condition, finite tuple module, two R-linear arrows, injectivity, exactness and
surjectivity all have the counterparts listed above. In particular N is not assumed
free or projective, i is not assumed split, and N is not given as an additional
hypothesis. The size of its existential type is justified by surjectivity from the
finite free module. Both zero-rank and independent ring/module universe cases are
retained. The two proof helper imports are private, and the four statement imports
are public in module mode. No mismatch was found and no change to the node statement
was necessary.
