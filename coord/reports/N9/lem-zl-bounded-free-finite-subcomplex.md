## Worker report

The module `Sheaf.Algebra.Homology.BoundedFreeFiniteSubcomplex` states
`CochainComplex.exists_bounded_finite_free_subcomplex`, with `sorry` as its entire proof.
It introduces no definition and changes no natural-language statement or dependency list.
The source is Stacks Tag 0FNR, `more-algebra.tex`,
`lemma-complex-bounded-above-free-colim-bounded-finite-free`, read in full together with
its proof at lines 38552–38586. The declaration docstring expands all six DAG proof steps.

Hypothesis and conclusion correspondence:

- A commutative ring is `{A : Type u} [CommRing A]`. There is no nontriviality assumption.
- The integer cochain complex of modules is
  `F : CochainComplex (ModuleCat.{v} A) ℤ`. Its differentials square to zero by the
  `HomologicalComplex` fields. Ring universe `u` and module universe `v` are independent.
- Vanishing in degrees above some integer is
  `hbounded : ∃ b : ℤ, ∀ n : ℤ, b < n → Subsingleton (F.X n)`.
  A module is zero precisely when its underlying type is subsingleton; this is strict
  termwise vanishing, not vanishing of cohomology.
- Freeness of each term is `hfree : ∀ n : ℤ, Module.Free A (F.X n)`.
  `Module.Free.exists_basis` supplies a basis and `Module.Basis.repr` identifies the module
  with finitely supported coefficient functions, the direct sum in the node.
- A finite list of degree-element pairs is `xs : List (Σ n : ℤ, F.X n)`.
  Sigma pairs preserve the dependence of each element's type on its degree.
- The subcomplex consists of `G : (n : ℤ) → Submodule A (F.X n)` and
  `(G n).map (F.d n (n + 1)).hom ≤ G (n + 1)` for every `n`.
  This is exactly the node's explicit meaning of subcomplex. The restricted linear maps
  exist by `LinearMap.restrict`; their squares are zero because the ambient maps square
  to zero. No additional subcomplex axiom is being assumed or omitted.
- Containment of every listed element is `∀ p ∈ xs, p.2 ∈ G p.1`.
- Boundedness is `∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → G n = ⊥`.
  Zero as a submodule is literally bottom. No fixed lower endpoint is imposed.
- Finite freeness in every degree is
  `∀ n : ℤ, ∃ r : ℕ, Nonempty ((G n) ≃ₗ[A] (Fin r → A))`.
  This states the actual isomorphism to `A^r`, not just finite generation or projectivity.
  Natural `r` includes zero. Finite-dimensional function modules are finite direct sums.

Dependency declarations read and used:

- `def-weil-abstract-derived-category` records `DerivedCategory` and `HasDerivedCategory`
  in `Mathlib.Algebra.Homology.DerivedCategory.Basic`, imported publicly as required.
  Its relevant underlying notion is `CochainComplex` from
  `Mathlib.Algebra.Homology.HomologicalComplex`: the `.up ℤ` shape and `d_comp_d` give
  the exact cochain convention of the dependency. I read both the recorded definitions
  and the underlying complex signature and docstring.
- `Mathlib.Algebra.Category.ModuleCat.Basic` supplies modules and their linear morphisms.
- `Mathlib.LinearAlgebra.FreeModule.Basic` supplies `Module.Free`; its class signature and
  `Module.Basis.repr : M ≃ₗ[R] (ι →₀ R)` were read in the Mathlib sources.

Existing-interface check: the source module
`WeilConjectures.Algebra.Homology.ModuleCat.Subcomplex` was read in full. Its
`CochainComplex.SubcomplexFamily` encodes the same map-of-submodule condition, but
requires `R : Type u` and `ModuleCat.{u} R` with the same universe. The theorem here
quantifies over submodules and stability directly, exactly as the node's final sentence
does, allowing independent universes without a second definition. Its `subcomplex`
construction confirms these data equip the submodules with the restricted differentials.
Its `SubcomplexFamily.IsFinite` and `exists_mem_range_tensor` assert finite generation,
not finite freeness, and therefore cannot attach this item to an existing declaration.

Edge cases checked before drafting: the empty list admits all bottom submodules and
rank zero; repeated pairs and several inputs in one degree remain allowed by `List`;
inputs above the upper bound are zero and belong to bottom; negative input degrees have
no restriction; the zero ring and zero complex are included; `Fin 0 → A` is the zero
module; a submodule need not itself be free in general, so the conclusion retains explicit
linear equivalences rather than relying on finite generation. For example, the differential
given by multiplication by 2 over `ℤ/4` does not justify using its image as a free term;
the source instead enlarges by finite coordinate submodules, as the proof docstring says.
No statement dispute, missing notion, or dependency defect was found.

Searches (2026-10-18; complete outputs are retained in the sandbox `searches.jsonl`):

- `msearch.py leanfinder`, query “Every finite collection of homogeneous elements of a
  bounded above complex of free modules lies in a bounded finite free subcomplex”:
  eight hits, on graded algebra generators, finite polynomial submodules, `FGModuleRepr.S`,
  Nobeling spans, homogeneous localization, and `HomologicalComplex.IsSupported`.
  None states the item.
- `msearch.py leansearch`, query “Every bounded above complex of free modules has a bounded
  finite free subcomplex containing any finite list of homogeneous elements”: eight hits,
  on limits/colimits of complexes, finite simplicial subcomplexes, localized shifted Hom,
  support, and `Module.Free.finsupp`. None states the item.
- `msearch.py loogle`, query `CochainComplex, Module.Free, Module.Finite`: zero hits.
- `msearch.py grep`, query
  `finite.free.*subcomplex|subcomplex.*finite.free|bounded.*subcomplex`: zero hits.
- Direct `rg` of these expressions and the item id in `WeilConjectures/` and `lean/Sheaf/`
  found only unrelated bounded-filtration material in the latter. A broader search for
  subcomplexes and modules found the upstream module discussed above. A search in
  `dag/nodes/` and `dag/lean_names_upstream.json` for `SubcomplexFamily`, its construction,
  and its module found no node attachment. Searching the proposed theorem name in
  Mathlib, upstream, and the side project found no collision.

Validation: `scompile.py N9 lem-zl-bounded-free-finite-subcomplex` compiled both the sandbox
check and the final library module successfully, with no errors or warnings (16.9 s and
38.3 s respectively). Only the prescribed `scompile.py` and `deliver2.py` wrappers are used;
no global build or direct Git command is used. The node copy changes only `lean`, with the
exact signature extracted from the delivered module.

## Second reading by N9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
