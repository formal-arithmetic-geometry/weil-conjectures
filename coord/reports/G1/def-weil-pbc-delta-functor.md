## Worker report

`Sheaf.CategoryTheory.DeltaFunctor` defines the three notions in Stacks Project,
Homology, Definitions 010Q, 010R, and 010S: a cohomological delta-functor,
its morphisms, and universality. The full source text was read at
`/home/ubuntu/c1-stacks-review/homology.tex`, lines 2623-2702.

Clause matching against the node:

- Abelian categories A and B: `[Abelian A] [Abelian B]`, with their category
  structures bound explicitly. All object universes and morphism universes are
  explicit. These use `CategoryTheory.Abelian` from
  `Mathlib.CategoryTheory.Abelian.Basic`.
- For every n >= 0, an additive functor F^n: `F : ℕ → A ⥤ B` and
  `additive : ∀ n : ℕ, (F n).Additive`. This uses
  `CategoryTheory.Functor.Additive` from
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`.
- For every short exact sequence, including its two arrows, and every n,
  a connecting map: `delta : ∀ (S : ShortComplex A), S.ShortExact →
  ∀ n : ℕ, (F n).obj S.X₃ ⟶ (F (n + 1)).obj S.X₁`. The actual maps `S.f` and
  `S.g` belong to `S`; `ShortComplex.ShortExact` comes from
  `Mathlib.Algebra.Homology.ShortComplex.ShortExact`.
- Exactness at F^0(A): `mono_zero`, equivalent to exactness of
  `0 → F^0(A) → F^0(B)`. Exactness at every F^n(B), F^n(C), and F^(n+1)(A):
  `exact_middle`, `exact_right`, and `exact_left`, respectively. Each supplies
  the zero composite and uses Mathlib's `ShortComplex.Exact` on the two adjacent
  arrows. Together these are every position in the node's infinite sequence.
- Naturality in a morphism of short exact sequences: `naturality` quantifies
  `φ : S ⟶ T`. Mathlib's `ShortComplex.Hom` carries the arrows
  `φ.τ₁`, `φ.τ₂`, `φ.τ₃` and its two commutative-square equalities. The field
  states `delta S hS n ≫ (F (n + 1)).map φ.τ₁ =
  (F n).map φ.τ₃ ≫ delta T hT n`.
- A morphism of delta-functors: `CohomologicalDeltaFunctor.Hom.app` gives one
  natural transformation for each n; `Hom.naturality` gives precisely its
  compatibility with each connecting map.
- Universality: `CohomologicalDeltaFunctor.IsUniversal` says for every G and
  natural transformation `t : F.F 0 ⟶ G.F 0`, there exists a unique
  `φ : Hom F G` with `φ.app 0 = t`.

Edge cases: degree zero is covered by `mono_zero` and all three repeated
exactness clauses at `n = 0`; every natural number occurs. Zero objects and
zero short exact sequences are included in the unrestricted quantifier over
`ShortComplex A`. The classes are arbitrary abelian categories, with no
characteristic or finiteness assumptions. The morphism universes `v₁`, `v₂`
and object universes `u₁`, `u₂` are unrestricted.

Searches for an existing declaration:

- `msearch leanfinder "cohomological delta functor additive functors indexed by
  natural numbers with connecting maps for short exact sequences natural and
  exact, morphisms and universal extension"`: only connecting maps and long
  sequences for particular examples; no general delta-functor structure.
- `msearch loogle "CategoryTheory.DeltaFunctor,CategoryTheory.CohomologicalDeltaFunctor,
  CategoryTheory.UniversalDeltaFunctor"`: no match.
- `msearch grep "delta.?functor|DeltaFunctor|UniversalDelta" CategoryTheory`:
  only a comment in `Monoidal/Tor.lean` suggesting future axiomatization.
- `rg "delta.?functor|DeltaFunctor|CohomologicalDelta|UniversalDelta"` in
  the source `WeilConjectures` and project `lean/Sheaf`: no match.
- `grep -rn "def-weil-pbc-delta-functor"` in source `WeilConjectures`: no match.

The server single-file compile succeeded with no warnings.

## Second reading by G1

Read the node against Stacks Project, Homology 010Q-010S and the Lean module.
The source assumes only that A and B are abelian categories.

- Categories A and B: `A : Type u₁`, `B : Type u₂`, their explicit category
  instances and `[Abelian A] [Abelian B]` match `def-sp-abelian` and 010Q.
  The four universe levels are unrestricted; no size, finiteness, or
  characteristic condition is added.
- Data (a), one additive functor in every nonnegative degree: `F : ℕ → A ⥤ B`
  and `additive : ∀ n : ℕ, (F n).Additive`. This is exactly the Mathlib
  `Functor.Additive` recorded by `def-weil-pbc-additive-functor`.
- Data (b), a connecting arrow for every short exact sequence including its
  two maps and every degree: `delta` quantifies `S : ShortComplex A`, a proof
  `S.ShortExact`, and `n : ℕ`; its codomain is `F n S.X₃ ⟶ F (n+1) S.X₁`.
  Mathlib's `ShortComplex.ShortExact` includes exactness, mono `S.f`, and epi
  `S.g`, as required by `def-weil-pbc-exact-sequence`.
- Axiom (1), initial exactness: `mono_zero` gives exactness at `F⁰(A)` after
  the zero map. `exact_middle`, `exact_right`, and `exact_left` give exactness
  at `Fⁿ(B)`, `Fⁿ(C)`, and `Fⁿ⁺¹(A)` respectively, for every `n : ℕ`.
  Each existential supplies the zero composite needed by `ShortComplex.mk`
  and asserts `ShortComplex.Exact`; these are precisely all positions of the
  one-sided long sequence.
- Axiom (2), naturality: `naturality` quantifies two short exact complexes,
  their proofs, a morphism `φ : S ⟶ T`, and every `n : ℕ`. The morphism has
  components `φ.τ₁`, `φ.τ₂`, `φ.τ₃` and commuting squares for both maps.
  Its equality is the node's connecting-map square, in Lean composition order.
- Morphisms of delta-functors: `Hom.app : ∀ n : ℕ, F.F n ⟶ G.F n` is a
  family of natural transformations; `Hom.naturality` is their compatibility
  with every connecting map of every short exact complex and every degree.
- Universality: `IsUniversal` quantifies every `G` and every degree-zero
  natural transformation `t`, then uses `∃! φ : Hom F G, φ.app 0 = t`.
  The quantifier order and unique extension condition match 010S.

The `n = 0` case is present in every indexed field. Zero objects and zero
short exact complexes are included by the unrestricted `ShortComplex` binders.
No scheme or index set is involved in this definition; empty schemes and
empty index sets impose no additional case. There is no base ring or
characteristic assumption. The source's four universe levels remain free.

Independent searches: `msearch leanfinder "universal cohomological delta
functor natural transformations exact sequence"` found only connecting maps
for particular derived, homology, or triangulated functors; `msearch loogle
"CohomologicalDeltaFunctor"` found no declaration; `msearch grep "universal
delta functor|cohomological delta functor|DeltaFunctor"` found none. An `rg`
search of the source `WeilConjectures`, project `lean/Sheaf`, and Mathlib's
category theory files found references to derived functors and a comment
proposing a delta-functor axiomatization, but no general delta-functor
definition, morphism, or universality predicate.

No mathematical mismatch was found, so the Lean module and node record needed
no change. The preflight's signature convention excludes the terminal `where`;
the original node record already used that convention. The single-file
compile completed without warnings.
