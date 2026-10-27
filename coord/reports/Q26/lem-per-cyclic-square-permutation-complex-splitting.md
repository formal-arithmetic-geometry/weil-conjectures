## Worker report

The module `Sheaf.RepresentationTheory.CyclicSquarePermutationComplexSplitting`
states `Rep.CyclicSquare.permutationComplex_splitting`. Its sole postponed
proof is this named theorem, with the entire six-step DAG proof in its docstring.
All helper definitions contain actual data; no existence choice defines an object.

Clause-by-clause correspondence:

- The prime is `ℓ : ℕ` with `[Fact ℓ.Prime]`. The coefficient ring is exactly
  `ZMod ℓ`, the prime field, not an arbitrary ring of characteristic ℓ.
- `C` is `Multiplicative (ZMod (ℓ ^ 2))`: the type tag only writes the original
  additive group multiplicatively for `Rep`'s group interface. Its generator is
  `Multiplicative.ofAdd 1`, the additive element one, not the multiplicative identity.
  `Q` is `ZMod ℓ`. `reduction ℓ` is `ZMod.castHom`, with the divisibility
  `ℓ ∣ ℓ ^ 2`, so it is precisely reduction. The imported ZMod topology is discrete,
  and the type tag inherits that topology.
- The ambient category is the dependency's actual
  `Rep.DiscreteContinuousRep.{0,0,0} (ZMod ℓ) (Multiplicative (ZMod (ℓ ^ 2)))`.
  Thus objects are linear representations with open point stabilizers and morphisms
  are equivariant linear maps, not a private replacement category. Modules here
  live in the ordinary small coefficient universe; the derived morphism universe
  is the explicit arbitrary `w` of `[HasDerivedCategory.{w} ...]`.
- `translation ℓ` has underlying module `ZMod ℓ → ZMod ℓ` and sends `h,q` to
  `h (q - reduction ℓ c.toAdd)`, exactly the stated action. `permutationModule ℓ`
  bundles this representation in the recorded discrete category; `isOpen_discrete`
  supplies its actual open-stabilizer proof.
- `differential ℓ` is `ObjectProperty.homMk` of
  `applyAsHom (Multiplicative.ofAdd 1) - 𝟙 _`, literally τ minus identity.
- `permutationComplex ℓ` uses Mathlib's `HomologicalComplex.double` at integer
  indices zero and one. Its terms there are the specified module and its only
  potentially nonzero differential is the specified differential; all other terms
  and maps are zero. The abelian structure is explicitly carried through the zero
  morphism instance, to match the derived category's complex type.
- `DerivedCategory.Q.obj` localizes this actual cochain complex. The target is the
  binary biproduct of `DerivedCategory.singleFunctor ... 0` applied to
  `trivialModule ℓ` and its cohomological shift by `(-1 : ℤ)`. The latter occupies
  degree one under Mathlib's cohomological convention.
- `Nonempty (K ≅ ...)` asserts existence only, and only in the derived category.
  It chooses no canonical isomorphism and asserts no isomorphism of complexes.
- The `[Abelian ...]` and `[HasDerivedCategory.{w} ...]` parameters supply the
  category structure and chosen localization required by the recorded derived
  category dependency. The former is provided for this finite discrete group by
  the proof dependency `Rep.discreteRep_abelian_structure`; it is not an additional
  mathematical restriction on the prime or coefficients.

Dependency declarations read and used:

- `WeilConjectures.RepresentationTheory.DiscreteContinuousRep`,
  `Rep.DiscreteContinuousRep`: full subcategory of `Rep` with open stabilizers.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.singleFunctor`:
  the recorded ordinary derived category, localization and degree-zero objects.
- The stated proof dependency `Sheaf.RepresentationTheory.DiscreteRep`,
  `Rep.discreteRep_abelian_structure`, is a plain proof import. Its full signature
  and docstring were read: finite coefficient rings and profinite groups admit
  the abelian structure with underlying-module kernels, cokernels and exactness.
- Mathlib's `Rep.applyAsHom`, `Rep.trivial`, `ObjectProperty.homMk`,
  `HomologicalComplex.double`, and `ZMod.castHom` give the existing constructions.

Sources read: the node's complete statement and six-step proof; both statement
nodes' full signatures and docstrings; the abelian-structure proof dependency;
ILO XVI printed pp.247--248 (PDF pages 253--254), especially the root tower and
last permutation-module paragraph after Lemma 3.4.9; the current blueprint
`lem-per-artin-gabber-affine-curve.md`. The finite roof is the node's explicit
agent-formulated refinement, not a purported verbatim theorem of ILO.

Edge cases checked mathematically: ℓ = 2 is retained and the same fibre-sum
argument kills constants since each fibre has exactly ℓ elements. The generator
is additive one, not additive zero. Constant functions form H⁰, and summation
identifies H¹ with the trivial coefficient module; these identifications alone
would not assert the desired derived splitting, hence the actual derived iso is
stated. Degrees outside 0 and 1 vanish by the existing double construction.
Primality excludes 0 and 1, but imposes no oddness or extra invertibility. No
choice of a splitting of the original complex is assumed. All variables and
universes are explicitly bound.

Searches actually run:

- `msearch.py ... leanfinder`: “The two term cyclic permutation representation
  complex tau minus one over F p splits in the derived category after inflation
  from Z modulo p to Z modulo p squared”. Eight hits: periodic resolutions,
  their augmentation maps, and mapping-cone degreewise splittings; none states
  the inflated two-term splitting. `Rep.FiniteCyclicGroup.resolution_quasiIso`
  concerns the entire infinite periodic resolution, a different complex.
- `msearch.py ... loogle`: `Rep.FiniteCyclicGroup.resolution, QuasiIso`.
  Successful service, zero hits.
- `msearch.py ... grep`:
  `permutation.*(complex|split)|inflation.*split|cyclic.*splitting`.
  Three unrelated number-field/Kummer hits, no match.
- `msearch.py ... leansearch`: “For a cyclic group of order p squared the
  inflated permutation complex Map Z mod p F p with differential generator
  minus one splits in the derived category”. Eight hits, including the periodic
  cyclic resolution and generic short-complex splitting; no exact match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`:
  `cyclic.*(splitt|permutation)|permutation.*(complex|splitt)|CyclicSquare|cyclicSquare`.
  Hits only in unrelated Koszul diagonal, root-cover and tame-extension modules.
- The item id was searched in `lean/WeilConjectures` with no hits. The new
  namespace and theorem name were searched in `dag/lean_names_upstream.json`,
  Mathlib, `lean/WeilConjectures`, and `lean/Sheaf`, with no conflicts.
- Mathlib source grep found `HomologicalComplex.double` and its exact two-term
  description; its full definition and `double_d`/zero-outside-support API were
  read. Source search found `Rep.applyAsHom`, avoiding a custom equivariance proof.

No statement correction, disputed clause, dependency repair or new DAG node.
The helpers are the very objects introduced in this item's statement, with
source and blueprint docstrings and inclusion in `lean.declarations`.

## Second reading by Q26

The dispatcher prohibits starting another agent, and the maintainer independently
reviews this delivery. This is a separate self-review, not a claim of independent
worker review. Re-read the item and the entire module together. Confirmed the
negative translation sign, the actual reduction from ℓ² to ℓ, the additive-one
generator, the full discrete subcategory, and the derived (not just cohomology)
isomorphism. Confirmed the right summand alone is shifted by -1 and the theorem
asserts existence only. The compiler exposed a mismatch between the canonical
full-subcategory zero morphisms and those inherited from a supplied abelian
structure; the complex constructor and its use carry the same structure
explicitly. No node statement or dependency meaning was changed.
