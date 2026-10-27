## Worker report

The module `Sheaf.RingTheory.StandardGradedVertexDimension` states
`GradedAlgebra.IsStandard.exists_isMaximal_irrelevant_ringKrullDim_eq`.
Its only postponed proof is this theorem's `sorry`. No definitions, new nodes,
dependency replacements, or statement corrections are needed.

Hypothesis and conclusion correspondence:

- The scalar field is `{k : Type u} [Field k]`.
- The commutative k-algebra is `{S : Type v} [CommRing S] [Algebra k S]`.
  The two universes are independent and explicitly bound.
- The nonnegative direct-sum grading is `(𝒜 : ℕ → Submodule k S)` with
  `[GradedAlgebra 𝒜]`. This supplies the unique finite homogeneous decomposition,
  the unit in degree zero, and multiplication into the sum of degrees.
- Finitely many degree-one generators are `[GradedAlgebra.IsStandard 𝒜]`:
  `fg_one` makes degree one finitely generated over k, and `adjoin_one`
  says it generates the entire algebra. This is exactly equivalent to a finite
  family of degree-one algebra generators.
- The clause `S₀ = k` is expressed by the preceding hypotheses and
  `[Nontrivial S]`: `GradedAlgebra.IsStandard.grade_zero_eq_one` identifies
  `𝒜 0` with `1 : Submodule k S`, the image of k, and the algebra map from
  the field is injective because S is nontrivial. Conversely, the source's
  actual equality S₀=k forces S nontrivial. The upstream IsStandard class
  alone allows the zero ring; the explicit Nontrivial instance rules out
  precisely that case, which the source already excludes. No domain or
  reducedness condition has been introduced.
- The irrelevant ideal is `(HomogeneousIdeal.irrelevant 𝒜).toIdeal`.
  Mathlib defines it as the kernel of the degree-zero projection, and
  `irrelevant_eq_iSup` identifies its additive monoid with the positive-degree
  sum. It is the node's S_+, not a chosen maximal ideal.
- Maximality is the conclusion's existential witness
  `∃ (_ : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.IsMaximal), ...`.
  Its class-typed binder supplies the prime instance needed to form the
  localization. Maximality is proved as part of the conclusion, not assumed.
- Localization is Mathlib's `Localization.AtPrime` at this same ideal.
- The remaining clause is literally
  `ringKrullDim (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal) =
  ringKrullDim S`. Both dimensions lie in Mathlib's `WithBot ℕ∞`.
- There is no positive-dimension restriction, infinite-field restriction,
  reducedness restriction, or integral-domain restriction on S.

Statement dependencies read and used:

- def-weil-field: Mathlib.Algebra.Field.Defs, `Field`.
- def-pc-standard-graded-algebra:
  WeilConjectures.RingTheory.GradedAlgebra.Standard,
  `GradedAlgebra.IsStandard`, `grade_eq_pow`, `grade_zero_eq_one`,
  and `finite_grade`; their signatures and docstrings were read.
- def-weil-pbc-localization-at-prime:
  Mathlib.RingTheory.Localization.AtPrime.Basic, `Localization.AtPrime`.
- def-weil-pbc-krull-dimension-ring:
  Mathlib.RingTheory.KrullDimension.Basic, `ringKrullDim`.

The irrelevant-ideal definition comes through the standard-grading module from
Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal, `HomogeneousIdeal.irrelevant`.
It is already a clause of def-pc-standard-graded-algebra, so needs no new node.

All stated proof dependencies are imported privately (except the standard
algebra interface, which the statement needs publicly):
Mathlib.RingTheory.GradedAlgebra.Radical (`Ideal.IsPrime.homogeneousCore`, with
`HomogeneousIdeal.isHomogeneous` and `Ideal.toIdeal_homogeneousCore_le` from its
imports); WeilConjectures.RingTheory.DimensionAtPointComponents
(`AlgebraicGeometry.dimension_at_point_components`);
WeilConjectures.Topology.DimensionSupremumLocalDimensions
(`topologicalKrullDim_eq_iSup_topologicalKrullDimAt`);
Mathlib.RingTheory.Spectrum.Prime.Topology
(`PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`). The four proof steps
from the DAG, including all named inputs, are retained in the theorem docstring.

Source read: literature/stacks-project/algebra.tex, lemma-dimension-graded
(Tag 00P6), lines 28402 onward, especially the first equality paragraph of its
proof; also lemma-smear-out and lemma-graded-ring-minimal-prime (00JT, 00JU).
The delivery states only maximality and the localization-dimension equality,
not the extra Hilbert polynomial assertions of 00P6.

Edge cases checked mathematically before writing:

- S=k with zero degree-one part: the empty generator family is allowed,
  the irrelevant ideal is zero, its localization is k, and both dimensions are 0.
- S=k[x]/(x²): nonreduced is allowed, the irrelevant ideal is (x), and
  both dimensions are 0. Nontrivial does not require reducedness.
- S=k[x,y]/(xy): multiple components and zero divisors are allowed;
  the vertex meets both components, and both dimensions are 1.
- S=k[x,y,z]/(xy,xz): components of different dimensions are allowed;
  the vertex sees the maximum, namely 2, on both sides.
- Finite fields are included because no cardinality assumption is present.
- The zero ring is excluded exactly by the source's S₀=k with k a field,
  not by a new geometric hypothesis. The upstream IsStandard predicate
  on its own would not enforce this clause.

Searches performed for an existing exact statement:

- msearch.py leanfinder, query "The localization of a finitely generated
  standard graded algebra over a field at its irrelevant maximal ideal has
  the same Krull dimension as the algebra": eight hits, including
  IsLocalization.AtPrime.ringKrullDim_eq_height and general localization
  dimension bounds, but none establishes attainment at the irrelevant ideal.
- msearch.py loogle, query `"ringKrullDim", "irrelevant"`: zero hits.
- msearch.py grep, query
  `ringKrullDim.*(irrelevant|homogeneous|graded)|(irrelevant|homogeneous|graded).*ringKrullDim`:
  zero Mathlib hits.
- rg with the same expression and `vertex.*dimension|dimension.*vertex`
  over lean/WeilConjectures and lean/Sheaf: no relevant theorem; only
  unrelated mentions of vertices in simplicial material.
- grep -rn of the exact node id in lean/WeilConjectures: no matches.
- rg for `ringKrullDim_irrelevant|isMaximal_irrelevant|vertex_dimension`
  in dag/lean_names_upstream.json, Mathlib, WeilConjectures and Sheaf: no matches.
- rg for `irrelevant|IsStandard` found the existing standard-grading class,
  Mathlib's irrelevant ideal, and unrelated linear-pair and Hilbert-function
  results. These existing definitions are reused rather than duplicated.

No disputed statement or unresolved node fault was found.

## Second reading by NV

A separate rereading of the node and completed module checked every binder
and the two conclusions against the source. In particular, IsStandard alone
would permit the zero algebra, whereas S₀=k in the node requires the scalar
field to embed. `[Nontrivial S]` supplies exactly this missing part of the
encoding, together with upstream grade_zero_eq_one. The existential maximality
witness is a conclusion and simultaneously enables the AtPrime expression;
no prime or maximality hypothesis is being smuggled into the assumptions.
The dimensions use the whole ring and its vertex localization in the stated
order. The examples above cover dimension zero, nilpotents and unequal
component dimensions. No change to the DAG statement was necessary.
This is an in-session second pass; no other worker was started, as the dispatch
brief prohibits starting other agents. The maintainer supplies independent review.
