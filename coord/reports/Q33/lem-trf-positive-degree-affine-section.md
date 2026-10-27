## Worker report

The module `Sheaf.AlgebraicGeometry.PositiveDegreeAffineSection` states
`AlgebraicGeometry.Scheme.Modules.exists_nonzero_section_affine_of_degree_pos`.
Its sole proof is `sorry`; it introduces no definitions, extra hypotheses, or new nodes.
The item's JSON changes only in `lean`.

Source read: `literature/stacks-project/varieties.tex`, Tag 0B5X,
`lemma-ample-curve`, lines 10016–10036: the second proof paragraph beginning
“Assume degree positive”, ending with the existence of a nonzero section with
affine nonvanishing locus. This is the supporting conclusion isolated by the node,
not the whole ampleness equivalence. The six-step DAG proof is recorded in the
theorem's docstring, including finite boundary residue fields and the evaluation
kernel argument.

Hypotheses and clauses, checked against the unchanged node:

| Node text | Lean rendering |
| --- | --- |
| A field k | `(k : Type u) [Field k]` |
| C a scheme over k | `{C : Scheme.{u}} [C.Over (Spec (.of k))]` |
| C integral | `[IsIntegral C]` |
| C proper over k | `[IsProper (C ↘ Spec (.of k))]` |
| Topological Krull dimension exactly one | `(hdim : topologicalKrullDim C = (1 : WithBot ℕ∞))` |
| An invertible O_C-module N | `(N : C.Modules) [N.IsInvertible]` |
| deg_k(N) = chi(N) - chi(O_C) > 0 | `(hdeg : 0 < N.degree k)`; the recorded `degree` definition is exactly that difference |
| An integer n >= 1 | `∃ n : ℕ, 1 ≤ n`; positive integers and positive natural numbers have the same exponents |
| A global section of N tensor-power n | `∃ s : (N.tensorPow n).val.presheaf.obj (Opposite.op ⊤)` |
| s nonzero | `s ≠ 0` |
| Its nonvanishing open C_s is affine | `∃ U : C.Opens, IsAffineOpen U ∧ (U : Set C) = nonvanishingLocus (N.tensorPow n) s` |

The equality of sets fixes U to the actual nonvanishing locus; U is not an
arbitrarily supplied affine neighbourhood or a subset of that locus. Existence
of this open simultaneously expresses openness and affineness of C_s. The tensor
power is the library's sheafified O_C tensor power. Its zero power is the structure
module, and its positive powers represent the node's tensor powers up to the
canonical unit, associativity and symmetry isomorphisms.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (line 180).
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`
  (lines 237–244), including nonemptiness and the integral-domain condition.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`
  (lines 40–42), with separatedness, universal closedness and locally finite type;
  universal closedness supplies quasi-compactness and hence finite type.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim` (lines 35–40),
  the supremum of lengths of irreducible closed chains.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` (lines 55–64) and
  `AlgebraicGeometry.Scheme.Modules.tensorPow` (lines 153–158).
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`:
  `AlgebraicGeometry.Scheme.Modules.degree` (lines 275–286), the difference of
  the two Euler characteristics over the given structure morphism.
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus` (lines 29–40), whose
  stalk condition is exactly outside maximalIdeal times the stalk module.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  the recorded `SheafOfModules.cochainModulesMonoidal` interface for the existing
  tensor product is publicly imported. The scheme tensor powers themselves are
  the existing `Scheme.Modules.tensorPow`; no second tensor is defined.

The stated proof-dependency modules are plain imports, including
`WeilConjectures.Mathlib.Topology.KrullDimension` (finite complement and closed
boundary points), `WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`,
`Sheaf.AlgebraicGeometry.CurveDegreeTensorAdditive`,
`WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharProper`,
`WeilConjectures.AlgebraicGeometry.PQFCohomology`, and
`WeilConjectures.AlgebraicGeometry.AffineCapSectionOpen`.
Mathlib proof inputs are imported from Noetherian, AffineScheme, FiniteType,
ResidueField and Jacobson.Ring. The proof-only node
`lem-trf-proper-field-invertible-coherent` has no recorded declaration in the
read snapshot; its future module is consequently not guessed or imported.
It is not needed to type this theorem's statement.

Edge cases checked before writing:

- Empty C is excluded by integrality itself; the statement adds no separate
  nonempty or inhabited assumption. Dimension is exactly one, so a point scheme
  is not accidentally admitted.
- The field may be finite, imperfect, or not algebraically closed. No smoothness,
  geometric integrality, or H^0(O_C) = k assumption appears.
- The zero section is explicitly excluded. Degree zero and negative degree do
  not meet `hdeg`; the trivial line bundle has degree zero.
- Exponent zero is excluded by `1 ≤ n`, and exponent one is allowed. Using a
  natural exponent loses no positive integer exponent.
- The proof's finite boundary may be empty, and boundary points need not be
  k-rational. The dimension argument uses the sum of residue-field degrees,
  not the number of points. Negative chi(O_C) is handled by B + |a| + 1.
- The universe u is arbitrary; the statement follows the existing degree API's
  common universe for the base field, scheme and scheme modules.

Searches actually performed, all on 2026-10-24:

1. `msearch.py ... leanfinder` with query “On a proper integral curve over a
   field a positive degree invertible sheaf has a nonzero section of a positive
   tensor power with affine nonvanishing locus”: eight hits on affine basic-open
   restriction, powers clearing denominators, and residue evaluation. No match.
2. `msearch.py ... loogle` with query
   `AlgebraicGeometry.Scheme.Modules.degree, AlgebraicGeometry.Scheme.Modules.nonvanishingLocus`:
   zero hits, unknown identifier `AlgebraicGeometry.Scheme.Modules.degree`
   (the remote Mathlib search does not index this project definition).
3. `msearch.py ... grep` with query `degree.*pos|nonvanishingLocus|IsAmple`,
   subdirectory `AlgebraicGeometry`: six unrelated hits on division-polynomial
   degrees in elliptic curves. No match.
4. `msearch.py ... leansearch` with query “positive degree line bundle on proper
   integral curve has nonzero section with affine nonvanishing locus”: eight
   hits on basic opens, evaluation and integral affine schemes. No match.
5. `rg -n 'lem-trf-positive-degree-affine-section' lean/WeilConjectures`:
   no hit. Searches of `dag/lean_names_upstream.json` and of both
   `lean/WeilConjectures` and `lean/Sheaf` for positive degree, affine sections,
   `nonvanishingLocus`, and the proposed declaration name found no exact theorem.
   Opened the relevant candidate sources, including
   `WeilConjectures/AlgebraicGeometry/Curve/RiemannRoch.lean` and
   `Sheaf/AlgebraicGeometry/ProperIntegralCurveAmpleDegree.lean`.
   The first gives smooth-curve ampleness with `GlobalSectionsBijective`, and
   the second states the full ampleness equivalence, not the isolated existence
   conclusion. It is a consumer of this argument, so it is not imported as an input.

No statement correction, dependency repair, or mathematical dispute was needed.

## Second reading by Q33

Written by the maintainer's independent second reader (NT-cc review of delivery
7669a991). It replaces the delivered self-check, which said that the independent
review was left to the maintainer. The Worker report above is unchanged.

Source: Stacks `varieties.tex`, Tag 0B5X (`lemma-ample-curve`), lines 10016–10036,
with "Assume deg(L) > 0" leading to "we can find an n > 0 and a nonzero section
s ∈ H^0(X, L^{⊗n}) such that X_s is affine". The node is unchanged and was read
against this paragraph.

| Node clause | Lean | Verdict |
| --- | --- | --- |
| k a field (def-weil-field) | `(k : Type u) [Field k]` | exact |
| C integral (def-pc-integral-scheme) | `[IsIntegral C]` (Mathlib; includes Nonempty) | exact |
| proper over k (def-weil-proper-morphism) | `[C.Over (Spec (.of k))] [IsProper (C ↘ Spec (.of k))]` | exact |
| topological Krull dim one (def-kun-...) | `topologicalKrullDim C = 1` | exact (equality, not ≤) |
| N invertible (def-sc-invertible-module) | `(N : C.Modules) [N.IsInvertible]` | exact |
| deg_k N = χ(N) − χ(O_C) > 0 (def-pc-degree-line-bundle) | `0 < N.degree k`; `Modules.degree` = `M.eulerChar k − eulerChar k (unit)` (EulerChar.lean:285) | exact |
| ∃ integer n ≥ 1 | `∃ n : ℕ, 1 ≤ n` | equivalent |
| nonzero s ∈ Γ(C, N^{⊗n}) (def-pur-sheaf-tensor-product) | `∃ s : (N.tensorPow n).val.presheaf.obj (op ⊤), s ≠ 0` | exact; `tensorPow` is the n-fold `⊗` of `SheafOfModules.monoidalCategory X.sheaf` (Invertible.lean), the sheafified tensor product, and is used by the def-weil-pbc-ample-invertible-module record itself |
| C_s affine (def-weil-pbc-ample-invertible-module) | `∃ U : C.Opens, IsAffineOpen U ∧ (U : Set C) = nonvanishingLocus (N.tensorPow n) s` | exact: the set equality pins U to C_s, and `nonvanishingLocus` is the recorded germ ∉ 𝔪_x·stalk predicate (Ample.lean) |

Edge cases. The empty scheme is excluded by IsIntegral. The finite boundary may
be empty (t = 0, so B = 0). Points need not be rational, and χ(O_C) may be negative
(n = B+|a|+1). k is arbitrary and no smoothness, geometric integrality or
H^0 = k assumption appears. n = 0 is excluded. The universe is the common `u` that the
`degree`/`eulerChar` API needs (k : Type u, C : Scheme.{u}), with no further restriction.

Searches. The worker's searches were reread. The trees `lean/Sheaf` and
`lean/WeilConjectures` of the live clone have no theorem with this conclusion.
`ProperIntegralCurveAmpleDegree` (the full 0B5X equivalence) and the smooth
Riemann–Roch ampleness consume this argument and do not duplicate it.

Records and imports. All stmt_dep lean records were read; every imported module
exists on the live tree, and none of them imports this new module. The proof is
`sorry` only, there are no definitions, and the docstrings carry the source place,
the blueprint id and the six proof steps.

Mismatches: none in the Lean or the node. The only change is this section.
