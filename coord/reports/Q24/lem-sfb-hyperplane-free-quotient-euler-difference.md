## Worker report

The module `Sheaf.AlgebraicGeometry.HyperplaneFreeQuotientEulerDifference` states
`AlgebraicGeometry.ProjectiveSpace.hyperplane_free_quotient_euler_difference`.
It introduces no definitions and leaves exactly the requested theorem proof as `sorry`.
The statement and proof plan were read against Stacks varieties.tex, Tags 08AG
(lines 6854 onward), 089Z (6455 onward), 08A0 (6496 onward) and 0EGK (6563 onward).
The current blueprint unit `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
is the six-functor stability unit; this item is a supporting geometric lemma, not
that unit's own statement.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Field k | `(k : Type u) [Field k]`, with no characteristic or infinitude restriction. |
| n >= 1 and r >= 1 | `(n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r)`. |
| X = projective n-space over k | `ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))` throughout. The lifted index set has exactly n+1 coordinates in the scheme universe. |
| K and F coherent | `K F : X.Modules` and `hK`, `hF : RingedSpace.IsCoherent X.toRingedSpace ...`. This is the exact finite-type plus finite-type-kernel definition, not only the quasi-coherent finite-type conjunction. |
| The free middle sheaf O_X^r | `SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))`. |
| The given short exact sequence | Maps `a`, `b`, their zero composite `w`, and `(ShortComplex.mk a b w).ShortExact`. The free sheaf's coherence follows from the projective-space setting. |
| E(d) = E tensor O(d) | All twists are the recorded `ProjectiveSpace.twist`; module twists are `E ⊗ twist ... d`. |
| Nonzero linear section | `s : Γ(twist ... 1, ⊤)` and `hs : s ≠ 0`. For projective space this is exactly a degree-one linear section. |
| Multiplication injective for all integer twists | `hinj : ∀ d : ℤ, Mono (regularHyperplaneMultiplication k n F d s)`. This is the recorded actual multiplication from F(d) to F(1+d). Substituting d=D-1 gives precisely the node's F(D-1) to F(D), with no degree omitted. |
| Hyperplane H = V(s) and its closed immersion | `H : Scheme.{u}`, `i : H ⟶ X`, `[IsClosedImmersion i]`, and `hH : i.ker = Scheme.Modules.Hom.zeroLocus (Scheme.Modules.homOfGlobalSection _ s)`. Equality of ideal sheaves specifies the scheme structure, not only the support. Both source and target of the section map are invertible, as required by zeroLocus. |
| Fixed identification H with projective (n-1)-space over k | `e : H ≅ ℙ(ULift.{u} (Fin ((n - 1) + 1)); Spec (.of k))`; `[H.Over ...]`, `[i.IsOver ...]`, `[e.hom.IsOver ...]` encode the compatible k-structure already present in the source. They do not impose another geometric condition: H has the induced structure through i, and the fixed identification is over k. |
| The identification carries all restricted twists to standard twists | `htwist : ∀ d : ℤ, Nonempty ((tensorPullback i).obj (twist ... d) ≅ (tensorPullback e.hom).obj (twist ... d))`. Every integer, including negative and zero, occurs. |
| K_H and F_H are i^*K and i^*F and are coherent | First two conclusion conjuncts are `RingedSpace.IsCoherent H.toRingedSpace ((tensorPullback i).obj K)` and the same for F. No separate arbitrary restricted module is introduced. |
| The canonical restricted sequence is short exact | Third conjunct gives its zero composite `wH` and `ShortExact` for the actual maps `(tensorPullback i).map a` and `(tensorPullback i).map b`. Fourth conjunct identifies its middle object `(tensorPullback i).obj (free ...)` with `free (R := H.ringCatSheaf) ...`. Transporting the middle object by this isomorphism writes exactly the displayed O_H^r row. The arrows themselves are tensor pullbacks of the specified original arrows; no arbitrary map replaces either. Exactness is independent of the particular middle-object isomorphism, so no extra normalization hypothesis is needed. |
| Euler difference in every integer degree | Fifth conjunct is integer equality `eulerChar k (i^*F ⊗ i^*O_X(d)) = eulerChar k (F ⊗ O_X(d)) - eulerChar k (F ⊗ O_X(d-1))`. The htwist assumption identifies the first twist with O_H(d). |
| Polynomial consequence for every P in Q[t] | Final conjunct quantifies `P : Polynomial ℚ`, assumes the integer Euler values cast to Q equal `P.eval (d : ℚ)` for every integer d, and concludes the corresponding equality with `P.eval (d : ℚ) - P.eval ((d : ℚ) - 1)` for every integer d. |

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field` in `Mathlib.Algebra.Field.Defs`.
- `pqf-def-coherent`: publicly imports `Sheaf.AlgebraicGeometry.CoherentFiniteType`,
  whose public `WeilConjectures.AlgebraicGeometry.Coherent` import exposes the exact
  `AlgebraicGeometry.RingedSpace.IsCoherent`. The landed conjunction
  `Scheme.Modules.IsQuasiCoherentFiniteType` is intentionally not used as coherence.
- `def-pc-projective-space-twist`: `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`,
  `AlgebraicGeometry.ProjectiveSpace.twist`.
- `pqf-def-cohomology`: `WeilConjectures.AlgebraicGeometry.PQFCohomology`,
  `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages` and the public
  `RingedSpace.moduleCohomology` interface. No third cohomology is defined.
- `def-pc-euler-characteristic`: `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`,
  `AlgebraicGeometry.Scheme.Modules.eulerChar`. It is the alternating finrank sum
  on the actual k-scheme. Coherence and properness here ensure the intended finite
  sum interpretation, including on H through its fixed projective identification.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`.
- `def-pc-module-pullback`: `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`,
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`, the actual inverse-image and
  tensor extension-of-scalars construction exposed by the recorded module.
- Added already-landed definition dependency `def-sfb-regular-hyperplane-restriction-maps`:
  `Sheaf.AlgebraicGeometry.CoherentRegularHyperplaneRestriction`,
  `AlgebraicGeometry.ProjectiveSpace.regularHyperplaneMultiplication`, with its
  full section-based signature read from the source. This is a real existing definition.
- Added already-landed definition dependency `def-pc-zero-scheme`:
  `WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus`,
  `AlgebraicGeometry.Scheme.Modules.Hom.zeroLocus`, read with its invertibility
  warning and its affine ideal formula. The invertibility requirement holds here.

The modules recorded for every already-stated proof dependency are imported as
plain proof imports; statement dependencies are public imports. In particular the
coherent criterion, pullback quasi-coherence and finite type, closed-immersion
quotient, stalk exactness, closed-immersion cohomology, Proj properness and Euler
additivity modules are retained for the node's documented proof route. The theorem's
docstring gives all six proof steps, including the local A intersect aB = aA
calculation and the substitution in two adjacent integer degrees.

Edge cases checked before writing:

- n=1 gives H identified with P^0, not an empty coordinate set; n=0 is excluded
  exactly as in the node. The subtraction n-1 is natural subtraction under hn.
- r=1 is allowed; r=0 is excluded exactly as in the node.
- F=0 is allowed (K is the free sheaf), with all Euler values zero. K=0 and a
  free quotient F are also allowed. No nonzero sheaf hypothesis is imposed.
- The field can be finite and of any characteristic. No existence-of-a-regular-section
  theorem over an infinite field is assumed; the section and its injectivity are given.
- Zero, positive and negative twists all occur. The d,1+d indexing is bijective
  with the D-1,D indexing over integers.
- Arbitrary nonzero scalar rescaling of s preserves its zero scheme and injectivity.
- The polynomial can be zero or constant, and values are compared in Q by the
  canonical embedding of integer Euler characteristics. No eventual-only condition
  replaces the hypothesis for all integer degrees.
- H is retained as the actual closed subscheme with an identification, rather than
  replacing the canonical immersion by an unconstrained scheme map.

Searches (2026-10-24):

1. `msearch.py ... leanfinder "Restricting a coherent free quotient to a regular hyperplane gives an exact sequence and Euler characteristic finite difference"`:
   eight results, including `QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last`
   and `ModuleCat.free_shortExact_finrank_add`. These only concern module quotient
   exactness or free-module ranks; none states the geometric and Euler clauses together.
2. `msearch.py ... loogle '"eulerChar", "ShortExact"'`: zero results.
3. `msearch.py ... grep 'hyperplane|eulerChar' AlgebraicGeometry`: zero Mathlib results.
4. `msearch.py ... leansearch "For coherent sheaves on projective space, restriction to a regular hyperplane has Euler characteristic equal to the difference in adjacent twists"`:
   eight results on Proj restrictions, `IncidenceAlgebra.eulerChar`, and global-sections
   restriction. No matching coherent hyperplane Euler theorem.
5. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for hyperplane/Euler combinations,
   `hyperplane_free_quotient`, and the item id: no existing statement. The item-id
   search in `dag/lean_names_upstream.json` also finds no declaration.
6. `rg` in the project and DAG found the existing regular hyperplane multiplication
   definition and its owning definition node, and the existing zeroLocus definition
   and node. `tools/blueprint_refs.py search 'zero scheme'` confirms the zero-scheme
   node. These are reused, with no new node and no duplicate notion.

No statement correction, disputed statement, new definition node, or dependency
repair is required. Only lean and additions of the two landed definition dependencies
change in the item copy.

Compilation: every compiler invocation used the authorized scompile.py wrapper.
The initial `ShortComplex.map` presentation required a missing typeclass instance
for preservation of zero maps by the tensor pullback functor. The final statement
instead explicitly existentially binds the zero-composite proof for the two actual
pulled-back maps; it adds no hypothesis and changes none of the mathematical data.
The final per-file compile and the delivery dry run are recorded below.

## Second reading by Q24

A separate reading pass in this worker session compared the final node and source
file; no other agent was started, as required by the dispatcher. The maintainer's
independent review remains separate. This pass checked the hypothesis and clause
correspondence above, especially the exact coherence predicate, the d versus 1+d
indexing, the definition of the scheme structure by i.ker, both base compatibilities,
and the two independent conclusion conjuncts identifying the free middle object
and asserting exactness of the actual pulled-back arrows. The polynomial clause
compares rational evaluations with cast integer Euler values and retains every
integer degree. The only change found during compilation was the zero-composite
proof presentation described above. No mathematical hypothesis or conclusion was
changed. No new definitions or dependency modules need a second comparison.

Validation completed: scompile.py exited successfully for both sandbox and library
module modes, with no compiler messages. deliver2.py --no-push printed
`OK (dry run): commit 31a6ba4ca95 passes the preflight and compiles; nothing pushed`.
The delivered Lean file has no line exceeding 100 characters and exactly one sorry.
A direct JSON comparison confirms only `lean` and `stmt_deps` changed.
