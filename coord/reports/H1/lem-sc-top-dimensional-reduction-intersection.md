## Worker report

The module `Sheaf.AlgebraicGeometry.TopDimensionalReductionIntersection` states
`AlgebraicGeometry.Scheme.Modules.intersectionNumber_topDimensionalReduction`, with only
`sorry` as proof. No definitions, new nodes, dependency modules, or statement corrections
are needed. The original node is changed only in `lean`.

Hypothesis and clause correspondence:

- The field is `(k : Type u) [Field k]`; the proper k-scheme is `(X : Scheme.{u})`
  with `[X.Over (Spec (.of k))]` and `[IsProper (X ↘ Spec (.of k))]`.
- The nonempty closed subscheme is `(Z : Scheme.{u}) [Nonempty Z]`,
  `(i : Z ⟶ X) [IsClosedImmersion i]`. Its dimension d is `(d : ℕ)` and
  `hd : topologicalKrullDim Z = ((d : ℕ∞) : WithBot ℕ∞)`.
- The finite list of all top-dimensional irreducible components, without repetition,
  is `components : Fin r ≃ {C : Set Z // C ∈ irreducibleComponents Z ∧
  topologicalKrullDim C = ((d : ℕ∞) : WithBot ℕ∞)}`. This is an equivalence, not just
  a covering family or an arbitrary subset of the components.
- The integral reduced induced structures are `Y : Fin r → Scheme.{u}` with
  `[∀ j, IsIntegral (Y j)]`, closed immersions `c : ∀ j, Y j ⟶ Z`, and
  `hc : ∀ j, Set.range (c j) = (components j).val`. An integral closed immersion
  with that range is precisely the reduced induced closed subscheme: reducedness
  forces the defining ideal to be radical. The inclusions into X are `c j ≫ i`.
- `hY` supplies the dimension d of each Y j, already stipulated in the node.
  It follows from `hc`, the dimension in `components`, and the homeomorphism of
  each Y j with its closed-immersion image. It is not an additional geometric restriction;
  it explicitly supplies the proof argument required by the existing intersection definition.
- The generic points are `ξ : Fin r → Z` and
  `hξ : ∀ j, IsGenericPoint (ξ j) (Set.range (c j))`. They are represented as
  points of Z, exactly where the stalk O_{Z,ξ_j} is taken; closed embeddings
  identify them with the generic points of Y j.
- The d invertible modules are `L : Fin d → X.Modules` and
  `[∀ a : Fin d, (L a).IsInvertible]`.
- The multiplicities are the unique natural numbers `m : Fin r → ℕ` such that
  `Module.length (Z.presheaf.stalk (ξ j)) (Z.presheaf.stalk (ξ j)) = (m j : ℕ∞)`.
  Existence is a conclusion, not a finiteness assumption. This expresses the node's
  definition of m_j, and `0 < m j` states that each is positive. It also keeps an
  infinite length from being silently converted to zero.
- The equality is `intersectionNumber k X Z i d hd L = ∑ j : Fin r,
  (m j : ℚ) * intersectionNumber k X (Y j) (c j ≫ i) d (hY j) L`.
  Rational coefficients are exactly the carrier of the recorded intersection number.
- The final clause quantifies over an invertible module A and assumes
  `IsAmple (X ↘ Spec (.of k)) A`. If every
  `selfIntersectionNumber k X (Y j) (c j ≫ i) d (hY j) A` is positive, it concludes
  `0 < selfIntersectionNumber k X Z i d hd A`. This is the stated all-L_i-equal
  ample consequence, with the repeated-module definition used unchanged.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.IntersectionNumber`:
  `AlgebraicGeometry.Scheme.Modules.intersectionNumber` and `selfIntersectionNumber`.
- `WeilConjectures.AlgebraicGeometry.Modules.Ample`: `AlgebraicGeometry.IsAmple`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` (available through the above imports).
- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.Topology.Sober`: `IsGenericPoint`.
- `Mathlib.RingTheory.Length`: `Module.length`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.

The theorem docstring carries both proof steps of the DAG node: the leading-term
Euler-polynomial comparison, including equality of lengths over the local ring and its
quotient, followed by positivity of the nonempty weighted sum. Also read the landed
`Sheaf.AlgebraicGeometry.NumericalPolynomialLeadingTerm.numericalPolynomial_leadingTerm`
(the declaration namespace is `AlgebraicGeometry.Scheme.Modules`), whose finite enumeration
and existential natural lengths guided this compatible encoding. It is a proof dependency,
so it is not imported just to state the theorem.

Edge cases checked before writing: d = 0 uses the empty list of modules and constant
coefficient; a zero-dimensional nonreduced scheme has generic length possibly larger than
one, which is retained. Empty Z is excluded by the node and `[Nonempty Z]`, not by an
unstated convention. The r = 0 enumeration cannot exist for a nonempty Noetherian Z of
finite dimension d: a finite set of components attains the maximal dimension, so the
positivity consequence does not accidentally use an empty sum. Lower-dimensional components
are excluded by the dimension subtype; components are not duplicated because `components`
is an equivalence. Non-equidimensional and nonreduced Z remain allowed. No separability,
algebraic closure, smoothness, characteristic, or reducedness hypothesis is imposed on Z.
Schemes and fields have explicit universe u; finite index sets impose no extra universe limit.

Searches made using `/home/ubuntu/weil-launcher/msearch.py`:

- leanfinder query `intersection numbers equal sum over top dimensional irreducible components
  weighted by generic stalk length`: eight hits, all zero-locus/ideal-sheaf infimum facts,
  no intersection-number component formula.
- loogle query `Module.length, IsGenericPoint`: zero hits.
- grep query `intersectionNumber|top_dimensional` in Mathlib `AlgebraicGeometry`: zero hits.
- leansearch query `intersection number sum irreducible components multiplicities`:
  service unavailable (Internal Server Error), recorded as unavailable, no verdict inferred.
- `rg -n 'intersectionNumber|top_dimensional|lem-sc-top-dimensional-reduction-intersection'`
  in the source repository and `lean/Sheaf`: only the landed intersection-number definition
  and its abbreviation, no component reduction theorem.
- `rg` for `intersectionNumber_topDimensionalReduction` in Mathlib, the source project,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no name collision.
- Read full signatures/docstrings of all statement dependencies, and nearby examples using
  generic points and stalk lengths to check carrier and point conventions.

Source checked directly at https://stacks.math.columbia.edu/tag/0BES (Lemma 33.45.6).
The local `literature/stacks-project/varieties.tex` is absent on this machine. The source's
length over O_{X,ξ} is equal to length over O_{Z,ξ} because O_{Z,ξ} is a quotient; the node
and its proof explicitly use this equality. No mathematical fault or disputed statement found.

Validation: `scompile.py H1 lem-sc-top-dimensional-reduction-intersection` compiled the
module cleanly on the server in 2.0 seconds, without errors or warnings.

## Second reading by H1

Independent verdict: the Lean statement says exactly what the node says. No mismatch
was found, and no Lean or node field was changed. This reading adds only this report
section and the independent search records.

I read the node and its source before checking the Lean. The local Stacks checkout is
absent, so I fetched the upstream `varieties.tex` into this item's scratchpad and read
`section-num`, `definition-intersection-number`,
`lemma-intersection-number-in-terms-of-components`, the leading-term lemma, and
`lemma-ample-positive`. These are [Tag 0BEP](https://stacks.math.columbia.edu/tag/0BEP),
[Tag 0BES](https://stacks.math.columbia.edu/tag/0BES),
[Tag 0BEN](https://stacks.math.columbia.edu/tag/0BEN), and
[Tag 0BEV](https://stacks.math.columbia.edu/tag/0BEV).
The section assumes proper schemes over a field, not algebraically closed fields,
smoothness, or equidimensional schemes. The source defines the length over the ambient
local ring; the node uses the quotient local ring of Z. A surjective ring map gives
identical submodule lattices on a module over its quotient, so the lengths agree.

My list of the node's objects, hypotheses, and conclusions, matched to the Lean:

1. A field k: `(k : Type u) [Field k]`. Pass. I opened `Field` and its inherited
   `DivisionRing` signature: commutative, nontrivial, with inverses for nonzero elements.
2. A proper k-scheme X: `(X : Scheme.{u}) [X.Over (Spec (.of k))]` and
   `[IsProper (X ↘ Spec (.of k))]`. Pass. The recorded properness class extends
   separatedness, universal closedness, and local finite type; universal closedness
   supplies quasi-compactness, hence finite type. No separate Noetherian assumption.
3. A nonempty closed subscheme Z of X: `(Z : Scheme.{u}) [Nonempty Z]`,
   `(i : Z ⟶ X) [IsClosedImmersion i]`. Pass. The recorded closed-immersion class is
   a closed embedding with surjective stalk maps, precisely the required subscheme.
4. Its dimension d: `(d : ℕ)` and
   `hd : topologicalKrullDim Z = ((d : ℕ∞) : WithBot ℕ∞)`. Pass. I opened the recorded
   dimension definition: strict chains of irreducible closed subsets, including bottom
   for the empty space. A nonempty proper finite-type scheme over a field has finite
   nonnegative dimension, so using a natural d loses no source case.
5. All and only the d-dimensional irreducible components, each once: `(r : ℕ)` and
   `components : Fin r ≃ {C : Set Z // C ∈ irreducibleComponents Z ∧
   topologicalKrullDim C = ((d : ℕ∞) : WithBot ℕ∞)}`. Pass. The equivalence excludes
   omissions and duplicates. I opened `irreducibleComponents`, which is exactly the
   maximal nonempty irreducible subsets, and its closedness theorem.
6. Their reduced induced integral subschemes: `Y : Fin r → Scheme.{u}`,
   `[∀ j, IsIntegral (Y j)]`, `c : ∀ j, Y j ⟶ Z`,
   `[∀ j, IsClosedImmersion (c j)]`, and
   `hc : ∀ j, Set.range (c j) = (components j).val`. Pass. `IsIntegral` implies reduced
   and irreducible and supplies nonemptiness; a reduced closed subscheme with that
   support is the reduced induced structure. These are not arbitrary integral schemes.
   Their closed immersions into X are `c j ≫ i`, with the composite instance inferred.
7. Component dimensions: `hY : ∀ j, topologicalKrullDim (Y j) =
   ((d : ℕ∞) : WithBot ℕ∞)`. Pass. This restates the component dimension already in the
   node. It follows from the closed embedding and `hc` by invariance under homeomorphism;
   its explicit binder supplies the existing intersection definition's proof argument.
8. Their generic points: `ξ : Fin r → Z` and
   `hξ : ∀ j, IsGenericPoint (ξ j) (Set.range (c j))`. Pass. I opened the recorded
   definition `closure {ξ j} = Set.range (c j)`. This puts the point in Z, where its
   structure-sheaf stalk is taken; it corresponds to the component's generic point.
9. The d invertible modules on X: `L : Fin d → X.Modules` and
   `[∀ a : Fin d, (L a).IsInvertible]`. Pass. I opened the recorded
   `Scheme.Modules.IsInvertible`: local isomorphisms with the structure sheaf.
   This is the scheme-module notion, not a private predicate or another module category.
10. The generic multiplicities and their positivity: `∃ m : Fin r → ℕ` with, for every j,
    `Module.length (Z.presheaf.stalk (ξ j)) (Z.presheaf.stalk (ξ j)) = (m j : ℕ∞)`
    and `0 < m j`. Pass. I opened `Module.length`, the dimension of the submodule lattice
    in extended naturals. The equality pins down the multiplicities uniquely and asserts
    finiteness as a conclusion. No arbitrary weights or assumed finite lengths occur.
11. The component formula: `intersectionNumber k X Z i d hd L = ∑ j : Fin r,
    (m j : ℚ) * intersectionNumber k X (Y j) (c j ≫ i) d (hY j) L`. Pass. I opened
    `IntersectionNumber.lean` and its definitions: the rational coefficient of the
    product monomial in the Euler polynomial of the pushed-forward structure sheaf.
    Both sides use exactly that recorded definition and the original modules on X.
12. The ample repeated-module consequence: the concluding universal quantifier
    `∀ (A : X.Modules) [A.IsInvertible]`, hypothesis `IsAmple (X ↘ Spec (.of k)) A`,
    component positivity for every j, and conclusion
    `0 < selfIntersectionNumber k X Z i d hd A`. Pass. I opened `IsAmple` and
    `selfIntersectionNumber`; the former is invertibility and a positive very ample
    tensor power (the source notion on proper schemes), the latter repeats A in all d
    places. This clause does not assume ampleness of the arbitrary family L or conclude
    positivity without the node's component positivity hypotheses.

Dependency audit: every node in `stmt_deps` was read, including its recorded Lean or
Mathlib match, and each declaration above was opened in its actual module. The imports
use the recorded intersection, ample, invertible, length, and generic-point notions;
other geometric and topological declarations arrive through the intersection module.
There are no new nodes, dependency modules, or statement corrections in the delivery,
so H12/H13 and correction-citer checks have no additional objects to review.
I also opened `NumericalPolynomialLeadingTerm.lean` to verify that the docstring's first
proof step has the recorded leading-term statement available for stage 3.

Edge cases: d = 0 gives `Fin 0`, the empty product monomial and constant coefficient,
including the multiplicity of a nonreduced zero-dimensional scheme. Empty Z is excluded
explicitly by the node; an empty X cannot contain the nonempty Z. The zero module is not
silently allowed as an invertible module on nonempty X. For r = 0 the equivalence cannot
exist: properness makes Z Noetherian with finitely many components, one of which attains
its finite dimension d. Thus the positive-sum conclusion is not falsely applied to an
empty sum. Lower-dimensional components are excluded without excluding them from Z.
Nonreduced, reducible, and nonequidimensional Z are permitted. No characteristic,
separability, or algebraic-closure restriction appears. All geometric objects have the
explicit universe u used by the recorded definitions; finite indices have no independent
universe or test-object universe that could make a hypothesis vacuous.

Independent searches, using different terms from the worker's searches:

- `msearch.py ... leanfinder "intersection product cycle fundamental cycle generic
  multiplicity additivity"`: eight permutation-cycle hits; none is a scheme intersection
  statement. No match.
- `msearch.py ... loogle "Module.length, irreducibleComponents"`: zero hits. No match.
- `msearch.py ... leansearch "intersection multiplicity fundamental cycle of a closed
  subscheme"`: service unavailable (Internal Server Error). No mathematical verdict
  inferred from unavailability.
- `msearch.py ... grep "cycle|multiplicity|intersection"`: returned number-theoretic
  multiplicity and permutation material; no matching component formula.
- Independent `rg` in the source project's `WeilConjectures`, Mathlib's
  `AlgebraicGeometry`, the project's `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for `intersectionNumber`, component/intersection phrases, `0BES`, generic
  multiplicities, and `fundamentalCycle`: the recorded intersection definition and
  unrelated component intersections only. The existing leading-term theorem is about
  arbitrary coherent modules and a polynomial remainder, not this intersection formula;
  it is correctly a proof dependency rather than a duplicate statement.

H5/H6/H8/H9: no definitions are added, and the only theorem has exactly `by sorry` as
proof. The module and theorem docstrings give the source and blueprint id. The theorem
proof docstring follows the node's two steps, including the quotient-ring length
comparison, coefficient comparison, and positive weighted sum. The header, namespace,
imports, line lengths, bound variables, and universe declaration satisfy the contract.
The node's `lean.statement` was checked verbatim against the theorem signature.

Validation: the independent `scompile.py H1 lem-sc-top-dimensional-reduction-intersection`
run compiled the module on the server in 2.0 seconds, exit code 0, with no warnings.
