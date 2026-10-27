## Worker report

The module `Sheaf.CategoryTheory.UnboundedLeftDerivedCriterion` states
`CategoryTheory.Functor.unbounded_leftDerived_definedAt_of_resolvingClass`, with
proof `sorry`. It is Stacks Project, Derived Categories, Tag 0794, read in
`literature/stacks-project/derived.tex`, proposition-left-derived-exists,
including its proof; definedness is Definition 05S9(2), in Situation 05S8.
The node is unchanged except for its `lean` field. No new definitions, additional
nodes, dependency modules, or statement correction are needed.

Hypothesis and clause correspondence:

- Abelian categories A and B: `{A : Type uA} [Category.{vA} A] [Abelian A]`
  and the corresponding B binders. Their object and morphism universes are
  independent. `[HasDerivedCategory.{wA} A]` and
  `[HasDerivedCategory.{wB} B]` supply the chosen unbounded derived categories,
  again with independent morphism universes.
- Additive right exact F: `(F : A ⥤ B) [F.Additive]
  [PreservesFiniteColimits F]`. This uses precisely the node's convention that
  right exact means preserving finite colimits, not preservation of all colimits
  or an assumption of exactness.
- The subset of objects: `(P : A → Prop)`, with no isomorphism-closure assumption.
- Contains zero: `(hzero : P (0 : A))`, using Mathlib's `ZeroObject` scope and
  the chosen zero object supplied by `Abelian.hasZeroObject`.
- Closed under finite direct sums: the binary condition
  `hsum : ∀ (X Y : A), P X → P Y → P (X ⊞ Y)`, together with `hzero` for the
  empty sum. Iteration gives finite direct sums. Binary biproducts already come
  from `Abelian.hasBinaryBiproducts`; no additional structure hypothesis is used.
- Every object is an epimorphic image: `hcover` quantifies over every `X : A`
  and supplies `Y`, `p : Y ⟶ X`, `P Y`, and `Epi p`.
- Bounded above acyclic P-complexes remain acyclic: `hacyclic` quantifies over
  every `K : CochainComplex A ℤ`; its first premise is
  `∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (K.X i)`, its second is termwise P,
  its third is `K.Acyclic`, and its conclusion is acyclicity of
  `(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K`.
- Existence of sequential colimits: `[HasColimitsOfShape ℕ A]` and the B
  counterpart. The category on ℕ is Mathlib's category associated to its usual
  order, not a discrete category.
- Exactness of those colimits: `[HasExactColimitsOfShape ℕ A]` and the B
  counterpart. In abelian categories the colimit functor is additive and
  already preserves colimits; preservation of finite limits is equivalent to
  preservation of short exact sequences. This does not assume exactness of
  arbitrary filtered colimits, arbitrary coproducts, or products.
- F commutes with them: `[PreservesColimitsOfShape ℕ F]`.
- Everywhere defined left derived functor: `X` is an arbitrary object of
  `HomotopyCategory A (ComplexShape.up ℤ)`, with no bound. The conclusion is
  `∃ Y : DerivedCategory B, IsEssentiallyConstantProDiagram ... Y`.
  The diagram is exactly the one in the recorded
  `Functor.IsTriangulatedLeftDerivedDefinedAt`: the denominator category is
  `(HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Over ⊤ X`, its forgetful
  functor takes a denominator to its source, and the composite is
  `F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh`.
  All commuting triangles are allowed; morphisms between denominators are not
  restricted to quasi-isomorphisms. The conclusion unfolds the recorded notion
  rather than defining a second one. The triangulated setup follows from
  additivity and the standard quasi-isomorphism localization, as explained in
  proof step 7; it is not an added hypothesis.

Dependency declarations and source interfaces read:

- `def-sp-abelian`: `CategoryTheory.Abelian`, in
  `Mathlib.CategoryTheory.Abelian.Basic` (Mathlib leaf).
- `def-weil-abstract-derived-category`: `HasDerivedCategory`, `DerivedCategory`,
  `DerivedCategory.Qh`, and its quasi-isomorphism localization instance, in
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.colimit`,
  `HasColimitsOfShape`, and the colimit cocone universal property, in
  `Mathlib.CategoryTheory.Limits.HasLimits`, transitively publicly imported.
- `def-pur-saturated-triangulated-localization`:
  `Functor.IsTriangulatedLeftDerivedDefinedAt` and
  `Functor.IsTriangulatedLeftDerivedValue`, read in
  `WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem`;
  their underlying `IsEssentiallyConstantProDiagram` is used directly.
- The ordinary complex and homotopy functors are Mathlib's
  `Functor.mapHomologicalComplex` (Algebra.Homology.Additive) and
  `Functor.mapHomotopyCategory` (Algebra.Homology.HomotopyCategory).
- Exact sequential colimits use `CategoryTheory.HasExactColimitsOfShape` in
  `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic`.

All already stated proof dependencies have plain imports:
`CochainComplex.mappingCone.quasiIso_iff_acyclic` in
`WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`;
`CategoryTheory.subcategory_truncation_resolution_system` in
`Sheaf.Algebra.Homology.SubcategoryTruncationResolutionSystem`;
the homology colimit-preservation instance in
`WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits`;
`Functor.resolvingClass_essentialConstancy` in
`WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy`;
and `HomotopyCategory.quasiIso_saturated_triangulated` in
`WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated`.
`lem-trf-bounded-stage-roof-comparison` has no recorded Lean module in the read
repository; it is a proof-only dependency, not needed to type this statement,
and remains named in the full seven-step proof docstring. The homology instance's
recorded generated name is stale locally, but its actual general declaration
with the recorded signature is present in the recorded module (line 142).

Edge cases checked before writing: zero complexes; the empty finite sum;
zero source/target objects and zero functors; arbitrary negative upper bounds
and cohomological degrees; the initial sequential stage 0; complexes unbounded
in both directions in the conclusion; and independent category and derived
morphism universes. No nonempty indexing premise is needed because ℕ is nonempty.
The class P need not contain every zero object or be isomorphism closed: the
first proof step passes to its isomorphism closure without changing hypotheses.

Searches for an existing statement (2026-10-22):

- `msearch.py ... leanfinder`: “An additive right exact functor has an unbounded
  left derived functor if it preserves bounded above acyclic complexes in a
  generating class and commutes with exact sequential colimits”. Eight hits,
  including `HasPointwiseLeftDerivedFunctor`, `HasLeftDerivedFunctor`,
  `hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor`, and
  `mapDerivedCategory`. These assume pointwise existence or exactness; none
  states the five-hypothesis criterion.
- `msearch.py ... leansearch`: “Unbounded left derived functor existence from
  bounded above acyclic resolutions and exact sequential colimits”. Eight
  hits: abstract derived-functor definitions/constructors and projective
  resolutions; none establishes this criterion.
- `msearch.py ... loogle`: `"HasLeftDerivedFunctor", "HasExactColimitsOfShape"`.
  Zero hits.
- `msearch.py ... grep`: `unbounded.*[Ll]eft|left[Dd]erived.*[Cc]riterion|HasExactColimitsOfShape`
  in Mathlib CategoryTheory. Twenty-five hits, giving exact-colimit APIs and
  Grothendieck-category instances; none is this criterion.
- `rg` over project `lean/WeilConjectures` and `lean/Sheaf` for
  `unbounded.*[Ll]eft|left[Dd]erived.*[Cc]riterion|unbounded_left_derived`:
  specialized K-flat/derived-functor constructions and users, including the
  parent ContinuousCocontinuousDerivedShriek; no general criterion.
- `grep -rn` for the exact item ID in `lean/WeilConjectures`: no hit.
  `rg` for the proposed full declaration's final component in Mathlib,
  `WeilConjectures`, `Sheaf`, and `dag/lean_names_upstream.json`: no collision.

Validation: `scompile.py Q45 lem-trf-unbounded-left-derived-criterion` compiled
both the sandbox and the actual module name cleanly (1.2 s each). The first
probe exposed a missing `ZeroObject` scope; opening the existing Mathlib scope
fixed it. Every variable and universe is explicitly bound, and every line is
at most 100 characters. The only proof is the requested named theorem's `sorry`.
No mathematical dispute or node statement fault was found.

## Second reading by Q45

Author's self-check, not an independent review: re-read Tag 0794, the node, and
all binders of the compiled theorem together. The five source assumptions match
the list above. In particular this does not replace right exactness by exactness,
does not assume P is isomorphism closed, does not assume the conclusion's input
complex is bounded, and uses the full pro-diagram condition of 05S9 rather than
only a Kan-extension existence claim. The conclusion is the literal body of the
recorded definedness predicate with its value existentially quantified. The
maintainer supplies the independent delivery review under the dispatcher's brief.
