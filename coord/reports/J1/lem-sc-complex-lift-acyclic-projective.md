## Worker report

The module `Sheaf.Algebra.Homology.AcyclicLift` states
`CochainComplex.exists_acyclic_lift_mod_ideal`, with its sole proof `sorry`.
It introduces no definitions, dependency modules or new nodes. The item's node changes only
in `lean`.

Source read: [Stacks Tag 0BC9](https://stacks.math.columbia.edu/tag/0BC9), including the
whole induction proof. The local literature copy is absent. The tag is now numbered
15.77.1, whereas the node's older numbering is 15.75.1; the stable tag is unchanged.
[Stacks conventions, Tag 00AQ](https://stacks.math.columbia.edu/tag/00AQ) specify that rings
are commutative with identity and include the zero ring. Thus `[CommRing R]` renders the
source's word “ring”; neither nontriviality nor a finiteness assumption is imposed.

Hypotheses and conclusions, clause by clause:

- Ring and ideal: `(R : Type u) [CommRing R] (I : Ideal R)`.
- Class of modules: `P : ModuleCat.{max u v} R → Prop`. Both universes are explicit;
  arbitrary module sizes are covered by choosing `v`. The maximum closes the module universe
  under tensoring with `R ⧸ I` without assuming the ring is small in a smaller universe.
- Condition (1): `hprojective : ∀ M, P M → Module.Projective R M`.
- Condition (2): `hsummand` quantifies over `M₁`, `M₂` and a representative `M₁₂` of
  their direct sum. Its antecedents are `P M₁`, `P M₁₂` and
  `Nonempty (M₁₂ ≅ ModuleCat.of R (M₁ × M₂))`, and its conclusion is `P M₂`.
  A finite direct sum of modules is the product. Quantifying over its representative
  expresses the source's direct-sum condition up to isomorphism, rather than depending on
  the implementation's underlying type. No separate closure or zero-member hypothesis is
  added. This point deserves explicit attention in the second reading.
- Condition (3): `hsurjective` quantifies over a morphism `f : M₁ ⟶ M₂` between
  members of `P`; surjectivity of `extendScalars (Ideal.Quotient.mk I)` applied to `f`
  implies `Function.Surjective f`. This is surjectivity modulo `I`, not just surjectivity
  of a map to an unrelated module.
- Input complex: `E : CochainComplex (ModuleCat (R ⧸ I)) ℤ`, with the displayed universe.
- Bounded above: `hbounded : ∃ b : ℤ, E.IsStrictlyLE b`. This means the *terms* vanish
  above `b`, not only that cohomology vanishes.
- Acyclic: `hacyclic : E.Acyclic`.
- Each input term has the required form: `hterms` gives for every integer `i` an `M`
  with `P M` and an isomorphism between its scalar extension and `E.X i`.
- Output: an existential `A : CochainComplex (ModuleCat R) ℤ`.
- Bounded above output: `∃ b : ℤ, A.IsStrictlyLE b`.
- Acyclic output: `A.Acyclic`.
- All output terms belong to the class: `∀ i : ℤ, P (A.X i)`.
- Isomorphism of complexes after reduction: `Nonempty` of an isomorphism from
  `((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
  (ComplexShape.up ℤ)).obj A` to `E`. It includes compatibility with all differentials,
  rather than merely a family of termwise isomorphisms. Scalar extension to `R/I` is
  canonically `M/IM`: the isomorphism sends `s ⊗ m` to `s m` modulo `IM`, with inverse
  sending the class of `m` to `1 ⊗ m`.

Dependency declarations read and used:

- `def-pc-cochain-complex-modules`: its Mathlib match `CochainComplex`, in
  `Mathlib.Algebra.Homology.HomologicalComplex`, is the general cochain-complex abbreviation
  over a category, with shape `ComplexShape.up ℤ`. It applies directly to ordinary modules.
- `def-pc-acyclic-complex-modules`: its Mathlib match `HomologicalComplex.Acyclic`, in
  `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`, is `∀ i, K.ExactAt i`.
  The adjacent `exactAt_iff_isZero_homology` confirms the cohomology interpretation.
  Neither node needs a sheaf-only replacement: both recorded matches are general declarations.
- Existing Mathlib notions used directly: `Module.Projective`;
  `ModuleCat.extendScalars` in `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`
  (its complete signature and docstring describe tensor extension and its action on maps);
  `CochainComplex.IsStrictlyLE` in `Mathlib.Algebra.Homology.Embedding.CochainComplex`;
  `CategoryTheory.Functor.mapHomologicalComplex` in `Mathlib.Algebra.Homology.Additive`.

Edge cases checked before writing: the zero ring, `I = 0`, `I = R`, the zero complex,
empty classes, arbitrary integer upper bounds and arbitrarily long left tails.
There is no `Nontrivial` or bounded-below assumption. An empty class cannot satisfy `hterms`
even for the zero complex, since it demands a class member in every degree. When `I = R`,
condition (3) applied to zero endomorphisms forces class members to be zero, consistently
with the zero reduction. Acyclicity concerns every integer degree, including the uppermost
nonzero term. No statement is disputed.

Searches made:

- `msearch.py ... leanfinder "Lift bounded above acyclic complex modulo ideal projective modules"`:
  eight hits, notably `ProjectiveResolution.ofComplex`,
  `CochainComplex.isKProjective_of_projective`, and `ShortComplex.Exact.liftFromProjective`;
  none states the lifting theorem.
- `msearch.py ... loogle "ModuleCat.extendScalars, CochainComplex"`: zero hits.
- `msearch.py ... grep "lift.*acyclic|acyclic.*lift"`: zero hits.
- `rg` on `WeilConjectures` and `lean/Sheaf` for `lift.*acyclic|acyclic.*lift` and the item id:
  zero hits. This also checks the item-id search requested in the brief.
- `rg` on Mathlib's `Algebra/Category/ModuleCat` for quotient functors and base change:
  found `extendScalars`, read its full definition and docstring; no new quotient notion needed.
- `rg` on Mathlib's homology modules for `IsStrictlyLE|IsBoundedAbove`:
  found and read `IsStrictlyLE` and its vanishing characterization.
- `rg` for `exists_acyclic_lift` in Mathlib, source Lean, project's Lean and
  `dag/lean_names_upstream.json`: no name collision.

Server compilation of the initial statement succeeded without errors or warnings in 1.4 s.
The final import was narrowed from the functor-category homology module to the module
actually defining `mapHomologicalComplex`; the dry run below recompiles this final file.

## Second reading by J1

I independently read the node statement, its Stacks source (More on Algebra, Lemma
15.75.1, Tag 0BC9), the Lean module, and both recorded dependency nodes. The Lean
signature renders the statement clause by clause as follows:

- `R : Type u` with `[CommRing R]` and `I : Ideal R` are the ring and ideal; no
  nontriviality, Noetherian, finiteness, or characteristic hypothesis is added.
- `P : ModuleCat.{max u v} R → Prop` is the arbitrary class of modules. The
  `max u v` universe permits arbitrary module sizes and does not restrict the
  source's class.
- `hprojective : ∀ M, P M → Module.Projective R M` is condition (1), exactly.
- `hsummand` says that for `P M₁`, `P M₁₂`, and an isomorphism from `M₁₂` to the
  binary direct sum represented by `ModuleCat.of R (M₁ × M₂)`, `P M₂` holds. This
  is condition (2), with direct-sum membership expressed up to isomorphism.
- `hsurjective` quantifies a map between two `P` members and requires that its
  scalar extension along `Ideal.Quotient.mk I` is surjective before concluding
  `Function.Surjective f`; this is condition (3), with no stronger map condition.
- `E : CochainComplex (ModuleCat (R ⧸ I)) ℤ`, `hbounded : ∃ b, E.IsStrictlyLE b`,
  and `hacyclic : E.Acyclic` are respectively the input complex, bounded-above
  terms, and acyclicity. `hterms` gives every term an `R`-module representative
  in `P` whose scalar extension is isomorphic to that term.
- The conclusion existentially supplies `A : CochainComplex (ModuleCat R) ℤ`
  with a bound, `A.Acyclic`, `∀ i, P (A.X i)`, and a `Nonempty` complex isomorphism
  from `mapHomologicalComplex ... A` after scalar extension to `E`. Thus the
  reduction is an isomorphism of complexes, including differentials, and all
  quantifiers and conjunctions match the node.

The dependency declarations match their nodes: `CochainComplex` is the general
Mathlib cochain-complex abbreviation, and `HomologicalComplex.Acyclic` is exactness
at every integer degree. No dependency module or new definition is needed. The
zero ring, `I = 0`, `I = R`, zero complex, empty class, arbitrary upper bounds,
and unbounded left tails all remain covered; an empty class correctly makes
`hterms` impossible. No mismatch was found and no source or node change was made.

The searches for Mathlib, slopmaster2, and the project found no existing lifting
statement or duplicate declaration (details are recorded above). The final module
compiles cleanly with `scompile.py`; its only proof is the required `sorry`.
