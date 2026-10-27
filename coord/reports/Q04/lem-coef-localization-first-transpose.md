## Worker report

The module `Sheaf.CategoryTheory.LocalizationFirstTranspose` states
`CategoryTheory.localization_first_transpose`, with its proof `sorry`. There are no
new definitions, helper axioms, additional nodes, dependency repairs, or statement
corrections. The sole changed field of the item is `lean`.

Sources read: the item's complete statement and three proof steps; both statement
dependency records and their full Mathlib interfaces; both additional proof dependency
records; blueprint `master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/`
`lem-coef-finite-closed-shriek.md`, especially proof paragraph 2; Stacks
`derived.tex`, definition-triangulated-category (0145), TR1--TR3 and the distinction
between pre-triangulated and triangulated, and lemma-third-isomorphism-triangle
(014A); `categories.tex`, definition-adjoint (0037) and the following adjunct formulas.
The item's general categorical assertion is precisely the normalization used in
that blueprint paragraph. No hypothesis of recollement is introduced into this
abstract lemma.

Hypothesis and clause correspondence:

- The four categories are `TA`, `TB`, `CA`, `CB`, each with its own `Type` universe
  and `Category` morphism universe. The full eight universes are explicitly bound.
- Pre-triangulatedness of each `TR` is `[Preadditive TR] [HasZeroObject TR]
  `[HasShift TR ℤ] [∀ n : ℤ, (shiftFunctor TR n).Additive] [Pretriangulated TR]`.
  These are exactly the recorded interface of `def-weil-triangulated-category`.
  Binary biproducts follow from these axioms; no octahedral axiom is assumed.
- The functors `IA`, `JA`, `IB`, `JB` and specified adjunctions are the corresponding
  binders and `adjA : IA ⊣ JA`, `adjB : IB ⊣ JB`. Mathlib's `Adjunction` includes
  the natural unit, counit and both triangle identities, and gives natural Hom-set
  bijections through `Adjunction.homEquiv`. This is the adjunction interface named
  in `def-weil-pbc-adjunction-mate`; `Mathlib.CategoryTheory.Adjunction.Mates` is
  imported directly. No private mate or adjunct definition is introduced.
- Full faithfulness of `IB` is `[IB.Full] [IB.Faithful]`, respectively surjectivity
  and injectivity on each Hom set. Full faithfulness of `IA` is not assumed.
- The exact functor is `SX : TA ⥤ TB` with `[SX.CommShift ℤ] [SX.IsTriangulated]`.
  Additivity follows from Mathlib's triangulated-functor instance. `SZ : CA ⥤ CB`
  is an arbitrary functor; neither additivity nor exactness is required of it.
- The natural isomorphism is `c : IA ⋙ SX ≅ SZ ⋙ IB`. Mathlib writes functor
  composition diagrammatically, so these are the stated composites `SX IA` and
  `IB SZ` in the source's order.
- `M LA : TA`, `LB : TB`, `ηA`, `δA`, `ηB`, `δB` supply exactly the objects and
  second and connecting arrows of the two displayed triangles. Their first maps
  are literally `adjA.counit.app M` and `adjB.counit.app (SX.obj M)`.
  `hA` and `hB` state membership of those `Triangle.mk` terms in `distTriang`.
  Connecting arrows are specified arbitrary data subject to distinguishedness,
  rather than being chosen from existence or omitted.
- The comparison is `d : SX.obj LA ≅ LB`, with exactly the equation
  `hd : SX.map ηA ≫ d.hom = ηB`.
- The prescribed `b` is written directly as
  `(adjB.homEquiv (SZ.obj (JA.obj M)) (SX.obj M))
    ((c.app (JA.obj M)).inv ≫ SX.map (adjA.counit.app M))`.
  Its source arrow is exactly `SX(εA) c⁻¹`, with the correct reversed order for
  Lean's diagrammatic composition. Thus no arbitrary comparison map is assumed.
- Existence is `∃ φ : SX.mapTriangle.obj (Triangle.mk ...) ⟶ Triangle.mk ...`.
  Mathlib's `mapTriangle` includes the specified shift comparison in the image's
  connecting map, and a morphism of triangles includes all three commuting squares.
  Distinguishedness of the image follows from exactness and `hA`.
- The prescribed second and third components are `φ.hom₂ = 𝟙 (SX.obj M)` and
  `φ.hom₃ = d.hom`; the first component is `a = φ.hom₁`.
- Its invertibility is `IsIso φ.hom₁`. Its normalizing equation is the explicit
  conjunct `φ.hom₁ ≫ adjB.counit.app (SX.obj M) = SX.map (adjA.counit.app M)`.
- Uniqueness is quantified over every morphism `a` between the first vertices:
  that same counit equation implies `a = φ.hom₁`. It is not limited to first
  components already supplied as part of triangle morphisms.
- The final conjunct is `(c.app (JA.obj M)).inv ≫ φ.hom₁ = IB.map (...)`, where
  the parenthesized expression is the prescribed `b` above. This is exactly
  `a c⁻¹ = IB(b)`.
- The final prose assertion about every such triangle morphism follows directly
  from the quantified uniqueness: its first square and identity middle component
  give the counit equation, hence its first component is `φ.hom₁` and satisfies
  the stated formula and invertibility. No extra independent assertion is hidden.

Dependency declarations used:

- `def-weil-triangulated-category`: `CategoryTheory.Pretriangulated`, its TR1--TR3
  fields, `CategoryTheory.Pretriangulated.Triangle`, and `TriangleMorphism`, from
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated` and its imported `Basic`;
  `CategoryTheory.Functor.CommShift`, `Functor.IsTriangulated`, and `mapTriangle`
  from `Mathlib.CategoryTheory.Triangulated.Functor` and its shift import.
- `def-weil-pbc-adjunction-mate`: the existing Mathlib adjunction and hom-equivalence
  interface from `Mathlib.CategoryTheory.Adjunction.Mates`, which records
  `CategoryTheory.mateEquiv` and imports `Adjunction.Basic`. The statement uses the
  objectwise transpose `adjB.homEquiv`; no natural mate construction is needed.
- `lem-sf-triangle-morphism-iso`: the recorded Mathlib
  `CategoryTheory.Pretriangulated.isIso₁_of_isIso₂₃` (the relevant position among
  its three recorded variants), in `Triangulated.Pretriangulated`.
- `lem-weil-pbc-adjunct-counit-identity`:
  `CategoryTheory.Adjunction.eq_unit_comp_map_iff`, in `Adjunction.Basic`, imported
  also as an ordinary proof-dependency import. Its full signature was read along
  with `homEquiv`, the adjunction structure and its docstring.

Edge cases checked before writing: zero objects and zero triangles are allowed;
identity functors and adjunctions recover the identity first component; a
nontrivial choice of `d` is allowed whenever its one prescribed square commutes;
there is no restriction on the connecting arrows beyond distinguishedness; `IA`
is allowed to be non-fully-faithful, and `CA`/`CB` are not required to be additive.
The categories' object and morphism universes are all independent. There is no
nonzero, boundedness, nonempty-index, characteristic or finite-coefficient
restriction, and no requirement of the octahedral axiom. Since the conclusion's
uniqueness is only for `a`, it does not incorrectly assert uniqueness of a cone
or of arbitrary TR3 extensions without the specified counit condition.

Searches made with `msearch.py` (2026-10-22):

- LeanFinder: "A morphism of distinguished triangles with fixed identity middle
  component and invertible third component has a unique first component normalized
  by the counit of a fully faithful left adjoint". Eight hits, including
  `complete_distinguished_triangle_morphism₁` and `isIso₁_of_isIso₂₃`;
  these give completion and invertibility separately, not the whole assertion.
- Loogle: `CategoryTheory.Adjunction, CategoryTheory.Triangle` gave no hits and
  reported the latter identifier unknown. Retried with
  `CategoryTheory.Adjunction, CategoryTheory.Functor.FullyFaithful`: ten hits about
  full-faithfulness of adjoints and restriction, none about this triangle result.
- LeanSearch: "A unique morphism of distinguished triangles whose first map is
  prescribed by adjunction counit and fully faithful left adjoint". Eight hits,
  including t-structure-specific `triangle_map_ext`, triangle-morphism generated
  declarations and adjunction triples. None states the item.
- Mathlib grep through `msearch.py`:
  `counit.*[Tt]riangle|[Tt]riangle.*counit` in `CategoryTheory`: 25 hits, covering
  adjunction and rotation triangle identities, but no such first-component result.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` with the same counit/triangle
  pattern and `localization_first|localizationFirst|firstTranspose|first_transpose`.
  Read the nearby `OrthogonalTriangleCounitNormalization` and upstream
  `WeilConjectures.Mathlib.CategoryTheory.Triangulated.Pretriangulated` counit
  completion theorem. The former constructs a counit triangle from orthogonality;
  the latter completes a counit from a single triangle and essential-image
  vanishing. Neither compares these two given triangles under `SX` or identifies
  their unique first comparison with the specified transpose. They do not match.
- Direct `rg` of the blueprint item id in `lean/WeilConjectures`: no match.
  Name checks in `dag/lean_names_upstream.json`, Mathlib and the project sources
  found no existing `CategoryTheory.localization_first_transpose` declaration.

Validation: the initial module compiled cleanly with `scompile.py`, both its
sandbox form and library module form. The final file binds all variables explicitly
and sets `autoImplicit false`; the signature in `lean.statement` is extracted
verbatim from its theorem declaration. The proof remains `sorry`, with all three
DAG proof steps documented. No mathematical dispute or node fault was found.

## Second reading by Q04

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
