## Worker report

The module `Sheaf.AlgebraicGeometry.EqualDimensionGenericStructureImage` states
`AlgebraicGeometry.Scheme.Hom.equalDimension_generic_structure_image`, with `sorry`
as its whole proof. Its docstring contains all eight steps of the DAG proof.
The only other declaration, `Scheme.Hom.dominantFunctionFieldModule`, packages the
existing canonical algebra `f.dominantFunctionFieldAlgebra` as a module object.
Its body is `ModuleCat.of` with precisely that algebra's `toModule`; there is no
new field, field embedding, chosen map, or postponed data. This owning-node helper
lets the statement use the actual function-field action without local instances,
let binders, or a second definition of the field map.

Hypotheses and clauses, checked against the unchanged node:

- The field k is `{k : Type u} [Field k]`.
- The nonempty integral schemes are `{X Y : Scheme.{u}} [IsIntegral X]
  [IsIntegral Y]`; `IsIntegral.nonempty` already supplies nonemptiness.
- Their k-scheme structures are `[X.Over (Spec (.of k))]` and the analogous
  binder for Y. Finite type is rendered by BOTH `LocallyOfFiniteType` and
  `QuasiCompact` on each structure morphism, following the dependency record.
- `g : ℕ`, `hX : topologicalKrullDim X = (g : WithBot ℕ∞)` and the matching
  hY render equality of the finite dimensions and g >= 0. No redundant
  nonnegativity hypothesis excludes dimension zero.
- `(f : X ⟶ Y) [f.IsOver (Spec (.of k))]` makes f a k-morphism;
  `[IsProper f]` is properness and `[IsDominant f]` is dense image.
- The generic points are Mathlib's `genericPoint X` and `genericPoint Y`.
  `Scheme.functionField` is the structure-sheaf stalk at exactly this point.
- The extension uses `dominantFunctionFieldModule f`, whose underlying object is
  `X.functionField` and whose Y.functionField-module structure is exactly
  `f.dominantFunctionFieldAlgebra.toModule`, not a free algebra binder.
  `FiniteDimensional Y.functionField f.dominantFunctionFieldModule` is finiteness
  of the stated field extension.
- `∃ U : Y.Opens, Nonempty U ∧ IsFinite (f ∣_ U) ∧ ...` gives exactly a
  nonempty open subscheme and the finiteness of its full inverse-image restriction.
  Opens are already the canonical open subschemes with their open immersions U.ι.
- For EVERY `i : ℤ` with `0 < i`, `IsZero ((restrictFunctor U.ι).obj
  ((schemeModuleHigherDirectImage f i).obj (Scheme.Modules.unit X)))` renders
  `(R^i f_* O_X)|_U = 0` using the recorded unbounded derived direct image.
  `unit X` is the structure sheaf as an O_X-module. The two explicitly bound
  `HasDerivedCategory.{wX/wY}` instances are the shared category-localization
  interfaces, with independent universes, not geometric or vanishing hypotheses.
- The displayed existential `e` is a `Y.functionField`-linear equivalence from
  the actual stalk of `(Scheme.Modules.pushforward f).obj (unit X)` at genericPoint Y
  to `f.dominantFunctionFieldModule`. Its source module structure is Mathlib's
  structure-sheaf-stalk action for the pushforward module.
- The clause following e fixes it canonically: for EVERY target open V,
  generic-point membership proofs hηY and hηX, and actual structure-sheaf section
  `s : Γ(X, f ⁻¹ᵁ V)`, e sends its direct-image germ to
  `X.presheaf.germ (f ⁻¹ᵁ V) (genericPoint X) hηX s`. The section types of the
  structure sheaf and its unit module are definitionally the same. Dominance
  ensures genericPoint X lies in the inverse image whenever genericPoint Y lies
  in V, so this characterization is not vacuous. Germs exhaust the source stalk;
  hence it specifies precisely the canonical germ map, not an arbitrary isomorphism.
- The last equality is `Module.finrank Y.functionField` of that actual stalk equal
  to `Module.finrank Y.functionField f.dominantFunctionFieldModule`, i.e. exactly
  `[k(X):f^*k(Y)]`. Finiteness is already a conclusion in the first conjunct.

Dependency declarations read and reused:

- `Mathlib.Algebra.Field.Defs`: `Field` (the mathlib match of def-weil-field).
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`.
- `Mathlib.Topology.Sober`: `IsGenericPoint`, `genericPoint`, `genericPoint_spec`.
- `WeilConjectures.AlgebraicGeometry.FunctionField`:
  `Scheme.functionFieldOfComponents` and its documented arbitrary integral-scheme
  clause using `Mathlib.AlgebraicGeometry.FunctionField`, `Scheme.functionField`.
  The integral clause is what this item uses; no component product is substituted.
- `Sheaf.TraceFormula.LocalDimensionFormula`:
  `Scheme.Hom.dominantFunctionFieldAlgebra`. Its body obtains the generic-point
  equality from dominance and uses the actual `Scheme.Hom.functionFieldMap` of
  `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`; the canonical
  target open inclusion is `U.ι`, and morphism restriction is `f ∣_ U`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `schemeDerivedDirectImage`, `schemeHigherDirectImage`,
  `schemeModuleHigherDirectImage`; the last is used literally.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullbackSectionAdjunction` and its public upstream
  tensor pullback/pushforward interface, including `Scheme.Modules.pushforward`.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor`, `stalkObj` and the accompanying stalk maps;
  their underlying carriers and scalar multiplication are Mathlib's presheaf
  stalks, used directly in the displayed module stalk. Mathlib's CommRingCat
  stalk-module instance supplies the action of the actual function field.

All stated proof dependencies are imported, with proof-only imports kept private:
`ClosedIrreducibleDimensionTrdeg`, `FiniteResiduePointClosedInFibre`,
`GenericFiniteOpenNeighborhood`, `CoherentFiniteType`,
`AffineMorphismCohomologyEdge`, `HigherDirectImageOpenRestriction`, and the Mathlib
fraction-field, transcendence-basis/tower, intermediate-field, fibre, Noetherian
and quasi-separatedness interfaces. No import cycle was found or import omitted.

Sources read directly in literature/stacks-project: varieties.tex,
lemma-dimension-locally-algebraic (0A21)(6) and
lemma-intersection-number-and-pullback (0BET), especially its generic-image
paragraph; morphisms.tex, lemma-generically-finite (02NW), equivalence (1)/(4);
coherent.tex, lemma-relative-affine-vanishing (01XC) and
lemma-finite-pushforward-coherent (01Y6). They support the unchanged node statement.

Edge cases checked before writing: dimension g=0 (finite field spectra), identity
maps (degree one), inseparable finite field extensions (no separability or perfect
field assumption), nonproper base varieties (only f is required proper), and empty
opens (explicitly ruled out by Nonempty U). The empty source or target is already
excluded by IsIntegral. Higher degree zero is intentionally not included in
vanishing. Arbitrary localization universes wX and wY are retained; no equality
of them, affine-global hypothesis, smoothness, normality or projectivity is added.
There are no statement corrections, disputed clauses, or dependency repairs.

Searches for an exact existing statement:

- msearch.py leanfinder, query: "A proper dominant morphism of integral finite type
  schemes of equal dimension is finite on a nonempty open and the generic stalk of
  its structure sheaf pushforward is the source function field". Eight hits:
  `Scheme.RationalMap.ofFunctionField`, `finite_appTop_of_universallyClosed`,
  `Scheme.RationalMap.fromFunctionField_ofFunctionField`,
  `Scheme.PartialMap.fromFunctionField`, `IsIntegralHom`, `IsFinite`,
  `Scheme.RationalMap.fromFunctionField`, `IsDominant`. None states this conjunction;
  the global-sections result concerns a map to a field spectrum.
- msearch.py loogle, query: `AlgebraicGeometry.Scheme.functionField, Module.Finite`.
  Zero hits.
- msearch.py grep under AlgebraicGeometry, query:
  `generic.*(stalk|pushforward)|functionField.*(FiniteDimensional|finrank)|toPushforwardStalkAlgHom`.
  Five hits in Mathlib/AlgebraicGeometry/Spec.lean for
  `StructureSheaf.toPushforwardStalkAlgHom` and its localization interface; these
  concern an affine structure-sheaf pushforward, not the claimed generic theorem.
- msearch.py leansearch, query: "generic stalk structure sheaf direct image proper
  dominant equal dimension". Eight hits: structure-sheaf localization/toStalk/germ
  results, `IsDominant`, local stalk-map results, `restrictStalkNatIso`, and
  `ModuleCat.Tilde.stalkIso`; no exact match.
- rg over lean/WeilConjectures and lean/Sheaf for
  `toPushforwardStalkAlgHom|dominantFunctionFieldAlgebra|generic.*[Ss]talk|generic.*[Pp]ushforward|functionField.*[Ff]inite`
  found the canonical field algebra, existing stalk comparisons, rational maps,
  etale generic stalks and unrelated generic-lattice results, but no theorem with
  the item's hypotheses and clauses. A follow-up narrower algebraic-geometry
  search confirmed this. The explicit grep for the item id in WeilConjectures
  returned no match. Searches for the two proposed declaration names in
  WeilConjectures, Sheaf and dag/lean_names_upstream.json returned no match.

Validation: scompile.py compiled this delivered module on the published live
library, both its sandbox probe and actual module, with no errors or warnings.
No proof is supplied in stage 2 beyond the permitted declaration uses sorry.

## Second reading by NG

Independent second reading by the maintainer reviewer (the dispatcher had the worker
deliver directly; this section replaces the worker's self-audit). The node statement
is unchanged; it was read against Stacks 0BET (varieties.tex, generic-image paragraph
of lemma-intersection-number-and-pullback: singleton generic fibre via 0A21, finite
over a nonempty open via 02NW, higher-image vanishing via 01Y6/01XC).

Node clauses and their Lean rendering:

- k a field: `{k : Type u} [Field k]`. Correct.
- X, Y nonempty integral: `[IsIntegral X] [IsIntegral Y]` (Mathlib's class includes
  `Nonempty`). Correct.
- Finite type over k: `X.Over (Spec k)` with `LocallyOfFiniteType` and `QuasiCompact`
  on `X ↘ Spec k`, and likewise for Y. This is the def-weil-finite-type-morphism record. Correct.
- dim X = dim Y = g < ∞, g ≥ 0: `g : ℕ`, `topologicalKrullDim X = (g : WithBot ℕ∞)`,
  and likewise for Y. This includes g = 0 and excludes ∞ and −∞. Correct.
- f a proper k-morphism with dense image: `f.IsOver (Spec k)`, `IsProper f`,
  `IsDominant f`. Correct.
- Generic points and function fields: `genericPoint`, `Scheme.functionField`, the
  integral clause of def-sc-function-field. Correct.
- f^*: `f.dominantFunctionFieldModule` is `ModuleCat.of` of X.functionField with
  exactly `f.dominantFunctionFieldAlgebra.toModule` (def-sfb-dominant-function-field-map).
  It carries real data, with no new map. Correct.
- Finite extension: `FiniteDimensional Y.functionField f.dominantFunctionFieldModule`.
  Correct.
- Nonempty open U with f^{-1}U → U finite: `∃ U : Y.Opens, Nonempty U ∧ IsFinite (f ∣_ U)`.
  Correct.
- (R^i f_* O_X)|_U = 0 for i > 0: `∀ i : ℤ, 0 < i → IsZero (restrictFunctor U.ι).obj
  ((schemeModuleHigherDirectImage f i).obj (Scheme.Modules.unit X))`. This is the
  recorded def-pc-derived-direct-image declaration. Its HasDerivedCategory binders
  have the free universes wX and wY, as in the dependency's own variables. Correct.
- Canonical germ isomorphism of (f_*O_X)_{η_Y} with k(X), K-linear through f^*: an
  `∃ e : stalk ≃ₗ[Y.functionField] f.dominantFunctionFieldModule`, pinned on every
  germ: `e (germ V η_Y s) = X.presheaf.germ (f⁻¹ᵁ V) η_X s`. The germs generate the
  stalk, so e is the canonical germ map, not an arbitrary isomorphism. The source
  scalar action is Mathlib's stalk-module instance (Algebra/Category/ModuleCat/Stalk.lean),
  which is the colimit of the sectionwise actions of `Scheme.Modules.pushforward f`.
  Those actions restrict scalars along f.app, which is the f^♯ action of the node. Correct.
- Dimension [k(X):f^*k(Y)]: `Module.finrank` of the stalk equals the finrank of
  `f.dominantFunctionFieldModule`. Correct.

Edge cases: g = 0 is covered. The identity map has degree one. Inseparable extensions
need no extra assumption. X and Y are nonempty through IsIntegral. U is nonempty
explicitly. Degree i = 0 is correctly excluded from the vanishing clause. The
hypotheses add no extra Noetherian, separatedness or properness assumption on X or Y.
The lemma states no universe restriction beyond k : Type u, which Spec over Scheme.{u}
requires.

Searches: rg for `dominantFunctionFieldModule|equalDimension_generic_structure_image`
over the live lean/Sheaf and lean/WeilConjectures trees found no clash. The nearby
`Scheme.Hom.finite_dominant_generic_pushforward_stalk` (lem-sfb-finite-dominant-generic-pushforward-stalk)
assumes f finite and does not give this item. Mathlib has no equivalent.

Records: lean.statement is verbatim in the file. The 13 stmt_deps are all used. The
proof is `sorry`. The docstrings give the source places and
`(blueprint: lem-sfb-equal-dimension-generic-structure-image)`, and the theorem
docstring carries the eight node steps. No mismatches were found and the Lean is unchanged.
