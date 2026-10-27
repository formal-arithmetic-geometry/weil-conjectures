## Worker report

States `AlgebraicGeometry.exists_finite_etale_generic_normal_cover` in
`Sheaf.AlgebraicGeometry.FiniteEtaleGenericNormalCover`. Its single proof is `sorry`.
There are no new definitions, dependency repairs, or statement corrections. The node copy
changes only `lean`. The theorem's docstring gives all four DAG proof steps and their
inputs. The source passages read were algebra.tex, lemma-etale-over-field (00U3), and
morphisms.tex, definition-normalization-X-in-Y (035H), lemma-normal-normalization (035L),
lemma-ubiquity-nagata (035B), and lemma-nagata-normalization-finite-general (0AVK).

Hypotheses and clauses, individually:

- The field k is `{k : Type u} [Field k]`. The base is `(S : Scheme.{u}) [IsIntegral S]`.
- Its structure map is `s : S ⟶ Spec (.of k)`. Separatedness is `[IsSeparated s]`, whose
  definition is closed immersion of the relative diagonal. Finite type is exactly
  `[LocallyOfFiniteType s] [QuasiCompact s]`.
- The generic point is Mathlib's `genericPoint S`, and its function field K is the
  generic stalk `S.functionField`. The canonical map is `S.fromSpecFunctionField`.
  An independently named generic point is unnecessary because it is unique.
- The nonempty finite étale K-scheme is `(P : Scheme.{u}) [Nonempty P]`
  `(p : P ⟶ Spec S.functionField) [IsFinite p] [Etale p]`.
- The existential `(L : Type u) (_ : Field L) (_ : Algebra S.functionField L)` introduces
  a field extension. `FiniteDimensional S.functionField L` expresses its finiteness;
  `Algebra.IsSeparable S.functionField L` expresses separability (including algebraicity).
- The point is `u : Spec (.of L) ⟶ P`. The equation `u ≫ p = Spec.map ...` says that it
  is a K-morphism for the specified extension, not an arbitrary scheme morphism.
- The actual normalization is the recorded `S.normalizationIn L`, and q is the recorded
  `S.fromNormalizationIn L`; both are the affine integral-closure construction, not
  existential substitute schemes or maps.
- `IsIntegral (S.normalizationIn L)` gives integrality. The following universal stalk
  condition gives `IsDomain` and `IsIntegrallyClosed` at every point, precisely normality.
- `IsFinite`, `IsProper`, and `Surjective` of `S.fromNormalizationIn L` render the three
  asserted properties of q. Finite type over k is `LocallyOfFiniteType` and `QuasiCompact`
  of `S.fromNormalizationIn L ≫ s`.
- The canonical j_L is `(S.fromSpecOfAlgebraFunctionField L).toNormalization`, the existing
  natural factorization of `Spec L → Spec K → S` through its relative normalization.
  `IsGenericPoint (j_L (IsLocalRing.closedPoint L)) Set.univ` identifies its unique source
  point with the generic point of the normalization.
- `e : Spec L ≅ Spec (S.normalizationIn L).functionField`, together with
  `e.hom ≫ (S.normalizationIn L).fromSpecFunctionField = j_L`, gives the function-field
  identification induced by j_L, including its residue-field isomorphism. Spectrum is
  fully faithful, so this is exactly a field isomorphism, not merely a point bijection.
- The map `a : Spec (S.normalizationIn L).functionField ⟶ Spec S.functionField` is
  specified by `fromSpecFunctionField ≫ q = a ≫ S.fromSpecFunctionField`; hence it is
  the map induced by q on generic fields. The additional equality
  `e.hom ≫ a = Spec.map (CommRingCat.ofHom (algebraMap S.functionField L))` records
  compatibility with the given K-extension. In particular this is not an arbitrary
  field identification. The canonical generic-point morphism is a monomorphism, so
  the specification of a is unique.
- The final existential is an isomorphism `Spec L ≅ pullback q S.fromSpecFunctionField`.
  Its first projection is j_L and its second projection is exactly the spectrum of
  `algebraMap S.functionField L`. The pullback universal property therefore identifies
  its hom with the canonical map and expresses the isomorphism over Spec K.

Dependency declarations read and used (including their full source signatures/docstrings):

| Node | Module | Declaration used |
| --- | --- | --- |
| def-weil-field | Mathlib.Algebra.Field.Defs | Field |
| def-pc-scheme | Mathlib.AlgebraicGeometry.Scheme | AlgebraicGeometry.Scheme; Scheme.Hom |
| def-pc-integral-scheme | Mathlib.AlgebraicGeometry.Properties | AlgebraicGeometry.IsIntegral |
| def-weil-finite-type-morphism | Mathlib.AlgebraicGeometry.Morphisms.FiniteType; Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact | LocallyOfFiniteType; QuasiCompact |
| def-weil-finite-integral-morphism | Mathlib.AlgebraicGeometry.Morphisms.Finite | AlgebraicGeometry.IsFinite |
| def-weil-surjective-morphism | Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap | AlgebraicGeometry.Surjective |
| def-weil-proper-morphism | Mathlib.AlgebraicGeometry.Morphisms.Proper | AlgebraicGeometry.IsProper; IsSeparated |
| def-sc-function-field | WeilConjectures.AlgebraicGeometry.FunctionField; Mathlib.AlgebraicGeometry.FunctionField | Scheme.functionField, the dependency's explicitly recorded integral-scheme clause |
| def-pc-field-extension | Mathlib.Algebra.Algebra.Defs | Algebra; algebraMap |
| def-weil-pbc-separable-algebraic-extension | Mathlib.FieldTheory.Separable | Algebra.IsSeparable |
| def-pc-fibre-product | Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback | pullback; pullback.fst; pullback.snd |
| def-sc-generic-point | Mathlib.Topology.Sober | IsGenericPoint |
| def-fin-normalization-extension | WeilConjectures.Mathlib.AlgebraicGeometry.Normalization | Scheme.normalizationIn; Scheme.fromNormalizationIn; Scheme.fromSpecOfAlgebraFunctionField |
| def-weil-closed-immersion | Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion | IsClosedImmersion, via the definition of IsSeparated |
| def-weil-etale-morphism | Mathlib.AlgebraicGeometry.Morphisms.Etale | AlgebraicGeometry.Etale |

For j_L the existing relative-normalization map is `Scheme.Hom.toNormalization` from
Mathlib.AlgebraicGeometry.Normalization, with its exact factorization identity
`toNormalization_fromNormalization`. No copy of the dependency's notions is introduced.
All recorded statement modules are imported publicly. The stated proof-dependency modules
are imported as well: the two upstream étale-fibre and residue-normalization modules,
Mathlib Noetherian, Pullbacks, and Localization.Integral; the remaining proof modules are
already public statement imports. All variables and the universe are explicitly bound,
with `set_option autoImplicit false`.

Edge cases checked before writing: integrality already excludes an empty base; nonemptiness
of P is essential and explicit. If P has several field factors, one factor is selected;
no K-rational point and no splitting of all factors is asserted. L=K and degree one are
allowed, including a nonnormal S (its ordinary normalization appears). Neither normality
of S nor perfection of k nor a characteristic restriction is imposed. Zero-dimensional S
is allowed. A finite extension is small in the same universe as K; no independent small
universe of test objects is used. The canonical maps and both projection equations retain
the identity-extension case and the originally specified K-structure.

Searches for an existing statement (2026-10-24; full machine results in searches.jsonl):

- LeanFinder: “A nonempty finite etale scheme over a function field admits a finite
  separable point whose normalization is a finite normal integral cover with the
  canonical generic fibre”. Eight results include relative normalization constructors
  and integral instances and `Algebra.Etale.iff_exists_algEquiv_prod`; none states the
  complete selection/normal-cover/generic-fibre result.
- Loogle: `"AlgebraicGeometry.Scheme.normalizationIn"`. No indexed results.
- Mathlib grep: `normalization.*finite|finite.*normalization|generic.*normalization`
  in AlgebraicGeometry. Five ZariskisMainTheorem hits, none the requested statement.
- LeanSearch: “Finite separable field point of a nonempty finite etale generic scheme
  and finite normal normalization cover”. Eight separability/formal-étale results;
  none the combined assertion.
- Project/source rg: searched `normalizationIn`, normalization/extension combinations,
  `genericNormalCover`, `generic_normal_cover`, and the item's exact blueprint id in
  WeilConjectures and Sheaf. Read the existing normalization/function-field modules,
  `FiniteEtaleNormalGenericComponents`, and `NormalizationCoverIn`. They provide
  ingredients or a cover already defined over an open/normal base, not this theorem.
  The upstream exact-id search found no declaration. The new declaration name has no
  match in either source root.

Validation: scompile.py compiled both the sandbox and library module cleanly on the
server; every subsequent delivered source version is rechecked by deliver2.py. No
STATEMENT-DISPUTED flag or node fault was found. No theorem is proved at this stage.

## Second reading by N0

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
