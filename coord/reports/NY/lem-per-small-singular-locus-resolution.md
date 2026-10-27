## Worker report

The item is stated by `AlgebraicGeometry.exists_smallSingularLocusResolutionRule` in
`Sheaf.AlgebraicGeometry.SmallSingularLocusResolution`. Its type is
`Nonempty SmallSingularLocusResolutionRule.{u}`: there is one assignment on the entire
pair type, with the required properties for all morphisms. Its only proof is `by sorry`.
All three accompanying definition modules have real data and no postponed proofs.
The item's natural-language statement is unchanged. Only `lean` and additions to
`stmt_deps` are delivered for the item.

I read Temkin, arXiv:0904.1592v2, the PDF linked by the node, especially §3.4.2,
Theorem 3.4.1 and Remark 3.4.2(i), printed pp.25–26, and the introduction's strong
variety input. The source's general category allows generically reduced inputs;
the node uses its reduced subcategory, which the Lean retains. The source explicitly
allows regular maps and explicitly leaves independence from the divisor unresolved.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

* A pair `(X,D)` is `SmallSingularLocusPair`. `scheme : Scheme.{u}` and
  `structureMap : scheme ⟶ Spec (.of (ULift.{u} ℚ))` express a scheme over Q.
  `ULift` changes only size, and imposes no finite-type condition on X.
* Reduced is the existing `IsReduced scheme` in `reduced`. It is sectionwise
  reducedness, equivalent to the node's reduced local rings.
* Noetherian is `IsNoetherian scheme` in `noetherian`, not merely locally
  Noetherian. Mathlib's `isNoetherian_iff_of_finite_iSup_eq_top` and
  `isNoetherian_iff_of_finite_affine_openCover` identify this with a finite affine
  cover by Noetherian coordinate rings. I read the class and these equivalences.
* Quasi-excellent means `∀ U : scheme.affineOpens, IsQuasiExcellent Γ(scheme, U.1)`
  in `quasiExcellent`, using the dependency's actual predicate, not a replacement.
* The ideal of D is `divisor : scheme.IdealSheafData`. This existing type records
  quasi-coherent ideals and supplies the actual closed scheme `divisor.subscheme`.
  `cartier : divisor.IsInvertible` is exactly the existing local non-zero-divisor
  generator condition. It does not replace an effective Cartier divisor by an
  arbitrary closed subset or by a principal divisor globally.
* The divisor contains the singular locus by `singularSupport`: every point where
  `IsRegularLocalRing (scheme.presheaf.stalk x)` fails belongs to `divisor.support`.
* The abstract divisor has the required finite disjoint-union presentation by
  `divisorPresentation`. There are a natural number n, schemes V indexed by `Fin n`,
  bundled commutative rings K indexed independently by `Fin n`, and morphisms
  `s i : V i ⟶ Spec (K i)`. Each K has `IsField` and `CharZero`; each morphism has
  `LocallyOfFiniteType` and `QuasiCompact`, exactly finite type. The isomorphism
  `divisor.subscheme ≅ ∐ V` is an isomorphism of abstract schemes. No common field,
  irreducibility, reducedness, or separatedness of the V is imposed.
  The presentation is existential in Prop, so H cannot depend on a chosen
  decomposition or coefficient field absent from the original pair.
* A regular morphism is `IsRegularSchemeMorphism f`: the conjunction of `Flat f`
  and regularity after every finite extension K of the residue field at every x.
  It uses `f.fiberToSpecResidueField x` and its scheme-theoretic pullback along
  `Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K))`. Finite extension
  means `[FiniteDimensional (X.residueField x) K]`. It neither tests all arbitrary
  extensions nor replaces regular by smooth. The test fields have `Type u`, the
  same universe as the residue fields, and include their identity extensions.
* The divisor pullback condition is `Q.divisor = P.divisor.comap f` in the rule's
  `comparison`. Extension of the actual ideal sheaf is precisely the schematic
  inverse-image closed subscheme. Morphisms require no extra map of coefficient
  fields and no finite-type or separation hypothesis. The structure map to Q is
  unique; no extra choice of a rational base map enters this condition.
* A single H on all pairs is the field
  `tower : ∀ P : SmallSingularLocusPair.{u}, OrdinaryBlowupTower P.scheme` inside
  the one structure whose nonemptiness the theorem asserts. This is not a separate
  existence assertion for each object. `OrdinaryBlowupTower` is the existing
  finite tower with initial identification and the actual blowup at every stage.
* `resolves : ∀ P, (tower P).IsRegularResolution` uses the existing predicate:
  locally finite-type center ideals, nonempty nowhere dense regular center
  schemes, and regular last scheme. Coherence is also imposed explicitly by
  `coherent`, using `RingedSpace.IsCoherent` on `(center i).toModules`, so no
  implicit reinterpretation of coherence is needed. Local finite generation
  and coherence agree here: X is Noetherian and successive ordinary blowups
  with finite-type centers are Noetherian.
* Every center lies over the original singular locus by the rule's
  `singularSupport`, quantified over points z of the actual center subscheme.
  It takes the point along `subschemeι` and the tower's existing `toBase` map and
  asserts failure of regularity of the stalk on the ORIGINAL input scheme.
* For EVERY morphism of pairs, `comparison` supplies a
  `Nonempty (OrdinaryResolutionComparison f (tower P) (tower Q))`.
  I read that existing structure in full. Its level maps and cartesian squares
  express schematic pullback, its monotone count and increasing retained-stage
  embedding express the original order, `retained_ideal` keeps each extended
  ideal exactly, and `deleted_iff_unit` deletes precisely the empty closed centers.
  In particular this never discards a nonempty center just because its blowup is
  an isomorphism. Nonempty here asserts an existing comparison, not a replacement
  of a canonical construction by an arbitrary map or choice.
* `empty_length` is length zero for every pair whose underlying scheme is empty.
  Neither the pair type nor the rule requires nonempty schemes or positive n.
* The rule is indexed by the entire pair P, and has no independence-from-D clause,
  as required by the final sentence of the node.

Dependency declarations and source interfaces read and used:

* `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
* `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`,
  and the finite affine cover equivalences.
* `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent`, including its G-ring and
  finite-type-algebra open-regular-locus conditions.
* `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`, the conjunction
  of local Noetherianity and upstream stalkwise `IsRegular`.
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `LocallyOfFiniteType`, `QuasiCompact`.
* `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup` and `.blowupMap`.
* `Sheaf.AlgebraicGeometry.CoherentFiniteType` and the exact upstream owner
  `WeilConjectures.AlgebraicGeometry.Coherent`: `RingedSpace.IsCoherent`.
  The first compile exposed that the published wrapper did not export this name;
  explicitly importing its published upstream owner resolved this without
  duplicating or changing the predicate. `scompile.py --source` confirmed the
  upstream source and its exact finite-type-kernel definition.
* `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`: `.toModules`.
* `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat` and its base-change instance.
* `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber` and
  `.fiberToSpecResidueField`, built from the canonical residue-field point.
* The additional landed definition `def-trf-ordinary-resolution-rule` owns
  `Sheaf.AlgebraicGeometry.OrdinaryResolutionRule`, from which the actual
  `OrdinaryBlowupTower`, `.toBase`, `.IsRegularResolution`, and
  `OrdinaryResolutionComparison` are reused. No second tower definition was made.
* The additional landed `def-nagata-invertible-ideal` owns `.IsInvertible` in
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`; its docstring
  and local non-zero-divisor signature were read in full.
* The theorem has proof-only imports of `WeilConjectures.Blowup.FlatBaseChange`
  (`blowupFlatBaseChangeIso`, recorded by the closed upstream audit of
  thm-nagata-blowup-flat-base-change) and `.InvertibleCenter`
  (`isIso_blowupMap_of_isInvertible`). The flat base-change dependency is already
  provided by the public flatness import. The four new formal-geometry proof
  prerequisites have no recorded statements and hence no modules to import yet;
  they remain the named proof dependencies and are explained step by step in the
  theorem's proof docstring. They are not needed to type this theorem.

Edge cases checked before writing: the empty scheme, n=0 in the divisor
presentation, the empty divisor on a regular scheme, zero-length towers, arbitrary
finite disjoint unions with different coefficient fields, identity residue-field
extensions, regular maps not of finite type, open restrictions deleting some
centers, and a nonempty center whose ordinary blowup is an isomorphism.
No nonempty index assumption, dimension bound, separation, common field, smoothness,
or divisor-independence condition has been introduced. All universes and variables
are explicit (`autoImplicit false`, `relaxedAutoImplicit false`).

Searches: msearch.py LeanFinder for strong resolution under regular morphisms
returned normalization, smoothness and étale declarations, no theorem match;
Loogle `"desingularization"` returned 0; Mathlib grep
`desingulari[sz]|SmallSingular|OrdinaryBlowupTower` returned 0. Searches for the
three missing notions are recorded verbatim in every new node's mathlib_searches:
LeanSearch for regular scheme morphisms returned Flat and smoothness ingredients;
LeanFinder for disjoint unions of characteristic-zero varieties returned
HasFiniteCoproducts and coproduct/normalization facts; Loogle for the regular
morphism name and grep for all three new names returned 0. LeanSearch for pairs
and ordered blowup rules returned smoothness and finite-morphism facts.
I also searched Mathlib/AlgebraicGeometry, WeilConjectures, Sheaf, the DAG definition
nodes and dag/lean_names_upstream.json by names and concepts. `grep -rn` of the item
id in WeilConjectures found nothing. blueprint_refs.py searches for small singular
locus and regular scheme morphism found no definition. OrdinaryResolutionRule was
the usable existing tower/comparison interface and is reused, as above.

Validation: all four delivered files compiled individually in dependency order
through scompile.py on the server. The final run has no errors and no unexpected
warnings. No project build or local direct Lean compile was run. No
STATEMENT-DISPUTED flag or source-based statement correction is needed.

## New nodes

`def-per-regular-scheme-morphism` owns `RegularSchemeMorphism.lean` and the real
predicate `IsRegularSchemeMorphism`. This is the finite-residue-field-extension
geometric regularity test, together with flatness, in Temkin §2.1.1 / Stacks 07BZ.
The existing DAG only expanded this notion in theorem statements and had no
definition node or scheme-level declaration; the ring-level regular-map predicate
has different objects. Searches are recorded verbatim and the scheme fibre,
flatness and regular-scheme predicates are reused.

`def-per-small-singular-locus-pair` owns `SmallSingularLocusPair.lean`.
It packages exactly the reduced pairs in Temkin §3.4.2, with the required Cartier
ideal, singular support and existential finite abstract disjoint-union
presentation. Searches found no existing pair definition. The component fields
are part of an existence proposition, so the pair has no presentation-dependent
auxiliary choice. It cites the existing invertible ideal node and all existing
geometric predicates it uses.

`def-per-small-singular-locus-resolution-rule` owns
`SmallSingularLocusResolutionRule.lean`. It packages the type of assignments whose
existence the item claims, including the explicit coherence, singular support,
regularity, comparison and empty-input clauses. It reuses the existing ordinary
towers and contraction comparisons from def-trf-ordinary-resolution-rule rather
than restating them; that older definition supplies a smooth-functorial rule on
finite-type rational schemes, not the pair category or regular-morphism rule here.
The source is Temkin §3.4.2 / Theorem 3.4.1 / Remark 3.4.2(i). Its searches are
recorded verbatim; no existing declaration supplies this rule type.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
