## Worker report

The module Sheaf.Paper.ContinuousAlgclScalarExtensionConstructible states
AlgebraicGeometry.ProEtale.ContinuousAlgclScalar.scalar_extension_constructible.
Its only theorem has proof `sorry`. The auxiliary definition
AlgebraicGeometry.ProEtale.CondensedRing.lisseSupportDerivedScalarMap has real data:
the universal derived counit, the single-complex comparison and the published
finiteStageSupportScalarMap. Two new existing-definition ownership nodes repair H2; no Lean construction is duplicated
and the natural-language statement is unchanged.

Clause-by-clause translation:

- A prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- The fixed normed algebraic closure is `(Ω : Type u) [NormedField Ω]
  [NormedAlgebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]`. NormedAlgebra says the
  norm extends the ell-adic norm. No CompleteSpace instance is required.
- The finite intermediate extension, with restricted norm topology, is
  `(E : IntermediateField ℚ_[ℓ] Ω) [FiniteDimensional ℚ_[ℓ] E]`.
- A and B are `Profinite.continuousCoefficientRingObj E` and the same
  construction for Ω. These are definitionally the recorded
  `continuousMapRingObjOfUniverse.{u,u}` constructions, whose sections are
  universe lifts of ALL continuous maps. No finite-range or finite-subextension
  image condition is present. This equality is also documented and checked by the
  existing ContinuousAlgclScalarConstructibility module.
- The inclusion is `ContinuousAlgclScalar.inclusion ℓ Ω E`, defined by the
  recorded continuousMapRingObjMapOfUniverse of the actual subtype inclusion.
  Its pullback to X is `coefficientInclusion ℓ Ω E X`.
- Noetherian Z is `[IsLocallyNoetherian Z] [CompactSpace Z]`, as in the node.
  No base field, characteristic, finite-type or separatedness assumption is added.
- A_Z and B_Z are `condensedRingObj ... Z`, the existing coefficientRing
  underlying objects, with their transported commutative ring structures.
- Internal module objects are exactly `Mod (Sheaf (Scheme.ProEt.topology Z)
  Ab.{u+1}) (condensedRingObj ... Z)`. Their ordinary unbounded category is
  `DerivedCategory` and T_Z is `scalarExtension ℓ Ω E Z`, the recorded
  `(Mod.extendScalars (coefficientInclusion ...)).leftDerivedFunctor`.
- Bounded constructibility is `constantModelBoundedConstructible ... Z K`:
  bounded cohomology and each homology object has the parent definition's finite
  constant scalar models on a finite constructible locally closed stratification.
  Over the scalar fields E and Ω, finitely presented scalar modules are exactly
  finite-dimensional vector spaces. This uses the actual existing constant-model
  definition, not the different arbitrary local finite-presentation predicate.
- The first conjunct quantifies EVERY such K. Its conclusion is the same
  bounded-constructible predicate at Ω for `T_Z.obj K`, conjoined with
  `DerivedCategory.finiteTorAmplitude _ (T_Z.obj K)`. The latter tests relative
  tensor against every module in degree zero, including nonconstructible ones.
- The precise supported clause quantifies S,C,j,i with j open and i closed.
  `Topology.IsConstructible (Set.range (j ≫ i))` is constructibility of c.
  `Set.range i = closure (Set.range (j ≫ i))` says C realizes its closure.
  Thus this is exactly the open-then-closed factorization specified by the node.
- `finiteStageSupportExtension ... j hj i` is the existing exact i_* j_!.
  No unbounded right-derived direct-image functor replaces this exact functor.
- L is an actual A_S internal module; the antecedent
  `IsLisseCoefficientModule ... L` uses the recorded pro-etale finite-free
  cover definition. The conclusion applies that same predicate to
  `(Mod.extendScalars (coefficientInclusion ... S)).obj L` over B_S.
- The rank clause quantifies V,f,r: a trivialization of f^*L by
  `Mod.finiteFree ... r` implies the analogous trivialization of f^*L_B by
  `Mod.finiteFree ... r`. Rank zero is included by r : Nat without a positivity
  hypothesis. All charts, not just a chosen cover, are covered.
- The last clause is `IsIso (lisseSupportDerivedScalarMap ... L)` in
  D(Mod_{B_Z}). Its source is T_Z(c_!L[0]); its target is (c_!L_B)[0].
  This is stronger specification of the map, not an arbitrary existence of an
  isomorphism: the arrow is explicitly the derived counit followed by the
  published closed pushforward mate and open scalar isomorphism, with the
  single-complex comparison between them. These are the balanced, unit-normalized
  maps; the proof docstring records identification with the two support projections
  and normalized pullback/tensor comparison. Every arrow is B-linear by its type.

Dependencies read and used (all recorded declarations and docstrings inspected):

| Node | Module and declaration(s) |
| --- | --- |
| def-weil-algebraic-closure | Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure: AlgebraicClosure; the arbitrary fixed closure is expressed by Mathlib.FieldTheory.IsAlgClosed.Basic: IsAlgClosure |
| def-weil-l-adic-coefficient-extension | Sheaf.NumberTheory.Padics.CoefficientExtensionFinite: Padic.finite_coefficientExtensionRing; the field portion is its FiniteDimensional ℚ_[ℓ] E binder, with the node's norm-extension condition expressed by NormedAlgebra |
| def-sfb-continuous-map-condensed-ring | Sheaf.Topology.ContinuousMapCondensedRing: Profinite.continuousMapRingSheafOfUniverse, continuousMapRingObjOfUniverse and their ring structures |
| def-sfb-continuous-map-condensed-ring-map | Sheaf.Topology.ContinuousMapCondensedRingMap: Profinite.continuousMapRingSheafMapOfUniverse and continuousMapRingObjMapOfUniverse |
| def-weil-pbc-quasi-compact-scheme | Mathlib.Topology.Defs.Filter: CompactSpace |
| pqf-def-locnoeth | Mathlib.AlgebraicGeometry.Noetherian: AlgebraicGeometry.IsLocallyNoetherian |
| sk-def-sfb-pulled-back-coefficients | WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic: coefficientRing, condensedRingObj |
| sk-def-sfb-module-objects | Mathlib.CategoryTheory.Monoidal.Mod: CategoryTheory.Mod |
| sk-def-sfb-derived-categories | Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions: rightDerivedFunctorOfQuasiIsoResolutions, with its imported ordinary DerivedCategory |
| sk-def-sfb-derived-extension-of-scalars | WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars: Mod.derivedExtendMapDerivedCategoryAdjunction, Mod.extendScalars and Functor.leftDerivedFunctor |
| def-constructible-stratification | Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification: Scheme.FiniteLocallyClosedStratification |
| sk-def-sfb-constructible | Sheaf.Paper.CondensedConstantConstructibility: HasFiniteConstantLocalModel, IsConstantModelConstructible, constantModelBoundedConstructible |
| det-def-sfb-constructible-local-model | Sheaf.AlgebraicGeometry.FiniteConstantLocalModel: finiteConstantLocalModel_iff_exists_cover |
| det-def-sfb-constructible-tor-amplitude | Sheaf.Paper.ConstantModelTorAmplitude: constantModelConstructibleFiniteTor_wellDefined; DerivedCategory.finiteTorAmplitude |
| lem-weil-pbc-condensed-open-closed-recollement | Sheaf.Paper.CondensedOpenClosedRecollement: CondensedRing.condensed_open_closed_recollement and the exact openImmersionLowerShriek/lowerStar functors |
| def-sfb-lisse-coefficient-module | Sheaf.Paper.CoefficientHeartStratificationDefs: IsLisseCoefficientModule |

The statement now cites two definition ownership nodes, not the theorem nodes whose
modules happen to contain these plain declarations. Both definitions use existing:true
records and retain the same directly imported modules. See New nodes below.

Proof-only dependency modules are imported for the four-step plan: LocallyFreeDerivedScalars,
CondensedSupportProjectionFormula, KFlatScalarComparisonNormalization,
ContinuousQbarConstructibleGenerators, CoefficientHeartGeneration and
OrdinaryDerivedChangeOfRings. The alpha-isomorphism proof dependency is supplied
by the directly imported ModuleObject.Basic. The recollement and Tor-amplitude
modules also serve as statement dependencies. The docstring spells out all four
reviewed proof steps and names these nodes.

Edge cases checked before writing: empty Z and empty S are admitted; zero K and
zero L are admitted; r=0 is admitted; c=id is admitted (j=i=id and closure is all Z).
Acyclic complexes remain included. There is no assumption on characteristic or
base field of Z, no completeness of Ω and no flatness of A→B. The common universe u
is the usual common scheme/coefficient size convention, with abelian coefficients
in u+1; the small pro-etale site's object and morphism universes remain unchanged.

Searches made:

- msearch.py leanfinder: “Derived scalar extension along continuous algebraic closure
  coefficient rings preserves bounded constructibility”: 8 hits, ordinary Chevalley,
  normed scalar extension and algebraic-closure facts, none about this theorem.
- msearch.py loogle: `"Sheaf", "extendScalars"`: 0 hits.
- msearch.py grep: `(constructible|lisse).*(extendScalars|scalar|tensor)`: 0 hits.
- rg in lean/WeilConjectures and lean/Sheaf for scalar/constructible combinations,
  continuousAlgcl and the exact item id: found the two reusable modules above and
  ContinuousAlgClConstructibleTor (only the fixed PadicAlgCl Tor theorem), not the
  full Noetherian scalar-extension statement or its supported canonical-map clause.
- rg in Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json for the new
  names lisseSupportDerivedScalarMap and scalar_extension_constructible: no matches.

Read the current literature/blueprint/latest direct-images proof paragraph (3),
as well as the complete node and the recorded statement dependencies. The source
itself calls this an agent-extracted argument with an exact published reference
wanted; the module does not claim it is a published theorem. No statement correction
or statement dispute was needed.

Validation: scompile.py compiled the module in both sandbox and library mode with
no errors or warnings. The first probe exposed a missing IsMonHom instance for the
underlying bundled inclusion; the final statement supplies the bundle's existing
isMonHom_hom explicitly, without a new assumption or theorem. Delivery preflight
and its final per-file compilation are run separately below.

## Repair of returned delivery 89c9bd0cea93

H2 is repaired by replacing the two theorem-node stmt_deps with definition owners:
`def-sfb-continuous-algcl-scalar-data` owns inclusion, coefficientInclusion,
coefficientInclusion_isMonHom and scalarExtension; `def-sfb-support-scalar-data`
owns finiteStageSupportExtension and finiteStageSupportScalarMap. Both are existing:true
records on the exact published declarations, so the retained direct public imports are
now imports of the definition-owning modules. Comments on these imports make the
ownership explicit. Neither scalar_constructibility nor
continuousAlgCl_finite_stage_devissage is cited or used as a hypothesis/conclusion.

Compared the retained delivered node with current main before editing: the only fields
that differed were lean and stmt_deps. Rebuilt the item node from current main, applying
only the repaired stmt_deps and Lean record. The main theorem signature and the
lisseSupportDerivedScalarMap body remain identical to the independently accepted
mathematics of immutable head 89c9bd0cea93. The new ownership nodes carry no new theorem,
no sorry and no definition module; they bind existing data only.

## New nodes

`def-sfb-continuous-algcl-scalar-data` owns the existing all-continuous intermediate-field
inclusion, its pulled-back coefficient ring map and its ring-map instance, and the ordinary
unbounded total-left-derived scalar extension. It allows arbitrary intermediate E and normed
Omega with an ell-adic algebra structure, exactly the existing definitions' binders; it
asserts no constructibility theorem. Source: the current direct-images proof paragraph (3),
extracted supported-lattice step 2's coefficient setup, and the existing construction
source's HRS Section 3 references. The primary recorded signature is the existing
`abbrev inclusion`, and declarations lists all four used construction names. Grep found
these names only under the theorem ownership record, not any definition node. The existing
names therefore receive a definition record, with no duplicate Lean definition.

`def-sfb-support-scalar-data` owns the actual composite j_! then i_* and the actual
scalar/support arrow, for arbitrary i and open j, exactly as defined. Its scalar arrow is
the direct-image mate followed by direct image of the open scalar isomorphism, with the
specified target coefficient action. It asserts no invertibility theorem and imposes no
closedness or flatness hypothesis in the general definition; the item's theorem specializes
to closed i and lisse L. Source: the same paragraph (3), canonical support comparison.
The existing def-sfb-locally-closed-coefficient-extension only provides the canonical
scheme-theoretic-image factorization functor; it does not own these arbitrary-factorization
support and scalar-map declarations. The primary recorded signature is the exact existing
`def finiteStageSupportScalarMap`, with both construction names listed in declarations.

Searches for BOTH nodes: msearch leansearch query “Continuous normed field inclusion induces
condensed ring scalar extension and module support scalar comparison” returned 8 ordinary
continuous/restricted-scalar normed-module hits, no exact condensed coefficient construction.
msearch leanfinder query “Canonical scalar extension coefficient inclusion and open closed
support extension of condensed modules” returned 8 CondensedMod/LightCondensed solid, free
or locally constant module hits, no exact construction. msearch grep query
`finiteStageSupportExtension|finiteStageSupportScalarMap|coefficientInclusion|scalarExtension`
returned zero Mathlib hits. Direct grep of the DAG found only the two theorem records;
project Lean searches found the exact existing definitions in the two named modules.
The new nodes retain those declarations with existing:true. Blueprint searches
`continuous scalar` found 0 matches and `support scalar` found only the unrelated finite
compact-support scalar-transport theorem; neither owns these constructions. The ancestry
tool reports null for this item, retained in both blueprint.from.node records; via starts
with this item and continues with its inherited path.

All hypotheses and clauses continue to have the translation in the Worker report above.
The repair changes ownership and dependency metadata only. No source-based statement
correction, mathematical change or dependency-interface replacement is required.

## Second reading by Q80

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
