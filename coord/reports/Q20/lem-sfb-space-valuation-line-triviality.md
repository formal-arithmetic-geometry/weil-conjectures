## Worker report

The single new module `Sheaf.AlgebraicGeometry.SpaceValuationLineTriviality` states
`AlgebraicGeometry.AlgebraicSpace.lineModule_trivial_of_generic_trivial_over_valuationRing`.
Its only theorem proof is `by sorry`; no definitions or auxiliary theorems are introduced.
Source read: `literature/stacks-project/moduli.tex`, Tag 0DNJ,
`lemma-pic-functor-uniqueness-part`, especially the paragraph beginning “Denote f”
and the final section argument (lines 1530–1584 in this checkout).
The five-step docstring records the complete supplied DAG proof, including the actual
section class and the proper closed-image argument over a local base.

Hypotheses and clauses, in the order of the node:

- A valuation ring R with fraction field K: `(R : Type u) [CommRing R] [IsDomain R]
  [ValuationRing R]`, `(K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]`.
  `ValuationRing.TFAE` identifies the divisibility-based Mathlib class with the node's
  either-x-or-inverse-in-R fraction-field condition. The chosen fraction-field model
  imposes no extra condition on R.
- An algebraic space X and its map to Spec R: `X : AlgebraicSpace (Spec (CommRingCat.of R))`
  and `f : X ⟶ schemeSpace (Over.mk (𝟙 (Spec (CommRingCat.of R))))`.
  The category is the recorded full subcategory of fppf sheaves with representable diagonal
  and an etale surjective scheme atlas, not the subcategory of schemes.
- Properness: `hproper : MapIsProper f`. Its definition is the conjunction of
  separatedness, finite type, and universal closedness, exactly as expanded in the node.
- Flatness: `hflat : MapIsFlat f`, testing flatness on every compatible pair of etale charts.
- Finite presentation: `hlfp : MapIsLocallyOfFinitePresentation f`, together with
  `hqc : MapIsQuasiCompact f.hom.hom` and
  `hqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom)`.
  These are the local finite presentation, quasi-compactness and quasi-separatedness
  clauses explicitly specified by the node. Some follow already from properness;
  keeping the full expansion does not impose a stronger geometric requirement.
- Every geometric fibre is integral: `hgeom` quantifies over every field `Ω : Type u`,
  its algebraic closedness `[IsAlgClosed Ω]`, and every ring homomorphism `a : R →+* Ω`.
  The map is the Yoneda image of `Spec.map (CommRingCat.ofHom a)` in the category over
  Spec R, with both represented source and target explicit. `enlargedFibreProduct f ...`
  is the actual sheaf pullback X times_SpecR Spec Ω. Its `.IsReduced` uses all etale
  scheme charts. `IrreducibleSpace (Point (...).obj.obj)` includes nonemptiness and
  irreducibility for the recorded atlas topology. Thus empty geometric fibres are excluded.
- A line module on the small etale structure sheaf: `(L : X.Modules) (hL : X.IsLineModule L)`.
  This is the recorded notion of locally being isomorphic to the structure module on
  covering sieves. The ordinary scheme invertible-module declaration is imported as
  the node's scheme specialization reference; it is not substituted for the space notion.
- Generic triviality: `hgeneric : Nonempty ((moduleTensorPullback
  (enlargedFibreProductFst f ...)).obj L ≅ SheafOfModules.unit (...).structureSheaf)`.
  Here the repeated map is exactly the represented Spec K to Spec R map induced by
  `algebraMap R K`. The fibre and its first projection use the existing definitions;
  the pullback uses the recorded canonical tensor functor, not an arbitrary map or functor.
- Global triviality: `Nonempty (L ≅ SheafOfModules.unit X.structureSheaf)`.
  The hypothesis asks only that some generic trivialization exists, and the conclusion
  asks only that some global trivialization exists; no specified trivialization is extended.
- Arbitrary valuation rank and absence of Noetherian hypotheses, sections, rigidifications
  and algebraic Picard spaces: no corresponding binders occur. All types use arbitrary `u`.
  Test fields are in that same universe, as in the existing algebraic-space site convention;
  algebraic closures and fraction fields are available there, so the geometric hypothesis
  is not vacuous for size reasons.
- Direct image and tensor pullback are the existing canonical functors of
  `AlgebraicSpaceModuleOperations`. Only tensor pullback is needed in the signature;
  direct image occurs in the proof plan.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.Modules`, `structureSheaf`, `IsLineModule`, including their full definitions.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`,
  read as the scheme-specialization reference (Zariski locally rank one).
- `Mathlib.RingTheory.Valuation.ValuationRing`: `ValuationRing`, `ValuationRing.TFAE`;
  the dependency is a Mathlib match and requires no new Lean record.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleTensorPullback`,
  specified as the left adjoint of the chart-limit `moduleDirectImage`, with its normalized
  `moduleTensorAdjunction` retained.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsProper`, `MapIsFlat`,
  `MapIsLocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapIsQuasiCompact` (also used on the diagonal).
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`,
  `enlargedFibreProduct`, `enlargedFibreProductFst`.
- `Sheaf.AlgebraicGeometry.ReducedAlgebraicSpace`: `AlgebraicSpace.IsReduced`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`;
  the standard `IrreducibleSpace` includes nonemptiness.

The item's `stmt_deps` gains only already-landed definition owners:
`def-sfb-space-morphism-properties`, `def-sfb-proper-curve-moduli`,
`def-trf-scheme-algebraic-space`, `def-sfb-space-sheaf-fibre-product`,
`def-sfb-reduced-algebraic-space`, `def-a1-space-point-topology`.
The existing statement and proof are unchanged. There are no new nodes, dependency repairs,
statement corrections or disputed statements.

All currently recorded proof-dependency modules are imported without `public`:
`SpaceProperFieldGlobalFunctions`, `PerfectJumpLoci`, `SpaceDualEffectiveLineTriviality`,
`PerfectAffineModulePreimage`, `AffineQCohDerivedEquivalence`,
`BoundedPseudoCoherentResidueModel`, `FlatComplexDerivedPullback`, and
`SpaceAffineBaseHigherImageSections` (with their exact Sheaf/WeilConjectures paths in the file).
`lem-sfb-proper-flat-space-derived-base-change` has no recorded Lean declaration at the
read base and is therefore not imported; its proof input is fully described in the docstring.
It is a proof dependency, not a missing notion required for this statement.

Edge cases checked before writing: R may itself be a field, when its generic map is an
isomorphism and the implication reduces to its given triviality; a zero ring is excluded
already by the valuation-domain definition; the empty space fails the required nonempty
geometric fibres; disconnected or nonreduced geometric fibres fail the indicated conjuncts.
Arbitrary rank and non-Noetherian valuations, positive characteristic, non-scheme algebraic
spaces and line modules without any chosen basis are all retained. The free-model argument
uses no discrete valuation parameter. A trivial line satisfies both isomorphism conclusions.

Searches made on 2026-10-24:

- `msearch.py ... leanfinder`, query “An invertible module on a proper flat algebraic space
  over a valuation ring with integral geometric fibres is trivial if its generic fibre is
  trivial”: 8 hits, headed by `CommRing.Pic.subsingleton_iff`, its semiring variant,
  `CommRing.Pic.instSubsingletonOfIsLocalRing`, and ring-module freeness. None is the
  algebraic-space statement.
- `msearch.py ... leansearch`, query “A line module on a proper flat finitely presented
  algebraic space over a valuation ring is trivial if its generic restriction is trivial
  and its geometric fibres are integral”: 8 hits about flat modules and trivial Lie
  actions, including `Module.Flat.of_forall_isTrivialRelation`; no match.
- `msearch.py ... loogle`, query `"ValuationRing", "IsInvertible"`: zero hits.
- `msearch.py ... grep`, regex `valuation.*[Pp]ic|generic.*[Tt]rivial|[Tt]rivial.*generic`:
  3 Mathlib hits in FunctionField, Tropical.BigOperators, and ModelTheory.IsAlgClosed;
  none states the required theorem.
- `rg` with that same regex in both `lean/WeilConjectures` and `lean/Sheaf`: assorted
  generic-point identities, descent results and the scheme-only valuation/coherent-sections
  theorem; none states the present algebraic-space implication. The source and docstring
  of `ValuationProperCoherentSections.lean` were read to exclude an exact existing match.
- `grep -rn "lem-sfb-space-valuation-line-triviality" lean/WeilConjectures`: no hits.
- Additional `rg` searches in `lean/Sheaf/AlgebraicGeometry` for `MapIsFlat`,
  `MapIs.*Presentation`, `GeometricallyIntegral`, `geometricFib`, `enlargedFibreProduct`
  and fibre/base-change declarations located the exact reusable interfaces above.
  `GroupSpaceIntegralFibres` was inspected: its structural-map predicate is attached
  to a different group-space node, so this statement writes its elementary conjunction
  using the existing fibre product, reducedness and point topology directly.

Validation: the prescribed `scompile.py Q20 lem-sfb-space-valuation-line-triviality`
compiled the final module in sandbox and library mode with no errors or warnings
(2.9 s and 2.7 s). The initial compile exposed missing type annotations on the
Yoneda map; both its represented source and target are now explicit. Auto-implicit
binding is disabled and all universes and variables are explicitly bound.

## Second reading by Q20

Author's separate clause-by-clause self-check, as required by the direct-delivery brief;
independent mathematical review is left to the maintainer, not claimed here.
I reread the node, Stacks 0DNJ and the final source together. The valuation-domain and
fraction-field binders match the first sentence. The next five geometric binders give
properness, flatness and all three finite-presentation components. `hgeom` uses all
maps to algebraically closed fields, not just the generic and closed fibres. Reducedness
and nonempty irreducibility are separate conjuncts on the actual fibre. `hL` is small-etale
local rank one. `hgeneric` uses the precise fraction-field map, the actual fibre projection
and the already recorded canonical tensor functor. The conclusion is an isomorphism to
the structure module in the same small-etale module category. No normalization, section,
Noetherian condition, valuation-rank restriction or scheme representability was inserted.
The only mismatch found during this reading was an initially insufficient annotation
of the represented field-to-base maps; the corrected annotations identify the actual
source schemes and do not change the mathematics. Definition ownership is explicit in
the added landed-node dependencies. No mathematical mismatch remains.
