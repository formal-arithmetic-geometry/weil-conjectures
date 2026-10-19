## Worker report

The target is stated in `lean/Sheaf/TraceFormula/NoIsolatedContractedFibreComponent.lean` as
`AlgebraicGeometry.no_isolated_contracted_fibre_component`.  It is a stage-2 statement
module; the proof is `sorry` as required for stage 2.

The theorem keeps the fixed schemes `T`, `X`, and `Y` in `Scheme.{u}`. A new canonical
construction `schemeUniverseLift.{u, v}` enlarges these fixed schemes to `Scheme.{max u v}`,
and `schemeUniverseLiftMap` enlarges their morphisms. Every geometric test field is
`Ω : Type (max u v)`, every geometric point has target `schemeUniverseLift T`, and component
schemes live in `Scheme.{max u v}`. Unlike the returned signature, the original schemes do
not change universe when `v` is instantiated.

* `T` is an integral Noetherian scheme, with a named generic point `η` and
  `IsGenericPoint η Set.univ` (`[IsIntegral T]`, `[IsNoetherian T]`, `hη`).
* `pX : X ⟶ T` and `pY : Y ⟶ T` are each flat, locally of finite presentation,
  quasi-compact and quasi-separated.  These are the four Mathlib classes for the
  parenthesized “flat finitely presented (locally finite presentation, quasi-compact
  and quasi-separated)” hypotheses in the node.
* `hXdim` and `hYdim` quantify over every algebraically closed field `Ω` of the
  enlarged universe `max u v` and every `s : Spec Ω ⟶ schemeUniverseLift T`.  They state directly, for
  every irreducible component `Z` of the underlying topological space of the
  geometric fibre, `topologicalKrullDim Z = 1`.  This is the node's pure
  one-dimensional geometric-fibre clause, written without introducing a second
  pure-dimension definition.
* `[Smooth (pX.fiberToSpecResidueField η)]` is smoothness of the generic fibre
  `X_η`.
* `hYnode` quantifies over all geometric fibres and all points.  At a point with
  no smooth open neighbourhood it supplies a nonempty isomorphism from the
  maximal-ideal adic completion of the stalk to
  `MvPowerSeries (Fin 2) Ω ⧸ Ideal.span {X 0 * X 1}`.  This is the completed
  local-ring nodal clause, with the algebraically closed residue field `Ω`.
* `g : Y ⟶ X`, `hg : g ≫ pX = pY`, and `[IsProper g]` state the proper `T`-morphism.
  The following `IsIso` instance is the canonical base-change map between the
  scheme-theoretic generic fibres over `Spec κ(η)`, so it states that `g` is a
  generic-fibre isomorphism.
* `hdense` gives an open `U ⊆ X`, injectivity of the structure-sheaf maps for
  `U` and `g⁻¹U` on every open (the stated meaning of schematic density), and
  the isomorphism after restricting `g` to these opens.
* The first conjunct ranges over a geometric fibre, a component scheme `W : Scheme.{max u v}` with an open and
  closed immersion `i : W ⟶ Y_s`, and a point `x`.  The equality
  `Set.range i = connectedComponent x` makes `W` exactly a connected component;
  connectedness is stated explicitly and the structure map is proper.  The
  conclusion says the image under the induced fibre map of `g` is not
  `Subsingleton`, i.e. the component is not mapped to one point.
* The second conjunct ranges over a closed irreducible component `i : C ⟶ Y_s` with `C : Scheme.{max u v}`,
  assumes its range is disjoint from every other irreducible component and its
  structure map is proper, and gives the same non-contraction conclusion.  This
  is the “in particular” isolated-component clause.

Dependency declarations used were the recorded Mathlib declarations:
`topologicalKrullDim` (`Mathlib.Topology.KrullDimension`),
`AlgebraicGeometry.IsIntegral` (`Mathlib.AlgebraicGeometry.Properties`),
`AlgebraicGeometry.LocallyOfFinitePresentation`
(`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`),
`AlgebraicGeometry.Smooth` (`Mathlib.AlgebraicGeometry.Morphisms.Smooth`),
`IsGenericPoint` (`Mathlib.Topology.Sober`),
`AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`
(`Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `QuasiCompact`),
`AlgebraicGeometry.Flat` (`Mathlib.AlgebraicGeometry.Morphisms.Flat`),
`Scheme.Hom.fiber` and `pullback` (`Mathlib.AlgebraicGeometry.Fiber`),
`AlgebraicClosure` (`Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`), `AdicCompletion` and `IsAdicComplete`
(`Mathlib.RingTheory.AdicCompletion.Basic`), `MvPowerSeries`
(`Mathlib.RingTheory.MvPowerSeries.Basic`), `IsNoetherianRing`
(`Mathlib.RingTheory.Noetherian.Defs`), `AlgebraicGeometry.IsProper`
(`Mathlib.AlgebraicGeometry.Morphisms.Proper`), and
`AlgebraicGeometry.QuasiSeparated`
(`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`).  The fibre-map term is
Mathlib's `CategoryTheory.Limits.pullback.map` on the canonical enlarged morphisms;
`schemeUniverseLiftMap_comp` transports `hg` into its required commuting square; the schematic-density maps use
`Function.Injective` on sheaf sections.  No private copy of a dependency notion
was introduced.

Edge cases checked: `T`, `X`, `Y` remain fixed in universe `u` while `v` is independent;
when `v = 0` the ring lift is ring-equivalent to the original ring, and for larger `v` the
affine-colimit construction gives actual target schemes in the larger universe; empty geometric fibres make the component quantifiers
vacuous; the first conclusion forces a nonempty component because
`connectedComponent x` contains `x`; the second conclusion has the nonempty
irreducible-component premise built into `irreducibleComponents`; zero or
nonreduced stalks are allowed by the raw completion isomorphism; no separatedness
or properness assumption was added for `X` or `Y`; and the generic-fibre map uses
an arbitrary generic residue field rather than silently choosing an algebraic
closure.

Searches made:

* `msearch.py ... leanfinder "proper generically isomorphic map flat nodal curves contracted connected component"`:
  hits for `Flat.generalizingMap`, `Flat`, `Flat.isIso_of_surjective_of_mono`,
  and unrelated Weierstrass declarations; no exact statement.
* `msearch.py ... leansearch "A proper modification of flat nodal curves that is generically an isomorphism does not collapse a whole proper connected fibre component to a point"`:
  flatness and proper-base-change declarations only; no exact statement.
* `msearch.py ... loogle "IsProper, Flat, IsIso, IsConnected"`:
  invalid/unresolved unqualified names and no match; qualified searches likewise gave
  no exact result.
* `msearch.py ... grep "contract.*component|isolated.*component" AlgebraicGeometry`:
  no match.  Direct `rg` over `WeilConjectures/` and project `lean/Sheaf/` found no
  declaration for this theorem (only unrelated comments and stable-modification
  notions).
* Direct DAG search found no node or declaration with this item id and no existing
  theorem statement matching the target.  Existing declarations for the individual
  notions were read in their recorded source files and reused through imports.

One new definition node supplies canonical universe enlargement; no dependency module was needed.  Both delivered modules compiled separately in dependency order with `scompile.py`,
with no errors or warnings beyond the permitted `sorry` handling.  No `STATEMENT-DISPUTED` flag is needed.

## Repair of returned H3

The previous packet put the original schemes in `Scheme.{max u v}`; this did not transport a
fixed `Scheme.{u}`. The repaired theorem binds `{T X Y : Scheme.{u}}` and constructs their
actual enlargements through `schemeUniverseLift.{u, v}`. Its explicit diagram ranges over
all affine maps `Spec A ⟶ X` and sends the ring `A` to `ULift.{v} A`. The enlargement is
Mathlib's chosen colimit, and the enlarged morphism is `colimit.desc` of the cocone obtained
by postcomposition. Thus none of the geometric maps is an arbitrary parameter. The
composition theorem gives the precise commuting square for the induced fibre map of `g`.
For the affine edge case `X = Spec A`, the affine-over-`X` category has terminal object
`(A, 𝟙 _)`, by full faithfulness of `Scheme.Spec`. Its lifted diagram therefore has colimit
`Spec (ULift A)`. Thus on an affine base the new geometric points are exactly ring maps
`ULift A →+* Ω`, and fibres are the usual tensor-product fibres; gluing gives the same
interpretation on general schemes. For the empty scheme the same construction gives the
empty scheme. These checks pin down the transport beyond its universe annotation.

## New nodes

`def-trf-scheme-universe-enlargement` defines the ring lift, affine diagram, chosen colimit,
and canonical enlarged morphism; it includes existence of that colimit and compatibility
with composition. The source is Stacks Tags 01JA–01JC, applied to ring-equivalent lifted
affine coordinate rings. Mathlib has `RingHom.ulift`, which is reused, and same-universe
affine-colimit/gluing results; neither Mathlib, the source project nor the DAG supplies a
universe enlargement of a fixed scheme. LeanSearch, LeanFinder, Loogle and text/DAG searches
are recorded in the new node. The data is determined up to the unique colimit isomorphism,
so using the postponed `HasColimit` proof to define `colimit` is the universal-property
exception explicitly allowed by AGENTS.md §5. The two postponed theorems match the colimit
existence and composition clauses of this definition node, and both have complete proof
docstrings. No definition contains `sorry` data.

## Second reading by Q43

This is the explicit author self-check requested by the repair brief; no additional agent
was started. I reopened the node and both final modules and checked the following clauses.

* Integral Noetherian base and its generic point: `[IsIntegral T]`, `[IsNoetherian T]`,
  `η`, `hη`. The base and both relative curves remain fixed in `Scheme.{u}`.
* Flat finite presentation of both structure maps: `[Flat]`,
  `[LocallyOfFinitePresentation]`, `[QuasiCompact]`, and `[QuasiSeparated]` on `pX` and `pY`.
* Every geometric fibre is pure one-dimensional: `hXdim` and `hYdim` range over all
  algebraically closed `Ω : Type (max u v)` and all maps to the actual enlarged `T`;
  each component has `topologicalKrullDim = 1`.
* Smooth generic fibre of `X`: `[Smooth (pX.fiberToSpecResidueField η)]` on the original
  fixed scheme; the generic isomorphism of `g` is its original residue-field pullback map.
* Nodal geometric fibres of `Y`: `hYnode` uses the enlarged `pY`, the failure of a smooth
  open neighbourhood, maximal-ideal `AdicCompletion`, and the `uv` power-series quotient.
* Proper `T`-morphism and schematic-density modification: `g`, `hg`, `[IsProper g]`,
  the generic `IsIso`, and `hdense` with both sets of injective sheaf-section maps and
  `IsIso (pullback.snd g U.ι)` are retained exactly.
* First conclusion: the geometric point is in the enlarged universe, `W` is a component
  scheme there, and the open/closed immersions, range equality to `connectedComponent x`,
  connectedness and properness over `Ω` describe precisely a nonempty proper connected
  component. Non-contraction is `¬ (Set.range (i ≫ fibreMap)).Subsingleton`.
* Second conclusion: `C` is a closed irreducible component, disjoint from all the other
  components, proper over `Ω`, and its enlarged fibre image is not a subsingleton.
  Neither conclusion introduces marking, stability, or separatedness/properness of `X/T`
  or `Y/T`.
* New construction: every object and arrow of the affine diagram is specified; the
  colimit universal property fixes the enlargement up to its unique comparison, and
  postcomposition fixes its maps. The `HasColimit` and composition proofs alone are
  postponed. The larger schemes are not arbitrary chosen models of the curves.

The mismatch found in this reading was H3: merely replacing all occurrences of `u` by
`max u v` did not enlarge the fixed input schemes. The new construction and rewritten fibre
clauses repair it. H8 is repaired by the complete thirteen-step proof docstring. H9 is
repaired by ordinary proof-only imports of every recorded project proof-dependency module;
the upstream coherence module was read through `scompile.py --source` and imported at its
current recorded `WeilConjectures` path. H11 is repaired by this clause-by-clause comparison.
The node's mathematical statement and proof are unchanged; its `stmt_deps` gains only the
new definition. No citer file is changed. No `STATEMENT-DISPUTED` flag is needed.

The proof-only project imports are the recorded modules for localization flatness,
constant local dimension, equidimensional opens, specialization traits, flat dense generic
fibres, common field extensions, dimension under field extension, affine Stein factorization,
coherent higher direct images and coherence over locally Noetherian schemes. Their declarations
are respectively `Module.Flat.localizedModule_of_algebra`,
`AlgebraicGeometry.topologicalKrullDim_component_eq_of_constant_local_dimension`,
`AlgebraicGeometry.topologicalKrullDimAt_eq_of_equidimensional_open`,
`AlgebraicGeometry.exists_trait_of_strict_specializes`,
`AlgebraicGeometry.flat_dense_generic_fibre_pure_dimension`,
`Field.exists_common_extension`,
`AlgebraicGeometry.topologicalKrullDimAt_spec_tensorProduct_field_extension`,
`AlgebraicGeometry.Scheme.Hom.steinFactorization_affine`,
`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage`, and
`AlgebraicGeometry.Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType`.
The first eight are in `Sheaf.RingTheory.Flat.LocalizationPreservesFlatness`,
`Sheaf.AlgebraicGeometry.ConstantLocalDimensionComponents`,
`Sheaf.AlgebraicGeometry.EquidimensionalOpenLocalDimension`,
`Sheaf.AlgebraicGeometry.NoetherianSpecializationTrait`,
`Sheaf.TraceFormula.FlatDenseGenericFibrePureDimension`,
`Sheaf.FieldTheory.CommonExtensionFields`,
`Sheaf.AlgebraicGeometry.DimensionAtPointFieldExtension`, and
`Sheaf.AlgebraicGeometry.SteinFactorizationAffine`. The last two are the recorded upstream
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex` and
`WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian` modules.

The first server dry run compiled both final statements and rejected only the helper record:
its signature extractor omits the `noncomputable` modifier from `lean.statement`. The record
now uses the exact extracted `def schemeUniverseLift ...` signature. The final import audit
also added direct imports of `Mathlib.AlgebraicGeometry.Morphisms.Finite` and
`Mathlib.RingTheory.RingHom.Flat`, so every proof dependency with a recorded `lean.module`
is imported directly, in addition to the Mathlib leaves reused transitively.
