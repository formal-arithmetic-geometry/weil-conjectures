## Worker report

The delivery states `AlgebraicGeometry.exists_nodalDualizingLineSystem` in
`Sheaf.AlgebraicGeometry.NodalRelativeDualizingLine`. Its only theorem has proof
`sorry`. The two definitions, documented cohomology abbreviation, and two structures have actual data and no postponed
proof in a definition. They describe the dualizing line introduced by this node;
they do not introduce a second algebraic-space, nodal, line-module, pullback,
quasi-coherence, cohomology, or dualizing-complex notion.

Sources read: `moduli-curves.tex`, the discussion before 0E6P, lemma-CM-dualizing
(0E6P), definition-relative-dualizing-sheaf (0E6Q), its following representability
display, and lemma-gorenstein-dualizing (0E6R); `curves.tex`,
lemma-facts-about-nodal-curves (0E37); `spaces-over-fields.tex`,
lemma-codim-1-point-in-schematic-locus (0ADD). The old compact-object example is
withdrawn in the current read clone, so it supplies no declaration to reuse. The
new file follows the current module/public-import/exposed-section convention.

Hypothesis and clause correspondence:

- Schemes and an algebraic-space morphism to a scheme: `S : Scheme.{u}`,
  `T : Over S`, and `C : ProperCurveFamily T`. `C.space` is the existing
  `AlgebraicSpace S`; `C.projection` is the natural transformation to `yoneda.obj T`.
  The auxiliary ambient base S restricts no family: one can take S=T and the
  identity structural map. Every scheme base change to T is then an object of
  `Over S`, and the theorem includes all of them.
- Flat, proper and finitely presented: these are the first seven conditions of
  `C.isCurve`, namely flatness on all representable etale charts, closed-immersion
  diagonal, quasi-compactness, local finite type on charts, universal closedness,
  quasi-compact diagonal, and local finite presentation on charts. Thus proper
  means separated, finite type and universally closed, and finite presentation
  includes quasi-compactness and quasi-separatedness. The dimension-at-most-one
  condition of `ProperCurveFamily` follows from the pure-one-dimensional fibre
  hypothesis and therefore imposes no further restriction on this node's families.
- Nonempty, pure dimension one, at worst nodal geometric fibres:
  `hnodal : C.HasNonemptyNodalGeometricFibres`. This is the already landed predicate,
  not a private test. It quantifies over every algebraically closed field in the
  scheme universe, every geometric base morphism and every etale scheme chart of
  the actual presheaf fibre product. It requires nonempty point space, pure
  dimension one on each chart and the smooth-or-ordinary-node condition. In the
  proper finite-type pure-curve setting this is the usual nodal condition in the
  node: testing nonsmooth closed points suffices; over an algebraically closed
  field the remaining generic points of a reduced curve are smooth. The
  hypothesis does not assume reducedness. It entails it by the closed-point
  completed-local-ring criterion used in proof step 1.
- Completion and two-variable power series: the existing predicate expands
  `IsOrdinaryNode` to closedness and
  `Nonempty (AdicCompletion (IsLocalRing.maximalIdeal (U.presheaf.stalk x))
    (U.presheaf.stalk x) ≃+*
    (MvPowerSeries (Fin 2) Ω ⧸ Ideal.span {X 0 * X 1}))`.
  These are the recorded Mathlib notions of the original statement dependencies.
- Geometric fibres are schemes: the first conjunct of the theorem supplies
  `U : Over S`, the structural map `r` to the given field spectrum, and
  `e : yoneda.obj U ≅ Limits.pullback C.projection (yoneda.map ...)`.
  The equation with `pullback.snd` fixes the structure morphism to the field.
  Thus this is a scheme representation of the actual fibre over Ω, not a scheme
  with an unrelated abstract isomorphism of underlying point sets.
- Reduced fibres: `IsReduced U.left` in that same existential.
- Gorenstein local rings at every point, not merely closed points:
  `∀ x : U.left, IsNoetherianRing (U.left.presheaf.stalk x) ∧
   ∃ n : ℕ, HasInjectiveDimensionLE
     (ModuleCat.of (U.left.presheaf.stalk x) (U.left.presheaf.stalk x)) n`.
  Mathlib's finite injective-dimension predicate on the regular module is used
  directly. Module categories have enough injectives, so this is equivalent to
  existence of the finite injective resolution required in the node.
- The relative dualizing line on the small etale site: the second conjunct is
  `Nonempty (NodalDualizingLineSystem C)`. Its `omega B : B.space.Modules` is a
  module on the existing small etale site, and `line B` is the dependency's
  `B.space.IsLineModule (omega B)`, locally isomorphic to its structure sheaf.
  `NodalDualizingLineBaseChange` includes every cartesian realization and includes
  the identity family; no base-change family is assumed schematic.
- The canonical relative dualizing object: `nodalLineSingle X M` is the actual
  restriction of M to the existing equivalent small model, placed in degree -1.
  `trace` and `dualizing` state that this shifted line, with its trace, is the
  existing `IsRelativeDualizingTracePair`. This is the source definition of
  relative dualizing sheaf as H^-1 of the relative dualizing complex. Its data
  are determined up to trace-preserving isomorphism; no unknown object is chosen
  from an uncharacterized existence statement.
- Affine base change, every ring A and every quasi-coherent F: `serre` quantifies
  over B, `A : Type u`, `[CommRing A]`,
  `a : B.base.left ≅ Spec (.of A)`, and `F : B.space.QCoh`. Its two sides are
  `(F.obj ⟶ omega B)` and
  `((nodalLineH1 A B.base a B.space B.projection).obj F ⟶
    ModuleCat.of A A)`, precisely the displayed Hom groups. It includes arbitrary
  quasi-coherent modules, not just coherent, finitely presented or flat modules.
- H^1 is right-derived module sections: `nodalLineH1` first includes
  QCoh in ALL modules, restricts through the fixed small-model equivalence, and
  applies `(affineScalarSections ...).rightDerived 1`. In particular it does not
  derive a functor in QCoh or replace module cohomology by an unrelated group.
- Naturality: `naturality` says the representing bijection carries composition
  `h.hom ≫ t` to `H^1(h) ≫ serre ... t`. A natural bijection of these representable
  Hom functors is the relative Serre-duality isomorphism; its additivity and scalar
  compatibility follow by naturality for sums, biproducts and scalar endomorphisms.
- Characterization locally on the base: `unique_affine` tests every other
  quasi-coherent representing module M and every natural family e, and supplies
  the unique module isomorphism `i : M ≅ omega B` preserving the representing
  bijections. Requiring M to be quasi-coherent places the representing object in
  the domain QCoh of the source's represented functor. The constructed line is
  quasi-coherent by local triviality; no extra hypothesis on the input is imposed.
- Every T'→T and canonical pullback isomorphism: `baseChange` supplies
  `(moduleTensorPullback g).obj (omega B) ≅ omega D` for every cartesian transition
  of the indexed families. `trace_baseChange` fixes its normalization: applying
  the canonical derived comparison followed by the target trace equals the
  pulled source trace followed by the canonical structure-sheaf map. This is the
  exact equation of `TraceBaseChangeCompatible`, expanded on the shifted lines.
  `nodalLinePullbackMap` is explicitly built from the universal left-derived
  counit, the single-complex comparison, and the fixed restriction equivalence.
  It is not an arbitrary derived map. Since the module is a line, this ordinary
  versus derived comparison is invertible.
- Iterated base changes: `identity` identifies the identity map with the existing
  tensor-unit comparison, and `composition` identifies direct and successive
  base changes using the existing tensor-associativity-normalized
  `moduleTensorComposition`. No arbitrary comparison is substituted.
- Restriction to a geometric fibre: the fibre is represented by the first
  conjunct, and taking B with field base in the system gives the line and Serre
  property on that fibre. The trace-pair characterization is its ordinary
  dualizing object under the scheme/etale comparison. Thus it is the ordinary
  dualizing invertible module, including for disconnected nodal fibres.
- Ordinary invertible modules on a scheme: `scheme` applies to every representation
  `e : schemeSpace U ≅ B.space`. It pulls the line back along this isomorphism and
  asserts that its actual `schemeRestriction` along the identity etale chart is
  `Scheme.Modules.IsInvertible`. The recorded restriction functor is exactly the
  inverse, restriction-to-Zariski-opens direction of the ordinary/etale line
  comparison. This includes the original family when it is a scheme and every
  scheme base change, not only the geometric fibres.

The arbitrary localization universe w and the `HasDerivedCategory` instances are
explicit. They choose presentations of the existing derived categories rather
than impose a geometric hypothesis or equate distinct site/coefficient universes.
The small-model equivalence keeps the section universe u, the full etale site has
its existing object universe u+1, and the localization morphism universe is w.
All variables are bound with `autoImplicit false`.

Dependency declarations read and used (modules after `Sheaf.AlgebraicGeometry.`
are abbreviated below, but the node records and source imports retain full names):

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `AlgebraicSpace`: `AlgebraicSpace`, `Modules`, `IsLineModule`, representability
  and etale chart definitions.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries` and its variables.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`.
- `AlgebraicSpaceQuasiCoherentModule`: `AlgebraicSpace.QCoh`, which is the full
  subcategory for Mathlib `SheafOfModules.IsQuasicoherent`.
- `ProperCurveModuli`: `ProperCurveFamily`, `IsProperCurveFamily`.
- `CurveModuliGroupoids`: `ProperCurveFamily.HasNonemptyNodalGeometricFibres`.
- `AlgebraicSpaceModuleOperations`: `moduleTensorPullback`.
- `AlgebraicSpaceSchemeRestriction`: `schemeRestriction`.
- `AlgebraicSpaceSmallRingedModel`: `SmallModules`, `smallModuleRestriction`,
  `smallModuleEquivalence`.
- `AlgebraicSpaceDerivedModules`: `DerivedModules`, `derivedDirectImage`,
  `derivedStructure`.
- `SpaceDerivedTensorPullback`: `smallModuleTensorPullback`,
  `smallTensorPullbackComplex`, `derivedTensorPullback` and its universal counit.
- `SpaceDerivedPullback`: `spaceDerivedPullback`, `moduleTensorPullbackId`.
- `SpaceFlatDirectImageBaseChange`: `moduleTensorComposition` (the dedicated
  definition node `def-sfb-space-module-tensor-composition` owns this helper).
- `SpaceModuleDerivedExchange`: `moduleDerivedExchange`.
- `SpaceAffineHomComparison`: `affineIdentityChart`.
- `RelativeDualizingTracePair`: `RelativeDualizingTracePair`,
  `IsRelativeDualizingTracePair`, `traceSchemeMap`, `traceDerivedStructureMap`.
- `SpaceAffineGlobalSections`: `affineScalarSections`; the owning definition node
  is `def-sfb-space-affine-global-sections`. The item abbreviates its first
  right-derived functor after the existing QCoh inclusion and model restriction
  as `AlgebraicSpace.nodalLineH1`.
- `Mathlib.Algebra.Category.ModuleCat.InjectiveDimension` and
  `Mathlib.CategoryTheory.Abelian.Injective.Dimension`: `HasInjectiveDimensionLE`.

The item's original statement and proof fields are unchanged. `stmt_deps` only gains
already landed nodes owning the additional interfaces explicitly used above.
No new definition node or dependency repair is needed. The theorem's docstring
carries all six original proof steps, with their cited DAG nodes. All currently
recorded proof-dependency modules are imported privately. The three proof nodes
`lem-sfb-proper-field-algebraic-dualizing`,
`lem-sfb-pseudocoherent-point-fibre-line` and
`lem-sfb-proper-space-curve-qcoh-bound` had no Lean module in the read DAG; they are
proof inputs only, not missing notions needed to type this statement.

Edge checks: the empty base is permitted (no geometric tests, and its sole module
is the line on the empty space); a nonempty base with an empty fibre is excluded
by exactly the stated nonemptiness requirement; empty etale charts remain allowed;
disconnected and reducible fibres are included; smooth curves satisfy the
smooth disjunct without requiring a singular point; characteristic two is allowed
because the split-node condition is the quotient by uv, with no division by two;
zero F is included and both Hom groups are singletons; infinite-rank and nonflat
quasi-coherent modules are included; identity, repeated, nonflat and non-Noetherian
base changes are all indexed without restriction. Pure dimension is not replaced
by connectedness, and the Gorenstein assertion tests all stalks.

Searches actually run:

- `msearch.py ... leanfinder` with query "A proper flat finitely presented nodal
  algebraic space curve has a relative dualizing invertible module with relative
  Serre duality and arbitrary base change": eight results about flat/smooth
  base-change properties; no relative dualizing-line statement.
- `msearch.py ... leansearch` with query "Relative dualizing invertible sheaf of a
  flat proper nodal curve family compatible with base change": eight results
  including Flat/IsProper base-change, dual vector-space base-change and Picard
  duals; none states this node.
- `msearch.py ... loogle` with query "AlgebraicGeometry.AlgebraicSpace, dualizing":
  zero results; the external Mathlib index does not know the project identifier.
- `msearch.py ... grep` with query `dualizing|Dualizing|Gorenstein` in
  `AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py ... loogle` with query `CategoryTheory.HasInjectiveDimensionLE`:
  returned its exact Mathlib declaration, the injective-dimension characterization,
  and module versions; reused the Mathlib predicate.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for nodal/relative dualizing,
  relative Serre, and this node's id: the scheme-only
  `exists_nodalRelativeDualizingSystem` and the LCI `NodalDualizingDatum` were found,
  but neither covers algebraic-space families with arbitrary affine Serre duality.
  `grep -rn` of this node id in `lean/WeilConjectures` returned no match.
- `rg` found the shared `HasNonemptyNodalGeometricFibres`, scalar cohomology,
  pullback, trace-pair, and scheme-restriction interfaces listed above. All were
  read before use. `dag/lean_names_upstream.json` has no match for this node or
  the five proposed declaration names, nor do the two source trees.
- `tools/blueprint_refs.py search 'relative dualizing'` returned the three
  coefficient-sheaf dualizing-complex nodes in sec-smooth-purity, none this
  coherent-module statement. Its `ancestor` command reports `None` for this item;
  no new node is created requiring an ancestor assignment.

Validation: the prescribed `scompile.py` has compiled the sandbox and named library
module successfully. The first draft required explicit structure-index typing,
parentheses around a dependent isomorphism result, and explicit types on identity
and composite algebraic-space maps. Both long lines were shortened. The final
trace-normalized statement compiled cleanly; the final explicit-import version
is checked again before dry run and delivery. No statement dispute or node fault
was found.

## Second reading by Q58

This is the author's second pass; the independent mathematical reading belongs to
the maintainer, as specified in the dispatcher brief. I reopened the original
node, the six original dependency records, the reused landed interfaces, the
source's relative-duality display and the resulting Lean file.

The family binder already contains precisely flatness/properness/finite
presentation, and the reused nodal predicate adds nonemptiness and purity without
connectedness or genus. I checked that its completion quotient is Ω[[u,v]]/(uv)
and not the smooth ring or a completion at an arbitrary ideal. I checked that
fibre schematicity and reduced/Gorenstein properties are conclusions rather than
input assumptions, and that the fibre representation preserves its projection.
The existential bound on injective dimension is allowed to depend on the stalk.

For the dualizing module I checked that omega is a full small-etale module and
line is the already recorded local-triviality predicate. Each affine B admits
ALL QCoh objects in serre; naturality uses the H1 map in the correct covariant
order. The uniqueness clause compares quasi-coherent representing objects for
that same contravariant functor, one affine presentation at a time, avoiding an
incorrect requirement that arbitrary unrelated choices for different coordinate
rings be simultaneously normalized.

The first draft had coherent but otherwise unconstrained base-change isomorphisms.
I repaired that before delivery by adding the actual relative dualizing trace
pair on each shifted line and the trace-preservation equation. Its derived map
is now the explicit universal counit comparison applied to the ordinary module
isomorphism. I checked the direction of the inverse moduleTensorComposition in
the composition field: its source is direct composite pullback, then the two
successive pullbacks, then omega E. The identity uses the existing normalized
identity comparison. The scheme field uses actual restriction to opens, not an
arbitrary equivalence or an assumed invertible substitute.

The theorem has one sorry, with all six source/DAG proof steps in its docstring.
There are no axioms, proof shortcuts, data sorries, auto-bound variables, new
private definitions, statement changes, new nodes or dependency replacements.

Final verification: the explicit-import module compiled cleanly in both sandbox
and library mode. `deliver2.py ... --no-push` reported
`OK (dry run): commit 261ba8bbda7 passes the preflight and compiles; nothing pushed`.


## Repair of returned head 5adf023e54eb

H2 was the only returned point. The previous delivery incorrectly placed the
higher-direct-image comparison theorem in statement dependencies merely because
its module owned a plain cohomology abbreviation. The current main node still
has the original six statement dependencies and no Lean record; comparison with
that node preserves every original statement, proof and metadata field.

Removed `lem-sfb-space-affine-base-higher-image-sections` from `stmt_deps` and
replaced it with the already recorded definition node
`def-sfb-space-affine-global-sections`. Switched the public import from
`SpaceAffineBaseHigherImageSections` to `SpaceAffineGlobalSections`. Added the
explicit right-derived and module-category infrastructure imports formerly
supplied by the removed module.

The one documented abbreviation `AlgebraicSpace.nodalLineH1` in the item's own
module is exactly
`(SheafOfModules.isQuasicoherent X.structureSheaf).ι ⋙ X.smallModuleRestriction ⋙
 (affineScalarSections A Y a X f).rightDerived 1`.
All four occurrences in `serre`, `naturality`, and `unique_affine` use it.
This is definitionally the same first cohomology functor as in the returned
version. No higher-direct-image theorem is assumed or used. The abbreviation
has its source and this item's blueprint id, and is listed in
`lean.declarations`. The main theorem signature was re-extracted verbatim into
`lean.statement`; its text itself is unchanged because it mentions the system
structure rather than its expanded fields. No mathematical statement correction
or additional definition node is needed.

Author's second reading of the repair: checked the definition of the removed
abbreviation and the full signature/docstring of `affineScalarSections` in the
current main sources. The composite and order of restriction/derivation are
identical; the degree is fixed to 1. The only structural changes are the four
references to this expanded abbreviation. Every other accepted hypothesis,
fibre conclusion, trace normalization, base-change equation, and scheme clause
is retained. The dependency list now names the definition actually consumed.
Validation is repeated below for this repaired version; the previous receipts
above refer only to the returned version.

The first repair compile exposed an instance previously supplied by the removed
module: `HasInjectiveResolutions X.SmallModules`. Retained that module's activation
of the existing `SheafOfModules.isGrothendieckAbelian` instance, which supplies
enough injectives through the standard imported infrastructure. No new theorem,
instance data, or hypothesis is introduced.

Repair compile passed cleanly through `scompile.py` in sandbox and named-library
modes (16.0 s and 12.4 s). Verified that the node differs from current main only
in `lean` and `stmt_deps`, its recorded main signature is verbatim, the four H1
uses point to `nodalLineH1`, and neither the removed import nor the rejected
theorem dependency remains.
