## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceFlatRelativePseudoCoherence` states
`AlgebraicGeometry.AlgebraicSpace.pseudoCoherentRelativeTo_iff_of_flat_locallyOfFinitePresentation`.
Its sole proof is `sorry`. No definition or additional theorem is introduced.
Source read: `literature/stacks-project/spaces-more-morphisms.tex`, Tag 0DII,
`lemma-relative-pseudo-coherent-is-moot`, and Tags 0CSW, 0CSX, 0CSY for the interpretation
of scheme charts and relative pseudo-coherence. The source agrees with the DAG statement.

Hypothesis and clause correspondence:

- The size convention is expressed by explicit universes `u w wS`; the space localization
  universe `w` is independent of the scheme localization universe `wS`. The binder `hD`
  supplies localizations for all scheme module categories in size `u`, as required by the
  recorded scheme relative-pseudo-coherence definition. It is size infrastructure only.
- The base scheme is `{S : Scheme.{u}}`. The two algebraic spaces over it are
  `{X Y : AlgebraicSpace S}` and the morphism is `(f : X ⟶ Y)`.
- Flatness is `(hflat : MapIsFlat f)` and local finite presentation is
  `(hlfp : MapIsLocallyOfFinitePresentation f)`. Both are the existing universal etale
  scheme-chart tests, using Mathlib `Flat` and `LocallyOfFinitePresentation`.
- The object `K : X.DerivedModules` lies in the unbounded derived category of the
  equivalent small affine etale model. `(hK : X.derivedQCohProperty K)` expresses precisely
  quasi-coherent cohomology, rather than assuming an object of the derived category of QCoh.
- The left side quantifies over every `m : ℤ`, `U : X.EtaleSite`, `V : Y.EtaleSite`,
  `h : U.obj.left ⟶ V.obj.left`, and the equality `comm`. An EtaleSite object is a scheme
  over S with a representable etale map to the space; no affine or surjectivity condition
  is imposed on these arbitrary test squares. The equality is the required commuting square.
- `derivedSchemeRestriction X U K` is the canonical right derived Zariski restriction of
  the chart restriction. On D_QCoh it is the scheme object E_U identified by the etale /
  Zariski comparison in Tag 0CSW. No arbitrary comparison map or object is supplied.
- `@Scheme.IsMPseudoCoherentRelativeTo hD _ _ h.left ... m (...)` is the recorded scheme
  relative condition. It contains the affine base/source covers, closed embeddings into
  finite affine spaces, derived pushforward, and local strictly perfect approximations
  inducing isomorphisms above m and an epimorphism in degree m. Its covers and embeddings
  occur inside the quantifier over m, so they can depend on m. Local finite type is supplied
  explicitly by Mathlib's `instLocallyOfFiniteTypeOfLocallyOfFinitePresentation`, applied
  to the chart conclusion of `hlfp`; it is not a further hypothesis.
- The equivalence `↔ X.IsPseudoCoherent K` is exactly the conclusion. This uses the recorded
  small-etale local bounded-above finite-free representative predicate, with varying bounds
  and ranks. There is no global upper bound or boundedness hypothesis on K.
- The contextual ring pseudo-coherence, perfectness, K-flat tensor and K-injective RΓ
  conventions are unchanged. No tensor, RΓ or independent perfect object occurs in this
  theorem's signature, so no extra coefficient package or resolution is quantified over.
- There is no quasi-compactness, separatedness, properness, Noetherian, nonemptiness or
  target-chart-surjectivity hypothesis.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.EtaleSite`, `etaleForget`, `IsEtale`, and the structure sheaf / Modules.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`, `MapIsFlat`,
  `MapIsLocallyOfFinitePresentation`. Its owning node `def-sfb-space-morphism-properties`
  is added as an already-landed statement dependency, not duplicated or repaired.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`,
  `derivedQCohProperty`, `derivedSchemeRestriction`, with its actual right derived
  functor definition and independent scheme localization universe. Its already-landed
  owning node `def-sfb-space-derived-module-calculus` is added to stmt_deps.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePseudoCoherentComplex`: `IsPseudoCoherent`.
- `Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex`:
  `Scheme.IsMPseudoCoherentRelativeTo`, `Scheme.IsPseudoCoherentRelativeTo`.
- `Sheaf.AlgebraicGeometry.MPseudoCoherentComplex`: `Scheme.IsMPseudoCoherent` (through
  the preceding definition); `WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex`:
  `Scheme.IsPseudoCoherent` (the proof's absolute scheme notion).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, specializing
  Mathlib `SheafOfModules.IsQuasicoherent`. These underlie the existing space framework.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`;
  `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`;
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`;
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`, `instLocallyOfFiniteTypeOfLocallyOfFinitePresentation`.
- Contextual declarations inspected, with no new occurrence needed in the signature:
  `CategoryTheory.ringedSiteZerothHypercohomologyOfUniverses` in its recorded module;
  `SheafOfModules.StrictPerfectCoefficientRepresentationOfUniverses` and its local-perfect
  predicates in `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`;
  `DerivedCategory.IsPseudoCoherent` in `WeilConjectures.RingTheory.RingPseudoCoherent`.

Available recorded proof-dependency modules are imported privately: scheme etale locality,
space etale presentation criterion, derived chart calculus, derived etale/Zariski equivalence,
fibre products/etale covers, K-injective restriction, and Mathlib
`Mathlib.Algebra.Homology.DerivedCategory.KInjective` for the recorded Mathlib match
`CochainComplex.IsKInjective.Qh_map_bijective` of
`lem-sc-kinjective-quasi-iso-comparison`. The two proof prerequisites with no recorded
module yet, and hence no import to add, are `lem-sfb-flat-ambient-relative-pseudocoherence`
and `lem-sfb-etale-pseudocoherence-descent`. `def-pur-kinjective-complex` is the Mathlib
match `CochainComplex.IsKInjective`, available transitively. Both full Mathlib signatures
and their docstrings were inspected. The theorem docstring contains all four DAG proof
steps and names their inputs, including these future imports.

Edge cases checked against the source and the actual predicates: empty source and empty
charts, zero complex and rank zero finite-free modules, identity f, every integer m
(including negative m), affine-space dimension zero, non-quasi-compact spaces, and complexes
with no uniform local upper bound. Empty charts do not require chosen points. The definition
of absolute pseudo-coherence uses covering sieves on every small-model object. The relative
side uses every chart square, not just a chosen atlas; surjectivity enters only the proof.
No excluded case or statement fault found. No statement correction is needed.

Searches for an existing theorem (all on 2026-10-24):

- msearch LeanFinder: “For a flat locally finitely presented morphism of algebraic spaces a
  complex is relatively pseudo coherent if and only if it is pseudo coherent”: eight hits
  on scheme flatness, universal openness and related properties, no matching theorem.
- msearch LeanSearch: “Relative pseudo coherence agrees with pseudo coherence for flat
  locally finitely presented morphisms of algebraic spaces”: eight hits on ordinary morphism
  properties / module presentations, no matching theorem. The finite-type consequence used
  in the signature was among the results.
- msearch Loogle: `AlgebraicGeometry.Flat, AlgebraicGeometry.LocallyOfFinitePresentation,
  DerivedCategory.IsPseudoCoherent`: zero hits; the service does not index the project
  declaration `DerivedCategory.IsPseudoCoherent` (unknown identifier).
- msearch grep: `PseudoCoherentRelative|pseudo.coherent` in Mathlib AlgebraicGeometry:
  zero hits.
- rg in project `lean/WeilConjectures` for `IsPseudoCoherentRelativeTo` and relative
  pseudo-coherence: no existing statement; exact node-id grep also had no occurrence.
- rg in `lean/Sheaf` for relative predicates, space pseudo-coherence and flat/lfp chart
  tests: found the reused scheme relative definition, space absolute definition and
  morphism-property definitions, but no equivalence of relative and absolute space
  pseudo-coherence. Searches of `dag/lean_names_upstream.json` and both source roots for
  the proposed theorem name found no collision.

Compilation: scompile.py compiled the completed file separately in sandbox and library
module modes, with no error or warning. Diagnostic #check commands were removed before
final compilation. The only theorem proof is the required sorry.

## Second reading by Q29

I reread the node, Tag 0DII / Tags 0CSW–0CSY, and the completed signature. This is a
self-check, not an independent agent review: the dispatcher explicitly prohibits spawning
agents, and the maintainer's independent delivery review follows. The check compared S,
X/Y over S, f, its flat/lfp chart tests, unbounded K with quasi-coherent cohomology, every
integer, every compatible chart square, and both directions of the equivalence. In
particular the explicit finite-type argument is a consequence of hlfp and does not
strengthen the statement. Derived chart restriction is the existing R-epsilon_* model,
not ordinary nonexact Zariski restriction. There is no extra affine, surjective or global
boundedness hypothesis. The only textual correction during the rereading was to cite
Definition 0CSY rather than Remark 0CSW as the relative definition in the Lean docstring.

Dry run: deliver2.py --no-push passed preflight and per-file server compilation.
The explicit Mathlib proof-comparison import and corresponding report entry were then
checked in a second dry run before delivery.
