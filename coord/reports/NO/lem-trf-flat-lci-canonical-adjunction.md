## Worker report

Repair of L's return of immutable head bc797487225a (H2/H3/H8 and H1/H11). This packet supplies two Lean modules, two complete node bindings, and this clause-by-clause report. The item node was recopied from the current published shared DAG; its statement, proof, proof dependencies, source, status and entire split_report are unchanged. In particular the returned unauthorized split_report edit is not retained. The only main-node changes are lean and the addition of two already landed definition dependencies. No source or shared-library file was edited.

The main statement is AlgebraicGeometry.exists_flatLCICanonicalAdjunction in Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction. It states the simultaneous adjunction-line construction on all cartesian changes of base. The original line is F.line (FlatLCIBaseChange.identity p). Definitions contain their actual formulas or records of mathematical data and properties. The only postponed proofs are the main theorem and the uniquely normalized tensor-adjunction theorem owned by the repaired pullback node; both have source references and complete proof docstrings.

Hypotheses, with the node and Lean read together:

- Schemes S and W and p:W→S: the explicit binders {X S : Scheme.{u}} (p : X ⟶ S). All universes and variables are bound, with autoImplicit and relaxedAutoImplicit false.
- Noetherian S: [IsNoetherian S]. Mathlib's scheme property means locally Noetherian and quasi-compact, equivalently a finite Noetherian affine cover. No Noetherian assumption is made on a changed base.
- Flatness: [Flat p]. Finite presentation: [LocallyOfFinitePresentation p], [QuasiCompact p], [QuasiSeparated p], exactly the node's three clauses. There is no separatedness assumption on p.
- Nonnegative relative dimension: d : ℕ. HasPureFlatLCIGeometricFibres p d quantifies over every point s of S and every irreducible component of the actual geometric fibre; topologicalKrullDim of that component is d. The geometric fibre uses pullback along Spec of the algebraic closure of S.residueField s, composed with S.fromSpecResidueField s. Empty fibres impose no condition.
- Local polynomial regular presentations: hlci gives, at each x, an open U containing x and a FlatLCIPresentation p d U. Its fields give n,c, n=c+d, P, an open immersion P→A^n_S, a closed immersion U→P, the commuting structure map, local generators of the kernel ideal, and regularity of the localized sequence at every prime containing that ideal. This is the stalk-local regular-immersion condition; it also expresses the source's stalkwise condition after non-Noetherian changes of base. Restricting the ambient to an open of S is included by its open immersion into A^n_S.

Conclusions, clause by clause:

- C=I/I²: FlatLCIPresentation.conormal is tensorPullback i applied to the actual kernel ideal's toModules, not an abstract module with an assumed isomorphism.
- V=i*Ω¹: FlatLCIPresentation.differentials is tensorPullback i of relativeDifferentials for P→S. The line definition is precisely homObj (exteriorSheaf C c) O_U tensor exteriorSheaf V n. The Hom is sheaf Hom, and exteriorSheaf is the landed sheafification construction.
- The invertible glued line: FlatLCIAdjunctionSystem.line and .invertible provide the line on each base change, and .localIso identifies every chart's displayed line with its restriction. There is a single global line even without separatedness. For charts C,D on the same open, the transition is localIso C followed by (localIso D)⁻¹. For differing opens these comparisons are restricted using FlatLCIPresentationPullback. Consequently transitions satisfy identity and the triple-overlap cocycle by cancellation.
- Canonical, presentation-independent comparisons: IsNormalized requires existence and uniqueness of the actual conormal and source-differential maps, as characterized on functions and 1 tensor ideal sections. It also requires the natural refinement and pullback maps to exist for every applicable scheme diagram, so its normalization clauses cannot be satisfied by simply omitting comparison diagrams. IsFlatLCIDeterminantComparison fixes refinement comparisons by the determinant of the exact cone with columns (f,-d) followed by lifts of a target differential basis. This includes generator changes, combined presentations, and the evaluation trivialization of an acyclic rank-one summand. The determinant formula fixes the scalar, rather than allowing arbitrary line isomorphisms.
- Sheaf Ext: HasExtIdentification uses the actual moduleSheafExt C.P c of i_*O_U and exteriorSheaf Ω_P/S n, and an isomorphism from i_*C.line. Its equation intertwines multiplication on C.line with the contravariant first-argument action of endomorphisms of O_U on Ext. Thus the identification retains the closed-source module action, rather than treating Ext as an unspecified module on U. Every chart is quantified, including restrictions. The canonical Koszul top-contraction computation and its generator-independent normalization are the proof's fourth and sixth steps, using the existing Koszul dependency.
- Relative dualizing complex: HasDualityModel identifies (i_*C.line)[d] with derivedInternalHom(i_*O_U, Ω^n_P/S[n]), in the ambient derived category. It likewise explicitly intertwines the natural O_U-action induced by precomposition. Closed-immersion direct image is exact; with localIso this is precisely the node's local model on the closed source. Every separated open is covered by these polynomial closed charts (which are separated over the base), with the determinant comparisons specified above. This uses the node's formulation of the relative dualizing object by these local models; no proper morphism or globally defined p! is assumed.
- Arbitrary base change: FlatLCIBaseChange contains an arbitrary cartesian square, with no extra property on its base. The second conjunct of the theorem ensures that the base-changed family still has presentations of the same rank. FlatLCIAdjunctionSystem.baseChange supplies g*line(B)≅line(D) for every compatible successive base-change square. .identity and .composition are equalities of isomorphisms using the normalized tensor-pullback identity and composition comparisons. IsFlatLCIPullbackDeterminantComparison fixes these maps on pulled-back wedge bases and their duals; it requires the canonical conormal and differential maps to be isomorphisms. Thus the supplied base-change map is tied to the same local adjunction construction.
- Smooth locus: the last conjunct quantifies over every smooth open and supplies an isomorphism to exteriorSheaf Ω¹ d. IsSmoothComparison specifies its value by the conormal exact-sequence wedge formula, with conormal vectors first and arbitrary lifts of the source differentials following. It fixes the usual smooth normalization including rank zero.

Dependency interfaces read and used:

| DAG dependency | Module and declaration |
| --- | --- |
| def-kun-topological-krull-dimension | Mathlib.Topology.KrullDimension; topologicalKrullDim |
| def-pc-module-pullback | WeilConjectures.AlgebraicGeometry.TensorPullback; Scheme.Modules.tensorPullback, with the section-normalized interface in this packet |
| def-sbc-locally-finite-presentation | Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation; LocallyOfFinitePresentation |
| def-sbc-smooth-morphisms | Mathlib.AlgebraicGeometry.Morphisms.Smooth; Smooth (and Etale for the differential restriction comparison) |
| def-sc-invertible-module | WeilConjectures.AlgebraicGeometry.Modules.Invertible; Scheme.Modules.IsInvertible |
| def-weil-closed-immersion | Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion; IsClosedImmersion |
| def-weil-finite-type-morphism | Mathlib.AlgebraicGeometry.Morphisms.FiniteType; QuasiCompact |
| def-weil-flat-morphism | Mathlib.AlgebraicGeometry.Morphisms.Flat; Flat |
| def-weil-geometric-fibre | Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback; pullback, with the recorded residue-field geometric point |
| def-weil-pbc-exterior-algebra | Mathlib.LinearAlgebra.ExteriorAlgebra.Basic; exteriorPower, through exteriorSheaf |
| def-weil-pbc-kahler-differentials | Mathlib.RingTheory.Kaehler.Basic; KaehlerDifferential, through relativeDifferentials |
| def-weil-pbc-noetherian-ring | Mathlib.RingTheory.Noetherian.Defs; IsNoetherianRing, through the scheme Noetherian property |
| def-weil-pbc-regular-sequence | Mathlib.RingTheory.Regular.RegularSequence; RingTheory.Sequence.IsRegular |
| def-weil-pbc-sheaf-ext | Sheaf.AlgebraicGeometry.SheafExt; moduleSheafExt and moduleSheafExtFunctor |
| def-weil-quasi-separated-morphism | Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated; QuasiSeparated |
| def-sc-sheaf-exterior-power (added landed dependency) | Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf; Scheme.Modules.exteriorSheaf and exteriorSheafSection |
| def-sc-relative-differential-sheaf (added landed dependency) | WeilConjectures.AlgebraicGeometry.Modules.Differentials; Scheme.Hom.relativeDifferentials and relativeDifferentialsDerivation |

Proof-dependency modules that have published statements are imported as non-public imports. The three unstated proof inputs (lci cotangent presentation, two-term determinant, polynomial-chart duality) are mentioned by ID in the nine-step proof docstring; the statement does not refer to their not-yet-defined declarations or introduce duplicate definitions of them. They are proof inputs, not missing objects in this signature.

Source reading: Stacks duality.tex Tags 0B6V and 0E2Y were read in the local source, including the Koszul argument and arbitrary-base-change argument. The node's nine-step proof provides the precise 0BQZ, 08QQ, 08R5, 0FJX/0FJY and 0BZI/0BZJ normalization references, retained verbatim in the node and spelled out in the main theorem docstring. The recently landed NodalDualizingDatum and MarkedNodalDualizingDegrees were also inspected: their relative-dimension-one nodal specialization is not this general flat-lci statement.

Edge cases: empty W and empty fibres; non-surjective p; empty base; d=0; c=0 and the empty conormal wedge; n=c+d=0; identity base change; two successive base changes; non-Noetherian changed base; nonseparated total space; a generator change; and adding one equation/coordinate with differential 1. The determinant cone formula gives identity for an identity comparison and evaluation for the rank-one acyclic stabilization. Exterior-degree-zero sections, tensor unitors, and the empty matrix determinant give the intended formulas in zero rank. Fibre purity excludes none of the allowed empty cases. Changed-base charts use stalkwise regularity at their closed source, never an unjustified Noetherian assertion.

Searches made before introducing the owning-node helpers:

- msearch.py leanfinder, query "flat local complete intersection canonical adjunction determinant relative dualizing line arbitrary base change": eight hits, on flat appLE/smoothness, localization and algebraic cotangent maps; no determinant-adjunction or dualizing-line statement.
- msearch.py loogle, query '"dualizing"': zero hits.
- msearch.py leansearch, query "relative canonical sheaf flat local complete intersection determinant conormal": eight hits on flatness, smoothness, structure sheaves and cotangent maps; no complete match.
- msearch.py grep, query "dualizing|canonical.*adjunction|lci.*determinant", Mathlib/AlgebraicGeometry: one hit, GammaSpecAdjunction's scheme/global-sections unit, unrelated to relative duality.
- rg in the upstream WeilConjectures and shared lean/Sheaf trees for the item ID, canonicalAdjunction, flatLCICanonical, FlatLCIAdjunctionSystem and IsFlatLCIDeterminantComparison: the downstream marked-nodal proof references this item; the unrelated tensor-adjunction module has a canonicalAdjunction name; there is no declaration of this statement or of these helpers.
- tools/blueprint_refs.py search "canonical adjunction": five unrelated blueprint items (Kunneth map, coefficient extension adjunction, global operator, modification extension by zero and the smooth base-change map). The ancestor query returns lem-trf-local-term-locality. The existing sheaf-exterior-power and relative-differential-sheaf nodes were reused, not recreated.
- The upstream names index and the recorded dependency declarations were read. Missing local source modules were read using scompile.py --source, which resolves the same published library as the compiler.

No statement correction or STATEMENT-DISPUTED flag is proposed. No independent mathematical notion is added: the structures and predicates in the main module are the chart data, actual determinant maps and compatibility clauses of this owning node.

## Dependency modules

Section 1(B), def-pc-module-pullback: TensorPullbackSectionAdjunction publicly imports the existing tensorPullback construction. Its former interface gave Nonempty adjunction and identity/composition isomorphisms, which cannot fix scalars for canonical determinant pullback. The repair defines the actual section 1 tensor m, states the unique adjunction with that unit, and takes that unique universal-property witness. The identity/composition isomorphisms are actual left-adjoint-uniqueness constructions from it. No arbitrary Nonempty isomorphism is chosen, no pullback functor is redefined, and only lean changes in this dependency's JSON. The sole postponed theorem is existsUnique_tensorPullbackSectionAdjunction, the named adjunction clause of this same dependency; its complete natural-language proof is in its docstring.

## Second reading by NO

Author's substantive second pass, not a claimed independent subagent review: the dispatcher explicitly forbids starting other agents and says that the maintainer supplies the independent reading. I reopened the main node, the dependency node, both modules and the Stacks source after elaboration. The checks above cover every hypothesis and clause, not merely compilation.

This pass found and repaired three concrete interface issues: the old Nonempty tensor adjunction did not determine scalar-normalized pullback comparisons, so it was replaced by the uniquely section-normalized interface; the non-Noetherian base-change presentation needed regularity at primes on the closed source, rather than an unsupported global Noetherian regularity assertion; and the derived/Ext models needed the natural closed-source module action, now stated by explicit precomposition equations. I also checked that the refinement/pullback predicates include existence of the canonical maps, rather than vacuous implications over missing maps, and that base-change identity/composition use the same normalized pullback comparisons.

The immutable-head return is repaired with actual Lean statements and complete lean records. The current main split_report was preserved without edits. Every file is passed separately through the authorized scompile.py wrapper; the delivery dry run also compiles and runs the server preflight. The final compile and preflight outcomes are recorded below after they finish.

Validation: the final two-module scompile.py invocation exited 0. Both sibling files were compiled separately in dependency order, including their library names, with no errors and no warnings. The Etale import and explicit scheme-module monoidal-category arguments repaired the earlier elaboration errors. The final node-field comparison found only lean/stmt_deps in the item and lean in the dependency; split_report is identical to the published base. The prescribed deliver2.py dry run is the next packet check.

Dry run: deliver2.py NO lem-trf-flat-lci-canonical-adjunction --no-push exited 0 and printed "OK (dry run): commit 72421a5b2b passes the preflight and compiles; nothing pushed". The packet contains exactly the two modules, two node records and this report. The final delivery recompiles the same signatures and reruns the packet checks before pushing.
