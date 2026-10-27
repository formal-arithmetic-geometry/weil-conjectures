## Worker report

The module `Sheaf.AlgebraicGeometry.RationalContractionLineCohomology` states
`AlgebraicGeometry.RationalContraction.Diagram.line_cohomology`, with `sorry` as its only
theorem proof. Every definition has actual data. The helper records expand the objects
and clauses of this same node; they do not introduce independent mathematical notions.
The item statement and accepted six-step proof are unchanged.

Source read: Knudsen, *The projectivity of the moduli space of stable curves II*,
Section 1, Corollary 1.5, printed p.167, in the primary-author scan linked in the node
(PDF page 46, counting from one). I read conditions (1), (2), conclusions (i)--(iv),
the proof by alternating Cech cochains and Nakayama, and the opening contraction
application on the same page. The arbitrary-base finite-presentation formulation is
the accepted node's explicit refinement; no Noetherian restriction is introduced.
The preceding printed p.165 was also read to locate Lemma 1.4.

Hypothesis and clause matching:

| Node text | Lean rendering |
| --- | --- |
| Any scheme T, with two families and a T-morphism q | `Diagram.T`, `.X`, `.Y`, `.pX`, `.pY`, `.q`, `.over : q ≫ pX = pY` |
| Both families proper | `[IsProper D.pX] [IsProper D.pY]` |
| Both flat | `[Flat D.pX] [Flat D.pY]` |
| Both finitely presented, including quasi-compact and quasi-separated | `[LocallyOfFinitePresentation D.pX]` and similarly for Y; properness supplies quasi-compactness and separatedness, hence quasi-separatedness |
| Nonempty, connected, one-dimensional nodal geometric fibres | `hX : HasNodalGeometricFibres D.pX` and `hY`; the existing predicate includes `ConnectedSpace` (including nonemptiness), dimension one, and the completed nodal-local-ring condition |
| Reduced and pure dimension one | `hXpure`, `hYpure`: for every algebraically closed `Ω : Type u` and `a : Spec Ω ⟶ D.T`, `IsReduced` and `.IsPureDimension 1` on the corresponding pullback |
| Each fibre map an isomorphism or contracts one P1 | `hq : D.IsElementary`: `IsIso (D.fiberMap a)` or an exceptional closed immersion from the existing `ProjectiveLine (Spec Ω)` |
| The contracted locus is a component over Ω | `Exceptional`: `IsClosedImmersion i`, `Set.range i ∈ irreducibleComponents ...`, and the equality with the standard P1-to-Spec-Ω projection |
| Contracts to a point, isomorphism off that component | `Exceptional` supplies a closed point `x`, equality of the point-preimage set with `Set.range i`, and `IsIso` of the pullback to the complementary open of x; scheme-theoretic reducedness is deliberately not assumed |
| Meets closure of complement in one or two distinct transverse nodes | The boundary `Set.range i ∩ closure ((Set.range i)ᶜ)` has `encard = 1 ∨ encard = 2` and every boundary point is outside the smooth locus; in a reduced nodal curve a smooth P1 component has one branch at each such boundary node, so the intersections with the complementary subcurve are transverse |
| L invertible | `(L : D.Y.Modules) [L.IsInvertible]`, using the existing invertible-module class |
| Degree at least -1 on every contracted geometric component | `hdegree : D.DegreeAtLeast L (-1)`, quantifying over every geometric fibre and every exceptional P1 parametrization, using the actual `tensorPullback (i ≫ pullback.fst ...)` and existing Euler-characteristic `Scheme.Modules.degree Ω` |
| q_* L quasi-coherent | First conclusion, `((Scheme.Modules.pushforward D.q).obj L).IsQuasicoherent` |
| q_* L finitely presented in the local finite-free-presentation sense | Second conclusion `.IsFinitePresentation`, Mathlib's local-cokernel-of-finite-free-modules predicate |
| Flat over T | Third conclusion `.IsFlatOver D.pX`, the recorded affine-local relative flatness predicate |
| R1 q_* L = 0 for structure-sheaf modules | `IsZero ((Scheme.Modules.higherDirectImage D.q 1).obj L)`; `higherDirectImage` is definitionally `(pushforward D.q).rightDerived 1` |
| Arbitrary base change, with the canonical comparison | For every `D'` and `A : D.Change D'`, `IsIso (A.comparison L)`; `Change` supplies actual cartesian X/T and Y/T squares and a commuting q-square, and `.comparison` is the existing `moduleBaseChangeMap` |
| Standard X', Y', projections and q' | Specialize `D'` to `pullback D.pX h`, `pullback D.pY h`, with `.q = D.fiberMap h`; `Change` retains every cartesian presentation rather than requiring a chosen identification with the standard pullback |
| All degrees nonnegative implies evaluation surjective | `D.DegreeAtLeast L 0 → Epi ((tensorPullbackSectionAdjunction D.q).counit.app L)`; epis of sheaves of modules are precisely sheaf-surjective morphisms |
| Comparisons commute with composition | First conjunct of `Compatible`, the equality between the direct comparison for `(B.x ≫ A.x, B.y ≫ A.y)` and the composite of the two comparisons, with `tensorPullbackSectionComp` on source and target |
| Comparisons commute with isomorphisms of diagrams | `Change` permits arbitrary cartesian diagram maps, including all isomorphisms; the composition equation applies also when either change is an isomorphism, giving transport before or after any base change |
| Comparisons commute with isomorphisms of line bundles | Second conjunct of `Compatible`, the naturality square for every `e : L ≅ M`; after any change one may use such an isomorphism on its pulled-back line as well |

The geometric-field tests use exactly the universe of the recorded nodal-fibre
predicate, `Ω : Type u` for `Scheme.{u}`. No independent smaller field universe is used.
There is no assumption that q, a base-change map, or the base scheme is flat or Noetherian.
There are no `let` binders, private definitions, local instances or local notations.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper` (including its class signature
  and docstring); `IsProper.of_comp` is the first proof-step input.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat` and its affine-local class signature.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.NodalGeometricFibres`: `HasNodalGeometricFibres`, whole definition.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`: `Scheme.Modules.degree`, whose
  formula is `eulerChar Ω L - eulerChar Ω O`, and its proper-curve interpretation.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: public exact
  `SheafOfModules.IsQuasicoherent`; the conjunction `IsQuasiCoherentFiniteType` is not
  substituted for finite presentation. Mathlib's `SheafOfModules.IsFinitePresentation`
  (Quasicoherent.lean, lines 265--270) is the exact finite-presentation predicate.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `Scheme.Modules.IsFlatOver`, `Scheme.Modules.higherDirectImage`.
- `WeilConjectures.AlgebraicGeometry.PQFCohomology`:
  `sheafCohomologyAndHigherDirectImages` records the right-derived-functor interpretation;
  the statement uses the definitionally right-derived scheme module pushforward.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `.fst`, `.snd`,
  `.map` (full signature read at lines 270--275), and cartesian squares `IsPullback`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: `tensorPullback`,
  `tensorPullbackSectionAdjunction`, `tensorPullbackSectionComp`. These retain the tensor
  construction and the section-normalized unit; no freely chosen adjunction is introduced.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits`: existing P1 and
  twisting-module framework; the more specialized marked contraction predicate in
  `ElementaryContractionEvaluation` is not used as a substitute for this unmarked node.
- `WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction`:
  `Scheme.Modules.moduleBaseChangeMap`. Its construction uses the normalized adjunction
  characterized by `exists_tensorPullbackAdjunction`; I read that theorem's full signature
  and sectionwise unit formula, so it agrees with the recorded section adjunction.

The final three nodes `def-weil-pure-dimension`, `def-sc-p1-standard`, and
`def-sfb-module-base-change-map` are added to `stmt_deps` as already
landed dependencies, as allowed by brief-stage2 section 5. No new definition node or
dependency repair is needed. Imports for the recorded proof inputs on differential
dimension, rational-point completion, normalization branches, and twist cohomology are
ordinary non-public imports. `lem-sfb-projective-line-invertible-classification` and
`lem-sfb-relative-acyclic-direct-image` currently have no recorded Lean declaration, so
there is no module to import for these proof-only prerequisites; their use remains
explicit in the complete six-step theorem docstring. All statement prerequisites exist.
The proper/fp-permanence Mathlib leaf is supplied by the existing public morphism imports.

Searches actually run:

1. `msearch.py ... leanfinder "Rational nodal curve contraction line bundle degree at least minus one higher direct image vanishing base change"`:
   eight hits, all Weierstrass division-polynomial or base-change facts, no matching statement.
2. `msearch.py ... loogle "AlgebraicGeometry.Scheme.Modules.degree, AlgebraicGeometry.Scheme.Modules.IsFlatOver"`:
   zero hits, unknown identifier `AlgebraicGeometry.Scheme.Modules.degree`; the index does
   not index this project declaration, which was instead read directly in its source.
3. `msearch.py ... grep "contraction|higherDirectImage|baseChange" AlgebraicGeometry`:
   25 displayed Mathlib hits, concerning stability of geometric properties under base
   change and elliptic-curve changes; no contraction/cohomology theorem.
4. `msearch.py ... leansearch "Proper rational component contraction invertible sheaf higher direct image vanishes base change"`:
   eight hits on proper/surjective/affine/integral/separated morphism base-change stability;
   no matching statement.
5. `rg -n 'rational.contraction|RationalContraction|contract.*[Cc]omponent|[Cc]ontraction.*[Ll]ine' lean/Sheaf lean/WeilConjectures` and the later focused
   `elementary.*contraction|rational.*contraction|contract.*projectiveLine|contract.*ProjectiveSpace`:
   found marked/stable-curve, valuation, exceptional-pushout and trace-formula statements.
   I opened `ElementaryContractionEvaluation`, `ExceptionalContractionDiamond` and
   `NodalContractionNormalizationBranches`; none states this general line-bundle theorem.
6. Node-ID search in `lean/WeilConjectures` and `dag/lean_names_upstream.json`:
   no match. `tools/lean_names_upstream.py show` printed the two index summaries and no
   item attachment. The required exact-ID source search is also recorded below.
7. Greps for `moduleBaseChangeMap`, `IsFinitePresentation`, and the degree/invertibility
   declarations found the shared interfaces listed above. A full-name/namespace search
   for `AlgebraicGeometry.RationalContraction` found no prior declaration. No construction
   from those shared interfaces was copied or redefined.

Edge cases checked before and after writing:

- Empty T: geometric tests are vacuous and both families over T are empty; all module
  conclusions make sense. No `Nonempty T` is imposed.
- Identity or all-isomorphism fibres: permitted explicitly by `IsIso` disjunct; the
  exceptional degree predicates are vacuous and evaluation is still asserted.
- Degree -1: O(-1) has H0=H1=0; vanishing/base change apply while generation is not asserted.
- Degree 0: the constant section generates, and the evaluation clause applies.
- Degree below -1: excluded exactly by `hdegree`, not by a stronger positivity assumption.
- Tail versus bridge: boundary cardinality 1 or 2, with no chosen order; set cardinality
  enforces distinct nodes and does not exclude a self-node on the complementary subcurve.
- Nonreduced base: allowed; only the geometric curves themselves are reduced.
- Arbitrary nonflat base change: allowed; no flatness assumptions on `Change.base/x/y`.
- Identity base with nontrivial curve automorphisms: allowed by `Change`, so equivariance
  has not been reduced to maps between only the chosen pullbacks.
- All field characteristics: no characteristic or separability restriction.

No statement correction or STATEMENT-DISPUTED issue was found.

## Second reading by Q84

This is the author's separate second pass, as required for this dispatcher delivery;
no other agent was started. The maintainer supplies the independent review.
I reread the node and the final module together, matching the hypotheses and seven
conclusion conjuncts in the table above. The two degree bounds remain separate; the
counit is the actual normalized adjunction counit, and the comparison is the existing
canonical map, not an arbitrary isomorphism. The exceptional-fibre equality is only
an equality of supports, preserving the reduced-scheme-fibre proof obligation in step 2.

During this pass I corrected the ambiguous coercion of pullback schemes in the helper
predicates by making `C := Scheme.{u}` explicit, replaced a smooth-locus expression
requiring an unavailable local finite-presentation instance by its exact open-smooth
condition, removed a redundant helper for reduced/pure fibres, and wrapped long lines.
These changes do not change the mathematical statement. I checked that transversality
is encoded by a smooth closed P1 component meeting the complementary subcurve at
nonsmooth nodal points, with boundary size one or two; it is not assumed smooth in the
ambient curve. I also checked the cartesian-change formulation covers the specified
standard fibre products and all diagram-isomorphism cases.

The first compile exposed only elaboration errors in those helper expressions.
The second compile elaborated both the sandbox and named module, but reported line-width
warnings from its earlier snapshot; the final source wraps all of those lines. A final
server compile and the delivery dry run are performed after this report is written.

Final validation: `scompile.py Q84 lem-sfb-rational-contraction-line-cohomology`
compiled both the sandbox and actual module with exit code 0 and no diagnostics.
`deliver2.py Q84 lem-sfb-rational-contraction-line-cohomology --no-push` then printed
`OK (dry run)` after server preflight and compilation. The exact-ID `grep -rn` of
`lean/WeilConjectures` also returned no match. Only this item module, node and report
are packaged; no source file in the shared read clone was edited.


## Repair of the return on 109f85303bf

H2: replaced `lem-weil-pbc-module-base-change-map-open-restriction` in `stmt_deps`
with the live definition-owner node `def-sfb-module-base-change-map`. I read that
node's statement and `existing: true` Lean record and the defining declaration
`AlgebraicGeometry.Scheme.Modules.moduleBaseChangeMap` in
`WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction`.
`Change.comparison` and `Change.compositeComparison` use this plain definition;
neither chooses data from nor invokes the open-restriction theorem. The added-
`stmt_deps` sentence above now names the definition owner.

I compared the retained delivery with the current live node: all fields other
than the intended `lean` record and added `stmt_deps` agree. The delivery wrapper
rebases the corrected package on the live branch. No mathematical statement,
proof plan, or Lean source was changed. The Lean SHA256 remains
`9145c7d523385af2ee2bd003f0d0f712772e2a4a3d04401386734dd1d1e4063f`.
This repairs the sole returned point; the independent review found the mathematics
faithful. Compilation and preflight are rerun for this repaired delivery.
