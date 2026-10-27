## Worker report

This repairs returned head `927223b21645` while retaining the saved packet's actual
objects and its legitimate dependency module. The initial required dry run passed
(commit `b26b0f8ecf5`), but that mechanical result did not repair the independent
mathematical review. The final packet changes the deficient clauses, not the DAG's
mathematical statement. The current shared node was compared with the sandbox:
all non-`lean` fields agree. Delivery/rebasing is performed only by `deliver2.py`.

The main module is `Sheaf.AlgebraicGeometry.GraphConeGluing`; the main theorem is
`AlgebraicGeometry.GraphCone.exists_graphCone_gluing`. It asserts closedness of
every affine graph and a simultaneous canonical construction for every diagram.
All theorem proofs in both delivered modules remain `sorry`. Every definition has
actual data; proofs needed by definitions are separate named theorems with source
and proof docstrings. There are no new definition nodes or source-statement changes.

The statement's hypotheses and clauses are rendered as follows.

| Node clause | Lean rendering |
| --- | --- |
| Schemes, arbitrary `f : X → T`, closed `i : Z → X` | `Diagram.Z`, `.X`, `.T`, `.i`, `.f`, `[Diagram.closed]`; all `Scheme.{u}`. |
| Affine `V ⊂ T`, affine `U ⊂ f⁻¹(V)` | `Chart.V`, `.U`, `.le`. |
| `Z_U`, restricted family, `Y_U` | `Chart.centre`, `.inclusion`, `.family`, `.ambient`; actual inverse image and fibre product. |
| Graph `(i,1)` and closedness | `Chart.graph` is `pullback.lift`; the first conjunct of `exists_graphCone_gluing` asserts `IsClosedImmersion`. |
| Actual graph ideal and all ideal-power quotients | `Chart.ideal = RingHom.ker (c.graph.app ⊤).hom`; `Ideal.associatedGradedPiece` and `Ideal.associatedGraded` are the existing upstream definitions. |
| Global quasi-coherent graded algebra | `Gluing.algebra : d.Z.GradedAlgebraData`; this existing affine-basis model includes degreewise base change and restriction identity/composition. |
| Local graded-algebra identifications, units, products | `Gluing.chart` is a ring equivalence, `.homogeneous` specifies its grading, and `.scalar` fixes constants. |
| Each homogeneous class goes to its restriction | `Gluing.restriction` equates the restricted class of every `a ∈ J'^n` to `DirectSum.of ... n (s.pieceMap n a)`, whose value is exactly `[s.g.appTop(a)]`. There is no existential image class. |
| Ideal inclusion and the local piece helper | `ChartSquare.idealPower_le` supplies the power inclusion from the actual graph square. `pieceClass` and `ChartSquare.pieceMap` construct the quotient class of the actual ring-map image. Representatives cover the entire quotient. |
| Identity, inverse and cocycle laws; independence of affine choices | Comparisons are through the same `Gluing.chart` and its inverse, after restriction in `Gluing.algebra`. Restriction laws and cancellation give these equalities. All affine pairs and all affine refinements are quantified, with no affine-intersection hypothesis. |
| Independence of the closed graph neighbourhood | `LocalChart` binds an affine ambient open immersion into `Diagram.ambient`, its actual inverse-image closed graph (`.square`), and its actual kernel (`.kernel`). `Gluing.localChart_agrees` ties these charts to the original ones. `.localRestriction` specifies the same representative formula on every common refinement. |
| Degree zero is `O_Z` | `Gluing.degreeZero` says the scalar map is injective and its image is precisely the degree-zero submodule, hence bijective onto that submodule. It does not assert surjectivity onto the whole graded ring. |
| Relative Proj exists with all affine restrictions | The existing `GradedAlgebraData.relProj`, `.relProjHom`, `.relProjι` and their affine pullback/restriction theorems are used on `Gluing.algebra`. |
| Functoriality under isomorphisms of the full diagram | `DiagramIso` contains all three isomorphisms and both commutative squares. `Construction.algebraMap` uses `AlgebraMapOver`; `.algebraMap_bijective` gives an isomorphism on corresponding opens. |
| Canonical functorial map on homogeneous classes | `Construction.algebraMap_class` specifies `[a] ↦ [s.g.appTop(a)]` through the actual induced `ChartSquare`, not merely preservation of the homogeneous degree. |
| Functorial identity/composition and projections | `Construction.algebraMap_id`, `.algebraMap_comp`, `.projMap_isIso`, `.projMap_over`, `.projMap_chart`, `.projMap_id`, `.projMap_comp`; the local Proj map is the existing `Proj.map` of that specified graded map. |
| Locally finite type; specified first-Fitting inclusion | `Construction.branch` binds `[LocallyOfFiniteType f]` and uses `singularDiagram f`, whose inclusion is exactly `Scheme.firstFittingSingularSubscheme f`. |
| Actual branch scheme and its projection | `Construction.branch` supplies an isomorphism with the fixed `Scheme.nodalBranchScheme f` and the equality over `Scheme.nodalBranchMap f`. |
| Canonical branch comparison, Step 8 | The same existential isomorphism carries `BranchNormalization`. Its `.quotient` fixes `a ⊗ r̄ ↦ [ar]` in every degree on every actual coborder blow-up chart. Its `.chart` fixes the corresponding Proj map followed by the actual `ker.blowupι W`. |
| No separatedness, nodal, flatness or quasi-compactness assumptions; graph need not be closed globally | None is bound in `Diagram` or `Construction`. `Diagram.graph` is only used through affine open neighbourhoods with their closed restrictions. Only the affine graph is asserted closed. |

`BranchNormalization.quotient` expresses the tensor formula in balanced form:
the image of `a ⊗ r̄` is `reesMap (a X^n)` multiplied by the degree-zero scalar
obtained by restricting `r` to the centre. This is exactly the pure-tensor formula
for the scalar extension of the Rees map. Taking `r = 1` fixes the map on every
homogeneous Rees monomial; these span the Rees algebra. The kernel and scalar
formulas make it depend only on `r mod J` and `a mod J^(n+1)`.
`BranchNormalization.chart`, together with the equality of projections to `Z`,
therefore fixes the isomorphism into the actual pullback exceptional fibre.
The map cannot be replaced by an arbitrary automorphism over `Z`.

The closed-neighbourhood charts are needed because an entire original graph
ambient need not fit inside a chosen affine coborder open. `LocalChart` permits
common affine refinements of their intersection. Its ring presentation records
`sections : R ≅ Γ(Y, ⊤)` and the actual transported kernel, not an arbitrary ideal.
For `branchChart f W`, the ring is literally `Γ(coborder, W)` and the ideal is
literally `(Scheme.nodalBranchClosedGraph f).ker.ideal W`, which is the ideal
used by the actual blow-up's affine chart. `branchChart_properties` gives the
pullback and top-section kernel transport; it postpones only these properties.

The following dependency declarations are actually used by the signatures or
constructions (the containing public modules also supply their Mathlib imports).

- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.lift`, `pullback.map`, `pullback.fst`, `pullback.snd`.
- `Mathlib.AlgebraicGeometry.Scheme` and `Morphisms.ClosedImmersion`: `Scheme`,
  `Scheme.Hom`, `IsClosedImmersion`; `Morphisms.FiniteType`: `LocallyOfFiniteType`.
- `Sheaf.AlgebraicGeometry.FirstFittingSingularSubscheme`:
  `Scheme.firstFittingIdealSheaf`, `Scheme.firstFittingSingularSubscheme`.
- The delivered `Sheaf.AlgebraicGeometry.NodalBranchSchemeRepair`:
  `Scheme.nodalBranchGraph`, `Scheme.nodalBranchClosedGraph`,
  `Scheme.nodalBranchClosedGraph_isClosedImmersion`, `Scheme.nodalBranchScheme`,
  `Scheme.nodalBranchMap`.
- `WeilConjectures.RingTheory.AssociatedGradedRing`:
  `Ideal.associatedGradedPiece`, `Ideal.associatedGraded`,
  `Ideal.associatedGradedRingHom`; Mathlib's `Submodule.Quotient.mk` and
  `DirectSum.of` give the actual representative classes.
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`:
  `Scheme.GradedAlgebraData`, `.relProj`, `.relProjHom`, `.relProjι`,
  and the imported `Proj.map` API.
- `WeilConjectures.Blowup.Affine.ReesGrading` and `WeilConjectures.Blowup.Gluing`,
  publicly supplied through the branch dependency: `reesGrading`, `reesMonomial`,
  `Scheme.IdealSheafData.blowupMap`, `.blowupι`.

The recorded `ConormalGradedAlgebra.exists_conormalGradedAlgebra` and
`ConormalAlgebraFlatBaseChange.existsUnique_baseChangeMap` were read for the
proof plan in Steps 2--5 and 7. The statement itself uses their existing affine
associated-graded model, not their sheaf-presentation declarations. The old
report incorrectly listed those declarations and the relative-Proj base-change
interface as directly used in the Lean signatures; this report does not.
The redundant/unused direct imports named by H9 were removed. No global conormal
algebra, Rees algebra, blow-up or relative Proj construction is redefined here.

Edge checks:

- Empty `Z` and empty affine opens are allowed; no nonemptiness condition appears.
- The zero/unit graph ideals and vanishing homogeneous pieces are allowed.
- For `n = 0`, the ideal power is the unit ideal, the representative map is the
  actual ring map, and the quotient/constant equations remain present.
- For `i = id`, the diagonal conormal algebra need not be concentrated in degree
  zero. The repaired `degreeZero` allows its positive pieces. In particular the
  false requirement that the entire scalar map be bijective has been removed.
- For `P¹` with `i = id`, a different line-bundle symmetric algebra cannot satisfy
  the new restriction equations merely because its charts preserve homogeneous
  degree: it must have exactly the restriction maps of the actual graph ideal
  classes. This addresses the review's `Sym O(-1)` versus `Sym Ω` counterexample.
- On nonseparated schemes the global graph may not be closed. The original
  affine graph charts and the fixed coborder charts still apply; their overlaps
  are refined by affines, rather than asserted affine.
- For the branch comparison, `r = 1` fixes each Rees monomial; arbitrary `r`
  fixes the balanced tensor formula, including the degree-zero unit. The chart
  equality also fixes the map to the actual blow-up, ruling out an unnormalized
  isomorphism over the centre.
- All schemes/rings are in the one source universe `u`; no extra size equality,
  finiteness, separatedness, flatness or nodality hypothesis has been added.

Searches (retained searches plus the repair search):

- `msearch.py leanfinder`: "Affine graph conormal graded algebras glue on closed
  centres without separatedness, with canonical relative Proj": 8 hits, including
  `Proj`, `Proj.fromOfGlobalSections`, `Proj.pullbackAwayιIso`, `Proj.awayι`;
  no matching graph-cone gluing statement.
- `msearch.py loogle`: `AlgebraicGeometry.Scheme, GradedAlgebra`: no hits.
- `msearch.py grep`: `graph.*conormal|conormal.*graph|graphCone` in Mathlib
  `AlgebraicGeometry`: no hits. `rg` of `lean/WeilConjectures` and `lean/Sheaf`
  for the graph-cone and branch names gave no duplicate of this item.
- Repair `msearch.py leanfinder`: "Canonical Rees quotient from the Rees algebra
  tensor the quotient ring to the associated graded ring sends a tensor r to
  the class of ar": 8 hits. These include
  `TensorProduct.tensorQuotEquivQuotSMul_comp_mk`,
  `Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk` and
  `TensorProduct.quotTensorEquivQuotSMul_mk_tmul`; they are generic quotient/tensor
  tools, not a normalized map from this graph-cone Proj into this actual blow-up.
- Repair `rg` for `GraphCone|pieceClass|BranchNormalization|LocalChart.ringMap`
  in both project source roots found no duplicate helper declarations.
- Read the existing associated-graded quotient definition, the affine Rees grading,
  affine blow-up and global blow-up charts, and the relative-Proj chart API.
  Read Stacks `divisors.tex`, `definition-conormal-sheaf`,
  `lemma-affine-conormal-sheaf`, `lemma-conormal-algebra-functorial`,
  `lemma-conormal-algebra-functorial-flat`, `lemma-blowing-up-affine`, and
  `constructions.tex`, `lemma-relative-proj-base-change`. Their actual restriction
  and quotient formulas are precisely the added normalization equations.

There is no remaining `STATEMENT-DISPUTED` flag. The original mathematical node
statement and all its dependency/proof lists are unchanged.

## Dependency modules

`def-sfb-nodal-branch-scheme`: its recorded O2 module `NodalBranchScheme` was not
available in the live source reader; the returned review explicitly accepted this
§1(B) repair. The retained `NodalBranchSchemeRepair` defines the same first-Fitting
graph, its fixed coborder closed immersion, the blow-up along its actual kernel,
and the actual pullback exceptional fibre and second projection. The new named
`nodalBranchClosedGraph_isClosedImmersion` exposes a property already required
by that node, allowing the affine inverse images used by `branchChart`. Its proof
is `sorry` with its source and cancellation/coborder proof in its docstring.
Only the dependency's `lean` field is changed. Its principal definition/signature
and all actual construction data are retained.

## Repairs to the returned review

- H3 (F1): replace both existential homogeneous-image clauses by the exact
  representative equations through `s.g.appTop`; supply the named power-inclusion
  theorem and the real local piece-class helper. The gluing docstring now describes
  the equation that the fields actually impose (H8).
- H3 (F2): strengthen the branch clause with `BranchNormalization`, binding the
  actual Rees quotient formula and the corresponding map into every actual blow-up
  chart. Tie the added local neighbourhood presentations to the original charts
  through the same representative restriction formula.
- H9 advisory: remove the unused direct imports listed in the return and correct
  the report's claimed declaration-use list. The needed Rees/blow-up definitions
  come from the branch dependency's public imports.
- H11: replace the conclusory second reading with the explicit clause list below.
- Additional fault found during repair: change `degreeZero` from bijectivity onto
  the whole algebra to injectivity and image equal to degree zero. This repairs
  the Lean rendering of the existing node, not the mathematical node statement.

## Second reading by Q19

A fresh self-reading of both modules and both node copies was performed after
compilation. No other agent was started, as the dispatch brief explicitly forbids
that. The individual clause checks were:

1. Arbitrary scheme morphism and closed centre: `Diagram` binds exactly these
   objects and the closed-immersion instance. No other geometric hypothesis.
2. Affine pair and containment: `Chart.V`, `.U`, `.le` match the quantified pair.
   `.centre`, `.ambient` and `.graph` are the actual inverse image, fibre product
   and graph with components `(i,1)`; no replacement scheme or map.
3. Closed affine graph and its ideal: the theorem's first conjunct gives
   closedness; `Chart.ideal` is the actual section-map kernel. The helper theorem
   `Chart.local_properties` postpones properties of those fixed objects only.
4. All conormal pieces: `Gluing.chart` uses exactly the upstream direct sum of
   `J^n/J^(n+1)`; `.homogeneous` identifies its actual grading.
5. Restriction of every class: the original existential image formula was a
   mismatch. It is replaced by `[a] ↦ [s.g.appTop(a)]` using `.idealPower_le` and
   `.pieceMap`. Quantification over ideal-power representatives covers every
   quotient class. The formula is not implied by degree preservation alone.
6. Units and multiplication: the charts are ring equivalences and the scalar
   formulas identify constants; hence neither multiplication nor the unit is
   merely chosen independently.
7. Identity, inverse and cocycle: common restrictions of the one global algebra
   and cancellation of chart/inverse-chart maps give the required laws. All
   affine pairs and common affine refinements are included.
8. Gluing and independence: `GradedAlgebraData` includes the actual degreewise
   quasi-coherent restriction/base-change condition. `LocalChart.square` and
   `.kernel`, `localChart_agrees` and `localRestriction` fix the same algebra
   across different closed graph neighbourhoods.
9. Degree zero: the old total-ring bijectivity was false for positive conormal
   pieces. The repaired injectivity plus image-equals-degree-zero condition says
   exactly `G_0 = O_Z` and leaves all positive pieces available.
10. Relative Proj and affine restrictions: the existing `.relProj`, `.relProjHom`
    and `.relProjι` are used on that same algebra, with the existing canonical
    relative-gluing restriction interface; no separately chosen Proj scheme.
11. Canonical diagram functoriality: the three isomorphisms and both squares are
    specified; the actual ambient map is constrained by both projections.
    `algebraMap_class` now fixes its pullback on every representative, correcting
    the second existential-image mismatch. The identity/composition fields for
    algebra and Proj and the local Proj formula are all present.
12. First-Fitting hypothesis: `singularDiagram f` uses precisely the dependency's
    inclusion and `[LocallyOfFiniteType f]`; no nodal or flatness assumption.
13. Actual branch scheme over `Z`: the target is literally the dependency's
    blow-up pullback, and the projection equation uses its second projection.
14. Canonical branch identification: the old bare isomorphism was insufficient.
    `BranchNormalization.quotient` now sends `a ⊗ r̄` to `[ar]` in all degrees
    on each coborder affine, and `.chart` fixes the actual map to `ker.blowupι W`.
    The transported ideal is proved equal to the actual blow-up ideal, not
    an unrelated local ideal. The new local charts agree on common refinements
    with the original charts, so their freedom cannot absorb a branch automorphism.
15. Exclusions/edge cases: empty centres, zero and unit ideals, `n = 0`, `i = id`
    and nonclosed global graphs remain included. No affine-intersection or
    nonemptiness assumption appears.
16. Dependency rereading: the same graph, canonical coborder, actual kernel
    blow-up and pullback exceptional fibre are retained. The added closedness
    theorem only exposes the property stated by the dependency; no construction
    is chosen from an uncharacterized existence statement.

The main theorem signature is unchanged and recorded verbatim; all helper
signatures explicitly bind their variables and universes. Both delivered files
compiled through `scompile.py` separately in dependency order with no error or
non-sorry warning. The main module compiled in under 32 seconds, within the
unchanged 60-second per-file limit. Final delivery preflight is run by the
prescribed wrapper; no local global build or project check script was run.
