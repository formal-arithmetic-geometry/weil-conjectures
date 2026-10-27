## Worker report

The module `Sheaf.AlgebraicGeometry.ThreeChartExceptionalCurve` states
`AlgebraicGeometry.ThreeChartExceptional.reciprocal_gluing_exceptional_curve`.
Its only postponed proof is this named theorem. All helper definitions and structures
have actual data or explicit fields, and the theorem docstring reproduces the ten DAG
proof steps with their cited nodes. The node's mathematical statement is unchanged.

The saved packet passed the initial dry run, including compilation. A further reading
found mathematical omissions: its reciprocal ring isomorphisms were independent of its
`Scheme.GlueData`; the conic map's chart formulas and two-open cover were absent; its
nodal predicate omitted distinctness and the axis/origin identifications; and its
base-change clause asserted only a projective-line isomorphism or reducedness.
The repaired packet retains the module path, theorem name, source and search history,
and replaces these insufficient interfaces by the following complete chart description.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- `k : Type u`, `[Field k]`, and `ε : Fin 2` are the field and the two-valued parameter.
  `epsilonScalar` interprets the two values as zero and one in the field. All schemes
  and extension fields live in one common universe; there is no separate smaller
  test-object universe or restriction on characteristic or algebraicity.
- `E`, its structure morphism `p`, and `C : Charts k ε E p` render "let E be the
  scheme obtained by gluing". `C.left`, `C.middle`, `C.right` have domains
  `Spec k[t]`, `Spec (middleRing k ε)`, `Spec k[h]`. The three open-immersion fields,
  `cover`, and the three `_over` equations specify an open cover over `Spec k`.
  `middleRing` is a specialization of the existing `strictNodalRing`, and
  `middleCoord` reuses `DvrNodal.coordinate`, with relation `rs=ε`.
- `C.left_overlap` is a cartesian square with top scheme `Spec k[t,t⁻¹]`, left map
  induced by the localization map, and right map induced by the ring homomorphism
  sending `r` to `t⁻¹`, `s` to `εt`, and coefficients to themselves.
  `C.right_overlap` similarly sends `s` to `h⁻¹` and `r` to `εh`.
  The `IsPullback` clauses identify these with the actual intersections of the
  specified chart embeddings, including their scheme structures.
- `C.outer_overlap` gives the actual outer intersection when `ε=1`, with `h=t⁻¹`;
  `C.outer_disjoint` specifies disjointness when `ε=0`.
- `d.conic h` for `h : ε=1` supplies `ConicData`. Its `lineIso` is an isomorphism
  with the existing `ProjectiveLine (Spec k)`, and `line_over` makes it a k-isomorphism.
  Its `conicIso` is a k-isomorphism with the existing `DvrNodal.conicIdeal` subscheme
  of projective space, whose defining quadratic section is `XY-P²` and whose
  scheme structure is not replaced by its radical. `smooth` is `Smooth p`;
  through the k-isomorphism this also says that the conic is smooth.
- `ConicData.left_formula`, `middle_formula`, and `right_formula` identify the
  composites into projective space with `ProjectiveSpace.homOfSections` on the
  vectors `[1,t,t²]`, `[r,1,s]`, `[h²,h,1]`. `coordinateSections` uses the canonical
  `Scheme.ΓSpecIso`. The existential witnesses here are proofs that these vectors
  generate the unit ideal (each contains 1), not arbitrary choices of maps.
- `ConicData.left_image` and `right_image` identify the two outer open images with
  the inverse images of `ProjectiveSpace.standardOpen` at X and Y. `outer_cover`
  gives the required two-open cover of the conic through its isomorphism with E.
  Since the given chart maps are open immersions, these are identifications with
  the specified affine lines. No characteristic hypothesis occurs.
- `d.nodal h` for `h : ε=0` supplies `NodalData`. `reduced` is `IsReduced E`;
  `rLine`, `sLine` are closed immersions from projective lines over k.
  `components` identifies `irreducibleComponents E` with their two image sets,
  and `distinct` ensures exactly two components rather than a collapsed singleton.
- `NodalData.r_axis` and `s_axis` are cartesian squares identifying the restrictions
  of these closed subschemes over V with the actual quotient maps `s↦0` and `r↦0`.
  Their coefficient and coordinate equations completely specify the ring maps.
  `r_completion`, `s_completion`, `r_avoids_right`, and `s_avoids_left` specify
  which outer line completes which axis and exclude the other outer line.
- `rOrigin`, `sOrigin` are rational sections of the two projective lines.
  `intersection : IsPullback rOrigin sOrigin rLine sLine` says that their
  scheme-theoretic intersection is exactly `Spec k`, hence one reduced point.
  `origin` locates that point in V by the coefficient-preserving evaluation
  `r=s=0`. The open immersion `C.middle` therefore gives the local equation
  `rs=0` at precisely this point, not at an unspecified singular point.
- The final quantifier ranges over every field K with `Algebra k K`.
  It supplies a complete new chart presentation `C'` on the actual fibre product
  `pullback p (Spec.map (algebraMap k K))`, and a complete `Description` there.
  Thus it repeats every conic/component/intersection assertion over K.
  `CompatibleExtension` additionally identifies the outer chart comparison maps
  with `Polynomial.mapRingHom`, and the middle one with coefficient extension,
  fixing both coordinates. It makes the chosen projective-line and embedded-conic
  isomorphisms commute with `ProjectiveSpace.map`. In the nodal case it makes both
  component embeddings and both origin sections commute with these same canonical
  maps. The cartesian intersection descriptions and axis restrictions therefore
  describe the extensions of the original subschemes and intersection, not merely
  unrelated descriptions of the base-changed curve.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`, `Scheme.ΓSpecIso`.
- `Mathlib.Algebra.Polynomial.Basic`: `Polynomial`, `Polynomial.C`, `Polynomial.X`;
  the coefficient comparison uses `Polynomial.mapRingHom`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits`: the existing
  projective line and its standard-coordinate convention (the recorded
  `ProjectiveLine.TwistData` packages twists, which this statement does not need).
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`: `Proj`; the existing
  projective-space and quadratic-zero-locus constructions realize the stated conic.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Properties`: `IsReduced`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- For `def-pc-base-change`, the recorded
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` explicitly directs
  scheme consumers to `CategoryTheory.Limits.pullback`, `pullback.fst`, and
  `pullback.snd`, used here. Its `moduleBaseChange` is for modules, not schemes.
- Reused supporting constructions: `Sheaf.TraceFormula.StrictSemistableCurve`
  (`strictNodalRing`); `Sheaf.AlgebraicGeometry.DvrNodalChartBlowupCalculus`
  (`DvrNodal.coordinate`, `DvrNodal.conicIdeal` only, with no appeal to its blowup
  theorem); `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections`
  (`homOfSections`, `standardOpen`); and `ProjectiveSpace.map` from
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`.
  No dependency theorem is used to manufacture data, and no dependency module is needed.

Edge cases checked: ε=0 and ε=1; characteristic two; imperfect fields; finite,
transcendental and identity extensions; the empty outer intersection for ε=0;
nonempty distinct components and reduced intersection; and coefficients in an
arbitrary common universe. The conic has the same chart equations in characteristic
two. The middle overlap maps preserve coefficients, so field automorphisms cannot
silently change the k-scheme structure. No zero ring is admitted as a field.

Searches retained from the saved attempt: `msearch.py ... leanfinder` on reciprocal
three-chart gluing returned general affine/Proj and unrelated Weierstrass results;
`... loogle` on `AlgebraicGeometry.ProjectiveLine, AlgebraicGeometry.Proj` returned
zero hits; `... grep` on conic/three-chart/reciprocal gluing returned zero hits.
The saved search records also include LeanSearch for the split smooth conic and
LeanFinder for the Veronese parametrization, with no exact statement match.
On resumption, `rg` over `lean/WeilConjectures/AlgebraicGeometry` and
`lean/Sheaf/AlgebraicGeometry` for `three.chart|reciprocal|exceptional_curve|conicIdeal`
found only general gluing tools, reciprocal-cover line-bundle results, and the
lower-level `DvrNodalChartBlowupCalculus` constructions. Searching the item id in
`lean/WeilConjectures` found no declaration. The supporting nodal ring, coordinates,
conic and projective maps are reused; none is privately reconstructed.

No `STATEMENT-DISPUTED` flag or mathematical node fault was found. There is no
statement correction, new DAG node, or dependency-record repair.

## Second reading by Q23

This resumed worker independently reread the saved worker's report, node and module.
The initial server dry run passed mechanically, but the reading found the disconnected
gluing transitions and missing formulas, component distinctions, origin and base-change
identifications described above. These have been repaired in the owning module.
A second pass through the repaired statement checked each hypothesis and clause against
the node: the `Charts` pullback squares now refer to its own embeddings; both coefficient
images and all reciprocal substitutions are explicit; `ConicData` contains all three
homogeneous-coordinate formulas and the two-open cover; `NodalData` contains exactly two
distinct irreducible images with the correct axis restrictions and reduced origin
intersection; and the extension statement supplies the same full data with the canonical
comparison equations. Only the theorem is `sorry`, with the entire ten-step proof in its
docstring. The node is changed only in `lean`, whose signature is copied verbatim from
the theorem. Every helper declaration is listed in `lean.declarations`.
