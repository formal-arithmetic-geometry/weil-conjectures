## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothCurvePointsDecomposition` states the decomposition theorem. It binds a field `k` with `Field` and `IsAlgClosed`, a scheme `C`, and its structure map `f` with `[IsCurve f]` and `[Smooth f]`. It existentially provides finite index types `I` and `J`, a family `D : I → Scheme`, and structure maps `d i`; `IsConnectedCurve (d i)` renders smooth separated connected one-dimensional finite-type curves, while `Smooth (d i)` renders smoothness. It provides the coproduct structure map `q`, an isomorphism `e` from `C` to the coproduct commuting with the maps to `Spec k`, and open and closed immersion instances for every coprojection. Empty `I` and `J` are allowed by the unrestricted finite types.

The statement uses `AlgebraicGeometry.IsCurve` from `WeilConjectures.AlgebraicGeometry.Curve`; `AlgebraicGeometry.IsOpenImmersion` and `IsClosedImmersion` are Mathlib declarations. The coproduct notation `∐`, `Sigma.ι`, and its finite coproduct instance come from `Mathlib.AlgebraicGeometry.Limits`, corresponding to `lem-weil-pbc-scheme-coproduct-family`.

Edge cases checked: either index type may be empty; the coproduct is indexed by `Sum I J`; the point summands are explicitly `Spec (.of k)`; no nonemptiness assumptions are imposed on `I` or `J`; all universes are the single explicit universe `u`.

Searches recorded in the node found no existing decomposition theorem in LeanSearch, LeanFinder, Loogle, Mathlib grep, or the source repository.

## Earlier second reading (a previous round; superseded)

The declaration was reread against every clause of the node. The field, algebraic-closed hypothesis, smooth curve hypotheses, finite index sets, connected smooth curve family, point summands, coproduct isomorphism, and open/closed coprojection conditions are all represented. No mismatch was found.

## Second reading by ND

Read the item node, all five statement-dependency nodes and their recorded declarations,
the delivered module, and the Stacks source before assessing the Lean. The statement list
and clause-by-clause verdicts are:

1. Object and hypothesis: an algebraically closed field k. Lean `(k : Type u) [Field k]
   [IsAlgClosed k]`. Exact: `IsAlgClosed` in Mathlib.FieldTheory.IsAlgClosed.Basic means
   polynomial splitting, equivalent there to the source's nonconstant-polynomial root
   condition. No characteristic or perfectness assumption is added.
2. Object and hypotheses: C a smooth separated finite-type k-scheme of dimension at most
   one. Lean `(C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsCurve f] [Smooth f]`.
   Exact: opened WeilConjectures.AlgebraicGeometry.Curve and checked that `IsCurve`
   extends `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f`, with
   `topologicalKrullDim C ≤ 1`. Smoothness is separately supplied by `Smooth f`, whose
   affine ring-map definition was read in Mathlib.AlgebraicGeometry.Morphisms.Smooth.
   The explicit f is appropriate since the conclusion compares structure maps.
3. Objects: two finite sets I and J, allowed to be empty. Lean existential `(I J : Type u)
   (_ : Fintype I) (_ : Fintype J)`. Exact: these are existential finite enumeration
   structures, not additional assumptions on C. Both indices precede the component family;
   choosing J before D is equivalent to the natural-language ordering since D does not
   depend on J.
4. Objects and properties: smooth separated connected one-dimensional finite-type schemes
   D_i over k. Lean `(D : I → Scheme.{u}) (d : ∀ i, D i ⟶ Spec (.of k))`, then
   `(∀ i, IsConnectedCurve (d i)) ∧ (∀ i, Smooth (d i))`. Exact: the opened
   `IsConnectedCurve` extends `IsCurve`, adds `ConnectedSpace (D i)` (including nonemptiness)
   and dimension exactly one. Contrary to the worker report's loose wording,
   `IsConnectedCurve` itself does not include smoothness; the separate conjunct supplies it.
5. Conclusion: an isomorphism over k with the coproduct of the D_i and J copies of Spec k.
   Lean uses the single family on `Sum I J`, with the two match branches D_i and
   `Spec (.of k)`. This is the canonical regrouping of the two displayed coproducts.
   Existential q has coprojection composites d_i on the curve summands and identity on
   the point summands, so q is precisely their coproduct structure map, by the universal
   property, not an unconstrained extra object. `e : C ≅ ∐ ...` and `e.hom ≫ q = f`
   give exactly the isomorphism of k-schemes. Opened the coproduct dependency node and
   Mathlib.AlgebraicGeometry.Limits: `HasColimitsOfShape (Discrete σ) Scheme` for small σ,
   `Sigma.ι`, the disjointness result, and `sigmaOpenCover` give the recorded notion.
6. Conclusion: every coprojection is open and closed. Lean has the final two universal
   conjuncts `IsOpenImmersion (Sigma.ι ... s)` and `IsClosedImmersion (Sigma.ι ... s)`.
   Exact: read the dependency nodes and Mathlib declarations. The former is the open
   immersion of locally ringed spaces; the latter is a closed embedding with surjective
   stalk maps. Transport along e gives the corresponding component immersions into C.

Source check: etale-cohomology.tex, `situation-what-to-prove` (lines 15324–15327), assumes
k algebraically closed, X separated finite type of dimension at most one; Tag 0A5B adds
smoothness and begins its proof with the finite disjoint-union reduction (15377–15391).
The torsion sheaf and prime in that cohomological lemma do not enter this geometric fact.
Also read properties.tex `lemma-regular-normal` (0569) and
`lemma-normal-locally-Noetherian` (033N), and varieties.tex
`lemma-algebraic-scheme-dim-0` (06LH), including its proof. These support exactly the
node's reduction, without properness or pure dimension one. No node correction is needed.

Edge cases: empty C is admitted by `IsCurve` (dimension bottom ≤ 1), with I = J empty.
A finite union of points allows I empty, a pure curve allows J empty, and mixed dimensions
allow both nonempty. The point summands have identity structure map, so twisted or
nonrational points are not substituted. Arbitrary characteristics are included. Universe u
is explicit and arbitrary; finite indices can always be represented in Type u, so there is
no lost index-universe case. No test objects or implicit variables occur. No integer n or
module zero object occurs in this statement. No extra Noetherian instance is assumed.

Independent searches (different wording from the first worker), recorded by msearch:

- LeanFinder: "A regular algebraic scheme of dimension at most one splits into finitely
  many integral one dimensional schemes and spectra of its algebraically closed base field".
  Eight hits, including `IsIntegral`, `affine_isIntegral_iff`,
  `isIntegral_iff_irreducibleSpace_and_isReduced`, and `isField_of_universallyClosed`;
  none states the decomposition.
- Loogle: `"IsCurve", "IsConnectedCurve"`; zero hits.
- LeanSearch: "A smooth curve over an algebraically closed field decomposes into finitely
  many connected curves and rational point schemes"; service unavailable (Internal Server
  Error). This is an availability finding, not a mathematical no-match verdict.
- rg in Mathlib, WeilConjectures, and this project's lean/Sheaf, using
  `smooth_curve_points_decomposition`, curve/decomposition in both orders, and
  `IsConnectedCurve.*∧.*Smooth`. Read the closest candidate in full:
  `AlgebraicGeometry.exists_smoothCurveConnectedCoproduct`, module
  Sheaf.AlgebraicGeometry.SmoothCurveConnectedCoproduct. It assumes
  `SmoothOfRelativeDimension 1 f` and has only curve summands. It cannot cover point or
  mixed-dimensional schemes, and is not this statement. The other hits concern
  compactification, Picard decomposition, or finite maps of connected curves.

Mismatches and repairs: no signature mismatch was found. The earlier proof docstring
only summarized the reduction and did not carry the node's five proof steps (H8). Replaced
it by the full component-graph, clopen restriction, regularity/integrality, dimension
partition, and coproduct-gluing proof, with the node citations and all source locations.
Added the standard copyright/module/public-section header, explicit public imports for
statement notions, and imports of the recorded proof-dependency modules. No theorem was
proved, no definition was added, and no new node or dependency module is delivered.

Proof-dependency metadata observation: `lem-pc-closed-imm-base-change` currently records
`IsVeryAmple.pullback_of_field`, which is not the general closed-immersion statement needed
by step 3. This is a proof dependency, not a statement dependency of this delivery; its node
was not changed. Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion already provides
`MorphismProperty.IsStableUnderBaseChange @IsClosedImmersion` (line 383), the precise
closed-immersion stability used in this argument. The recorded VeryAmple module is imported
as required by the proof-import contract; stage 3 should use the Mathlib stability result.

Validation: scompile.py compiled the single delivered module on the server, nice 19,
two threads, 60-second per-file limit; clean in 1.6 seconds, no warnings. Checked by eye
all binders and universes, and mechanically checked the line widths and that lean.statement
is verbatim the unchanged theorem signature.
