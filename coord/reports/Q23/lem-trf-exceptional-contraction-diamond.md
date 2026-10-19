## Worker report

The module `Sheaf.AlgebraicGeometry.ExceptionalContractionDiamond` states
`AlgebraicGeometry.exceptional_contraction_diamond`, with proof `sorry`. It retains the
saved attempt's statement and eight-step proof docstring, checked against the current
node. The saved packet lacked report.md and its node had no lean record; these are restored.
The first dry run diagnosed precisely the missing report. The current natural statement
already includes the stage-1 correction requiring a proper k-morphism r. This delivery
does not change that statement or any other field except lean.

Hypotheses and notions, clause by clause:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- The reference k-scheme is `(C : Scheme.{u}) (c : C ⟶ Spec (.of k))`.
- The semistable multipointed k-curve is `P : MultipointedCurve (Spec (.of k))`
  with `hP : P.IsSemistable`. Its underlying data include flat finitely presented
  curve and marking, pure fibre dimensions one and zero, and a closed marking.
- The proper k-morphism is `r : P.X ⟶ C`, `hr : r ≫ c = P.x`,
  and `hrproper : IsProper r`. No properness of c or P.x is imposed.
- Componentwise noncollapse is
  `∀ x : P.X, ¬ (r '' connectedComponent x).Subsingleton`. Every connected component
  contains one of these x; its image is nonempty, so this means more than one point.
- An exceptional component is the existing `P.IsReferenceExceptionalComponent k r a`.
  Its definition requires a closed immersion of the actual projective line, the
  equation over Spec k, irreducible-component image, singleton reference image, and
  `(Set.range a ∩ (Set.range P.i ∪ {x | x ∉ P.x.smoothLocus})).encard ≤ 2`.
  This counts distinct marked or nonsmooth points, not multiplicity. A projective line
  is nonempty, so the subsingleton reference image is precisely a singleton.

The first universally quantified clause handles every supplied contraction:

- Q and hQ give the semistable quotient, `h : P.Hom Q` is a morphism of pointed
  k-curves, `hm : IsIso h.marking` transports the marking isomorphically, and
  `hs : h.curve ≫ s = r` is the reference factorization.
- a and ha specify the exceptional component. The point leg b and
  `IsPushout a (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) h.curve b`
  assert the actual scheme pushout universal property, not a chosen arbitrary map.
- `IsProper h.curve ∧ Surjective h.curve ∧ GeometricallyConnected h.curve`
  gives properness, surjectivity and connected geometric fibres.
- U and V are precisely the complementary opens by their displayed underlying-set
  equations. `e : U.toScheme ≅ V.toScheme` and
  `e.hom ≫ V.ι = U.ι ≫ h.curve` assert that the restriction of the supplied curve
  map is the isomorphism between these complements.
- `IsProper s` and the final quantified nonsubsingleton image are the properness
  and componentwise noncollapse of the induced reference map.

The second universally quantified clause gives the diamond:

- PA, PB, hPA, hPB, rA, rB, hA, hB, hmA, hmB, hrA and hrB specify two
  supplied contractions with semistable quotients, invertible marking maps and
  reference factorizations. haA and haB specify their exceptional components.
- `Set.range aA ≠ Set.range aB` expresses distinct components independently of
  their chosen projective-line parameterizations; hpA and hpB are the two pushouts.
- `PA.IsReferenceExceptionalComponent k rA (aB ≫ hA.curve)` and its symmetric
  clause state that the restrictions are closed immersions with exceptional
  irreducible-component images, including the projective-line identification.
- The existential T is the common multipointed target with `T.IsSemistable`.
  `jA : PA.Hom T` and `jB : PB.Hom T` are pointed k-morphisms; both marking
  maps are isomorphisms. rT is their common reference map, with the two stated
  factorization equations.
- The two IsPushout clauses, with dA and dB, contract exactly the residual components.
  Together with the exceptional-component clauses they are elementary contractions.
- The final curve and marking equations are equality of the composites as pointed
  k-morphisms, rather than just equality of underlying topological maps.

The point legs need no extra over-k hypothesis: the pushout square, curve_over and
the exceptional component's over-k equation imply it after cancelling the scalar
map P1 → Spec k, which has a k-point section. The induced reference maps are likewise
k-morphisms by cancellation of the elementary pushout, whose point leg is recovered
through that same section. Thus these are not unspecified extra structures.

Dependency declarations read and used:

- `Sheaf.TraceFormula.MultipointedCurve`: `AlgebraicGeometry.MultipointedCurve`.
- `Sheaf.AlgebraicGeometry.MultipointedCurveModification`:
  `AlgebraicGeometry.MultipointedCurve.Hom`, including curve_over, marking_over and
  comm, and `AlgebraicGeometry.MultipointedCurve.IsSemistable`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits`:
  `AlgebraicGeometry.ProjectiveLine.TwistData`; the underlying projective line is
  `AlgebraicGeometry.ProjectiveLine` from ProjectiveSpace, with its actual structural map.
- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.FieldTheory.IsAlgClosed.Basic`:
  `IsAlgClosed` (the algebraically-closed part of the algebraic-closure dependency).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `IsColimit` and its scheme-pushout
  specialization `CategoryTheory.IsPushout` from
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, `connectedComponent`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, used by
  `AlgebraicGeometry.GeometricallyConnected` in
  `Mathlib.AlgebraicGeometry.Geometrically.Connected`. The latter means connectedness
  after every field-valued base change and equivalently connected geometric fibres.
- The already landed `AlgebraicGeometry.MultipointedCurve.IsReferenceExceptionalComponent`
  is reused from `Sheaf.AlgebraicGeometry.ValuationStableBlowdownUniqueness`.
  No second exceptional-component predicate is defined. That node is a proof consumer
  of this item, so adding it as a DAG dependency or importing this module back into its
  module would create a cycle. Its current module contains the shared helper and does
  not import this theorem. The maintainer must retain that proof-import omission unless
  the shared helper is moved to its own owning module later.

The two already stated proof dependencies NodalGeometricFibresReduced and
NodalSubcurveBoundary are imported without public, following the statement-stage rules.
The closed-immersion/proper-to-separated proof inputs are supplied by the existing
Mathlib Proper interface. ClosedUnionPushout and RelativeNodalPointPinching have no
recorded Lean modules on the current base; their future proof imports are omitted.
Neither is needed to type this statement. No new node or dependency repair is required.

Source check: read Temkin's PDF https://arxiv.org/pdf/0707.3953, printed pp. 57–58,
especially the paragraph defining elementary exceptional contractions and Lemma B.3.
Its proper-reference assumption agrees with the already corrected node. The node's
eight-step argument supplies the relative local-diamond refinement. The theorem docstring
preserves all eight steps, including the two applications of nodal-subcurve-boundary.

Edge cases checked: empty markings impose no nonemptiness condition on P.D; empty P
makes the component/contraction quantifiers vacuous. Disconnected P is allowed since
noncollapse is componentwise. The reference C and structural maps need not be separated
or proper over k. A whole collapsed connected component, including a lone projective
line and the two-component loop, is excluded by noncollapse. Distinct parameterizations
of the same component do not activate the diamond clause. Disjoint components and
components meeting once both activate it. One boundary point can carry at most one
marking after contraction; two boundary points create an unmarked node. No characteristic
restriction or extra universe equation is introduced.

Searches made and retained from the earlier attempt:

- msearch LeanFinder: "Two elementary exceptional rational component contractions of a
  semistable multipointed curve commute in a diamond": eight unrelated existence/gluing
  and Weierstrass composition results, no diamond theorem.
- msearch Loogle: `IsPushout, Scheme`: zero hits (unknown unqualified IsPushout); this
  unsuccessful query is not treated as evidence that Mathlib lacks pushouts.
- msearch LeanFinder for exceptional components: eight Weierstrass nonsingularity hits;
  Loogle `"IsReferenceExceptionalComponent"`: zero Mathlib hits.
- msearch LeanSearch for exceptional components: irreducibleComponents and generic-point
  facts only. Repeated LeanSearch for the two-component diamond returned Weierstrass point
  equalities and Scheme.RationalMap, none with this statement.
- msearch grep `exceptional.*component|contraction.*curve|blowdown` in Mathlib's
  AlgebraicGeometry directory: zero hits.
- rg of the source WeilConjectures and lean/Sheaf with exceptional-component,
  contraction and declaration-name patterns: no existing diamond; found and read the
  landed IsReferenceExceptionalComponent helper, reused here. Searching this blueprint
  id in source WeilConjectures returned no hits.

Validation: the saved statement compiled through scompile.py without errors or warnings.
The final file, including its two proof-only imports, is compiled again through the same
wrapper and the required delivery dry run. All universe and term variables are explicitly
bound and autoImplicit is false. The only postponed declaration is this node's theorem.
No statement fault was found beyond the already recorded stage-1 properness correction;
the old split_report's disputed flag refers to the old statement, not the corrected one.

## Second reading by Q23

Self-check by the dispatched worker, not a claimed independent reviewer: the dispatch
explicitly forbids starting other agents; the maintainer supplies the independent review.
I reopened the current node and Lean file and compared all clauses above. Proper r,
the over-k equation, semistability, componentwise noncollapse, invertible marking maps,
both supplied pushouts, proper/connected-fibre permanence, complementary-open restriction,
the two residual closed component embeddings, the common pointed semistable target,
both second pushouts and both composition equalities all have the stated counterparts.
The missing report and lean record were repaired; two available proof imports were added.
No signature change, new notion, statement correction or additional hypothesis was needed.
