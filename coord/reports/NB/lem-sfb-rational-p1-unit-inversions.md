## Worker report

Attach the existing theorem
`AlgebraicGeometry.ProEtale.RationalP1.unitInversions` in
`Sheaf.Paper.RationalP1UnitCounit`, read at lines 430–440 together with the section
parameters at lines 362–366. Its proof is already `sorry`, as stage 2 requires.
There is no new module, construction, helper, dependency repair, or statement correction.
The node is changed only in `lean`.

The node's `lean_candidates` already identifies this exact declaration, while suggesting
an intended separate module. The live source reader (`scompile.py --source
Sheaf.Paper.RationalP1UnitCounit`) confirms that the restored live module still owns the
declaration. The one-definition rule takes precedence over the candidate's suggested
future file location: this delivery records the existing owner without moving or
restating any declaration. The parent node also still lists this declaration among its
existing exports; that ownership bookkeeping is for the maintainer.

Source read: the current blueprint file
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-p1-adjunction-rational/sk-prop-p1-adjunction-rational-unit-counit.proof.md`,
Well-definedness (2)–(3), and its unit `_section.md`. The proof states proper base change
on the localizing category and the projection formula for the specified constituent
maps. The node refines those statements by fixing the exchange and shifted comparison.

Hypotheses and clauses:

- The prime ℓ is `l : ℕ` with `[Fact l.Prime]`. The prime p and characteristic-p field
  are `k : Type u`, `[Field k]`, `p : ℕ`, `[Fact p.Prime]`, `[CharP k p]`.
  The distinctness hypothesis is `hpl : p ≠ l`. Thus characteristic zero, equal primes,
  and nonprime p or l are not included in the intended specialization.
- A k-scheme is `Y : Scheme.{u}` with `[Y.Over (Spec (.of k))]`. The standing
  separated finite-type hypotheses are `[IsSeparated (Y ↘ Spec (.of k))]`,
  `[LocallyOfFiniteType (Y ↘ Spec (.of k))]`, and
  `[QuasiCompact (Y ↘ Spec (.of k))]`. They are the context printed immediately above
  the theorem. The server probe confirms all three instances are retained in the
  elaborated theorem type. No properness, smoothness, nonemptiness, or algebraic
  closedness of Y or k is needed.
- The chosen algebraic closure is the published `PadicAlgCl l`. The coefficient index
  `c : Option (PadicAlgCl.FiniteIntermediateField l)` covers both cases: `some E`
  for a finite intermediate field, `none` for the algebraic closure.
  `RationalP1.coefficient l c` is `Mon.mk (Profinite.continuousMapRingObj E.1)` in
  the finite case and `Mon.mk (Profinite.padicAlgClRingObj l)` in the closure case.
  The latter is the finite-subextension-valued sheaf, not all continuous functions.
  The optional finite E when the coefficient is the whole closure is unused auxiliary
  data; the conclusion has no dependency on that choice.
- P is `ProjectiveLine Y`, the existing projective space with two homogeneous
  coordinates, and q is `ProjectiveLine Y ↘ Y`. W is `diagonalSurface Y`, the actual
  self-pullback of q. `firstProjection Y`, `secondProjection Y`, and
  `diagonalImmersion Y` are the actual two pullback projections and diagonal. Their
  self-cartesian square is `square Y`; no substitute product or arbitrary square is used.
- `DiagonalCoefficients.Modules Λ Z` is the existing internal-module category over
  `condensedRingObj Λ Z = p_Z^* Λ`. The ambient category in the theorem's argument is
  the ordinary `DerivedCategory (Modules Λ (ProjectiveLine Y))`.
  `moduleObjectDerivedPullback` and `moduleObjectDerivedPushforward` are exactly
  `upperStar.leftDerivedFunctor` and `lowerStar.rightDerivedFunctor` of the full
  underived module-object functors. No completion or boundedness condition is added
  to these ambient categories.
- `rationalLocalizingCategory Λ Z` is the full subcategory on
  `CategoryTheory.localizingClosure (constantModelBoundedConstructible Λ Z)`.
  `constantModelBoundedConstructible` means bounded cohomology and
  `IsConstantModelConstructible` in every degree. The latter uses finite
  constructible locally closed stratifications and finite presentations over the
  condensed coefficient point. Thus these are finite constant local models, rather
  than merely locally finitely presented ring-object modules.
  `localizingClosure` is the intersection of replete triangulated properties
  containing those generators and closed under all small ambient coproducts in its
  fixed object-indexing universe. There is no finite-Tor or completeness restriction
  on M.
- The theorem argument
  `M : rationalLocalizingCategory (coefficient l c).X (ProjectiveLine Y)`
  encodes both an arbitrary ambient object `M.obj` and its localizing-membership
  proof `M.property`; all objects in that full subcategory are quantified, including
  unbounded ones.
- The positive Tate line is the published `line l c Z`: `spRationalTwist Z l E` or
  `spQbarTwist Z l`. The exact chosen shifted comparison is
  `secondLineComparison l c k p hpl Y`. It instantiates `shiftedLineComparison`
  at the actual `secondProjection Y`, uses the degree-zero root-normalized
  `lineComparison`, the single-functor comparison and derived shift comparison,
  and obtains residue-field invertibility of l via `residueIsUnit` from the given
  field. No residue-field unit hypothesis or arbitrary line isomorphism is added.
- The conclusion is precisely
  `UnitInversionCondition (coefficient l c).X Y (line l c)
    (secondLineComparison l c k p hpl Y) M.obj`.
  Reading the recorded definition gives the two clauses verbatim:
  `IsIso ((condensedAmbientExchange Λ (square Y)).app M.obj)` and
  `IsIso (twistProjectionMap Λ (secondProjection Y)
    (line l c (ProjectiveLine Y)) (line l c (diagonalSurface Y))
    (secondLineComparison l c k p hpl Y)
    ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M.obj))`.
  The first map has direction q* Rq* → Rp₂* p₁*. Its definition is the mate of
  the canonical pullback-composition identification under the actual derived
  adjunctions: insert the unit, apply that identification, contract the counit.
  The second map uses the inverse tensor-shift isomorphism, the canonical
  right-factor projection mate at the actual shifted line, and Rp₂* of identity
  tensor the specified comparison followed by tensor-shift. It has direction
  T_P Rp₂* → Rp₂* T_W at A = p₁* M. The conjunction is exactly the last predicate
  clause of the node, not just existence of endpoint isomorphisms.

Dependency declarations read and reused, with their owning/exporting modules:

| Dependency | Module and declarations |
| --- | --- |
| sk-def-sfb-dc-setting | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`: standing scheme context and `CondensedRing.compactificationOverField`; the theorem renders the standing context with explicit scheme/morphism instances. No compactification is needed in this conclusion. |
| sk-def-sfb-condensed-ring | `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, publicly retaining the continuous-function constructors. |
| sk-def-sfb-qlbar-condensed | `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`: `Profinite.padicAlgClSubfunctor`, `padicAlgClCondensedRing`, `padicAlgClRingObj`. |
| sk-def-sfb-pulled-back-coefficients | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`, `coefficientRing_X`, `condensedRingObj`. |
| def-nagata-projective-space-base-change | `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `AlgebraicGeometry.ProjectiveSpace`, its structure map, and the `ProjectiveLine` specialization. |
| sk-def-sfb-module-derived-pushpull | `Sheaf.Paper.CondensedModuleDerivedPushpull`: `moduleObjectDerivedPushforward`, `moduleObjectDerivedPullback`; the exported underlying derived adjunction. |
| sk-def-sfb-derived-tensor-hom | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`: `derivedTensor`, `derivedHom`, `derivedTensorHomAdjunction`. Only Layer B relative tensor is used here. |
| sk-def-sfb-constructible | `Sheaf.Paper.ProfiniteFiniteConstantLocalModel` publicly retains `HasFiniteConstantLocalModel`, `IsFiniteConstantStratified`, `IsConstantModelConstructible`, `constantModelBoundedConstructible` from `Sheaf.Paper.CondensedConstantConstructibility`. The extra profinite-slice predicate is not needed. |
| sk-def-localizing-closure | `Sheaf.Paper.LocalizingAdmissibleCoefficients` publicly retains `CategoryTheory.localizingClosure` from `Sheaf.Paper.LocalizingClosure`; its `OfSize` variant gives the same definition at the ambient object-indexing universe. `rationalLocalizingCategory` is the existing full-subcategory abbreviation in `Sheaf.Paper.RationalLocalizingTwist`. |
| def-sfb-rational-tate-pullback-comparison | `Sheaf.Paper.RationalTatePullback`: `coefficient`, `line`, `lineComparison`, `shiftedLineComparison`, `residueIsUnit`, `secondLineComparison`. |
| def-weil-pbc-ambient-ringed-exchange | `Sheaf.Paper.CondensedAmbientExchange`: `condensedAmbientPullbackComparison`, `condensedAmbientExchange`. |
| def-sfb-tate-twisted-projection-comparison | `Sheaf.Paper.TateTwistedProjection`: `twist`, `tensorShiftIso`, `projectionMateMap`, `twistProjectionMap`. |
| def-sfb-rational-p1-unit-inversion-condition | `Sheaf.Paper.RationalP1UnitInversionCondition`: `UnitInversionCondition`. |

Auxiliary existing geometry was read in `Sheaf.Paper.ProjectiveDiagonalPullback`
(first and second projections) and `Sheaf.Paper.ProjectiveDiagonalComposition`
(the self-cartesian `square`). They are already transitively exposed by the recorded
unit-condition dependency. There is no new notion needing its own node.

Edge cases checked before attachment: Y can be empty; M can be zero or unbounded;
no basis or nonzero-section choice enters the condition. Both `some E` and `none`
are preserved. The characteristic assumptions derive the needed unit even for
l = 2 (with p different), and impose no residue-field condition beyond them.
The localizing closure includes empty coproducts, arbitrary shifts and triangles.
Both arrows retain their direction and their chosen normalizations.

Searches made in this session:

- `msearch.py ... leanfinder` with query
  `The canonical proper self base change exchange on the projective line and the fixed Tate twisted projection are isomorphisms on Loc of bounded constructible rational proetale modules`:
  8 hits on Proj pullback identifications and Proj-to-Spec isomorphisms; none gives
  invertibility of these internal-module maps.
- `msearch.py ... loogle '"projectionFormula"'`: OK, 0 hits.
- `msearch.py ... grep 'unitInversions|UnitInversionCondition|twistProjectionMap'`:
  OK, 0 Mathlib hits.
- `msearch.py ... leansearch` with query
  `Proper base change and the twisted projection formula are invertible for rational proetale internal module objects in the localizing closure of bounded constructible complexes`:
  8 hits on ordinary module localization/base change, dual base change and invertible
  modules; no match for this pro-etale derived statement.
- `rg -n 'unitInversions|lem-sfb-rational-p1-unit-inversions'` in
  `lean/WeilConjectures` and `dag/lean_names_upstream.json`: no hit.
  The same search in `lean/Sheaf` finds the existing theorem in
  `Sheaf.Paper.RationalP1UnitCounit` at line 437 and its consumer at line 497.
  Searching `UnitInversionCondition`, `twistProjectionMap` and `RationalP1` in
  `lean/Sheaf` locates the exact dependency definitions inspected above.

No statement dispute is raised. The existing proof remains open; this delivery does
not claim the isomorphism assertions are proved.

## Validation

The current server source was read with `scompile.py --source
Sheaf.Paper.RationalP1UnitCounit`. The unchanged server `#check` probe passed
with exit 0 and no warning: sandbox check 8.7 seconds, library check 4.9 seconds.
Its elaborated type explicitly retains both prime hypotheses, characteristic p,
p ≠ l, the k-scheme structure, locally finite type, quasi-compactness, separatedness,
and precisely the displayed `UnitInversionCondition` at `M.obj`. The required
`deliver2.py --no-push` dry run is also run before the final delivery.

## Second reading by NB

No second reading by a worker: the dispatcher brief forbids starting another agent.
The maintainer's independent review reads this direct delivery. The table and clauses
above provide the source-to-Lean comparison for that review.
