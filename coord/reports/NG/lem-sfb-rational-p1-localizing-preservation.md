## Worker report

The delivery states `AlgebraicGeometry.ProEtale.RationalP1.localizingPreservationChecks`
in `Sheaf.Paper.RationalP1LocalizingPreservation`. Its only postponed proof is this theorem.
Four auxiliary Prop structures expand the clauses of this same node and have no chosen or
postponed construction data. No theorem is proved. The node's statement is unchanged.

I read the complete node and its eight proof steps, every statement dependency and its
recorded declarations/docstrings, the live source theorem in RationalP1UnitCounit, the
parent's 2026-10-27 repair order and stage-1 reports, and the latest blueprint proof at
`sec-six-functors-basics/sk-prop-p1-adjunction-rational/`.

Hypotheses and objects:

- `l : ℕ` with `[Fact l.Prime]` and `p : ℕ` with `[Fact p.Prime]` are the two primes;
  `hpl : p ≠ l` is their distinctness. `[Field k] [CharP k p]` supplies the field and
  positive characteristic, without algebraic or separable closedness assumptions.
- `Y : Scheme.{u}` with `[Y.Over (Spec (.of k))]`, its structure morphism's
  `[LocallyOfFiniteType] [QuasiCompact] [IsSeparated]` are exactly a separated finite-type
  k-scheme. There is no properness assumption on Y over k.
- `c : Option (PadicAlgCl.FiniteIntermediateField l)` selects either a finite intermediate
  E (`some E`) or the fixed algebraic closure (`none`). The existing `coefficient l c`
  uses `continuousMapRingObj E` in the first case and `padicAlgClRingObj l` in the second;
  the second is the finite-subextension-valued ring, not all continuous closure-valued maps.
  This indexing loses no coefficient case; the E unused when Lambda is Qbar is immaterial.
- `ProjectiveLine Y` is the existing base-change projective space with two homogeneous
  coordinates; `diagonalSurface Y` is its actual self-pullback; `firstProjection`,
  `secondProjection`, `diagonalImmersion` are the fixed maps. The complementary open is
  `(diagonalImmersion Y).openComplement`, with its canonical `.ι`.
- `Modules Λ Z` is the existing internal `Mod` over `condensedRingObj Λ Z = p_Z^* Λ`.
  `DerivedCategory (Modules Λ Z)` is the ordinary unbounded category. Derived pullback and
  pushforward are the recorded total derived functors of the composites, not derived
  functors of underlying abelian sheaves. `derivedTensor` is the existing relative tensor.
- `constantModelBoundedConstructible Λ Z` uses bounded cohomology with the finite constant
  scalar-model constructibility definition. `CategoryTheory.localizingClosure` is the
  existing full replete triangulated ambient-coproduct closure, with its fixed ambient
  indexing universe; no derived-completeness restriction is imposed.
- `line l c Z` is the existing positive rational or Qbar Tate module. It is placed in degree
  zero by `DerivedCategory.singleFunctor _ 0`. `RationalP1.twist` is the existing tensor
  with this line followed by the positive shift `(2 : ℤ)`.

Conclusion clauses:

- `geometry.noetherianY/P/W` states Noetherianity; `geometry.qcqsY/P/W` states compactness
  and quasi-separatedness of each of Y, P, W.
- `geometry.properQ/properFirst/properSecond/properDiagonal` gives properness of every
  named map. `geometry.closedDiagonal` gives the closed immersion.
  `geometry.quasiCompactComplement` gives quasi-compactness of the actual open complement.
- `geometry.invertibleY/P/W/Complement` gives `IsUnit (l : Z.residueField x)` at every point,
  exactly invertibility of l on the schemes. This remains meaningful for empty schemes.
- `geometry.standingP/W/Complement` states separatedness and both parts of finite type
  for the displayed structure composites to Spec k. Y's standing setting is the original
  binders. All arrows are k-morphisms for these structure maps by the existing projective
  and self-pullback constructions; the second projection uses the pullback equality.
  No extra assertion equating arbitrary structural choices or a tautological equality is
  added to the theorem.
- `pullQ/pushQ`, `pullFirst/pushFirst`, `pullSecond/pushSecond`,
  `pullDiagonal/pushDiagonal` each instantiate `LocalizingFunctorChecks` with precisely
  the corresponding ambient functor. Its `preserves` is the objectwise implication between
  the appropriate localizing closures, for every unbounded derived object in that closure.
  Its `exactRestriction` supplies shift commutation and `Functor.IsTriangulated` for both
  the ambient functor and its actual `ObjectProperty.lift` through the full inclusions.
  `sourceTriangulated/targetTriangulated` supply the inherited subcategory triangulations.
- `objectsY/P/W.coefficientUnit` and `.positiveLine` are membership of the coefficient unit
  and the positive Tate module, in degree zero, in the specified Dbc.
  `.tensorClosed` quantifies over arbitrary A and B in Loc(Dbc) and gives their derived
  relative tensor in that same closure.
  `.twist` gives preservation and exactness for the existing T_Z.
- `pushQ.preserves` is the original pushforward preservation obligation;
  `twistedPullQ.preserves` is the original twisted-pullback preservation obligation,
  in exactly the original order of composition. Their `exactRestriction` fields give the
  two well-defined exact functors on the full localizing categories. The canonical lifts
  carry the ambient object and morphism actions, so no arbitrary substitute functor occurs.

Dependency declarations used (module, declaration):

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  the explicit separated finite-type Over-setting and its `compactificationOverField` API;
  the chosen compactification is not needed to form this theorem's two functors.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing`, `Profinite.padicAlgClRingObj`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj` and its commutative ring-object structure.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`:
  `ProjectiveSpace`, `ProjectiveLine` and its canonical structural map.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `moduleObjectDerivedPushforward`, `moduleObjectDerivedPullback`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`:
  public derived tensor/monoidal interfaces, especially `CondensedRing.derivedTensor`.
- `Sheaf.Paper.ProfiniteFiniteConstantLocalModel` publicly retains the recorded scheme
  `HasFiniteConstantLocalModel`, `IsConstantModelConstructible`,
  `constantModelBoundedConstructible` from `CondensedConstantConstructibility`.
- `Sheaf.Paper.LocalizingAdmissibleCoefficients` publicly retains the localizing closure
  interface; `CategoryTheory.localizingClosure` from `Sheaf.Paper.LocalizingClosure`
  is the exact closure used in the existing rational projective-line assembly.
- `Sheaf.Paper.ProEtaleTateTwistsOfUniverses` retains the actual Tate constructors.
  `Sheaf.Paper.RationalTatePullback` supplies their existing `coefficient` and `line`
  selections; `Sheaf.Paper.TateTwistedProjection` supplies the existing `twist`.
- `Sheaf.Paper.ProjectiveDiagonalPullback` (publicly imported by the twist module) supplies
  the fixed `firstProjection`, `secondProjection`, and shared tensor bundle.
  `DiagonalTowerSystemInterface` supplies the fixed self-product and diagonal.
- Mathlib's `IsNoetherian`, `CompactSpace`, `QuasiSeparatedSpace`, `IsProper`,
  `IsClosedImmersion`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, and
  `ObjectProperty.IsTriangulated` are used without private replacements.
  `Scheme.Hom.openComplement` is the existing upstream closed-immersion construction.

The plain imports retain all recorded non-Mathlib proof dependencies: CartesianCoefficients,
LocalizingClosureCtfEqualsBc, UnboundedLocalizingPullback, ProperImageLocalizingProper,
FieldTensor and ProjectionMateExact. The projective-space and Noetherian/proper/finite-type
Mathlib dependencies are also present. The theorem docstring follows all eight node steps.

Edge cases checked: Y may be empty and need not be proper; then P and W may be empty too,
and the complement may be empty. All geometry and residue-field quantifications retain
these cases. No global section is required to be nonzero on the empty scheme. The zero
complex is admitted, and no boundedness restriction is placed on objects in the localizing
closure. Both coefficient choices, including E=Q_l, are retained. The characteristic is
positive and distinct from l, including l=2 or p=2 when they are distinct. The site object
universe remains u+1, site morphism universe u, coefficients u+1, and standard ambient
internal-module derived category; no universe equality or small-site specialization is added.

Searches:

- `msearch.py leanfinder`: “Proper projective-line derived pushforward and Tate-twisted
  pullback preserve localizing bounded constructible internal modules”. Eight results,
  including Scheme.Modules.pushforward and light-condensed internally-projective results;
  none states this internal rational pro-etale package.
- `msearch.py loogle`: `CategoryTheory.Functor.IsTriangulated, CategoryTheory.ObjectProperty`.
  Seven results, including `ObjectProperty.isTriangulated_lift`; these supply the generic
  restriction API but not the assigned geometric/preservation theorem.
- `msearch.py leansearch`: “Exact functor restricts to a triangulated full subcategory when
  it preserves the defining object property”. Eight results, including `ObjectProperty.lift`,
  `ObjectProperty.ι` and `Functor.IsTriangulated`; the existing constructions are reused.
- `msearch.py grep`: `localizingPreservation|Localizing.*Preservation|rationalLocalizingCategory`:
  zero Mathlib hits.
- `rg` in live `lean/WeilConjectures` for the item id and preservation names: no matching
  theorem. `rg` in `lean/Sheaf` found the older `localizingPreservation` in
  `RationalP1UnitCounit.lean`; I read its full signature and proof docstring. It is only the
  final preservation pair, not the full current node (also observed in ND's stage-1 report).
  Therefore this is not an exact `existing: true` match. Reusing its name would duplicate a
  live declaration; the new full-package theorem is named `localizingPreservationChecks`.
  No original assembly source is modified. Searches for this name and all four helper
  structure names in Mathlib/WeilConjectures/Sheaf returned no collisions.

There is no statement correction, disputed mathematical claim, new DAG node or dependency
module. The helper structures only package the clauses already stated in this node.

Validation: `scompile.py NG lem-sfb-rational-p1-localizing-preservation` passes for the
complete module, in both sandbox mode (18.1 seconds) and library mode (12.6 seconds),
with no errors or warnings. The canonical restriction elaborates with the inherited
additive shift families shared explicitly, without increasing the heartbeat limit or
changing transparency. The node changes only `lean`, its recorded theorem signature
matches the file verbatim up to its proof delimiter, and every source line has at most 100 characters.
The required `deliver2.py --no-push` dry run passes preflight and per-file compilation
(2026-10-27; dry-run commit 8326c3959ac).

## Second reading by NG

This is a second pass by the assigned worker; the prompt prohibits starting other agents,
and the maintainer performs the independent review. I reread the source node alongside the
new module. The initial extraction of the old pair omitted geometry, the three object
checks, eight arrow functors and exactness. I replaced that draft with the full package
listed above. I also removed the attempted reuse of the already declared old theorem name.
Each source clause now has the corresponding explicit field, and the coefficient line,
relative derived tensor, ordinary derived category and ambient localizing closure are the
existing declarations. There are no hypotheses of properness of Y or boundedness of objects
in Loc, no alternate coefficient ring, and no arbitrary functor replacing a canonical lift.
