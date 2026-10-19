## Worker report

Q08 states `WeilConjectures.PurityFiniteSetting.gysin_structure` in
`Sheaf.Paper.PurityGysinStructure`. Its proof is the delivery's only `sorry`.
All thirteen auxiliary declarations have actual data or existing instance proofs.
The mathematical statement and proof fields of the DAG item are unchanged. Two
already-landed nodes are added to `stmt_deps`, because their canonical comparison
and coefficient realization are used explicitly. There are no new nodes and no
dependency repairs.

The current source read was
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/lem-pur-gysin-structure.md`
and its `.proof.md`, together with the current nine-step DAG proof. The current
source, rather than the old snapshot named in `source.document`, determines the
interpretation. No source error or statement dispute was found.

Hypotheses, individually:

- `P : PurityFiniteSetting.{u}` supplies the fixed finite field and algebraic
  closure, the prime ell distinct from p, the finite extension of Q_ell, the
  actual coefficient quotient, and the positive level. Thus there is no new
  finiteness, invertibility, or exceptional-adjoint assumption.
- `h : P.ramificationIndex ∣ P.level` is exactly e dividing n. `P.twistEtale h`
  uses exponent ell^(n/e), and the prescribed `P.coordinateKummer h Y a` uses
  this same h and coordinate.
- `Y : Scheme.{u}` and `a : Y ⟶ Spec (CommRingCat.of P.field.k)` give the
  k-scheme. The explicit structure map is needed by the recorded declaration
  `coordinateKummer`. `[IsSeparated a]`, `[LocallyOfFiniteType a]`, and
  `[QuasiCompact a]` express separated and finite type, without a second,
  unrelated structure map.
- `Line`, `zeroSection`, `Punctured`, `openImmersion`, and `lineProjection`
  are the recorded affine-line datum, not copies. Closedness and openness
  are inherited from their definitions. `AffineSpace.zeroSection_comp_over`
  supplies the retraction identity without a new hypothesis or postponed lemma.

Conclusions, clause by clause:

1. `gysinEtaleInput` is the actual root-tensor twist in degree zero;
   `gysinInput` applies exact etale/pro-etale comparison. The canonical
   `mapDerivedCategorySingleFunctor` comparison identifies its unbounded
   image with the recorded `P.twist h (Line Y)` in degree zero.
   `gysinClosed` applies the recorded `RetractedSupport.closedTerm`, hence
   literally `sfFiniteExceptionalFixed P.Ring` at the proper compactification
   of the zero section, and `gysinValue` shifts the result by 2. This is the
   finite-level exceptional formula Rnu_* followed by the ordinary etale
   exceptional inverse image followed by nu^*, in its existing fixed-scalar
   presentation. No adjunction on all pro-etale objects is assumed.
2. The first conjunct uses the dependency's actual `finiteTorConstructible`
   predicate, after applying `finiteCoefficientIntrinsicRealization` termwise.
   This existing exact coefficient realization extends the constant scalar
   action by associated-module-sheafification, so it tests precisely intrinsic
   D^b_ctf, including both bounded constructibility and finite Tor amplitude.
3. The second conjunct is `∀ q : ℤ, q ≠ 0 → IsZero (H^q(gysinValue))`.
   Both negative degrees and all positive degrees are included.
4. The third conjunct gives an etale sheaf H whose comparison is H^0 of
   the exceptional value, and an etale cover on which H is isomorphic to
   the actual coefficient sheaf. This expresses lisse rank one, without
   replacing it by constant numerical rank, global freeness, or a chosen
   orientation. Empty and disconnected covers are allowed.
5. `gysinHomToSections` takes H^0 of a derived morphism, identifies H^0(A[0])
   with A by the canonical single comparison, and evaluates on 1 through the
   actual constant-sheaf/comparison adjunctions. Its bijectivity identifies
   the stated derived Hom space with global sections of H^0.
6. `GysinSupportIdentification` supplies the supported-cohomology isomorphism
   as a module isomorphism. The normalization is the displayed equality of
   morphisms: apply Gamma to H^0(B[2])=H^2(B), then invert the cocycle-normalized
   global-to-local edge, then use `c.supportIso 2`. Here `c` is the existing
   `RetractedSupport.Comparison`, whose first comparison is fixed by the
   etale exceptional counit, whose boundary has injective-model snake
   normalization, and whose support comparison commutes with the actual
   supported-section inclusion and boundary. The isomorphism is therefore
   tied to those canonical constructions; it is not a bare `Nonempty` iso.
   Nonemptiness of this existing comparison datum is included, and the
   assertion holds for every such normalized datum, so none is an extra
   hypothesis or an arbitrary chosen natural isomorphism.
7. `gysinOpenCoefficient` specifies the forward map of the coefficient
   isomorphism b. It composes the exact-comparison/single comparison, the
   single comparison for open inverse image, the recorded comparison square,
   and `P.twistEtalePullback h j`. Consequently b cannot be rescaled.
8. `gysinGlobalClass` turns a derived morphism into its cohomology class by
   applying derived global sections to it and evaluating at the actual unit.
   The unit enters via `toRightDerivedZero` and the canonical comparison
   `homologyRightDerivedFunctorObjSingleFunctorIso`, and the result uses the
   standard cohomological shift comparison. `gysinKummerSection` applies this
   construction specifically to `(P.coordinateKummer h Y a).hom`, transports
   along b inverse, and uses the canonical derived open-sections and
   bounded-below comparisons and the specified complement isomorphism.
9. The last equation applies `(δ 1).app` to this actual coordinate class for
   every pro-etale `SupportSequenceBoundary` satisfying `SupportSequenceExact`.
   It produces a morphism m from the actual coefficient unit to `gysinValue`
   and asserts that the support isomorphism sends its evaluated H^0 section
   to precisely that boundary. Thus the coordinate Kummer class, the boundary,
   the supported class, and the derived morphism occur in one equation.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`, `Ring`,
  `Coefficient`, `constantEtale`, `twistEtale`, `constant`, `twist`,
  `derivedSheaf`.
- `Sheaf.Paper.PurityAffineLineDatum`: `Line`, `zeroSection`, `Punctured`,
  `openImmersion`, `lineProjection`, `twistEtalePullback`, `coordinateKummer`.
- Mathlib's `DerivedCategory.homologyFunctor`,
  `singleFunctorCompHomologyFunctorIso`, and `Functor.shiftIso`, from the
  recorded cohomology-sheaf match and shift infrastructure.
- `Sheaf.AlgebraicGeometry.SupportCohomology`:
  `ProEtale.supportHypercohomology`, `supportRestrictionArrow`; these use
  the kernel-derived supported sections, not a newly defined cohomology.
- `Sheaf.Paper.FiniteTorAmplitude`: `WeilConjectures.finiteTorConstructible`.
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`:
  `finiteCoefficientIntrinsicRealization` and its exactness instances.
  The latter is the existing associated-module-sheaf construction owned by
  `def-weil-pbc-proetale-modules`, now cited in `stmt_deps`.
- `Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage`:
  `sfFiniteExceptionalFixed`, the finite fixed-scalar interface reexported
  by the currently recorded exceptional-inverse-image module
  `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`. It is the interface
  used literally by the landed retracted-support comparison.
- `Sheaf.AlgebraicGeometry.SupportLongExact`:
  `Sheaf.SupportSequenceBoundary`, `SupportSequenceExact`,
  `sectionHypercohomologyFunctor`, and the pro-etale part of
  `AlgebraicGeometry.exists_support_longExact`.
- Added landed node `lem-pur-retracted-support-localization-comparison`,
  module `Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison`:
  `Comparison`, `closedTerm`, `nuPlus`, `localClasses`, `hyper`,
  `openSectionsIso`, `sectionPlusIso`, `complementSectionsIso`, and the
  normalized `edge` and `supportIso` fields. Its DAG has no dependency on
  this item, so the new edge is acyclic.
- `Functor.homologyRightDerivedFunctorObjSingleFunctorIso` in upstream
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`;
  `Functor.toRightDerivedZero` and exact open-inverse-image adjunction
  instances supply the derived evaluation formula.

Edge cases checked before finalizing:

- Y empty: the sheaves, supported cohomology, and morphism groups are zero;
  local triviality and all normalized comparison equations still make sense.
- Y disconnected: evaluation at 1 uses the constant-sheaf adjunction, not
  an identification of global constant-sheaf sections with a single copy of A.
- Positive n with ramification: h, not an unstated unramified assumption,
  controls n/e. Positive level already belongs to P.
- q negative, q=0, and q positive: the displayed shift is after the
  exceptional functor, H^0(B[2])=H^2(B), and only q=0 is exempted from vanishing.
- Arbitrary exact support boundary, including its negative: the final
  morphism is allowed to depend on δ, while the comparison e is fixed by
  its canonical normalization. Thus no boundary sign is silently imposed.
- Coefficient sizes: Scheme universe u, module values u+1, and the existing
  small pro-etale object/morphism universes are retained. No universe
  equality or coefficient-size restriction was imposed.

Searches made:

- `msearch.py Q08 lem-pur-gysin-structure leanfinder` with
  `exceptional inverse image zero section affine line supported cohomology Kummer`:
  eight generic affine-local results; none states this result.
- `msearch.py ... loogle` with
  `rightDerivedUpperShriek, affineLineOrientation, supportHypercohomology`:
  no match; the expected name `rightDerivedUpperShriek` was not recognized
  by that Mathlib-only service.
- `msearch.py ... grep` with `gysin|exceptional.?inverse|support.*cohomology`
  in `AlgebraicGeometry`: no exact Mathlib match.
- `rg` in upstream `WeilConjectures` and shared `lean/Sheaf` found the
  existing exceptional, support, finite-Tor, and normalized localization
  interfaces listed above. The old abstract affine-line APIs do not state
  the finite-coefficient actual-coordinate assertion here.
- `grep -rn 'lem-pur-gysin-structure'` in upstream `WeilConjectures`: no match.
- Exact-name searches for `gysinValue`, `gysinGlobalClass`,
  `gysinOpenCoefficient`, `gysinKummerSection`, `gysin_structure`, and
  `GysinSupportIdentification` in upstream, Mathlib, shared `lean/Sheaf`,
  and `dag/lean_names_upstream.json`: no collisions.

Validation uses only the prescribed `scompile.py` and `deliver2.py` wrappers.
The nine-step natural-language proof is included in the theorem docstring.

## Second reading by Q08

This is a separate reading pass by the same dispatcher worker; the brief forbids
starting another agent and assigns independent review to the maintainer.
The item, its current blueprint source, and the final module were compared again
hypothesis by hypothesis and clause by clause as detailed above.

The pass removed an unnecessary proposed statement correction: the DAG already
contains separated finite type. It also rejected the earlier baseline's bare
existence of additive equivalences and its omission of an actual boundary-class
equation. The final file instead gives the normalized isomorphism formula,
the concrete derived-global-section image of `coordinateKummer`, and its equation
under every exact boundary. The local-triviality clause was retained rather than
replaced by a stronger assertion of a globally constant cohomology sheaf. The
finite-Tor condition now uses the recorded intrinsic predicate directly through
the existing canonical realization. No extra finite-type condition, coefficient
condition, orientation, or exceptional-adjoint datum remains as a hypothesis.
