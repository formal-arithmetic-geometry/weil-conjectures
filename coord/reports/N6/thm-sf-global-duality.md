## Worker report

Recorded the existing declaration
`WeilConjectures.GlobalVerdierDuality.global_verdier_duality` in
`Sheaf.Paper.GlobalVerdierDuality`, already attached to
`sk-thm-sf-global-duality`. No Lean module is delivered. The current blueprint's
`thm-sf-global-duality.md` and the enclosing unit's `_section.md` have the same
geometric hypotheses, displayed isomorphism, naturality, coefficient and shift
compatibilities, and constant-coefficient specialization. This node expands the
setting and point-category interpretation of that same assertion.

I read the live source using `scompile.py --source Sheaf.Paper.GlobalVerdierDuality`
and then its refreshed local source, including every definition used by the
theorem. This is the full four-stage theorem, not the older finite-only theorem
in `WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality`.

Hypothesis and clause correspondence:

- The finite-field objects are `D : FiniteFieldDatum.{u}`: its fields record
  p, a, q, primality, positive exponent, cardinality, k0, k and the chosen
  algebraic closure. The section variables `l`, `[Fact l.Prime]`, `hl : l ≠ D.p`,
  `Ω`, its field/algebra instances and `IsAlgClosure` give the coefficient prime
  and algebraic closure. `ConstructibleExceptionalCoefficients.FieldStage`
  contains a finite-dimensional extension E/Q_l. `Stage.finite` uses a positive
  exponent, while `.integral`, `.rational` and `.closed` give exactly the four
  stages. Selecting the fixed E and n in the node selects the corresponding
  components of the package. The integer rings, uniformizers and quotients are
  the dependency's existing Padic coefficient constructions.
- The six-functor datum in the node fixes the actual coefficient constructions
  and normalized operations, rather than arbitrary functors. The existing
  assertion quantifies over the published normalized
  `ConstructibleExceptionalCoefficients.System` for the structure morphism.
  Thus it applies to the specified constructible operations in that datum; it
  imposes no additional axiom or ambient-adjoint hypothesis. Its conclusions
  retain the actual Hom, projection, evaluation and coefficient comparisons.
- `X : Scheme.{u}` with `[X.Over (Spec (.of D.k))]` supplies a_X.
  `Smooth`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, and
  `GeometricallyConnected` are precisely the five geometric conditions. Finite
  type is locally finite type and quasi-compact. `d : ℕ` and
  `_hd : X.IsPureDimension d` express the nonnegative pure dimension.
  The geometric-properties dependency includes connectedness, not an extra
  irreducibility hypothesis.
- `GeometricAlternative` is the disjunction of properness and an existential
  smooth, separated, locally finite-type, quasi-compact, geometrically connected
  X0 over k0 with `Nonempty (X ≅ D.geometricFiber X₀)` in the over category.
  This is base change over k, including the structure map; it does not require
  properness in the descended branch. The displayed base-change equality in
  the informal statement is represented invariantly by that over-isomorphism.
- There is no exceptional-admissibility premise. The universally quantified
  systems use the already specified constructible exceptional adjunction.
  The finite-stage uniform cohomological and Tor bounds are the availability
  assertion of `def-weil-exceptional-inverse-image`/`def-trf-admissibility`;
  the integral, rational and common-stage systems are their specified higher
  coefficient constructions. These context sentences are not new hypotheses
  on X or K. No unbounded ambient exceptional adjoint is assumed.
- `Assertion` supplies `Nonempty (Package ... A c)` for every normalized system
  A and compactification c. `Package.stage` is the existing
  `VerdierExchange.StageData` specialized to the structure map and the literal
  identity operation at the point. Consequently `d.dualY` is RHom(-,Lambda_s),
  and `d.dualX` is RHom(-,Ra_X^! Lambda_s). Its source categories `C l Ω X s`
  are exactly D^b_ctf at ring stages and the full constructible categories at
  field stages, so every K in the node is included.
- `Conclusion.exchange.epsilon` is a natural isomorphism
  `F.F.op ⋙ d.dualY ≅ d.dualX ⋙ d.star`. Its components are fixed to the actual
  projection/evaluation/adjunction transpose by `StageConclusion.components`.
  `Conclusion.dualizing` fixes the dualizing comparison to the identity.
  `RingRealization`, `RingProjection` and the unit-normalization equations
  identify these with the actual ringed-site operations and evaluations.
  This states the canonical arrow, not merely unrelated objectwise isomorphisms.
- This is the point-category form of `(Ra_X! K)^vee ≅ Ra_X* D_X K`.
  The dependency's full point-fibre equivalences turn these two objects into
  the stated coefficient complexes RΓ_c(X,K)^vee and RΓ(X,D_X K), in their
  four different finite/fg/fd/common-stage targets. Transport by their inverse
  is exactly the point-category interpretation specified in the node. No
  integral or field stage is identified with the finite-ring target.
- Naturality in every K and every morphism is part of the natural isomorphism;
  its source is the opposite category, so it is contravariant in K.
- `StageConclusion.shift` is the compatibility equation for that same natural
  transformation with its dual and direct-image shift structures.
  `Package.ringShifts` fixes the signed Hom-complex model, so the dual shift is
  [-r], not a freely chosen shifted object isomorphism.
- `Package.ringScalar` gives `ScalarConclusion.exchange` for every allowed
  finite quotient, integral reduction and integral coefficient change. Its q
  and unit equations identify the maps with the actual system comparisons.
  `.rationalization`, `.rationalScalar` and `.common` give the corresponding
  equations for localization, field scalar extension and common-stage
  inclusion. `ScalarShifts` records their shift compatibility. These are
  commuting squares for the same epsilon; no field-to-finite-ring reduction
  functor is asserted.
- For K=Lambda_X, `Conclusion.unitIso` identifies RHom(Lambda_X,omega_X) with
  omega_X. Its maps are fixed by `evaluation` and `coevaluation` to the
  existing closed evaluation and right-unitor transpose.
  `Conclusion.constant_hom` identifies the specialized isomorphism with the
  same epsilon component followed by `d.star.map unitIso.hom`.

Dependency declarations read (including their signatures and docstrings):

- `def-sf-datum`: `Sheaf.Paper.SixFunctorDatum`, `SixFunctorDatum`, its A1--A6
  fields, `SixFunctorClosedDomain`, `SixFunctorClosedChange` and the operation
  datum's four `Verdier` functors. They fix the finite-Tor domains and actual
  coefficient constructions used in the contextual formulation.
- `def-weil-exceptional-inverse-image`:
  `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`,
  `ConstructibleExceptionalCoefficients.System`, `Stage`, `C`, `Operation`,
  `RingSystem`, `FieldSystem`, `CommonSystem`, and their normalized comparisons.
  These are directly reused by the existing theorem.
- `def-trf-admissibility`: `Sheaf.Paper.TraceExceptionalAdmissibility`,
  `IsExceptionallyAdmissible`, `TrfExceptionalStage`, and `trfExceptional`.
  Positive finite levels are indexed by m+1 and the bounds are independent
  of m. The geometric hypotheses supply their availability, not an extra
  premise of global duality.
- `def-weil-finite-coefficient-point`: `Sheaf.Paper.FiniteCoefficientPoint`,
  `pointFiniteFibre`, `pointIntegralFibre`, `pointRationalFibre`, `pointQbarFibre`.
- `def-sf-pf`: `Sheaf.Paper.SixFunctorDualNotation`,
  `sixFunctorCoefficientDual` and
  `SixFunctorDatum.{finite,integral,rational,commonStage}CoefficientDual`.
  Its definition is internal Hom into the coefficient unit, the same definition
  as `StageData.dualY` for the literal point identity operation. Verdier dual
  is the recorded Hom into exceptional pullback of the unit; the existing
  theorem's ring realizations retain exactly those operations.
- `def-weil-ordinary-compact-cohomology`:
  `Sheaf.Paper.CommonStageCompactWeilCohomology`,
  `commonStageCompactWeilCohomology`, and its public ordinary/compact coefficient
  complex constructions in `OrdinaryCompactWeilCohomology`.
- `def-pc-geometrically-irreducible`: its recorded Mathlib geometric classes,
  in particular `Mathlib.AlgebraicGeometry.Geometrically.Connected`,
  `AlgebraicGeometry.GeometricallyConnected`. The node defines all four
  geometric properties, so its name does not add irreducibility here.
- `def-weil-pure-dimension`: `Sheaf.AlgebraicGeometry.PureDimension`,
  `AlgebraicGeometry.Scheme.IsPureDimension`.
- `lem-weil-point-fibre-equivalence`: `Sheaf.Paper.PointFibreEquivalence`,
  `point_fibre_equivalence`, including its four equivalence, shift and triangle
  clauses. This justifies both formulations of the same displayed isomorphism.

Edge cases checked: X=Spec k, d=0 gives the coefficient-unit identification;
K=0 is allowed at every stage; geometric connectedness excludes the empty scheme
although pure dimension by itself is vacuous there. Nonproper affine space and
G_m descended from k0 are included. Positive exponents include n=1; n=0 is not
claimed. Identity quotient maps and identity scalar embeddings occur among the
allowed comparisons. Nonflat reduction is derived. All integer shifts, including
negative shifts, are included. The algebraically closed category retains common
finite-stage objects and arrows. Original site object/morphism universes are
preserved; no equality between them is imposed.

Searches:

- `msearch.py N6 thm-sf-global-duality leanfinder` with the query recorded in
  searches.jsonl, asking for global Verdier duality naturally and with coefficient
  changes: eight unrelated derived-category/group-cohomology hits, no match.
- `msearch.py ... loogle "coefficientDual, rightDerivedLowerShriek"`: zero hits,
  with unknown identifier coefficientDual.
- `msearch.py ... grep "globalDuality|global_duality|coefficientDual.*LowerShriek"`:
  zero indexed Mathlib hits.
- `rg` and the blueprint-id search in `lean/WeilConjectures` found the upstream
  finite-coefficient GlobalDuality module. Its full docstring explicitly says
  it omits higher coefficient stages and the shift compatibility equation;
  therefore it is not the existing match used here.
- Repeating the source search in the refreshed `lean/Sheaf` found the newly
  published full `GlobalVerdierDuality` module. I read its complete source and
  the node `sk-thm-sf-global-duality`, then read both current blueprint texts.
  The latter is the exact existing statement carried by this expanded node.
  The server `--source` read confirmed the live declaration independently of
  the older checkout. Accordingly the unfinished duplicate draft was removed.

No statement correction, new node, dependency repair, or STATEMENT-DISPUTED flag
is needed. The only node change is its `lean` record.

## Second reading by N6

The dispatcher requires direct worker delivery and forbids spawning another
agent; the maintainer supplies the independent review. In the final worker
rereading I compared the item, both blueprint texts and the full existing module.
The five X conditions, pure dimension and both geometric alternatives agree.
The profile-based draft was discarded: its free Prop compatibility fields would
not have expressed any compatibility, and its extra irreducibility binder was
not in the node. None of that draft is delivered. The published interface instead
has actual canonical-component, coefficient, shift and constant-component
equations on the four coefficient stages. Its fixed point identity makes the
point dual RHom into the coefficient unit; the four fibre equivalences explain
the coefficient-complex rendering. This reading found no remaining missing
clause in the existing declaration used for the binding.

Validation is through the prescribed delivery dry run, including its server
existing-declaration import and `#check` probe; no new module needs compilation.
