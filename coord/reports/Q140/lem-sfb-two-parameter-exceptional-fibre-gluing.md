## Worker report

Module: `Sheaf.AlgebraicGeometry.TwoParameterExceptionalFibreGluing`.
Main declaration: `AlgebraicGeometry.twoParameterExceptionalFibreGluing`.
The theorem is stated with `sorry`; no mathematical theorem is proved in this delivery.
The twelve auxiliary declarations are concrete names for the constructions in this
node, and are listed in `lean.declarations`. No additional notion, node, dependency
repair, or statement correction is needed.

Source read: `literature/stacks-project/resolve.tex`, Tag 0AGQ, lemma-blowup and its
proof, including the identification E=X_k; `more-algebra.tex`, Tag 0BIQ,
lemma-blowup-regular-sequence and its proof. The former is the regular-local-surface
application. The DAG explicitly abstracts the chart argument to two ordered regular
sequences; the latter supplies its polynomial presentations without a local-ring
hypothesis. The statement here retains that abstraction and every clause of the node.
The current node has no Lean attachment or repair note. The existing
`LocalSurfaceMaximalBlowupGeometry` theorem requires a regular local ring of dimension
two and does not give the chart/overlap statement; it is not an exact reuse candidate.

Hypothesis and clause correspondence:

- Commutative Noetherian A: `{A : Type u} [CommRing A] [IsNoetherianRing A]`.
- The two elements are `(x y : A)`; the ordered sequences are independently
  `hxy : RingTheory.Sequence.IsRegular A [x,y]` and
  `hyx : RingTheory.Sequence.IsRegular A [y,x]`. Neither order is silently inferred.
- I=(x,y): `twoParameterIdeal x y := Ideal.span {x,y}`. The literal k=A/I is
  `TwoParameterQuotient x y`. The field hypothesis is
  `[(twoParameterIdeal x y).IsMaximal]`, equivalent to this nonzero commutative
  quotient being a field. This uses the canonical quotient field structure; it does
  not supply an unrelated `Field` structure on the underlying quotient type.
- Y is the recorded GLOBAL blowup: `twoParameterCenter` is the kernel ideal sheaf
  of `Spec (A/I) → Spec A`, and `.blowup` and `.blowupMap` are the recorded upstream
  constructions. The witness `b` identifies its canonical affine model
  `AffineBlowup I` with this global blowup, over Spec A. This is the usual
  identification implicit in the node's use of Rees-Proj charts on a global blowup.
- E is exactly `twoParameterExceptional`, the categorical pullback of that global
  `.blowupMap` and `Spec.map (Ideal.Quotient.mk I)`. Its projections are
  `twoParameterExceptionalι` and `twoParameterExceptionalBase`. No reduction or
  set-theoretic fibre substitutes for this scheme-theoretic fibre.
- The two indices are `0` for x and `1` for y. `twoParameterRees` is xT or yT.
  `TwoParameterChartRing` is the recorded degree-zero homogeneous localization.
  `twoParameterChart` is the recorded `AffineBlowup.chart`. `twoParameterRatio`
  is the actual `HomogeneousLocalization.Away.mk` fraction yT/xT or xT/yT,
  with denominator exponent one and degree-one numerator.
- The chart maps `a i : Spec k[t] → E` are open immersions. Their `Set.range`
  is precisely the inverse image of the corresponding Rees basic open under the
  projection E→Y (transported by b). The explicit union of their ranges is all E.
  An open immersion with that range is the claimed isomorphism to E∩U_i.
- Canonical affine descriptions, including coordinates: the ring maps `r i`
  reduce the Rees chart to k[t]. They send every coefficient z to C(z mod I)
  and `twoParameterRatio` to `Polynomial.X`. The equation for
  `a i ≫ twoParameterExceptionalι` makes these exactly the displayed chart
  maps on the blowup. Their composites to Spec k are `Spec.map Polynomial.C`,
  so the descriptions are over the prescribed quotient field.
- The overlap is D(t) on the first chart and D(u) on the second: the two
  preimage equalities have right side `PrimeSpectrum.basicOpen Polynomial.X`.
  The scheme overlap itself is `pullback (a 0) (a 1)`, with an isomorphism
  `d : Spec (LaurentPolynomial k) ≅ pullback (a 0) (a 1)`. Its first and second
  projections are Spec of the coefficient-fixing maps t↦T and u↦T^(-1),
  respectively. Thus this is a scheme-theoretic reciprocal-coordinate overlap,
  not merely an assertion about point sets or an unspecified isomorphic scheme.
- P is the recorded `ProjectiveLine (Spec k)`, i.e. the existing base-change
  `ProjectiveSpace (ULift (Fin 2)) (Spec k)`. `twoParameterProjectiveOpen`
  is `ProjectiveSpace.standardOpen` for T_0 or T_1. The ratio section
  `twoParameterProjectiveRatio` uses the published `standardOpenIso` and its
  affine coordinate; by that canonical chart's construction/documentation it
  is T_1/T_0 or T_0/T_1, not an arbitrary affine coordinate.
- The isomorphisms `c i : Spec k[t] ≅ P_i` preserve the base morphism and
  pull back the displayed ratio section to the canonical global section X
  (`Scheme.ΓSpecIso ... .inv Polynomial.X`). This is the prescribed polynomial
  identification t↦T_1/T_0, u↦T_0/T_1, expressed contravariantly on sections.
- The global isomorphism is `e : E ≅ ProjectiveLine (Spec k)`.
  `a i ≫ e.hom = (c i).hom ≫ P_i.ι` says the two chart maps glue to e.hom;
  `(c i).inv ≫ a i = P_i.ι ≫ e.inv` says the inverse chart maps glue to e.inv.
  Since e is an actual `Iso`, both composites are identities. These equations
  also give equality of the two maps and their inverses on the overlap, and
  transport the reciprocal-coordinate overlap to the projective-line charts.
  The final equation `e.hom ≫ (P ↘ Spec k) = twoParameterExceptionalBase x y`
  makes this a k-scheme isomorphism (and implies the inverse is over k).
- Every point p of either polynomial spectrum has a ring isomorphism
  from the stalk of E at `a i p` to `Localization.AtPrime p.asIdeal`, and that
  stalk is `IsRegularLocalRing`. The covering includes every point of E.
  The final `IsRegularScheme E` is the recorded locally-Noetherian AND
  stalkwise-regular predicate, not just regularity of individual stalks.

Dependency interfaces used, with their source declarations and docstrings read:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.Regular.RegularSequence`: `RingTheory.Sequence.IsRegular`
  (weak regularity plus nonzero final quotient).
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `blowupMap`.
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme` and `.Basic`:
  `Proj`, `Proj.basicOpen`, `Proj.awayι`, and the homogeneous chart interface.
- `WeilConjectures.Blowup.Affine.Defs`: `AffineBlowup`, `AffineBlowup.toSpec`,
  `AffineBlowup.chart`, `AffineBlowup.awayAlgebraMap`; `.ReesGrading` provides
  `reesGrading`, `reesX`, `reesX_mem`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; schemes supply the pullbacks.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`, and `Scheme.ΓSpecIso`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `ProjectiveSpace`,
  `ProjectiveLine`, and its canonical structure morphism to the base.
  `.OfSections` gives `ProjectiveSpace.standardOpen`; `.Charts` gives
  `ProjectiveSpace.standardOpenIso`, with its prescribed ratio coordinate.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`, defined using
  `IsLocallyNoetherian` and the existing `IsRegular` stalk condition.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.
- `Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`:
  `HomogeneousLocalization.Away`, `Away.mk`.
- `Mathlib.Algebra.Polynomial.Laurent`: `LaurentPolynomial`, `.C`, `.T`.

The proof-only imports retain the stated proof plan: Pullbacks (open pullback and
`pullbackSpecIso`), ProjectiveSpectrum.Basic (intersection of standard opens),
AffineScheme (affine basic opens and stalk localization), Gluing (morphism gluing),
RegularLocalRing.Polynomial (`Polynomial.isRegularRing_of_isRegularRing`), and
`Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts`
(`ProjectiveSpace.projectiveSpace_standardCharts`). The atlas proof dependency
`lem-sfb-two-parameter-blowup-atlas` currently has no recorded Lean module, so no
nonexistent atlas import is introduced; its role is retained in the proof docstring.
All statement dependencies use the recorded declarations or their recorded
Mathlib matches; none requires a private replacement.

Edge cases checked:

- A need not be local, regular, integral, excellent, or a domain. No such condition
  appears. Both ordered regular sequences remain explicit hypotheses.
- The zero quotient and the unit ideal are excluded precisely by the field hypothesis
  (maximality), as in the node. The zero ring A and a unit among x,y cannot satisfy it.
- No algebraic closedness, perfection, characteristic, rationality of points, or residue
  degree assumption is imposed on k. Non-rational closed points and the zero prime of
  k[t] are included in `∀ p : PrimeSpectrum ...`.
- Universes: A is any `Type u`; the quotient, polynomial and Laurent rings and schemes
  all use u. The projective homogeneous index set is `ULift.{u} (Fin 2)`, retaining
  the published projective-space interface without setting u=0.
- Scheme-theoretic fibres are pullbacks even for a nonreduced ambient A. Their chart
  description is an actual open immersion of polynomial spectra, not reduced points.
- The overlap contains all primes avoiding the chart variable, including its generic
  point; reciprocal-coordinate projection maps fix every coefficient of k.
- The theorem uses no let/show binder, auto-bound implicit, local notation, local
  instance, noncanonical choice of map, or hollow data.

Searches for an exact existing statement (2026-10-24):

- `msearch.py ... leanfinder "The exceptional fibre of the blowup of a two generator
  regular sequence ideal is the projective line with affine charts glued by reciprocal
  coordinates"`: 8 hits, including `Proj.pullbackAwayιIso`, `Proj`, `projIsoSpec`,
  `Proj.awayι`, and `Proj.fromOfGlobalSections`. These are general Proj ingredients;
  none states the blowup exceptional-fibre calculation and projective-line gluing.
- `msearch.py ... loogle "AlgebraicGeometry.AffineBlowup,
  AlgebraicGeometry.ProjectiveLine"`: 0 hits, unknown AffineBlowup in Mathlib;
  these are project-specific notions and were read from their upstream source.
- `msearch.py ... grep "exceptional.*(fibre|fiber)|blowup.*(fibre|fiber)"
  AlgebraicGeometry`: 0 Mathlib hits.
- `rg` for `twoParameter|two_parameter|exceptional[Ff]|exceptional_f|fibre_gluing`
  in `lean/WeilConjectures` and `lean/Sheaf`: unrelated translation actions,
  exceptional functors, and curve fibres; no exact theorem. Searches for the item id
  in `lean/WeilConjectures` and `dag/lean_names_upstream.json` found no attachment.
- Read the related existing modules `LocalSurfaceMaximalBlowupGeometry`,
  `BlowupChartRegularSequencePresentation`, `ProjectiveSpaceStandardCharts`, and
  the upstream blowup and projective-space definitions. The first concerns only
  regular local surfaces; the second only chart presentations; the third only
  projective-space charts. None supplies this complete statement.
- Checked all new full declaration names against `lean/WeilConjectures`, `lean/Sheaf`
  and `dag/lean_names_upstream.json`; no conflicts. The auxiliary names specialize
  existing canonical constructions and do not duplicate an independent notion.

Validation: prescribed `scompile.py`, one delivered file separately, 60 seconds.
Initial elaboration issues were fixed (parentheses around a family of scheme homs,
explicit degree in a homogeneous fraction, and canonical quotient field hypothesis).
One compile encountered server-side resource exhaustion, no space left on device;
its retry's fallback confirmation against current server sources returned exit 0.
The prescribed deliver2.py --no-push dry run passed preflight and compiled the
module (validated dry-run commit bae50935c62).

No statement fault or dispute was found.

## Second reading by Q140

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
