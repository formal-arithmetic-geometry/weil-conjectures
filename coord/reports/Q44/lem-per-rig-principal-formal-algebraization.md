## Worker report

The module `Sheaf.AlgebraicGeometry.RigPrincipalFormalAlgebraization` states
`AlgebraicGeometry.rigPrincipalFormalAlgebraization`, with one `sorry` and no new
definitions. The node's statement, proof, and proof dependencies are unchanged.
The statement dependencies gain the two already landed definition nodes
`def-per-formal-completion-geometry` and
`def-per-supported-centered-blowup-towers`, whose actual notions the signature uses.
There are no new nodes and no dependency repairs.

Source read: Temkin, Non_Embedded_Desingularization.pdf, arXiv:0904.1592v2,
§§2.4.4–2.4.11, §§3.1.1–3.1.4, and §3.4.1 first sentence (printed pp.15–18,25),
at the URL in the node. In particular Remark 3.1.4(iii) gives the principal affine
algebraization, §3.4.1 gives an Elkik pair, and §2.4.6 states compatibility of
completion and blowups. The current blueprint ancestor is
`lem-per-artin-gabber-affine-curve`; this item is an auxiliary sourced lemma, not
the statement of that blueprint unit.

Hypothesis and clause correspondence:

- The operative hypothesis is a principal **affine** pair. It is represented by
  its coordinate ring `B : CommRingCat.{u}`, with `[IsNoetherianRing B]` and
  `[IsAdicComplete (Ideal.span {pi}) B]`. Thus the ideal is finitely generated,
  the ring is complete and separated, and its formal spectrum has the required
  inverse-limit sheaf. The opening description of arbitrary finite covers is
  contextual: no arbitrary formal scheme is silently assumed affine. These are
  the complete-ring coordinates of the source's principal affine hypothesis.
- Reducedness is `[_root_.IsReduced B]`. Quasi-excellence is
  `hQE : _root_.IsQuasiExcellent B`. For an affine quasi-excellent formal scheme,
  the conditions on this complete chart are the chartwise conditions: formal
  localizations preserve quasi-excellence and reducedness. We do not use the
  reduced infinitesimal quotients as a substitute for reduced complete rings.
- The distinguished ideal is `Ideal.span {pi}` and its generator is a
  non-zero-divisor by `hpi : pi ∈ nonZeroDivisors B`. This is the principal
  invertible ideal of definition; no properness or nonemptiness assumption is
  imposed. The general locally principal terminology in the preamble explains
  this specialization and is not a separate theorem about nonaffine objects.
- `hvar` existentially quantifies a field `k`, a `CharZero k` instance, and a
  ring map into `B ⧸ (Ideal.span {pi}).radical` satisfying `f.FiniteType`.
  This is exactly the reduced closed fibre being finite type over some
  characteristic-zero field. It fixes no coefficient lift to B.
- `absoluteSingularIdeal B` is the existing radical vanishing ideal of the
  nonregular prime locus. `hrig` requires a positive power of the distinguished
  ideal to lie in that ideal, exactly rig-regularity. It uses absolute regular
  local rings, not smoothness over a chosen field.
- The conclusion existentially quantifies a characteristic-zero field, a
  commutative ring `A`, its structure homomorphism `f`, and an element `a`.
  `f.FiniteType`, `_root_.IsReduced A`, and `a ∈ nonZeroDivisors A` are,
  respectively, finite type, reducedness, and the principal Cartier condition.
  Fields and rings are allowed to vary with the input. The input field in hvar
  is not identified with the output field.
- `∀ p : PrimeSpectrum A, ¬ IsRegularLocalRing (Localization.AtPrime p.asIdeal)
  → a ∈ p.asIdeal` is exactly `X_sing ⊆ V(a)` for `X = Spec A`. No relative
  nonsmoothness locus replaces this absolute singular locus. Together with the
  preceding output conditions this is the node's Elkik pair.
- `e : AdicCompletion (Ideal.span {a}) A ≃+* B`, together with equality of the
  image of `(a)` under the completion map followed by `e` with `(pi)`, is the
  complete-affine-coordinate expression of the isomorphism of formal pairs.
  On complete affine adic rings this is precisely the formal pair isomorphism:
  it identifies all quotient rings and their transition maps, hence their formal
  spectra with their inverse-limit sheaves and distinguished ideals. Equality
  of ideals, rather than equality of radicals, is required. No chosen generators
  or coefficient-field action must be preserved. The theorem does not merely
  assert an abstract isomorphism of the underlying rings or formal spaces.
- For every length `r` and every `AdicFormal.OrdinaryTower` of `Spec A`
  supported on its principal ideal, the conclusion provides a `FormalTower`
  and an actual `Completion T F` with `c.CentersAgree`. These are the previously
  landed notions, not a new tower encoding. `Completion.centers` identifies every
  ideal at every infinitesimal order; its `arrows` and `over` equations preserve
  the order and maps. `CentersAgree` identifies the same actual center schemes.
  Via the fixed ideal-preserving ring isomorphism e, the base completion is the
  original formal pair. The tower is expressed over that identified completion;
  it is not asserted over an unrelated formal model. No stages are deleted.
- The node's paragraph defining regular morphisms of pairs supplies terminology
  for its surrounding results. This theorem quantifies no such morphism and
  adds no morphism hypothesis or functoriality conclusion. Its constituent
  regular ring-map notion is the recorded `RingHom.IsRegular`, publicly imported.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, and its imported
  `AlgebraicGeometry.QuasiCompact`. On the affine reduced closed fibre the exact
  equivalent expression is `RingHom.FiniteType`; no new finite-type notion.
- `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent` (with `IsExcellent` read
  as the other clause of that node).
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`;
  the ring clause of the same dependency is Mathlib's `IsRegularLocalRing` and
  `IsRegularRing`, read in RegularLocalRing/Defs.lean.
- `WeilConjectures.RingTheory.GRing`: `RingHom.IsRegular`,
  `Algebra.IsGeometricallyRegular`, and `IsGRing`.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType` and `Algebra.FiniteType`.
- `Mathlib.RingTheory.AdicCompletion.Basic` and its Algebra interface:
  `AdicCompletion`, `IsAdicComplete`, and the canonical algebraMap.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`, with public upstream coherence:
  `AlgebraicGeometry.RingedSpace.IsCoherent`, `SheafOfModules.IsQuasicoherent`,
  `SheafOfModules.IsFiniteType`, used by the existing tower interfaces.
- `Sheaf.AlgebraicGeometry.FormalCompletionGeometry`:
  `AlgebraicGeometry.absoluteSingularIdeal`; its docstring and full formula were
  read, as were the existing formal-spectrum and completion constructions.
- `Sheaf.AlgebraicGeometry.SupportedCenteredBlowupTowers`:
  `AdicFormal.OrdinaryTower`, `FormalTower`, `Completion`, and
  `Completion.CentersAgree`; `AdicFormal.affineIdeal` is its public imported
  canonical ideal on Spec A. Their full fields were read, including the
  infinitesimal-center equations and the specified length index.

The stated proof dependencies are imported as private proof imports:
`FieldsExcellent`, `IsExcellentFiniteTypeLocalization`, and
`SupportedFormalBlowupAlgebraization`; their full declarations and proof docstrings
were read. The four other proof lemmas currently have no Lean records or Mathlib
matches, so they have no module to import yet. They are not needed to type this
statement; the proof docstring retains each one and all five accepted proof steps.

Edge cases checked before writing:

- `B = 0` and the empty formal spectrum are permitted. Its generator can be zero
  and still belong to `nonZeroDivisors B` because multiplication is injective on
  the zero ring. A zero output algebra over a characteristic-zero field is
  allowed; no `Nontrivial A` or injectivity of its structure map is added.
- If pi is a unit, adic separatedness forces B to be zero. This is included.
  If pi is zero, the non-zero-divisor hypothesis likewise forces B to be zero.
  A nilpotent non-zero-divisor also only occurs in that case. In a nonzero ring
  these exclusions follow from the source's hypotheses, not extra binders.
- For `r = 0`, the signature still returns the formal base comparison; the center
  conditions quantify over `Fin 0`. Unit centers (empty centers) and zero centers
  permitted by the existing supported tower structure are retained. There is no
  regularity, nonemptiness, or nowhere-density condition on centers.
- All rings and the existential fields are in `Type u`, with arbitrary explicit
  universe u. An affine pair of any size is covered. A field acting on a nonzero
  reduced quotient embeds in that quotient, so can be represented in this
  universe; for the zero quotient a lift of Q suffices. There are no test algebras
  in an independent smaller universe and no auto-bound implicits.

Searches actually run:

- `msearch.py`, leanfinder: "Elkik algebraization reduced rig regular principal
  affine formal variety completion finite type algebra". Eight hits, including
  smooth algebra descent, affine reducedness, and finite-type scheme morphisms;
  none asserts this algebraization or its tower clause.
- `msearch.py`, loogle: "AdicCompletion, IsAdicComplete". Twelve hits supply the
  existing completion equivalences and their properties, not this theorem.
- `msearch.py`, grep: "FormalScheme|formalBlowup|Spf|Elkik" in Mathlib
  AlgebraicGeometry. Zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `FormalScheme|formalScheme|formalBlowup|FormalBlowup|Spf|Elkik|RigRegular|rigRegular|Supported.*Tower`:
  found the existing formal geometry, formal completion geometry, and supported
  tower modules used here. No principal rig-regular algebraization theorem.
- `rg` in the upstream source for the exact item id: no hits.
- DAG searches for "Elkik pair" and "principal.*formal variet" found this item,
  the coefficient-presentation lemma, and downstream resolution lemmas; none
  already states the whole claim. `tools/blueprint_refs.py search 'principal formal'`
  returned zero blueprint matches. Searched the current blueprint ancestor path.
- Further source search for `Principal.*Formal|Formal.*Principal|ElkikPair|IsRegularPrincipal|IsLocallyPrincipal`
  found the existing ordinary invertible-ideal/regular-principal predicates and
  formal completion geometry, not a duplicate of this theorem.

No statement correction or statement dispute was needed. The affine complete-ring
presentation is an exact coordinate rendering of the node's principal affine claim.

Validation: the prescribed server single-file compilation succeeds in both sandbox
and library module modes with no errors or unexpected warnings. All variables and
universes are explicit (`set_option autoImplicit false`).

## Second reading by Q44

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
