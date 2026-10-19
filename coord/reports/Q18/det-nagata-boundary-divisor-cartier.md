## Worker report

The delivered module is
`lean/Sheaf/AlgebraicGeometry/NagataBoundaryDivisorCartier.lean`. It states
`AlgebraicGeometry.exists_admissibleBlowup_cartierBoundary_of_coe_support_eq_compl_with_density`
for a scheme `T : Scheme.{u}`, instances `CompactSpace T` and
`QuasiSeparatedSpace T`, a quasi-compact open `U : T.Opens`, and an ideal
`I : T.IdealSheafData` with `I.ofFiniteType` and
`(I.support : Set T) = (U : Set T)ᶜ`. The proof is intentionally `sorry`; the
statement has no additional hypotheses.

The existential witness `B : IsAdmissible T U` is accompanied by the equality
`B.I = I`, so its blow-up is the specified `Bl_I(T)`. The conjunction renders
all clauses of the item as follows.

* (a) `B : IsAdmissible T U` is the `U`-admissible blow-up datum.
* (b) `B.I = I` identifies the center of that datum with the given ideal,
  hence `B.I.blowup` and `B.I.blowupMap` are the specified `T'` and `b`.
* (c) `IsSchemeTheoreticallyDominant (B.I.blowupMap ⁻¹ᵁ U).ι` says that
  `b⁻¹(U)` is scheme-theoretically dense in `T'`.
* (d) `(I.comap B.I.blowupMap).IsInvertible` says that the extended ideal
  `I O_{T'}` is invertible (the effective Cartier ideal clause).
* (e) `(I.comap B.I.blowupMap).support =
  ((B.I.blowupMap ⁻¹ᵁ U : B.I.blowup.Opens) : Set B.I.blowup)ᶜ` gives exactly
  `|E| = T' \ b⁻¹(U)`.
* (f) For every
  `C : IsAdmissible B.I.blowup (B.I.blowupMap ⁻¹ᵁ U)`, the term
  `((I.comap B.I.blowupMap).comap C.I.blowupMap).IsInvertible` is the
  pulled-back ideal on `T''` and gives the persistence Cartier clause.
* (g) For the same `C`, the next conjunct identifies its support with
  `(((C.I.blowupMap ≫ B.I.blowupMap) ⁻¹ᵁ U : C.I.blowup.Opens) :
  Set C.I.blowup)ᶜ`, and the final conjunct
  `IsSchemeTheoreticallyDominant ((C.I.blowupMap ≫ B.I.blowupMap) ⁻¹ᵁ U).ι`
  gives persistence of scheme-theoretic density for `(bc)⁻¹(U)`.

The source proof is recorded in the declaration docstring in its four source
steps: (1) the support equality makes `I` the unit ideal on `U`, giving
admissibility; (2) blow-up principalization gives invertibility and the
support computation gives the boundary; (3) the complement of an invertible
ideal is scheme-theoretically dense; and (4) Cartier total transform, support
pullback, and the same density result give persistence under every further
admissible blow-up. The module uses the dependency APIs exactly as recorded:

* `WeilConjectures.Blowup.AdmissibleBlowup`,
  `AlgebraicGeometry.IsAdmissible`;
* `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`,
  `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible`;
* `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`,
  `AlgebraicGeometry.Scheme.IdealSheafData.comap`;
* `Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`,
  `AlgebraicGeometry.IsSchemeTheoreticallyDominant`;
* proof-route modules `WeilConjectures.Blowup.Principalization`,
  `WeilConjectures.Blowup.BlowupUniversal`,
  `Sheaf.AlgebraicGeometry.CartierDivisorNowhereDense`, and
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic` for the
  recorded proof dependencies.

I checked the edge cases named by the statement: `U = ⊤` (then the support
hypothesis forces the unit ideal), `U = ⊥` (the whole scheme is the boundary),
empty schemes, non-reduced schemes such as dual numbers, and disconnected
schemes. The formulation quantifies over `Scheme.{u}` with the same universe
for all schemes and does not impose reducedness, Noetherianity, or density of
`U` in `T`. A further blow-up is quantified over the actual inverse-image open,
and the composite morphism is written explicitly rather than hidden in a
`let` binder.

The recorded stage-1 searches were preserved byte-for-byte in the node's
`mathlib_searches`: grep for blow-up/Cartier support, LeanSearch for
finite-type blow-up principalization and dense complements, Loogle for
`Scheme`/`Blowup`/`IdealSheafData.IsInvertible`, and LeanFinder for the exact
boundary-divisor and persistence statements. They found no exact Mathlib or
upstream declaration. I additionally checked the source repository for
`exists_admissibleBlowup_cartierBoundary_of_coe_support_eq_compl`; it gives
admissibility, invertibility, and support only, so it does not state the
required density or persistence clauses and is not an existing match.

The item node was copied unchanged from the returned stage-1 head except for
its new `lean` record. `existing` is `false`; no new DAG node and no statement
correction were needed.

## Second reading by Q18

I reread the complete Lean module and matched every binder and conjunction
against the blueprint statement and proof paragraphs. The only assumptions
are `[CompactSpace T]`, `[QuasiSeparatedSpace T]`, `IsCompact U`,
`I.ofFiniteType`, and the support-complement equality. The center equality
`B.I = I` prevents the existential admissible datum from silently changing the
specified ideal. The first support expression uses `I.comap B.I.blowupMap`,
and the persistence expression uses its further comap along
`C.I.blowupMap`; the composite map is in the correct order
`C.I.blowupMap ≫ B.I.blowupMap`. Both support complements are explicitly
coerced to sets on the corresponding blow-up schemes, and both density clauses
use the inclusion of the displayed inverse-image opens. No local notation,
private declaration, auto-bound variable, hidden `let`, or extra hypothesis is
present. The file compiled cleanly with the required `scompile.py` wrapper.
