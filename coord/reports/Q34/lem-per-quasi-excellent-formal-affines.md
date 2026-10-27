## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiExcellentFormalAffines` states the general
completion theorem as `AlgebraicGeometry.quasiExcellent_formalCompletion` and its
explicit affine specialization as
`AlgebraicGeometry.quasiExcellent_adicCompletion_formalAffines`.
Both proofs are `sorry`; there are no new definitions and no proved lemmas.
The node statement, proof and proof dependencies are unchanged.

Hypothesis and clause correspondence:

- A scheme X is `{X : Scheme.{u}}`. Its finite Noetherian affine cover is expressed
  by `[IsNoetherian X]`: Mathlib's
  `isNoetherian_iff_of_finite_iSup_eq_top` and
  `isNoetherian_iff_of_finite_affine_openCover` identify this with the node's wording.
  This includes local Noetherianity, rather than merely assuming compactness.
- Every affine open of X has quasi-excellent ring is
  `_hX : ∀ V : X.affineOpens, IsQuasiExcellent Γ(X, V)`.
- The ideal subsheaf is `I : X.IdealSheafData`, whose `toModules` is its actual ideal
  module, not an independently supplied module or an arbitrary monomorphism.
  `_hI : RingedSpace.IsCoherent X.toRingedSpace I.toModules` is precisely coherence
  (finite type and finite-type kernels), not only a finite-generation condition.
  IdealSheafData records quasi-coherence, which follows from coherence on this
  Noetherian scheme by the recorded coherence/finite-type equivalence.
- The completed formal ringed space is the existing `adicFormalCompletion I`.
  Its definition is the ringed-space colimit of the closed schemes V(I^n), giving
  underlying space V(I) and inverse-limit structure sheaf. Including n = 0 adds
  only the initial empty closed scheme and does not change this colimit.
  Thus it is the same completion as gluing the completed affine charts.
- The first conclusion is
  `IsNoetherianAdicFormalScheme (adicFormalCompletion I)`: its existing definition
  is a finite open cover by complete Noetherian formal spectra.
- An arbitrary formal affine open is an arbitrary
  `U : Opens (adicFormalCompletion I)`, with `R : CommRingCat.{u}`, `K : Ideal R`,
  `IsNoetherianRing R`, `IsAdicComplete K R`, and the ringed-space isomorphism
  `Nonempty ((adicFormalCompletion I).restrict U.isOpenEmbedding ≅ adicFormalSpec R K)`.
  This renders the node's definition literally and does not require U to lie in
  an original chart, be principal, or be induced by an affine open of X.
  Finite generation of K follows from Noetherianity; it is not an extra hypothesis.
  The result `IsNoetherianRing R ∧ IsQuasiExcellent R` retains both stated clauses.
  The isomorphism's Nonempty wrapper only expresses the existence of an isomorphism
  of two concretely constructed objects; it chooses no unspecified object or map.
- In the affine specialization, `(A : Type u) [CommRing A] [IsNoetherianRing A]`,
  `_hA : IsQuasiExcellent A` and `(I : Ideal A)` are exactly the ring hypotheses.
  `IsQuasiExcellent (AdicCompletion I A)` is the first conclusion. The second
  quantifies over every open of
  `adicFormalSpec (CommRingCat.of (AdicCompletion I A))
    (I.map (algebraMap A (AdicCompletion I A)))`, with precisely the formal-affine
  presentation above, and concludes `IsQuasiExcellent R`.
- There is no characteristic, regular morphism, reducedness, catenarity, dimension,
  nonzero-ring or nonempty-open assumption. All variables and universes are explicit;
  `set_option autoImplicit false` is enabled. The ring of sections of a small open
  has the same universe as the scheme; arbitrary ring presentations up to isomorphism
  are represented in that universe as in the existing formal-geometry interface.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`,
  and the finite-affine-cover characterizations cited above.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`,
  `isNoetherianRing_iff_ideal_fg`.
- `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent`, the conjunction of
  Noetherianity, `IsGRing`, and the open regular locus of every finite type algebra.
  The node also records `IsExcellent`; its additional catenarity clause is not assumed.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`, which publicly imports
  `WeilConjectures.AlgebraicGeometry.Coherent`: `RingedSpace.IsCoherent` is the
  exact recorded coherence predicate; its source and docstring were read.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`: the canonical
  ideal module `Scheme.IdealSheafData.toModules`.
- `Mathlib.RingTheory.AdicCompletion.Basic` / `.Algebra`: `AdicCompletion I A`,
  its commutative-ring and algebra structures, and `IsAdicComplete K R`.
- `Sheaf.AlgebraicGeometry.AdicFormalGeometry`: `adicFormalCompletion`,
  `adicFormalSpec`, `IsAdicFormalAffineOpen`, and `IsNoetherianAdicFormalScheme`.
  The already-landed owning node `def-per-adic-formal-geometry` is added to
  `stmt_deps`; the existing notions are not redefined. The arbitrary-ring presentation
  in the statement spells out the node's Spf R wording instead of fixing R to the
  literal section object in `IsAdicFormalAffineOpen`.

All currently stated proof dependencies are imported non-publicly:
`WeilConjectures.RingTheory.AdicCompletionNoetherian` (`AdicCompletion.isNoetherianRing`),
`Mathlib.RingTheory.AdicCompletion.LocalRing` (`AdicCompletion.isAdicComplete_self`,
with the evaluation/quotient lemmas from Algebra and Completeness),
`Mathlib.RingTheory.Noetherian.Basic` (`isNoetherianRing_of_surjective`),
`WeilConjectures.RingTheory.FiniteTypeGRing` (`isGRing_of_finiteType`),
`Sheaf.AlgebraicGeometry.GRingAffineCover` (`isGRing_of_affine_open_cover`),
`Sheaf.AlgebraicGeometry.JTwoAffineCover` (`j2_of_affine_open_cover`), and
`WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
(`Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType`).
The regular-ring and G-ring definitions are supplied by the statement imports.
The two new stage-1 proof nodes `lem-per-formal-completion-reduction-dictionary`
and `lem-per-gabber-adic-quasi-excellence` have no recorded Lean declaration yet;
no import is invented. Their mathematical statements are fully recorded in the
proof docstrings. Neither is needed to type the statement.

Source check: opened Temkin's cited PDF, sections 2.4.1 and 2.4.3 and Theorem 2.1.8.
Section 2.4.3 explicitly says quasi-excellence is preserved by formal completion;
Theorem 2.1.8 removes the rational-algebra restriction of Theorem 2.1.6.
The node already supplies the later published Gabber reference (ILO Expose I 9.2).
No source-driven correction was needed and there is no STATEMENT-DISPUTED flag.

Edge cases checked before writing:

- Empty X and the zero ring are allowed; the finite formal cover may have n = 0.
- I = the unit ideal gives the empty completion and zero completed ring. An empty
  formal affine presentation with a complete unit ideal forces the zero ring.
- I = 0 gives the ordinary scheme or ring; nilpotent I gives the stationary tower.
- Positive and mixed characteristic (F_p[[t]] and Z_p) are included, using Gabber
  rather than the rational-algebra-only complete-pair theorem.
- Formal affine opens crossing several original charts are covered by the universal
  U,R,K quantifier and by Step 4 of the proof plan; no affine-intersection assumption.

Searches made with the prescribed msearch wrapper:

- leanfinder, `Every formal affine open in the adic completion of a quasi excellent
  Noetherian scheme has a quasi excellent ring`: eight ordinary scheme/affine/
  Noetherian results, no theorem matching this item.
- loogle, `AdicCompletion, IsNoetherianRing`: twelve results on exactness, flatness,
  tensor descriptions and local rings of completions, none giving quasi-excellence.
- grep, `FormalScheme|FormalSpectrum|Spf|QuasiExcellent`: only unrelated cusp-form
  matches (the substring Spf); no match for this statement.
- Refined grep in RingTheory, `QuasiExcellent|FormalScheme|FormalSpectrum|formalSpectrum`:
  zero Mathlib matches.
- rg in `lean/WeilConjectures` and `lean/Sheaf`: found the already-landed
  AdicFormalGeometry/AdicFormalCompletion constructions and the excellent-ring
  definition, but no statement of this item. The exact blueprint-id grep in
  WeilConjectures returned no match. The complete-pair theorem in
  `Sheaf.RingTheory.QuasiExcellentCompletePair` assumes a rational algebra, so it
  does not cover this arbitrary-characteristic theorem.
- DAG search found `def-per-adic-formal-geometry` already owns all formal notions;
  `tools/blueprint_refs.py search 'formal affine'` returned no blueprint node match.
  No new notion/node or dependency repair is required.

Validation: scompile.py compiled the sandbox and final module on the server
successfully (5.1 s and 2.3 s), with no errors or unexpected warnings.

## Second reading by Q34

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
