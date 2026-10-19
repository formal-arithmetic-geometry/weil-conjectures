## Worker report

The module `Sheaf.SecTraceFormula.FppfLocalQfRefinement` states
`AlgebraicGeometry.exists_fppf_localQf_refinement`. It formalizes Tag 0572: for a scheme `S`,
a small family `Sᵢ i ⟶ S` that is flat, locally of finite presentation, and jointly surjective,
there is a small family `g j : T j ⟶ S` that is flat, locally of finite presentation, and locally
quasi-finite, together with an index map `ι` and factor maps `h j : T j ⟶ Sᵢ (ι j)`.

The Lean rendering of each hypothesis is:

* The base scheme is `(S : Scheme.{u})`.
* The original small index family is `(I : Type u)`, `(Sᵢ : I → Scheme.{u})`, and
  `(f : ∀ i : I, Sᵢ i ⟶ S)`.
* Flatness is `(hf : ∀ i : I, Flat (f i))`.
* Local finite presentation is `(hfp : ∀ i : I, LocallyOfFinitePresentation (f i))`.
* Joint surjectivity is `(hcover : ∀ s : S, ∃ i : I, ∃ x : Sᵢ i, f i x = s)`.

The Lean rendering of each conclusion clause is:

* The refined family is `(J : Type u)`, `(T : J → Scheme.{u})`, and
  `(g : ∀ j : J, T j ⟶ S)`.
* Its flatness is `(hflat : ∀ j : J, Flat (g j))`.
* Its local finite presentation is
  `(hfp' : ∀ j : J, LocallyOfFinitePresentation (g j))`.
* Its local quasi-finiteness is
  `(hqf : ∀ j : J, Scheme.Hom.IsLocallyQuasiFinite (g j))`.
* Refinement through an original member is given by
  `(ι : J → I)` and `(h : ∀ j : J, T j ⟶ Sᵢ (ι j))`.
* Factorization is `(∀ j : J, h j ≫ f (ι j) = g j)`.
* Joint surjectivity of the refinement is
  `(∀ s : S, ∃ j : J, ∃ x : T j, g j x = s)`.

All index types use `Type u`, matching the scheme universe and the size convention; no
nonemptiness assumption is imposed, so empty schemes and empty families are allowed. The
empty-index edge case is compatible with the joint-surjectivity hypothesis because that
hypothesis then forces `S` to have no points.

Dependencies used:

* `def-pc-scheme`: `AlgebraicGeometry.Scheme` from `Mathlib.AlgebraicGeometry.Scheme`.
* `def-pc-fppf-site`: the Mathlib fppf precoverage/topology declarations
  `AlgebraicGeometry.Scheme.fppfPrecoverage` and `AlgebraicGeometry.Scheme.fppfTopology`; the
  statement uses their explicit family characterization.
* `def-weil-flat-morphism`: `AlgebraicGeometry.Flat` from
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`.
* `def-sbc-locally-finite-presentation`: `AlgebraicGeometry.LocallyOfFinitePresentation` from
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
* `pqf-def-quasifinite`: `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite` from
  `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`.
* `def-weil-size-convention`: represented by the explicit universe `u` and `Type u` binders.
* `lem-trf-fppf-local-qf-neighbourhood`: proof dependency from Tag 0571/0572; its statement is
  imported conceptually and the present theorem is left with `sorry` as required at stage 2.

Searches made: `msearch.py ... leanfinder` for an fppf refinement theorem (generic cover and
locally quasi-finite declarations only; no refinement theorem); `msearch.py ... loogle`
for `AlgebraicGeometry.LocallyQuasiFinite, AlgebraicGeometry.Flat` (0 hits);
`msearch.py ... grep` for `qf.*fp.*flat.*fppf|locally.*quasi.*finite.*fppf` in Mathlib
AlgebraicGeometry (0 hits); `msearch.py ... leanfinder` for the same refinement statement
(no match); and `rg` over `WeilConjectures/` and project `lean/Sheaf` (no existing theorem with
this statement). Thus no existing declaration was found.

The theorem proof is intentionally `sorry`, as this is a stage-2 statement delivery. No
`STATEMENT-DISPUTED` issue was found.

## Second reading by Q61

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
