## Worker report

The module `Sheaf.AlgebraicGeometry.CoordinatePrimeAffineChart` states
`AlgebraicGeometry.coordinatePrimeAffineChart_realization` with `sorry`.
The node's statement, statement dependencies, proof and proof dependencies are unchanged.
No new nodes or dependency repairs are needed. There are no disputed statements.

The two real-data helpers belong to the chart construction in this node:
`coordinatePrimeChartMap f d n θ` is the composite of Mathlib's canonical
`basicOpenIsoSpecAway d`, `Spec.map θ`, and `(AffineSpace.SpecIso ...).inv`;
`coordinatePrimeChartBaseProjection f n` is the affine-space projection followed by
`Spec.map (algebraMap R (Localization.Away f))`. These introduce no alternative
localization, scheme, affine space, quasi-finiteness or residue-field notion.

Hypothesis-by-hypothesis correspondence:

- Commutative rings and rho: `{R A : Type u} [CommRing R] [CommRing A] (ρ : R →+* A)`.
  A common arbitrary universe is the scheme-category convention; this imposes no
  mathematical cardinality bound on the rings. Coordinates are `ULift.{u} (Fin n)`
  to meet Mathlib affine space's coordinate-universe convention.
- The prime q_A is `qA : PrimeSpectrum A`; p is the canonical contraction
  `(qA.comap ρ).asIdeal`. No arbitrary extra prime or primality assumption is used.
- The elements outside these primes are `f`, `d`, `hf`, and `hd`.
- The image rho(f) being invertible in A_d is exactly
  `hunit : IsUnit (algebraMap A (Localization.Away d) (ρ f))`.
- The nonnegative integers r and n with r <= n are `(n r : ℕ) (hrn : r ≤ n)`.
- C is literally `MvPolynomial (ULift.{u} (Fin n)) (Localization.Away f)`.
  The homomorphism is `θ`; `hθ` says its composite with `MvPolynomial.C` equals
  the canonical `IsLocalization.Away.lift` of rho. Specifying a ring homomorphism
  with this constants equation is precisely specifying the node's R_f-algebra map;
  no additional independent algebra action is assumed.
- Finite type is `hft : θ.FiniteType` (`RingHom.FiniteType`). The predicate reduces
  to `Algebra.FiniteType` for `θ.toAlgebra`, so it is passed directly as the instance
  argument in `hqf : ∀ Q, @Algebra.IsQuasiFiniteAtPrime ... θ.toAlgebra hft Q`.
  The latter is the recorded project definition, including the finite-type convention.
- The prescribed inverse-image prime is `hprime`. The ideal q_A A_d is
  `qA.asIdeal.map (algebraMap A (Localization.Away d))`.
  The base-prime ideal in C is the map of `(qA.comap ρ).asIdeal` under
  `MvPolynomial.C.comp (algebraMap R (Localization.Away f))`, equivalently the
  extension of p R_f. Its supremum with
  `Ideal.span {x | ∃ i : ULift (Fin n), r ≤ i.down.val ∧ x = MvPolynomial.X i}`
  is exactly `(p R_f,x_{r+1},...,x_n)` in the node's one-based indexing.

Conclusion-by-conclusion correspondence:

- S, Z, p, z are `Spec (.of R)`, `Spec (.of A)`, `Spec.map (ofHom ρ)`, and `qA`.
  The first two conjuncts assert membership of p(z) and z in `PrimeSpectrum.basicOpen f`
  and `PrimeSpectrum.basicOpen d`.
- The third conjunct is the inclusion D(d) subset p^{-1}(D(f)), with the open sets'
  `.carrier` used to avoid a coercion ambiguity between spectra and scheme spaces.
- The principal open subschemes are Mathlib `Scheme.Opens.toScheme` of these opens.
  Their canonical isomorphisms with Spec R_f and Spec A_d are the existing
  `basicOpenIsoSpecAway f` and `basicOpenIsoSpecAway d`; the latter is part of the
  actual chart definition. They are constructions, rather than postponed existences.
- The target is the actual `AffineSpace (ULift (Fin n)) (Spec (.of R_f))`.
  Its canonical identification with Spec C is `AffineSpace.SpecIso`; the chart uses
  its inverse after `Spec.map θ`. Thus the morphism is the one induced by θ.
- The over-S_0 clause is the displayed equality of the chart followed by the
  affine-space projection with `basicOpenIsoSpecAway d` followed by Spec of the
  canonical localized base map. Under `basicOpenIsoSpecAway f`, this is the
  restriction of p with target D(f), as required by the constants equation `hθ`.
- Finite type is `LocallyOfFiniteType q ∧ QuasiCompact q`, exactly the recorded
  `def-weil-finite-type-morphism`. Quasi-finiteness is the recorded `q.IsQuasiFinite`.
- For EVERY target point t, the statement asserts both `Finite (q.fiber t)` and
  `DiscreteTopology (q.fiber t)`. These are scheme fibres, not merely inverse-image sets.
- The marked source point is represented by `z0` in the actual open subscheme with
  `z0.val = qA`. The universal formulation covers its unique lift; `hd` ensures
  this lift exists, so the clause is not vacuous. Its image t is `q z0`.
- The image-coordinate prime is explicitly the `.asIdeal` of
  `(AffineSpace.SpecIso ...).hom (q z0)`, and is asserted equal to P.
- The next equality says `coordinatePrimeChartBaseProjection f n (q z0) = p z`.
  Write s for its left side. The last clause gives a ring equivalence from the
  ACTUAL scheme residue field at t to
  `FractionRing (MvPolynomial (Fin r) ((Spec (.of R)).residueField s))`.
  It requires, for every a in the ACTUAL base residue field at s,
  `e ((baseProjection.residueFieldMap t).hom a) = algebraMap _ _ a`.
  This is exactly an isomorphism of kappa(s)-algebras with the structural scalar
  action, expressed without installing a local algebra instance. The preceding
  point equality identifies s with p(z); no arbitrary field embedding is substituted.
- There is no fibre-dimension, presentation, Noetherian, reducedness, characteristic,
  or nonemptiness hypothesis beyond the given marked prime. No extra theorem is proved.

The docstring contains the node's complete seven-step natural-language proof,
with the same dependencies: principal opens and the localization lift; the
Spec/affine-space factorization; finite type via the affine criterion; isolated and
finite scheme fibres; the marked prime and natural residue maps; the evaluation
kernel computation; and the fraction-field surjectivity and scalar compatibility.

Dependency declarations read and used (including the proof-only imports):

- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`, with the ring
  structure and `IsLocalization.Away.lift` from
  `Mathlib.RingTheory.Localization.Away.Basic`.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, `MvPolynomial.C`,
  `MvPolynomial.algHom_ext`; evaluation `MvPolynomial.aeval` is in `.Eval`.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`.
- `WeilConjectures.RingTheory.QuasiFiniteAtPrime`: `Algebra.IsQuasiFiniteAtPrime`,
  publicly imported through `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Spec`, `Spec.map`, `Spec.map_apply`.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace`, `AffineSpace.over`,
  `AffineSpace.SpecIso`, and `AffineSpace.SpecIso_inv_over`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `LocallyOfFiniteType` and `QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `Scheme.Hom.IsQuasiFinite` (and its pointwise definition).
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.Spec.residueFieldIso` and its natural maps.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberHomeo`.
- `Mathlib.AlgebraicGeometry.Restrict`: `basicOpenIsoSpecAway` and its inclusion equation.
- `Mathlib.AlgebraicGeometry.AffineScheme`: affine principal opens and their localization
  interface; `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `isAffineHom_of_isAffine`
  and the quasi-compact instance for affine morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`:
  `HasRingHomProperty.iff_exists_appLE` (proof-only import).
- `WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso`:
  `IsLocalization.prime_localRing_residueField_iso` (proof-only import).
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated`:
  `Scheme.Hom.quasiFiniteAtPoint_isolated_in_fiber` (proof-only import).
- `WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite`:
  `locallyQuasiFinite_and_quasiCompact_iff_finite_preimage_singleton` (proof-only import).
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.PropertyC`:
  `Spec.residueFieldMap_residueFieldIso_hom` (proof-only import).
- `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`:
  `Ideal.ResidueField` and its fraction-field and universal-property interface;
  `Mathlib.RingTheory.Localization.Defs`: `IsLocalization.lift` and `ringHom_ext`.

Edge cases checked before drafting:

- r=n=0: there are no coordinates; affine zero-space is canonically the base and
  the coordinate ideal is p R_f. The fraction field of the zero-variable polynomial
  ring over K is canonically K. The statement retains this case.
- r=0<n: every variable is in P and the marked residue field is K.
- r=n: the last-coordinate span is the zero ideal and the residue field is K(u_1,...,u_n).
- Nonreduced R and A: the prime quotient/fraction computation removes nilpotents;
  neither domain nor reduced hypotheses are introduced on R or A.
- Invertible f or d, arbitrary characteristic, and inseparable source residue extensions
  cause no change. The marked prime excludes a zero source ring but is already part
  of the node; no extra nontriviality hypothesis is imposed.
- Unmarked fibres may be empty. `Finite` and `DiscreteTopology` allow empty fibres.
- The prescribed coordinate prime is prime because it is the contraction of the
  localized marked prime; its primality is not a hidden additional assumption.

Searches for an existing whole statement:

- `msearch.py leanfinder`, query "A finite type quasi finite polynomial map of localized
  rings induces an affine scheme chart with coordinate prime residue field a rational
  function field": eight hits (affine basis covers, function fields, rational maps,
  and the field-valued Spec equivalence), no matching whole statement.
- `msearch.py loogle`, query `"residueField", "MvPolynomial"`: zero hits.
- `msearch.py leansearch`, query "Residue field at a coordinate prime of a multivariate
  polynomial ring and quasi finite affine chart": eight hits, including ring
  quasi-finite residue-field properties and residue-field definitions; no full chart result.
- `msearch.py grep`, query
  `residueFieldMapCAlgEquiv|coordinate.*[Pp]rime|[Pp]rime.*coordinate`: seven hits,
  all the one-variable `Polynomial.residueFieldMapCAlgEquiv` or its use in the
  one-variable quasi-finite polynomial argument. No multivariable coordinate-prime chart.
- `rg` in the upstream `WeilConjectures` and project `Sheaf` source trees for
  `coordinate.*[Pp]rime|[Pp]rime.*coordinate|coordinate_prime_affine|rational.*residue|residue.*rational`
  found related but distinct results (e.g. field normalization, quasi-finite affine
  criteria and coordinate strata). Searching the exact item ID found no declaration.
  Searching the chosen declaration/helper names found no existing ones.

Sources read: local Stacks `more-morphisms.tex`, lemma-local-structure-finite-type
(052E), especially its first proof paragraph; `algebra.tex`,
lemma-refined-quasi-finite-over-polynomial-algebra (0520); the current blueprint's
`sk-i-curve-zero/lem-trf-local-term-locality.proof.md`; all statement-dependency nodes
and recorded signatures/docstrings, and the recorded proof-dependency interfaces.

Validation: the server sandbox compile passes with no warnings (3.5 seconds).
The library compile fails with `resource exhausted (error code: 28, no space left on device)`
(12.0 seconds). Retrying the prescribed `scompile.py` wrapper and running the required
`deliver2.py NK lem-trf-coordinate-prime-affine-chart-realization --no-push` both
return that same storage failure. The dry run prints `COMPILE FAILED on the server,
nothing pushed`; preflight and delivery cannot proceed. No compiler or launcher tools
were changed, and no live files were edited. The sandbox module, node Lean record,
and report are ready for retry after the server storage failure is repaired.

Metadata self-check: the only changed node field is `lean`; its statement exactly
matches the module signature; no Lean line exceeds 100 characters; one named theorem
has the sole `sorry`; both helper definitions have real construction data.

No second reading by a worker: the dispatcher prohibits spawning agents and the worker
delivers directly; the maintainer supplies the independent review.

## Saved-packet retry (2026-10-24T10:48:40+00:00)

Inspected the saved report and module, and started with the required `deliver2.py NK lem-trf-coordinate-prime-affine-chart-realization --no-push`. The sandbox compile again passes (3.5 s), but the library compile fails (12.0 s) with `resource exhausted (error code: 28, no space left on device)`. An independent retry through the prescribed `scompile.py` with the saved module produces the identical result. This is the persistent server storage failure; no Lean elaboration error is reported and nothing was pushed.

Compared the saved node with the current read clone: only `lean` differs. The recorded signature is verbatim in the module, no line exceeds 100 characters, and the sole postponed proof remains the named theorem. There is no item repair note in the current read clone. The packet is retained without changing the Lean source or node for a retry after server storage is repaired.

## Saved-packet retry (2026-10-24T10:52:41+00:00)

Started with the required saved-packet dry run through `deliver2.py NK
lem-trf-coordinate-prime-affine-chart-realization --no-push`. The sandbox compile
passes (3.5 s), but the library compile fails (12.0 s) with
`resource exhausted (error code: 28, no space left on device)`. Retried independently
through the prescribed `scompile.py` with the saved module: the sandbox compile
passes (3.5 s) and the library compile reports the identical storage error (12.0 s).
The dry run says `COMPILE FAILED on the server, nothing pushed`. No tool was edited
or worked around, and no live source was changed. Delivery remains blocked by the
persistent server storage failure, with the packet retained.

Rechecked the saved module and current node: only `lean` differs, the recorded
signature matches the module verbatim, all Lean lines meet the 100-character limit,
and the only `sorry` is the named theorem's proof. No current repair note exists.
The Lean source and node are retained unchanged.

## Saved-packet retry (2026-10-24T10:56:09+00:00)

Started with the required saved-packet dry run, `deliver2.py NK
lem-trf-coordinate-prime-affine-chart-realization --no-push`. The sandbox compile
passes (3.5 s), but the server library compile fails (12.0 s) with
`resource exhausted (error code: 28, no space left on device)`. An independent retry
using the prescribed `scompile.py` and the retained module produces the identical
result. The dry run reports `COMPILE FAILED on the server, nothing pushed`.
No Lean elaboration error is reported. The persistent server storage failure
prevents completing preflight and delivery; no launcher tools were modified or
worked around, and no live files were changed.

The saved module and current node were rechecked: only `lean` differs, its recorded
signature occurs verbatim in the module, no Lean line exceeds 100 characters,
`autoImplicit` is disabled, and the sole `sorry` remains the named theorem proof.
There is no current item repair note. The Lean module and node are retained unchanged.

## Saved-packet retry (2026-10-24T10:58:58+00:00)

Started with the required `deliver2.py NK
lem-trf-coordinate-prime-affine-chart-realization --no-push` on the retained packet.
The sandbox compile passes (3.5 s), but the library compile fails (12.0 s) with
`resource exhausted (error code: 28, no space left on device)`. An independent
`scompile.py` retry of the saved module gives the same sandbox success and server
library storage failure. The dry run prints `COMPILE FAILED on the server, nothing pushed`.
No Lean elaboration error was reported. No tools were changed or worked around.

Self-check against the current shared read clone: only the node's `lean` field
differs, its recorded signature occurs verbatim in the saved module, all lines
meet the 100-character limit, `autoImplicit` is disabled, and the sole `sorry` is
the named theorem's proof. No current repair note exists. The module and node
remain unchanged; the packet is retained for retry after server storage is repaired.

## Saved-packet retry (2026-10-24T11:01:56+00:00)

Started with the required saved-packet dry run through `deliver2.py NK
lem-trf-coordinate-prime-affine-chart-realization --no-push`. The sandbox compile
passes (3.5 s), but the server library compile fails (12.0 s) with
`resource exhausted (error code: 28, no space left on device)`. An independent
retry using `scompile.py` on the retained module produces the identical result.
The dry run reports `COMPILE FAILED on the server, nothing pushed`. This is a
persistent server storage failure, with no Lean elaboration diagnostic to repair.
No live files or launcher tools were changed or worked around.

Self-check against the current read clone: only the node's `lean` field differs;
the recorded signature is verbatim in the module, every line meets the
100-character limit, `autoImplicit` is disabled, and the sole `sorry` is the
named theorem's proof. No current repair note exists. The Lean module and node
are retained unchanged for retry after server storage is repaired.

## Saved-packet retry (2026-10-24T11:04:51+00:00)

Started with the required saved-packet dry run using `deliver2.py NK
lem-trf-coordinate-prime-affine-chart-realization --no-push`. The sandbox compile
passes (3.5 s), but the server library compile fails (12.0 s) with
`resource exhausted (error code: 28, no space left on device)`. An independent
retry through the prescribed `scompile.py` on the retained module produces the
identical sandbox success and server library storage failure. The dry run reports
`COMPILE FAILED on the server, nothing pushed`. There is no Lean elaboration
diagnostic to repair. No live files or launcher tools were changed or worked around.

Self-check against the current read clone: only the node's `lean` field differs,
the recorded signature occurs verbatim in the module, every Lean line meets the
100-character limit, `autoImplicit` is disabled, and the sole `sorry` is the named
theorem's proof. No current repair note exists. The module and node are retained
unchanged; delivery remains blocked by the persistent server storage failure.

## Saved-packet retry (2026-10-24T11:07:39+00:00)

Started with the required saved-packet dry run through `deliver2.py NK
lem-trf-coordinate-prime-affine-chart-realization --no-push`. Sandbox compilation
passes (3.5 s), but server library compilation fails (12.0 s) with
`resource exhausted (error code: 28, no space left on device)`. An independent
retry through the prescribed `scompile.py` produces the same results. The dry run
reports `COMPILE FAILED on the server, nothing pushed`. This is a persistent
server storage failure; no Lean elaboration diagnostic was reported.

Checked the retained module and current node: only `lean` differs, the recorded
signature appears verbatim in the module, every Lean line meets the 100-character
limit, `autoImplicit` is disabled, and the only `sorry` is the named theorem proof.
No item repair note was found in the current repair-notes or returns directories.
The Lean source and node remain unchanged. No live source or launcher tool was
modified or worked around; the packet is retained.

## Second reading by NK

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
