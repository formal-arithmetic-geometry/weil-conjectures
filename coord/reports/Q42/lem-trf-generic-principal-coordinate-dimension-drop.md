## Worker report

The module defines `AlgebraicGeometry.exists_principal_coordinate_dimension_drop`.
It states the Tag 0GTG generic principal-open coordinate assertion.  The explicit
variables `R` and `S` are commutative rings of finite type over `ℤ`, and `φ : R →+* S`
is the ring homomorphism.  The `letI` installs the corresponding `Algebra R S`
structure.  The integer hypothesis is `d : ℕ` with `hd : 1 ≤ d`.  The fibre
hypothesis quantifies every point `y` of `Spec R` and bounds
`topologicalKrullDim` of `Scheme.Hom.fiber` for the morphism induced by `φ` by
`(d : WithBot ℕ∞)`.  The conclusion supplies `a : S` and `f : R`; its first
conjunct says `f` is outside every prime in `minimalPrimes R`, rendering the node's
“belongs to no minimal prime” clause.  The second conjunct quantifies every point of
`Spec (Polynomial (Localization.Away f))`, constructs the canonical localized map
using `IsLocalization.Away.map` followed by `Polynomial.eval₂RingHom`, with the
variable sent to `algebraMap S (Localization.Away (φ f)) a`, and bounds every
resulting fibre by `((d - 1 : ℕ) : WithBot ℕ∞)`.  `topologicalKrullDim` has bottom
value for empty spectra, so empty fibres remain allowed.  The proof is `sorry` as
required at stage 2.

The statement dependencies used are Mathlib `Algebra.FiniteType` from
`Mathlib.RingTheory.FiniteType`, `AlgebraicGeometry.Scheme` and
`Scheme.Hom` from `Mathlib.AlgebraicGeometry.Scheme`, `Scheme.Hom.fiber` from
`Mathlib.AlgebraicGeometry.Fiber`, `topologicalKrullDim` from
`Mathlib.Topology.KrullDimension`, `Localization.Away` and
`IsLocalization.Away.map` from `Mathlib.RingTheory.Localization.Away.Basic`, and
`Polynomial.eval₂RingHom` from `Mathlib.Algebra.Polynomial.Eval.Defs`.  The recorded
DAG declarations for all six statement dependencies were read; each is a Mathlib
match and no project declaration or dependency module was needed.

Edge cases checked: `d = 1` gives the bound zero; the minimal-prime condition is
vacuous when `R` has no prime points; `a = 0` is permitted; localization at a unit
is covered by `Localization.Away`; zero and empty spectra are permitted; and the
polynomial ring has its ordinary one-variable interpretation.  No reducedness,
nonzero, integrality, separatedness, or nonemptiness hypothesis was added.

Searches for an existing statement or definition found no match.  `msearch.py Q42
lem-trf-generic-principal-coordinate-dimension-drop leanfinder` with the finite-type
fibre dimension-drop query returned only generic finite-type, quasi-finite, and
Noether-normalization declarations.  The corresponding `loogle` query for
`Algebra.FiniteType, Polynomial.eval₂RingHom, topologicalKrullDim` returned no
matching theorem.  `msearch.py ... grep "dimension.*(drop|coordinate|generic)"
Mathlib` found no such result.  `rg` in `WeilConjectures` and `lean/Sheaf` for
`generic-principal-coordinate-dimension-drop`, `exists_principal_coordinate`, and
`dimension.*drop.*fibre` found no declaration.  The module compiled cleanly with
`scompile.py`; only the expected `sorry` proof is present.

## Second reading by Q42

I reread the node and the module clause by clause.  The hypotheses match the node:
`φ`, finite-type commutative rings over `ℤ`, `d ≥ 1`, and the bound on every
scheme-theoretic fibre.  The conclusion retains both witnesses, the explicit
avoidance of every minimal prime, the localization `R[1/f]` and `S[1/φ(f)]`, the
polynomial target, the canonical evaluation map `t ↦ a/1`, and the dimension bound
`d - 1`.  The `WithBot ℕ∞` codomain records the allowed `-∞` value for empty spectra.
No mismatch or statement correction was found.
