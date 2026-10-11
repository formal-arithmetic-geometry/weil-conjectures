## Worker report

The module states ascent of regularity of the completion map along a finite type map at a
quasi-finite prime, using `RingHom.IsRegular` from `Sheaf.RingTheory.GRing`. The binders
`[CommRing]`, Noetherian instances, `Algebra.FiniteType`, prime ideals and inclusion render
the ring hypotheses and `hq` renders the isolated fibre point condition via
`Algebra.IsQuasiFiniteAtPrime`. The hypothesis and conclusion are the regularity of the
localization-to-adic-completion maps at the contracted and target primes.

Dependencies used: `Sheaf.RingTheory.GRing` (`RingHom.IsRegular`),
`Sheaf.RingTheory.QuasiFiniteAtPrime` (`Algebra.IsQuasiFiniteAtPrime`); Mathlib
`Localization.AtPrime`, `AdicCompletion`, and `IsNoetherianRing`.

Edge cases checked include equal primes, zero and maximal primes, and arbitrary universe
levels. Searches in the node records and repository for formal-fibre ascent found no existing
statement. The source statement is more specifically phrased using geometric regularity of
fibre algebras; the available project predicate packages this as regularity of the completion
map.

## Earlier second reading (a previous round; superseded)

The file was compiled cleanly. Every ring, finiteness, prime, inclusion, quasi-finite and
regularity clause is represented by an explicit binder or hypothesis; no proof is supplied.

## Second reading by M1

The source is Stacks, More on Algebra, Lemma 07PP (item (1)). Its objects and clauses are: a finite-type map of Noetherian rings R → R'; primes q' ⊆ p' in R' and their contractions q ⊆ p in R; quasi-finiteness at p' (isolated point of the affine fibre); and geometric regularity of the formal fibre at q implying geometric regularity of the formal fibre at q'. The Lean binders `[CommRing R] [CommRing R']`, `[IsNoetherianRing R] [IsNoetherianRing R']`, `[Algebra R R'] [Algebra.FiniteType R R']`, `(q' p')` with prime instances, and `hqp : q' ≤ p'` render these hypotheses. The `let q` and `let p` contractions render the contracted primes. `hq` uses `Algebra.IsQuasiFiniteAtPrime R R' ⟨p', inferInstance⟩`, the recorded affine ring notion. The antecedent is `Algebra.IsGeometricallyRegular q.ResidueField (q.Fiber C)` for `C = AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)`, and the conclusion is the corresponding expression for q' and p'. This matches every source clause and keeps the empty/zero and arbitrary-universe cases available through the type parameters and Mathlib fibre/completion definitions.

The initial worker statement instead assumed `RingHom.IsRegular` for the whole completion map and concluded regularity of the whole target completion map; that is stronger and is not Lemma 07PP(1). I replaced it with the two formal-fibre geometric-regularity predicates. I also corrected the dependency from the scheme-level `pqf-def-quasifinite` to the affine ring-level `def-weil-pbc-ring-map-quasi-finite-at-prime`, which is exactly the notion used by `Algebra.IsQuasiFiniteAtPrime`; this is recorded in `statement_change`. No proof was added.

Searches: node/DAG and project search found no existing statement; searches used LeanSearch (unavailable), Loogle (no hits for GeometricallyRegular), and Mathlib grep (no formal-fibre/geometric-regularity ascent declaration). Existing definitions `Algebra.IsGeometricallyRegular`, `Ideal.Fiber`, `Localization.AtPrime`, `AdicCompletion`, and `Algebra.IsQuasiFiniteAtPrime` were read and used.

## Statement corrected

The correction follows Stacks 07PP(1): the original Lean conclusion was a map-level regularity assertion rather than the source's individual formal-fibre assertion, and its quasi-finiteness dependency named a scheme notion. The corrected Lean and dependency now state the source's fibre algebras exactly. Citers checked: lem-weil-pbc-complete-local-g-ring (holds: true) and lem-weil-pbc-polynomial-complete-local-formal-fibres (holds: true).
