## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleFibreSpecialization` states the two clauses of the
node. It uses the source declaration `AlgebraicGeometry.Scheme.Hom.GeometricFiber` from
`WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber`, whose elements are
geometric points of a scheme-theoretic fibre.

The main theorem binds schemes `X Y`, a quasi-compact, separated, étale morphism `f`, two
algebraically closed field geometric points `ygen` and `ysp`, and a specialization relation
between their underlying points. Its hypothesis `[Finite (GeometricFiber f ygen)]` renders
finiteness of the generic geometric fibre. Its conclusion is finiteness of the special fibre
and the inequality of `Nat.card`s. The dense-open theorem binds an open dense subset `U`
and an integer `d`; on every geometric point over `U` its hypothesis gives finiteness and
cardinality `< d`, and the conclusion gives the same finiteness and strict bound for every
geometric point. The explicit `Finite` conjuncts ensure that `Nat.card` has its intended
finite-cardinality meaning.

All proof bodies are `sorry`, as required at stage 2. Edge cases checked include `d = 0`,
empty fibres (their card is `0`), identity morphisms (cardinality `1`), and specialization
between equal points. The theorem permits different algebraically closed residue-field
extensions for the two geometric points, as in the node's geometric-point formulation.

Dependencies used: `AlgebraicGeometry.Etale`, `AlgebraicGeometry.QuasiCompact`, and
`AlgebraicGeometry.IsSeparated` from Mathlib; and
`AlgebraicGeometry.Scheme.Hom.GeometricFiber` from
`WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber`.

Searches for an existing statement or definition: LeanFinder query “The cardinality of
geometric fibres of a quasi compact separated etale morphism does not increase under
specialization” returned only generic specialization and étale lemmas, with no match;
Loogle query `Specializes, Cardinal.mk` returned no hits; grep query
`fiber.*special|fibre.*special|card.*special` over Mathlib AlgebraicGeometry and the source
returned no matching theorem. A LeanSearch query for “geometric fibre cardinality separated
etale specialization” was unavailable (HTTP service error). The source search found the
related geometric-fibre declaration, which is imported rather than duplicated.

No statement correction or disputed statement.

## Earlier second reading (a previous round; superseded)

I reread the node and module clause by clause. The hypotheses quasi-compact, separated,
and étale are typeclass binders on the same morphism. The specialization clause compares
underlying points of the two geometric points. The finite-generic-fibre hypothesis and the
finite-special-fibre/cardinality inequality conclusion are present verbatim in the first
theorem. The dense-open clause has open and dense hypotheses, the strict integer bound on
every geometric point over the open, and the corresponding bound everywhere. The explicit
finiteness conjuncts make the Lean `Nat.card` expression faithful to finite geometric
cardinality. No mismatch was found.

## Second reading by J1

I read the node's single prose statement as two conclusion clauses rendered by two Lean
statements. The introduced objects and hypotheses match as follows:

1. The node's quasi-compact separated étale morphism (f:X\to Y) is rendered by
`{X Y : Scheme.{u}}`, `(f : X ⟶ Y)`, `[QuasiCompact f]`, `[IsSeparated f]`, and
`[Etale f]`. No Noetherian, proper, finite, or other extra hypothesis is present.
2. A geometric point over (Y) is rendered by
`ygen : Spec (.of Ωgen) ⟶ Y` and `ysp : Spec (.of Ωsp) ⟶ Y`, with `Field` and
`IsAlgClosed` instances for each field. The universe is shared with the scheme, as in
the imported `GeometricFiber` declaration; this covers all geometric points admitted by
that dependency.
3. The specialization `ygen (default : Spec (.of Ωgen)) ⤳ ysp (default : Spec (.of Ωsp))` is rendered by
`hsp : ygen (default : Spec (.of Ωgen)) ⤳ ysp (default : Spec (.of Ωsp))`, i.e. the
underlying points in the same target scheme. The direction is generic to special.
4. The generic fibre finiteness hypothesis is exactly
`[Finite (Scheme.Hom.GeometricFiber f ygen)]`.
5. The first conclusion is exactly finiteness of the special geometric fibre and
`Nat.card (GeometricFiber f ysp) ≤ Nat.card (GeometricFiber f ygen)` in
`etale_geometricFiber_card_le_of_specializes`; the fibre is the imported
`AlgebraicGeometry.Scheme.Hom.GeometricFiber`, not a private duplicate.
6. The node's dense-open clause is rendered by `U : Set Y`, `IsOpen U`, `Dense U`,
`d : ℕ`, and `hU`, which gives finiteness and cardinality `< d` for every algebraically
closed geometric point whose underlying point lies in `U`. The conclusion quantifies over
every such geometric point and gives the same finiteness and strict bound.

I checked edge cases: `d = 0` makes the dense-open premise impossible unless the relevant
fibres are empty; an empty fibre has `Nat.card = 0`; identity morphisms give cardinality
one; equal-point specialization is allowed; and no nonzero or characteristic assumption
is introduced. The empty scheme and empty index cases are unrestricted by the binders.

Searches were independently checked with LeanSearch (geometric-fibre cardinality under
specialization; service unavailable), Loogle (`Specializes, Cardinal.mk`; no matching
result), and grep over Mathlib and `WeilConjectures` (`fibre.*special`,
`fiber.*special`, `card.*special`; no matching theorem). The only existing notion found
was the imported `Scheme.Hom.GeometricFiber`, whose declaration matches the dependency
node exactly.

No mismatch was found, so no Lean or node statement was changed. The module compiles with
`scompile.py`; all theorem bodies remain `sorry` and no declaration is proved at stage 2.

## Reviewer fix (R-efs1009, stage 2)

The delivered statement counted `Scheme.Hom.GeometricFiber f ȳ`, the set of Ω-lifts
`Spec Ω ⟶ X` of ȳ: the notion of def-weil-pbc-geometric-fibre, which is not a stmt_dep of
this node. The node's stmt_dep def-weil-geometric-fibre is the scheme X ×_Y Spec Ω along ȳ,
and "its cardinality" is the number of its points. The two counts agree only for étale f
(every point of the geometric fibre has residue field Ω), which is a lemma, not the
statement. The fix states both theorems with `↥(pullback f ȳ : Scheme.{u})` (Mathlib
`pullback`, as `Scheme.Hom.fiber` is built), drops the WeilConjectures GeometricFiber import,
and adds the node's proof in words to both docstrings. Hypotheses (QuasiCompact, IsSeparated,
Etale, algebraically closed Ω, specialization of underlying points, finite generic fibre,
open dense U, d : ℕ) are unchanged.
