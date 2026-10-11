## Worker report

The module states `AlgebraicGeometry.kummer_base_change_compatibility` in
`lean/Sheaf/AlgebraicGeometry/Curve/KummerBaseChangeCompatibility.lean`. It introduces the
base change scheme `P` and morphism `π`, exact Kummer short complexes, a comparison map on roots
of unity, and a `ShortComplex.Hom` whose middle and right components are
`upperStarGmSheafToGmSheaf π`. The first conjunction clause is the left square, followed by the
naturality equation for `Sheaf.H.δSucc`; the next two clauses are the maps on the first and second
arrows of the long exact sequence after `Etale.cohomologyMap`. The Picard clause is rendered by
`Pic.toCohomologicalPicardGroup` and `Pic.map π`. Degree zero is rendered as pullback of global
units via `Units.map π.appTop.hom.toMonoidHom`. The final implication gives a bijection on
`n`-torsion Picard classes for affine `C`, with its underlying function equal to `Pic.map π`.

The field hypotheses are the two fields, algebraic closedness, and the algebra structure. The
curve hypotheses are `IsConnectedCurve f` and `Smooth f`; `n` is nonzero through `[NeZero n]` and
`hn : (n : k) ≠ 0`. The base-change equality is exactly the displayed pullback. Exactness is
included through `hC` and `hP`; the proof establishes these from the Kummer exactness dependency.
The cohomology clauses quantify every degree and every element, including the connecting maps and
both short-complex arrows. The affine clause has no hidden properness assumption.

Dependencies used are `AlgebraicGeometry.Scheme.kummerSequence` and
`kummerSequence_shortExact` (WeilConjectures.AlgebraicGeometry.Sites.Kummer),
`AlgebraicGeometry.Etale.cohomologyMap` (WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance),
`AlgebraicGeometry.Scheme.upperStarGmSheafToGmSheaf` (WeilConjectures.AlgebraicGeometry.Sites.Gm),
`Sheaf.H.δSucc` and `Sheaf.H.map` (Mathlib sheaf cohomology), `Pic.map`
(WeilConjectures.AlgebraicGeometry.PicardFunctor), and the statement dependencies
`lem-sc-kummer-les`, `lem-sc-kummer-exact`, `lem-sc-h1-gm-pic-pullback`,
`lem-sc-pic-affine`, `thm-av-final`, and `lem-sc-divisible-quotient-torsion`.

Edge cases checked: `n = 0` is excluded by `NeZero n`; arbitrary positive `n` prime to the
characteristic is retained by `hn`; no nonemptiness or properness is added beyond connectedness;
the index `q` ranges over all natural degrees; and the affine implication is conditional.

Searches: `msearch.py leanfinder 'Kummer sequence naturality base change affine curve Picard torsion'`
returned only unrelated Weierstrass base-change declarations; `msearch.py loogle
'Sheaf.H.map, ShortComplex'` returned no hits (unknown identifier); `msearch.py grep
'kummer.*(base|pull|natur)|upperStar.*rootsOfUnity'` returned no hits; `msearch.py leansearch
'Kummer sequence naturality base change Picard torsion affine curve'` was unavailable. `rg` over
Mathlib, WeilConjectures, and `lean/Sheaf` found no declaration of this node.

No STATEMENT-DISPUTED flag or node fault.

## Second reading by V1

I read the node, its source place, and the module signature clause by clause. The binders
`k k'`, their field, algebraically closed, and algebra hypotheses render the two algebraically
closed fields and extension. `C`, `f`, `[IsConnectedCurve f]`, and `[Smooth f]` render the smooth
separated connected curve over `k`; `n`, `[NeZero n]`, and `hn` render positive `n` prime to the
characteristic. The existential `P`, `π`, and displayed pullback equality render the base change.
The witnesses `hC`, `hP`, `cμ`, and `φ` render the two short exact Kummer sequences, the roots
comparison, and the short-complex morphism. The three component equalities render the left,
middle, and right squares. The next three universal clauses render respectively connecting-map
naturality, the first Kummer arrow, and the second arrow, for every degree and element. The Picard
clause is exactly the `Pic.toCohomologicalPicardGroup`/`Pic.map π` compatibility. The degree-zero
clause now uses the canonical `Sheaf.H.equiv₀` identifications, cohomology pullback, the comparison
map, and `Units.map π.appTop.hom.toMonoidHom`; this was corrected from a tautological self-equality.
The final implication gives a bijection on the displayed `n`-torsion Picard subtypes and identifies
its underlying function with `Pic.map π`.

The empty and zero cases are covered by the unrestricted universal quantifiers; `n = 0` is excluded
by `[NeZero n]` and `hn`, while arbitrary characteristic-compatible positive `n` remains allowed.
No nonemptiness, properness, or extra finiteness hypothesis is introduced, and all objects remain in
universe `u`. Searches with LeanFinder/Loogle/grep over Mathlib, WeilConjectures, and `lean/Sheaf`
found no existing declaration of this statement.

The mismatch found was the degree-zero clause: the worker's Lean equated the same units map on both
sides, so it did not express pullback on cohomology as required by the source. I replaced it with the
explicit canonical degree-zero equation from `picard_cohomology_pullback`, updated the node's
statement and `lean.statement`, and recorded the correction and citer checks in `statement_change`.
The corrected module compiles cleanly with `scompile.py`.

## Statement corrected

The old formal clause was the tautology
`Units.map π.appTop.hom.toMonoidHom a = Units.map π.appTop.hom.toMonoidHom a`.
The source requires the canonical degree-zero cohomology pullback followed by the units comparison,
identified with `Units.map π.appTop.hom.toMonoidHom`; this is the source place recorded in the node.
The sole citer, `thm-sc-constant-invariance`, continues to hold, as recorded in `statement_change`.
