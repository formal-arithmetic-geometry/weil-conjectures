## Worker report

The module states `AlgebraicGeometry.Scheme.picard_diagonal_locally_closed` in
`lean/Sheaf/AlgebraicGeometry/PicardDiagonalLocallyClosed.lean`.  The binders `[Flat f]`,
`[IsProper f]`, and `[LocallyOfFinitePresentation f]` render the three hypotheses on `f`.
The premise `hO` quantifies every base change `g : T ⟶ S` and asserts that the canonical
unit of the pullback–pushforward adjunction on the structure module is an isomorphism,
rendering `O_T ≅ p_* O_{X_T}`.  `E : X.Modules` with `[E.IsFiniteLocallyFree]` is the finite
locally free module.  The conclusion supplies a scheme `Z`, an immersion `j : Z ⟶ S`, and
local finite presentation of `j`; for every `g`, factorization through `j` is equivalent to
the existence of a finite locally free `N : T.Modules` and an isomorphism between the
pullbacks of `E` along `q = pullback.fst f g` and `N` along `p = pullback.snd f g`.

Dependencies used are Mathlib's `AlgebraicGeometry.Flat`, `AlgebraicGeometry.IsProper`,
`AlgebraicGeometry.Scheme.Over`, and `AlgebraicGeometry.LocallyOfFinitePresentation`.
The module additionally uses `Scheme.Modules.pullback`,
`Scheme.Modules.pullbackPushforwardAdjunction`, `SheafOfModules.unit`,
`SheafOfModules.IsFiniteLocallyFree`, and `IsImmersion` from Mathlib/project modules.

Edge cases checked: `T` is universally quantified (including the empty scheme), `E` and
`N` may have rank zero, and no nonemptiness or constant-rank hypothesis is added.  The
universe is explicit (`Scheme.{u}`) and all variables are bound.

Searches for an existing declaration: `msearch.py ... leanfinder "invertible module universal
locally closed locus pullback"` (only free-locus results; no theorem); `msearch.py ... loogle
"IsImmersion, IsFiniteLocallyFree"` (no matching universal Picard locus); grep of Mathlib and
`WeilConjectures/` for `picard_diagonal_locally_closed` (no hits); `rg` of `lean/Sheaf` for
Picard diagonal/locus statements (no exact declaration).  Therefore a new statement module
was required.

## Earlier second reading (a previous round; superseded)

Re-read the node and the generated file.  `pullback.fst` and `pullback.snd` are respectively
`q` and `p`; the displayed equivalence has exactly the two clauses of the node.  No node
hypothesis or conclusion clause is omitted, and no extra mathematical assumption is present
beyond the typeclass forms of flatness, properness, finite presentation, immersion, and finite
local freeness.

## Second reading by C1

I opened the node and the module and matched the statement item by item.  The objects and
verdicts are:

- `f : X ⟶ S` with `X,S : Scheme.{u}` renders a morphism of schemes over the same universe;
  verdict: exact.
- `[Flat f]`, `[IsProper f]`, and `[LocallyOfFinitePresentation f]` render flatness,
  properness, and locally finite presentation; verdict: exact hypotheses, with no added
  Noetherian, separated, or finite-type assumption.
- `∀ {T : Scheme.{u}} (g : T ⟶ S)` and `pullback f g` render every base change, including
  the empty scheme; `pullback.fst f g` is `q : X_T ⟶ X` and `pullback.snd f g` is
  `p : X_T ⟶ T`; verdict: exact.
- `hO` says `IsIso` for the unit at `SheafOfModules.unit T.ringCatSheaf`, rendering
  `O_T → p_* O_{X_T}` for every `g`; verdict: exact universal structure-sheaf hypothesis.
- `(E : X.Modules) [E.IsFiniteLocallyFree]` renders the finite locally free module on `X`;
  verdict: exact, including rank zero.
- `∃ Z, j, IsImmersion j ∧ LocallyOfFinitePresentation j` renders the finitely presented
  immersion `j : Z → S`; verdict: exact.
- The final `∀ g`, factorization witness `h` with `h ≫ j = g`, and the equivalence with
  `∃ N, N.IsFiniteLocallyFree, Nonempty (pullback_fst E ≅ pullback_snd N)` render both
  clauses of the node's conclusion in the same order; verdict: exact.

Edge cases checked: the universal `T` quantifier includes the empty scheme; `E` and `N` can
have rank zero; no fibre nonemptiness or constant-rank assumption was added; `Scheme.{u}`
does not impose a smaller universe; and the characteristic is unrestricted.

I searched Mathlib and `WeilConjectures/` with LeanFinder/Loogle and grep for the theorem
name and for universal Picard-locus formulations, and searched `lean/Sheaf` for the same
notions.  The only hits were generic pullback, immersion, and locally-free declarations;
no existing declaration states this result.

The prior signature was mathematically correct and needed no statement change.  I changed
only the theorem docstring: it now records the four Tag 0BDP proof steps (rank components,
perfect direct images, the projection-formula pairing criterion, and the determinant-open
construction), satisfying the required statement proof documentation.  Compilation was
clean with `scompile.py`.
