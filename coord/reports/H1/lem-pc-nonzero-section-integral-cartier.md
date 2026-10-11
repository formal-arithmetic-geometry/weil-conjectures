## Worker report

The module `lean/Sheaf/AlgebraicGeometry/NonzeroSectionIntegralCartier.lean`
states `AlgebraicGeometry.Scheme.Modules.nonzero_section_integral_cartier`.
It uses `X : Scheme`, the Mathlib instance `IsIntegral X`, an
`X.Modules` object `M` with the source-project class `M.IsInvertible`, and a
global section `s : Γ(M, ⊤)` with hypothesis `hs : s ≠ 0`.

The zero scheme is rendered by `let Z := (homOfGlobalSection M s).zeroLocus`,
using the source declaration for the zero scheme. The local conclusion is
quantified over every affine open `U : X.affineOpens`, a hypothesis
`Nonempty U.1`, every section `e : Γ(M, U.1)`, and a hypothesis
`he : IsFreeGenerator e`. Its coefficient is
`IsFreeGenerator.coeff he (M.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op s)`;
this renders “writing `s|_U = a e`”. The three local clauses are rendered by
`a ≠ 0`, `Z.ideal U = Ideal.span {a}`, and
`a ∈ nonZeroDivisors Γ(X, U.1)`, respectively. The final clause is
`Z.IsInvertible`, the project predicate for an effective Cartier ideal and
therefore the effective Cartier divisor conclusion.

Dependency declarations used:

- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral` from Mathlib,
  `Mathlib.AlgebraicGeometry.Properties`.
- `def-sc-invertible-module`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` from
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible` (imported by the
  module dependency chain).
- `def-pc-zero-scheme`:
  `AlgebraicGeometry.Scheme.Modules.Hom.zeroLocus` from
  `WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus`.
- `def-nagata-effective-cartier-ideal`:
  `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible` from
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible` (the
  project effective-Cartier modules expose the predicate used here).
- `def-pc-divisor-line-bundle`: the associated effective-Cartier notion is
  the same `IdealSheafData.IsInvertible` predicate; the source declaration
  `IdealSheafData.IsInvertible.isInvertible_dual_toModules` records the
  invertible dual module.
- The proof dependency `lem-sc-invertible-module-generic-stalk` is reflected
  in the theorem's `hs` and local nonzero clause but is not needed to type the
  statement.

Edge cases checked: the explicit `Nonempty U.1` excludes the empty affine
open exactly as in the node; `IsIntegral X` supplies a domain on every such
open, so the nonzerodivisor clause is meaningful; `s ≠ 0` handles the zero
section countercase; the trivial module case is covered by `M.IsInvertible`
and `IsFreeGenerator`; no finite-type, separatedness, or characteristic
hypothesis was added.

Searches for an existing declaration:

- `msearch.py H1 lem-pc-nonzero-section-integral-cartier leanfinder` for a
  nonzero section of an invertible sheaf on an integral scheme: only
  structure-sheaf germ results, no matching theorem.
- `msearch.py H1 lem-pc-nonzero-section-integral-cartier loogle`
  (`AlgebraicGeometry.Scheme.IdealSheafData`, `nonZeroDivisors`): no matching
  declaration for the combined statement.
- `rg` over `WeilConjectures/` for `nonzero_section`, `zeroLocus`, and the node
  id: no existing theorem with this statement; the recorded declarations are
  only the component notions listed above.
- `rg` over Mathlib AlgebraicGeometry for Cartier divisors, zero schemes,
  invertible modules, and `germ_injective`: no combined result; Mathlib's
  `IsIntegral` is the exact existing integral-scheme notion.

The module was compiled with:
`python3 /home/ubuntu/weil-launcher/scompile.py H1 lem-pc-nonzero-section-integral-cartier`
and produced no errors or warnings other than the expected `sorry` declaration warning.

## Earlier second reading (a previous round; superseded)

The independent second reader is assigned after this worker delivery. The
module and node record were checked for the stated hypotheses and local clauses
before the dry run; no worker-side statement change is recorded here.

## Second reading by H1

The node introduces an integral scheme (X), an invertible module (M), a
nonzero global section (s), its zero scheme (Z(s)), and, for every nonempty
affine open (U) and free generator (e), the coefficient (a) of the
restriction of (s).  The Lean theorem has exactly these binders:
`[IsIntegral X]`, `(M : X.Modules) [M.IsInvertible]`, `(s : Γ(M, ⊤))`,
`(hs : s ≠ 0)`, then `let Z := ...zeroLocus`, followed by the universal
`U`, `Nonempty U.1`, `e`, and `he` binders and `let a := ...coeff`.  Its three
conclusion clauses are respectively `a ≠ 0`, `Z.ideal U = Ideal.span {a}`,
and `a ∈ nonZeroDivisors Γ(X, U.1)`, followed by `Z.IsInvertible`; these render
the node's nonzero coefficient, principal ideal, nonzerodivisor, and effective
Cartier conclusions in the same order.  No extra finiteness, separation,
Noetherian, characteristic, or universe assumptions occur.

Edge cases were checked: empty affine opens are excluded by the node's
`Nonempty U.1`; the zero section is excluded by `hs`; the zero module cannot
provide `M.IsInvertible` with a free generator; and an integral affine scheme
with a nonzero coefficient gives the expected principal Cartier ideal.

Searches (`msearch.py` LeanFinder and Loogle queries for nonzero sections,
zero loci, and Cartier divisors, plus `rg` in Mathlib and `WeilConjectures/`)
found only the component declarations (`IsIntegral`, `zeroLocus`, and the
effective-Cartier predicate), with no theorem having this combined statement.

One mismatch was found in the delivery copy of the node: its `lean.statement`
had expanded the theorem's `let Z` and `let a` binders.  It was repaired to be
verbatim the signature in `NonzeroSectionIntegralCartier.lean`; the mathematical
statement and module body were otherwise correct.  The module compiles cleanly
with only the expected `sorry` proof warning.

## Review by R-nsc0925 (FIX)

The module contains no `let` binders: the zero scheme is written out as
`(homOfGlobalSection M s).zeroLocus` and the coefficient `a` as
`IsFreeGenerator.coeff he (M.presheaf.map (homOfLE le_top).op s)` in each clause; the
mentions of `let Z` / `let a` above describe an earlier draft. Clauses match the node
(`IsIntegral X` is `AlgebraicGeometry.IsIntegral`; `homOfGlobalSection M s` sends `1` to
`s|_U`, so the coefficient of `Hom.ideal_zeroLocus` with `eM = 1`, `eN = e` is exactly the
`a` of `s|_U = a e`). Reviewer fixes: the docstring now gives the node's proof (it omitted the
injectivity step via `lem-sc-invertible-module-generic-stalk`); the import
`WeilConjectures.AlgebraicGeometry.EffectiveCartier` (unused directly) was replaced by
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`, which declares
`IdealSheafData.IsInvertible`.
