## Worker report

The module `lean/Sheaf/SecTraceFormula/SmoothCenterBlowupGeometry.lean` states
`AlgebraicGeometry.smooth_center_blowup_geometry` for schemes over `Spec ℚ`.
The center is represented by the canonical ideal sheaf `c.ker`; its blowup is
`c.ker.blowup`, with structure morphism `c.ker.blowupMap`. The strict transform is the
recorded canonical construction `c.ker.strictTransform x`.

The Lean hypotheses match the node clause by clause:

* `P C X : Scheme.{0}` and `p : P ⟶ Spec (CommRingCat.of ℚ)` introduce the schemes and
  the base field `ℚ`.
* `[Smooth p]` says that `P` is smooth over `ℚ`.
* `[IsSeparated p]`, `[LocallyOfFiniteType p]`, and `[QuasiCompact p]` are separatedness and
  finite type of `P` over `ℚ` (finite type is the conjunction of the latter two Mathlib
  properties).
* `c : C ⟶ P`, `[Smooth (c ≫ p)]`, and `[IsClosedImmersion c]` say that `C ↪ P` is a
  smooth closed subscheme over `ℚ`.
* `x : X ⟶ P`, `[IsReduced X]`, and `[IsClosedImmersion x]` say that `X ↪ P` is an
  arbitrary reduced closed subscheme.
* The conclusion's first four conjuncts,
  `Smooth (c.ker.blowupMap ≫ p)`, `IsSeparated (c.ker.blowupMap ≫ p)`,
  `LocallyOfFiniteType (c.ker.blowupMap ≫ p)`, and
  `QuasiCompact (c.ker.blowupMap ≫ p)`, state that the blowup is smooth, separated, and of
  finite type over `ℚ`.
* `IsReduced (c.ker.strictTransform x)` states reducedness of the scheme-theoretic strict
  transform. No hypothesis requires a nonempty center, a maximal stratum, or containment
  of `X` in `C`.

The statement dependencies used are `AlgebraicGeometry.IsClosedImmersion` from
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsReduced` from
`Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.Smooth` from
`Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
`AlgebraicGeometry.Scheme.IdealSheafData.blowup` from
`WeilConjectures.Blowup.Gluing`,
`AlgebraicGeometry.Scheme.IdealSheafData.strictTransform` from
`WeilConjectures.Compactification.StrictTransform`, and
`AlgebraicGeometry.IsSeparated`, `AlgebraicGeometry.LocallyOfFiniteType`, and
`AlgebraicGeometry.QuasiCompact` from the corresponding Mathlib morphism modules.
The center ideal is the canonical `Scheme.Hom.ker`, supplied by Mathlib's ideal-sheaf API;
no private replacement is introduced.

Edge cases checked against the source argument were an empty center (permitted by the
closed-immersion hypotheses), the whole ambient scheme as center (the zero-dimensional
local chart case), a Cartier center, an empty ambient or reduced subscheme, a reduced
reducible subscheme, and `X` contained in the center (empty strict-transform open). The
statement imposes no nonemptiness, stratum, or containment assumptions.

Searches for an existing declaration were run with:

* `msearch.py Q38 lem-trf-smooth-center-blowup-geometry leanfinder "blowup of a smooth scheme along a smooth closed center is smooth separated finite type and reduced strict transform"` — smoothness declarations were returned, but no blowup/strict-transform theorem matching this statement.
* `msearch.py Q38 lem-trf-smooth-center-blowup-geometry loogle "AlgebraicGeometry.Scheme.IdealSheafData.blowup, AlgebraicGeometry.strictTransform, AlgebraicGeometry.IsSmooth"` — no hits (the blowup name is not in Mathlib's index).
* `msearch.py Q38 lem-trf-smooth-center-blowup-geometry grep "blowup|strictTransform|Smooth" AlgebraicGeometry` — Mathlib smoothness declarations were found, but no matching theorem.
* `rg` over `WeilConjectures/` and `lean/Sheaf/`, plus `grep -rn` for the node id — the canonical blowup and strict-transform definitions were found in the recorded upstream modules, but no declaration of this theorem.

The file was compiled with `scompile.py`; it has no warnings other than the expected theorem
`sorry`.

## Second reading by Q38

I reread the node and the complete module signature. The base is exactly `Spec ℚ`; all
three properties of `P` are on its structure map, and smoothness of the center is on
`c ≫ p`, as required by the source's “two smooth S-schemes” argument. The conclusion uses
the canonical kernel ideal, global blowup, and specialized strict-transform declarations,
with all four finite-type/separated/smooth clauses and the reducedness clause present. The
empty-center and `X ⊆ C` cases remain admissible, and no maximum-stratum or containment
hypothesis was introduced. No mismatch was found.
