## Worker report

The module `Sheaf.TraceFormula.CatenaryAffineOpenCover` states
`AlgebraicGeometry.isCatenaryRing_of_affine_openCover`. It uses the existing Mathlib
scheme notion and the landed `IsCatenaryRing` predicate from
`Sheaf.RingTheory.ExcellentRing`. The theorem has no definitions and postpones its proof
with `sorry`.

The Lean rendering of each hypothesis and conclusion clause is:

- `S` is a scheme: `(S : Scheme.{u})`.
- The cover index is an arbitrary type at the scheme universe: `(I : Type u)`.
- The covering family is `U : I → S.Opens`.
- Covering means `(hU : iSup U = ⊤)`.
- Every member is affine: `(hUi : ∀ i : I, IsAffineOpen (U i))`.
- Every member's coordinate ring is catenary: `(hcat : ∀ i : I, IsCatenaryRing Γ(S, U i))`.
- For every affine open `V`, the conclusion is
  `∀ (V : S.Opens), IsAffineOpen V → IsCatenaryRing Γ(S, V)`.

The dependency declarations used are `AlgebraicGeometry.Scheme` and
`AlgebraicGeometry.Scheme.Hom` from the Mathlib match recorded by `def-pc-scheme`, and
`IsCatenaryRing` from `Sheaf.RingTheory.ExcellentRing` (the landed declaration recorded by
`def-exc-excellent-ring`). The latter defines catenarity by a finite upper bound on prime
chain lengths and equality of lengths of saturated chains, exactly the notion used by the
source statement.

Edge cases checked from the source statement and cover encoding: an empty index type can
satisfy the cover only for the empty scheme; an empty affine open has the zero coordinate
ring and no prime ideals, so the chain condition is vacuous; a singleton cover and a field
coordinate ring are included; no quasi-compactness, separatedness, Noetherianity, or
nonemptiness hypothesis is added; the index universe is `Type u`, matching `S.Opens`.

Searches made: the node's recorded LeanFinder, Loogle, LeanSearch, and grep searches found
no catenarity theorem in Mathlib or the project. I additionally searched with `rg` for
`IsExcellent`, `IsCatenaryRing`, affine-cover predicates, and `Γ` section-ring usage in
`lean/Sheaf` and the slopmaster2 source. These found the landed
`Sheaf.RingTheory.ExcellentRing` declaration and existing cover encodings, but no duplicate
statement of this theorem. A temporary `#check` probe confirmed the signatures of
`IsAffineOpen`, `Scheme.Opens`, `Scheme.Γ`, and `IsCatenaryRing`.

Compilation was run with:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q13 lem-trf-catenary-affine-open-cover lean/Sheaf/TraceFormula/CatenaryAffineOpenCover.lean`
It completed cleanly; the expected `sorry` warning is suppressed by the project options.

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
