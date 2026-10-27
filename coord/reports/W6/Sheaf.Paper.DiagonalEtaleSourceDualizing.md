## What changed

Replaced the proof of
`WeilConjectures.PurityFiniteSetting.diagonalEtaleSourceDualizing` by the actual
composition of two factor equations, using functoriality and associativity.
The original statement, public import, and docstring are unchanged. The only
new imports of the item are private proof imports of `DiagonalEtaleAlphaSquare`
and `DiagonalEtaleRhoUnitSquare`.

Added `DiagonalEtaleRestrictedDualizingData`, whose
`DiagonalEtaleComparison.restrictedDualizingTransport` is constructed explicitly:
pass to ordinary coordinates with `Dnc.pullComparison`, use the normalized
exceptional locality for jO and f|V on the monoidal unit, transport across the
proved equality jO≫f|V=vO≫g|V, invert the locality for vO and g|V, and invert
the second site comparison. This construction contains neither sourceTransport
nor alpha, rho, unitChange, deformation, normal transport, or vector integration.
Its data contain no sorry or choice of an arbitrary existence witness.

The alpha square compares only the diagonal source and alpha factors with that
transport. The rho/unit square compares the same transport with target-open
restriction and coefficient-unit change, and contains no diagonal source or
alpha. These are distinct parts of the existing three-step argument, not a
renaming of the item's equation. Each is in its own new module with its source,
complete proof in words, and a matching DAG node. The item node now records the
Lean combination of these two equations. Existing dependency nodes were read
and are retained below the new steps.

Validation: `lcompile.py --all` accepts all four modules in import order, including
the complete composition proof of the unchanged item statement.

## Proved and sorry left

The old local hole in
`WeilConjectures.PurityFiniteSetting.diagonalEtaleSourceDualizing`
(node `lem-pur-diagonal-etale-source-dualizing-square`) is replaced by a complete
Lean proof from the two lower factor statements. There is no sorry left in the
item module or the new data module.

This is a decomposition, not a completed proof of the underlying compatibility:
one upper hole removed, two lower holes added, net holes closed minus added = -1.
The two remaining holes introduced by this delivery are exactly:

- `WeilConjectures.PurityFiniteSetting.diagonalEtaleAlphaSquare`, node
  `lem-pur-diagonal-etale-alpha-square`;
- `WeilConjectures.PurityFiniteSetting.diagonalEtaleRhoUnitSquare`, node
  `lem-pur-diagonal-etale-rho-unit-square`.

Both proofs are exactly `:= by sorry`. No hole is put inside a definition or a
private declaration. Rank zero, empty O, identity etale maps, and an arbitrary
smaller O inside the target preimage were checked in the stated arguments. In
particular the rho/unit proof explicitly factors an arbitrary O through the full
preimage rather than treating its square as Cartesian.

## No longer needed

None. No existing import, declaration, module, or dependency node is removed.
The original six planned proof dependencies remain needed below the alpha and
rho/unit steps, rather than being asserted pruned. No unit statement or unit
proof step is bypassed. The only imports added to the existing item are the two
proof imports used by its final proof.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The originally declared dependencies provide the
smooth base-change mates, their invertibility, a section naturality theorem
conditional on a rectangle equation, and left-adjoint etale/base-change
interchange. They do not directly state the two factor equations instantiated
with this constructed sourceTransport and arbitrary target-open O.
`ChartDiagonalSourceSquare` is not a usable shortcut: import_direction.py reports
that it already reaches the item, so importing it would create a cycle.

The source read was latest blueprint
`sec-smooth-purity/sk-prop-sp-orientation/thm-pur-diagonal-dualizing-object.proof.md`,
Steps 1--2 and canonicity paragraph, together with
`sk-prop-sp-orientation-charts.proof.md`, especially Step 3. The latter explains
source-etale exceptional locality, independently of deformation and integration.
The new split separates precisely that alpha compatibility from target-open and
coefficient-unit compatibility.

Mathlib searches ran through msearch: LeanFinder for diagonal section dualizing
naturality (eight scheme-diagonal/pullback hits, no dualizing equation), Loogle
for `CategoryTheory.Functor.map_comp` (six hits, including the lemma used in the
assembly), and grep for the two project mate/locality names (zero Mathlib hits).
Project searches located the declared dependencies and the cyclic chart shortcut.
Blueprint duplicate searches included alpha and source-etale; no acyclic blueprint
statement supplies either new factor equation. All existing shared modules remain
unchanged, so there are no forced consumer adaptations or change records.

## New nodes

`def-pur-diagonal-etale-restricted-dualizing-transport` attaches the explicitly
constructed transport over V, independent of the source invariant and alpha.
Its new module is `Sheaf.Paper.DiagonalEtaleRestrictedDualizingData`; zero holes.

`lem-pur-diagonal-etale-alpha-square` attaches the alpha-only naturality equation
in `Sheaf.Paper.DiagonalEtaleAlphaSquare`. Its proof plan uses the existing
source-etale/base-change interchange and section inverse-exchange naturality,
followed by cancellation of common-source alpha. One hole.

`lem-pur-diagonal-etale-rho-unit-square` attaches the independent target-open and
coefficient-unit equation in `Sheaf.Paper.DiagonalEtaleRhoUnitSquare`. Its proof
plan first handles the full preimage Cartesian squares, then arbitrary O by
restriction and locality composition, and finally unit naturality. One hole.

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
