## What changed

Replaced the proof hole of
`AlgebraicGeometry.Etale.exactCompactificationUnit_composition` by a reduction to the
forward unit equation on one fixed compatible tower. The existing theorem statement,
its docstring and its two public imports are unchanged. The item privately imports
`ExactCompactificationUnitRefinement` and the new `ExactCompactificationUnitTower`.

The proof uses the concrete `ofComp` tower already defining
`unboundedEtaleLowerShriekCompIso`. It derives its sheaf normalization from `nh`, `ne`,
`nhe` and `nσ`; applies the fixed-tower equation; and transports both end units by
`exactCompactificationUnit_refinement`. Private proved helpers establish naturality of
`exactCompactificationUnit` under an exact sheaf natural isomorphism, and the categorical
inversion/cancellation of the resulting forward unit square. There is no change to a
shared interface, a definition, a target, or the unit route. The theorem uses a scoped
`maxRecDepth 4096` to elaborate the concrete tower conversions; compilation keeps the
standard time limit.

Validation: `lcompile.py` compiled the item without warnings in 24.6 seconds and the
new tower module in 30.7 seconds (with its one expected proof hole). The original
statement and public-import lists were compared verbatim with the current source.
Both DAG proof-dependency lists equal the union of their proof steps’ uses. No existing
consumer requires adaptation because no shared interface changes.

## Proved and sorry left

This is a decomposition, not a net closure of a mathematical hole.

- Original hole removed:
  `AlgebraicGeometry.Etale.exactCompactificationUnit_composition`
  (`lem-sfb-exact-compactification-unit-composition`). Its proof from the fixed-tower
  theorem and the existing refinement theorem is complete.
- One new hole:
  `AlgebraicGeometry.Etale.exactCompactificationUnit_tower`
  (`lem-sfb-exact-compactification-unit-tower`). Its entire proof is `by sorry` in its
  own new module, with the source and resolution argument in its docstring and node.
- No other holes added or left in the delivered modules. The existing imported
  `exactCompactificationUnit_refinement` is used as stated; it is not changed here.

The new theorem isolates the forward calculation on a supplied single tower: it has
only F and G, their two local factorizations, and a normalized factorization of their
composite. It does not assume invertibility of the units and does not mention H, σ,
ch, ce, che, a family of compactifications, or the chosen unbounded compositor.
The item proves the independent source-naturality, refinement-transport and inverse
cancellation steps. The unresolved work is matching the existing chain-resolution
calculation `properOpenTowerDerivedUnit` to these exact source functors and the canonical
fixed-tower compositor. No definition obtains data from this new proof hole.

## No longer needed

No original public imports were removed: both occur in the unchanged statement.
The separate dependency `lem-weil-pbc-compatible-compactification-triangle`
(module `Sheaf.AlgebraicGeometry.CompatibleCompactificationTriangle`) is unnecessary
for this proof. The proof uses `Compactification.ofComp` directly, exactly as the
actual compositor does, so no additional compatible-triangle existence result is used.
This is a local dependency removal, not a claim that other users of that module vanish.

`lem-sfb-proper-open-tower-derived-unit` and
`lem-cbc-proper-support-sheaf-composition` remain needed by the new fixed-tower node;
they are no longer direct proof dependencies of the item. Localization remains a direct
dependency through the proved naturality helper. There are no withdrawn modules or nodes.

## Where the brief, the DAG or earlier work was wrong

The planned chain-level theorem does not directly state the unit equation for the exact
functors in the item: it gives resolution paths for ordinary proper/open functors.
The remaining matching argument is now precisely stated on a fixed tower. The original
DAG also called for a separate compatible-triangle existence theorem, although the
compositor already has its own concrete tower. No false statement was identified.

Edge cases of the new theorem: identity and empty schemes, zero functors where the
specified isomorphisms exist, and the zero coefficient ring give the same unit-pasting
identity. The argument assumes no exactness of a proper direct image and no invertibility
of a normalized unit. The two exact functors make the composite exact, supplying its
ordinary `mapDerivedCategory` without additional hypotheses.

## New nodes

`lem-sfb-exact-compactification-unit-tower`, in
`dag/nodes/sec-six-functors-basics/lem-sfb-exact-compactification-unit-tower.json`, states
only the fixed compatible-tower forward calculation (the local calculation in steps
1–2 of the original plan). Its module is
`Sheaf.AlgebraicGeometry.ExactCompactificationUnitTower`; its node cites the existing
proper/open resolution calculation, the section normalization, and localization.
It keeps the parent unit `sk-lem-geo-affine-local`. No change record is required because
no existing declaration signature, definition, visibility or public import is changed.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
