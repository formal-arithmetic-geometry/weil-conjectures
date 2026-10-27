## What changed

Restored `lean/WeilConjectures/PoincareDuality/Poincare.lean` from its current
quarantine archive. Repaired the proof of
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_poincareMap` using a proved
private categorical helper `poincareMap_isIso_aux`. The helper applies the
existing abstract Yoneda exchange theorem to invertible projection components,
then combines the exchange, the mapped purity inverse and the unit-to-internal-Hom
isomorphism by instance inference. The concrete proof specializes this helper
to the existing adjunctions, projection transformation and chosen purity.
This avoids unfolding the concrete Verdier exchange proof and its stale
monoidal-closed instance applications.

All existing signatures, attributes, public imports, documentation and
non-theorem bodies are preserved. The normalization of purity, trace, cup and
the Poincare morphism is unchanged. Only the proved private helper is added; no new public declaration is
introduced. The accompanying change record is
`coord/changes/J3-poincare-quarantine-restoration.md`.

## Proved and sorry left

The assigned module has zero holes before and after this repair. Holes closed:
none (0 of 0); holes added: none; split off: none. The repaired declaration is
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_poincareMap`.
`uncurry_poincareMap` retains its complete existing proof.

This is a quarantine repair, not a claim to close any holes in imported smooth
purity or Verdier-duality inputs. No sorry remains in the assigned module.

## No longer needed

None. Both original public imports are retained. The proof continues to use
the existing abstract Poincare morphism and Verdier exchange, with the same
projection-formula and smooth-purity route; no unit step is bypassed. No
module or DAG node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The assigned source is absent from `lean/` because it is quarantined, not
because it was withdrawn. The current archive has zero holes and its Tate
constructibility wrapper now belongs to `WeilConjectures.SmoothPurity.Defs`.
The rework row records a kernel application type mismatch involving the
bounded-constructible monoidal-closed instance in the old isomorphism proof.

The first compile against the published build reported unknown
`boundedConstructibleTateTwist` and `smoothPurityMap`, although the current
restored source of `SmoothPurity.Defs` contains both. Byte-identical copies of
that dependency and `WeilConjectures.PoincareDuality.Verdier` were used for the
sandbox compilation set; neither is an interface change or an additional
repair. Recompiling the current Verdier source removed the original kernel
mismatch. The private helper also makes the repaired proof independent of
unfolding the concrete Verdier exchange theorem.

The repository downstream script reports the item as an unknown module
because its live source is quarantined. Direct import searches over `lean/`
and `quarantine/` identify `Sheaf.Targets.PoincareUncurry` as its sole direct
module consumer. The restored declarations retain their exact signatures,
so that consumer requires no adaptation.

Validation: all three modules compiled together without warnings using
`lcompile.py --all`. Both dependency copies match the shared sources exactly.
The original 136-line archive and the restored module have zero `sorry`s.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
