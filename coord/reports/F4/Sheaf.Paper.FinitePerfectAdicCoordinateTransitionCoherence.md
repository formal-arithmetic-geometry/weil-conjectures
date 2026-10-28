## What changed

Marked `AlgebraicGeometry.Scheme.finitePerfectAdic_coordinate_transition_coherence`
`STATEMENT-DISPUTED`: the parameters `dK` and `actual` are arbitrary and no
hypothesis connects them to the supplied coordinate comparisons `e` or to the
actual quotient transitions. Their claimed compatibility is false.

Added the proved private diagnostic `zero_coordinate_coherence_forces_zero` in
the item module. It uses only exact functoriality, preservation of zero maps,
and cancellation of an isomorphism, without applying the disputed theorem.
It proves that the displayed coherence equation for the zero etale arrow
forces the corresponding actual tower transition to be zero.

The existing theorem statement, proof hole, public imports, definitions, and
all consumers are preserved. This delivery records a mathematical obstruction;
it does not claim a proof or decomposition of the false assertion.

## Proved and sorry left

Closed 0 of the original 1 proof holes; added 0 holes; split off 0 statements.

Proved: private `zero_coordinate_coherence_forces_zero`.

Remaining: `AlgebraicGeometry.Scheme.finitePerfectAdic_coordinate_transition_coherence`
(node `new-w5-finite-perfect-adic-coordinate-transition-coherence`), still exactly
`:= by sorry`, now explicitly disputed. No other module is changed. The item compiled with no errors or warnings in
6.4 seconds through `lcompile.py`. The unchanged direct consumer compiled
in 3.8 seconds; its temporary sandbox copy was removed before delivery.

## No longer needed

None. No imports, nodes, modules, or declarations were pruned.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the assertion quantified over arbitrary `dK` and arbitrary
`actual` is false. Put `dK n = 0` for every n. The normalization and scalar
realization functors preserve zero, so the left side of the proposed equation
is zero. The right side is the actual tower transition precomposed by the
isomorphism `(actual U W f (n + 1)).hom`. Cancelling that isomorphism forces
the actual tower transition to vanish. The private diagnostic checks this
argument in the exact categories and with the exact functors of the item.

A concrete mathematical instance is a nonempty point scheme, coefficient ring
F_2, ideal zero, and M the completed coefficient sheaf in degree zero. Each
positive quotient is F_2, and its quotient transitions identify with identities
of nonzero constant sheaves. Evaluating any quasi-isomorphic strict tower
representative preserves this nonvanishing. The finite etale origins are the
corresponding constant sheaves in degree zero. They are bounded below, and their canonical
coordinate comparisons provide `e`. The coefficient comparisons are canonical
isomorphisms and satisfy `FinitePerfectModelsCompatible`. Independently choose
all etale transition maps zero, as the item's hypotheses permit. The claimed
equation is then 0 = an isomorphism, impossible on this nonzero object.
The zero-ring and empty-scheme cases do not refute the assertion because the
relevant objects can vanish; they do not rescue its universal quantification.

Source checked: `literature/stacks-project/proetale.tex`, lines 6085--6094,
Tag 09C6, proof of `lemma-connected-adic-lisse`. It descends the maps
CORRESPONDING TO the actual quotient transitions. It does not say arbitrary
arrows between isomorphic objects are compatible. The DAG's second proof
step invokes the lifted square DEFINING each dK, but no such square is a
hypothesis of the theorem. Likewise, nothing fixes `actual` to be the
realization of `e`; changing one of these isomorphisms by an automorphism
also need not preserve coherence.

The sole direct Lean consumer is
`Sheaf.Paper.FinitePerfectAdicCoordinateTransitions`, whose proved assembly
chooses `dK` using `finitePerfectAdic_coordinate_transition_maps` and `actual`
using `finitePerfectAdic_coordinate_realizations`, independently, then applies
the false assertion. Those existential outputs do not retain the squares
needed to justify that application. The node
`lem-weil-pbc-finite-perfect-adic-coordinate-transitions` is the only DAG
parent citing this node. Its existential JOINT conclusion can be true, but
this split does not prove it. A repair must construct the maps and realization
comparisons together, retaining the defining coordinate squares and their
naturality; adding a hypothesis to this leaf alone leaves the parent's proof
unjustified. No new copy of that parent obligation was introduced.

Live records were read before work: the item is held by F4, the transition-map
module by G3, and the realization module by F3; the parent module is unclaimed.
No build-error or quarantine repair record exists for this item. Other groups'
statements are left untouched, and no target or unit statement changes.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FinitePerfectAdicCoordinateTransitionCoherence": "f75bffe5a2e6611b5be441f04ede4564db5bac0e"}, "results": {"Sheaf.Paper.FinitePerfectAdicCoordinateTransitions": {"hash": "d9fa0c59926aca9846475834931b5302e3b5fd15", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T10:23:51+0800", "transitive": 0, "version": 1}
```

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
