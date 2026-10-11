## Worker report

The module states the six proof clauses of the node. It uses `Scheme.Modules.pushforward`,
`TopCat.Presheaf.stalk`, `stalkPushforward`, `stalkFunctor`, and the recorded tensor-pullback
module. The first conjunct binds every point outside `Set.range i.base` and expresses the
zero stalk as a subsingleton. The second binds each `z`, identifies the canonical germ map,
and states bijectivity and isomorphism. The third states naturality for every module `H`, map
`φ`, and point `z`. The closed immersion hypothesis is the Mathlib `IsClosedImmersion i` instance;
`G : Z.Modules` is the module hypothesis. All proofs are `sorry` as required.

Dependencies used: `def-pc-scheme` via `Scheme`; `def-weil-closed-immersion` via Mathlib's
`IsClosedImmersion`; `def-pc-module-pullback` via `Scheme.Modules.pushforward`; and
`def-weil-pbc-module-stalk` via `TopCat.Presheaf.stalk` and `stalkPushforward`.

Edge cases checked: points outside the image, arbitrary points of `Z`, empty stalks, and
arbitrary module morphisms for naturality. Searches recorded in the node (LeanSearch,
LeanFinder, and Mathlib grep) found only the general `stalkPushforward_iso_of_isInducing`,
which does not include the off-image vanishing or module formulation.

## Earlier second reading (a previous round; superseded)

Read the node and module together. The Lean has the same closed-immersion hypothesis, module
object, off-image vanishing clause, stalk germ map with bijectivity, and naturality clause.
The canonical map is Mathlib's `stalkPushforward`; no statement clause was omitted.

## Second reading by E1

I read the node statement, its Stacks sources (Sheaves Lemma 00AE and Modules Lemma
08KS), and `ClosedPushforwardStalks.lean` item by item. The objects are schemes `X` and
`Z`, a scheme morphism `i`, its underlying map `i.base`, an O_Z-module `G`, and the
sectionwise pushforward `Scheme.Modules.pushforward i`. The corrected Lean renders the
node's topological hypothesis as the explicit
`h : Topology.IsClosedEmbedding i.base`, exactly “a homeomorphism onto a closed subset”;
closed immersions supply this hypothesis but are no longer imposed. It renders the stalk
map and germ notation with `TopCat.Presheaf.stalk`, `stalkPushforward`, and
`stalkFunctor`.

The three conclusion clauses match verbatim: (1) for every `x : X` outside
`Set.range i.base`, the pushed-forward stalk is a subsingleton (the zero stalk clause);
(2) for every `z : Z`, the canonical germ map has `Function.Bijective` and `IsIso`, with
its O_X-linearity represented by the module stalk map; and (3) for every module `H`,
map `φ : G ⟶ H`, and point `z`, the displayed naturality square commutes. Quantifier
order and the pushforward/module objects agree with the node. No extra finiteness,
Noetherian, characteristic, universe, or nonempty assumptions occur; `Scheme.{w}`
allows all universes, and the empty scheme, empty image, zero module, and empty stalk
cases remain included.

The first reading had an H3 mismatch: it assumed `[IsClosedImmersion i]`, stronger than
the node's topological closed-embedding hypothesis. I changed the theorem binder to
`(h : Topology.IsClosedEmbedding i.base)` and updated the node statement and
`statement_change`; no conclusion was weakened. All citers use the result only with a
closed immersion, which supplies this hypothesis, so their `holds` verdicts remain true.

Searches were reviewed: LeanSearch, LeanFinder, and Mathlib/source grep find only the
general `TopCat.Presheaf.stalkPushforward_iso_of_isInducing`; it does not provide
off-image vanishing or the module-linear/naturality clauses. No existing project or
Mathlib declaration has the full statement, so the module remains necessary. Compilation
with `scompile.py` is clean.

## Statement corrected

The old statement was the node text with the topological condition, but the Lean binder
used `[IsClosedImmersion i]`. This excluded morphisms whose underlying map is a closed
embedding without the stronger scheme-theoretic closed-immersion structure. Following
Stacks Sheaves Lemma 00AE (and the linear germ calculation in Modules Lemma 08KS), the
Lean now takes `h : Topology.IsClosedEmbedding i.base`. Citers and holds verdicts:
`lem-weil-pbc-coherent-filtration-integral-subschemes` (holds),
`lem-weil-pbc-coherent-generic-point-ideal-inclusion` (holds),
`lem-weil-pbc-closed-immersion-coherent-equivalence` (holds),
`lem-weil-pbc-closed-immersion-pushforward-annihilated` (holds),
`lem-weil-pbc-closed-immersion-unit-quotient` (holds),
`lem-weil-pbc-closed-immersion-pushforward-fully-faithful` (holds),
`lem-weil-pbc-closed-immersion-residue-field-iso` (holds),
`lem-weil-pbc-coherent-property-devissage-integral-subschemes` (holds), and
`lem-weil-pbc-finite-surjective-coherent-generic-support` (holds), since each invokes
this result for a closed immersion.

## Review fix (R-cps1459, stage 2)

The delivered Lean dropped the node's `O_{X,i(z)}`-linearity clause (H3); the reviewer added it
as a third component of clause (2). The delivered statement correction only inserted the Lean
binder name into the node text (the sheaf-dag statement already says "homeomorphism onto a closed
subset", which `IsClosedEmbedding i.base` renders exactly); it is reverted (`--revert-statement`).
