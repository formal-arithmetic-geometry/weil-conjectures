## What changed

Replaced the body of
`AlgebraicGeometry.Scheme.lisse_tower_constant_stalk_models` by a complete Lean proof
from two strictly separate steps of its existing argument. The published signature,
all specified coefficient maps, and both existing public imports are unchanged.
Added private proof imports of `Sheaf.Paper.LisseTowerStalkLevelModels` and
`Sheaf.Paper.LisseTowerCompatibleStalkMarkings`, each containing one new named theorem.
No definitions, source-library modules, other existing Lean modules, or unit records change.

The first step constructs an algebraic normalized stalk tower with separate local
markings, finite cohomology and vanishing transfer. It supplies no coherent markings.
The second step takes an already supplied bounded finite normalized algebraic tower
and separate markings, and constructs compatible markings on a further cover. It
constructs no algebraic tower or finiteness/vanishing witnesses and does not assume
Noetherianity or an immersion. Neither statement restates the original conclusion.

The main proof derives each algebraic level bound from the corresponding original
bound and the vanishing-transfer implication. It applies the compatibility step to
each member of the first covering sieve, then uses `Sieve.bind` and
`GrothendieckTopology.bind_covering`. Factoring a member of the bound sieve retains
the first member's algebraic data and the refinement's coherent markings and lissity.
This assembly is proved in Lean and contains no holes.

Remote `lcompile.py --all` compiled the three modules in import order: compatibility
12.5 s, stalk construction 10.2 s, and the original theorem 17.0 s. The original
signature was also compared verbatim, and all Lean lines are at most 100 characters.
The delivery command performs the final compilation and preflight checks.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.lisse_tower_constant_stalk_models`
(node `lem-weil-pbc-lisse-tower-constant-stalk-models`). Its module now has zero holes.

Added two holes, each exactly `:= by sorry` in its own public theorem and module:

- `AlgebraicGeometry.Scheme.lisse_tower_stalk_level_models`
  (`Sheaf.Paper.LisseTowerStalkLevelModels`,
  node `lem-weil-pbc-lisse-tower-stalk-level-models`).
- `AlgebraicGeometry.Scheme.lisse_tower_compatible_stalk_markings`
  (`Sheaf.Paper.LisseTowerCompatibleStalkMarkings`,
  node `lem-weil-pbc-lisse-tower-compatible-stalk-markings`).

This is a decomposition: one original hole closed and two lower holes added,
net minus one. It is not a claim that the stalk construction or compatible
trivialization mathematics is fully proved. Both remaining statements have their
source, detailed proof in words, exact Lean signature, and DAG node. There are no
other holes in this delivery and no holes in definitions.

## No longer needed

None. No existing imports, declarations, modules, or mathematical dependencies are
pruned. The original theorem's immediate proof dependencies are now the two new
nodes; its former geometric and coefficient-comparison dependencies remain below
them. In particular, `CompatibleFiniteDerivedTrivializations` is still needed and
is neither withdrawn nor replaced by an empty module. The approved geometric-stalk
tool remains used by the stalk-construction argument.

## Where the brief, the DAG or earlier work was wrong

The declared dependency `Sheaf.Paper.CompatibleFiniteDerivedTrivializations` is
currently absent from `lean/` and preserved at its `coord/rework.tsv` quarantine
path. I read that preserved source and retained its node and dependency. I did not
change or withdraw it. Its interface concerns fixed-coefficient etale origins and
local comparison functors, whereas this item uses actual inverse-image ring sheaves
and specified completion-quotient restriction maps. The remaining compatibility
step records precisely that localization/coefficient transport and the all-pairs
normalization, rather than assuming the two interfaces are definitionally equal.

The bounds supplied in this item depend on the level; the Lean assembly uses them
separately and introduces no uniform bound or finite Tor-dimension assumption.
The geometric source is the bounded finite-cohomology adaptation of the normalized
stalk construction in Tag 09C6 and the Isom/stable-image argument in Tag 09BV; the
latter tag alone is originally a statement about sheaves, not the entire derived
interface in this item.

Edge cases checked in stating the new lemmas: empty bases and empty covering
members, zero complexes and zero coefficient rings, an empty cohomological interval,
nonuniform level bounds, and equal-index transitions. The stalk statement makes no
choice of data in a definition. The compatibility statement assumes the universal
normalization arrows: unrelated level isomorphisms alone are not used as if they
were compatible. Its conclusion retains the identity and all-pairs scalar squares.

The broad preflight inspection also encountered a pre-existing dependency cycle
between `lem-pc-ring-hom-extension-differential` and
`lem-pc-ring-hom-extension-differential-adjacent` below the original coefficient-data
dependencies. Neither node nor any edge of that cycle is changed by this packet.

## New nodes

`lem-weil-pbc-lisse-tower-stalk-level-models`, in
`dag/nodes/sec-proper-base-change/`, records only normalized algebraic stalk
construction, its finite/vanishing cohomology, pullback lissity and separate
level-dependent markings. It retains the existing origin, stalk, exactness,
tensor-pullback, completion and finite-ring local-constancy dependencies.

`lem-weil-pbc-lisse-tower-compatible-stalk-markings`, in the same directory,
records compatibility for a fixed supplied algebraic tower over any localized
pro-etale object. Its proof uses the existing simultaneous finite-derived
trivialization theorem, then the specified scalar comparison and cocycle laws.
It supplies no algebraic reconstruction or effective cone. Both new nodes keep
the original chapter, unit and blueprint ancestry; whole-blueprint searches for
stalk towers and compatible derived markings found no duplicate blueprint node.
No change record is needed because no existing signature or definition changes.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
