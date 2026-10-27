## What changed

Replaced the proof hole of `WeilConjectures.SemilinearSections.semilinearGeometryOrdinary`
by a proof from two separate ordinary system construction statements. The original signature,
`GeometryOrdinary` fields, public import, derived bridge definitions and subtype equalities
are unchanged.

Added `Sheaf.Paper.SemilinearModuleAdjunction`, with a complete proof of
`normalizedModuleAdjunction_exists`. This retains the actual underlying set-sheaf transpose
from the existing product-preserving module construction. The proof uses the existing proved
private construction and linear-map helpers through private `import all` imports; it changes
no adopted source module.

Added `Sheaf.Paper.SemilinearOrdinaryInverseSystem` and
`Sheaf.Paper.SemilinearOrdinaryDirectSystem`. The first isolates assembly of the exact inverse
system and its normalized horizontal transitions. The second assumes that inverse system
and normalized coefficient-level adjunctions, and isolates assembly of the direct system
and its component Hom bijection. It does not assert the system adjunction or its unit laws.
Each is strictly part of the original construction.

The item proves left exactness of the specified level inverse images by reflecting finite
limits through their underlying-sheaf functors. Their newly constructed adjunctions give
colimit preservation and additivity. Joint faithfulness of ordinary system evaluations,
the two evaluation naturality squares and level adjunction naturality prove both naturality
laws for the system Hom bijection. `Adjunction.mkOfHomEquiv` then gives the system adjunction.
Transposition of identity maps proves both the evaluated system unit equation and its
normalization by the original topos unit. Right-adjoint additivity follows formally.
The supplied towers and inverse images are retained verbatim.

Only the item and new modules and their node records are changed. No existing interface
or consumer requires adaptation.

Validation: `lcompile.py --all` compiled all four delivery modules successfully.
The item took 24.2 seconds, within the 60-second limit. No transparency overrides
or profiling options are present in the delivery.

## Proved and sorry left

Original hole closed by decomposition:
`WeilConjectures.SemilinearSections.semilinearGeometryOrdinary`
(`lem-coef-semilinear-ordinary-geometric-realization`). Its proof and all combining
naturality, exactness, additivity and unit calculations contain no `sorry`.

New fully proved theorem:
`WeilConjectures.SemilinearSections.normalizedModuleAdjunction_exists`
(`lem-coef-normalized-module-adjunction`).

Two new holes remain, each the entire proof of a public named theorem:

- `WeilConjectures.SemilinearSections.ordinaryInverseSystem_exists`
  (`lem-coef-ordinary-inverse-system`).
- `WeilConjectures.SemilinearSections.ordinaryDirectSystem_exists`
  (`lem-coef-ordinary-direct-system`).

This is a decomposition, not a net proof: one original hole closed, two holes added,
zero holes left in the item itself. There are no holes in data, definitions or private
helpers. No arbitrary object is defined by choosing a witness of an unproved existence
statement: the two witnesses are eliminated only inside the theorem proof.

## No longer needed

No existing module is withdrawn, and no original import is removed. No claim of global
pruning is made. The original module-transport and independent module-adjunction modules
remain required by the proved normalized level adjunction, including its private helpers.
The parent now names the three precise construction dependencies; the original semilinear
system and geometric interfaces remain in its public import closure.

The already stated `geometricSystemOrdinaryComparison` provides an unnormalized comparison
on `StrictRingSystem` with additional singleton/scalar data. Its statement does not provide
the required identity-on-sections evaluation or the whole direct-image construction, so
it cannot close the item by application. The existing normalized scalar-restriction
comparison is recorded in the inverse construction's proof dependencies for reuse.

## Where the brief, the DAG or earlier work was wrong

The original dependencies state coefficient-level constructions but do not state either
assembly of normalized inverse systems on the sequence site or restriction of the actual
level transposes to system morphisms. The original independent module-adjunction theorem
also discards the underlying transpose equation needed by this item. This delivery proves
that retained normalization from its existing construction helpers and separates the two
remaining system arguments. It does not simply move `GeometryOrdinary` existence to a new
name, and does not assume a system adjunction or either desired unit equation.

Edge cases checked in the statements and proof plans: equality indices use identity
transitions; composites use the actual tower maps; zero coefficient rings are allowed;
there is no coefficient-flatness, boundedness, K-injective, or derived-evaluation assumption.
The unit's statement and route are unchanged. The newest blueprint unit was read from
`literature/blueprint/latest/blueprint/sec-six-functors-basics/`.

## New nodes

`lem-coef-normalized-module-adjunction` records the fully proved coefficient-level
adjunction and its underlying transpose, in `Sheaf.Paper.SemilinearModuleAdjunction`.
It strengthens the retained output of the existing independent module-adjunction
construction without changing that declaration.

`lem-coef-ordinary-inverse-system` records only exact ordinary inverse-system assembly,
identity-on-sections evaluation and normalized scalar-restriction/horizontal maps, in
`Sheaf.Paper.SemilinearOrdinaryInverseSystem`. It assumes the level exactness already
proved by the parent and contains no right-adjoint conclusion.

`lem-coef-ordinary-direct-system` records only the direct-system functor, its normalized
evaluation and component Hom bijection, in `Sheaf.Paper.SemilinearOrdinaryDirectSystem`.
The inverse system and the normalized level adjunctions are genuine previously supplied
inputs. Naturality and both unit equations are proved in the parent, not split off.

All three nodes have source citations, complete proof plans and the actual Mathlib search
records. No change record is needed because existing signatures and definitions are unchanged.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
