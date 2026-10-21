## What changed

Proved `SheafOfModules.SequenceProjection.derivedAdjunction` without changing its
signature, the three existing public helper declarations, or any public imports.
All added constructions and lemmas are private and proved.

The ordinary left functor uses the existing normalized scalar-extension models.
Its transitions transpose the level units through the canonical scalar-restriction
composition isomorphisms. Local tensor generators prove the strict system laws,
functoriality and the required transition formula. The right functor is the actual
categorical limit of the restricted level diagram. Its projections satisfy the
full compatible-family existence and uniqueness assertion. Transposing at each
level constructs the ordinary adjunction and proves its specified tensor formula.

A single independent-coefficient flat-term K-flat resolution supplies the resolving
class. Componentwise detection and the existing scalar models prove preservation
of its quasi-isomorphisms. The resolving-class theorem constructs the universal
left derived pair; the existing homotopy-to-cochain comparison helper transfers
its universal property. The Grothendieck abelian structure of strict systems gives
K-injective resolutions and the universal right derived pair. The existing
resolving derived-adjunction theorem supplies the normalized chain-map equation.
The representative comparison is explicitly the inverse of `L.map (Q.map q)`
followed by the left comparison.

Updated the item's DAG proof, proof dependencies and proof origin to this route.
No new node, statement, axiom, definition repair or consumer adaptation is needed.
The static interface check requests a record for the added proof-context commands;
`coord/changes/sequence-projection-derived-adjunction-proof-context.md` documents
them and the two proved private instances. Its downstream scan finds zero consumer
modules. All writes are confined to the assigned sandbox.

## Proved and sorry left

Closed one hole: `SheafOfModules.SequenceProjection.derivedAdjunction`
(node `lem-coef-sequence-projection-derived-adjunction`).
Added zero holes. There are zero `sorry`s left in the item and no new modules.
This is a proof from existing declarations, not a decomposition.

Validation: the public theorem signature was compared verbatim with the shared
source; every Lean line has at most 100 characters. The complete module compiled cleanly through
`lcompile.py` in 32.9 seconds. Delivery also runs the server compilation and
declaration/axiom checks. The empty site, zero coefficient rings, identity transitions, constant
coefficient systems and nonflat structural ring maps require no special case:
all constructions use categorical limits and the scalar adjunction, and only
K-flat representatives are used for quasi-isomorphism preservation.

## No longer needed

Removed these direct proof imports:

- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`: level scalar
  adjunctions and the explicit compatible-family Hom equivalence suffice.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`: use the
  coefficient-universe Grothendieck theorem for strict systems instead.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`: the existing universal cochain
  right-derived construction `CategoryTheory.exists_derived` gives both required
  clauses directly.
- `Sheaf.Paper.RingedTopoiDerivedPullback`: scalar preservation and componentwise
  detection give the resolving class without transporting a whole geometric
  morphism through site-universe equivalences.
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`: the required
  termwise adjunction API is already publicly imported by the normalization
  theorem; this redundant direct import is unnecessary.

Accordingly removed the direct proof dependencies and their obsolete top-level
`tool_uses` approvals for `lem-weil-pbc-ringed-topoi-module-adjunction`,
`prop-pur-kinjective-resolutions-exist`, `lem-weil-pbc-kinjective-total-derived`,
and `lem-weil-pbc-ringed-topoi-derived-pullback`. The generic termwise adjunction,
K-flat resolution and resolving normalization remain needed. The sequence-site
interpretation remains needed through the strict-system Grothendieck theorem.
No source declaration or module is withdrawn; some removed direct dependencies
may still be required transitively by existing library declarations.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan is valid, but its general ringed-topos pullback interface
fixes both site universes and the coefficient universe together. The item has
independent `u`, `v`, `w`, `d` and assumes only essential smallness in `w`.
Likewise, the listed K-injective resolution theorem uses coefficients at a
maximum of the raw site universes. The existing scalar cochain models and the
strict-system Grothendieck theorem have precisely the independent-universe
interfaces needed here. They realize the same scalar/limit and resolving/K-injective
argument directly, avoiding otherwise unnecessary site-universe transport.
The unit's statement and route are preserved; its recorded `realized` lists are
empty, and no unit or chapter record is changed.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
