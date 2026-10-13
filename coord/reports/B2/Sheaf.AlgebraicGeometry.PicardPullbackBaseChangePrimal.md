## What changed

Proved `AlgebraicGeometry.Scheme.picard_pullback_base_change_primal` with its exact existing
signature. Five private helpers express the chosen adjunction, the pushforward-square
isomorphism, the canonical base-change/unit equation, unit transport along a scheme
isomorphism, and tensor-pullback preservation of finite local freeness (two definitions
and three theorems in total). All helpers are fully proved or concrete constructions.

The proof applies `isIso_tensorPullback_unit_of_finiteLocallyFree` at g and h ≫ g, pastes
pullback squares, transports the latter unit through the resulting scheme isomorphism,
cancels the two unit isomorphisms in the canonical-map equation, and uses naturality
along e. The canonical-map equation is proved by `unit_conjugateEquiv_symm`, not assumed.
The rank-zero and empty-scheme cases are covered by the categorical argument.

Added private `WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent` for its proved
`Modules.isFiniteLocallyFree_pullback` instance. Removed public Dual, made the finite-unit
import private, and added public Mathlib scheme Pullbacks for the instances required by
the unchanged signature. These import changes are recorded in
`coord/changes/picard-primal-proof-imports.md`. Updated the existing node's proof and
proof_origin; its proof_deps remain exactly the two existing dependencies actually used.

Local compilation passed without warnings. The static import pruning check passed. The unchanged direct importers
`Sheaf.AlgebraicGeometry.PicardPullbackBaseChange` and
`Sheaf.AlgebraicGeometry.PicardPullbackBaseChangeDual` also compiled against the new module
in a scratch overlay, without warnings or adaptation.
Sources read: https://stacks.math.columbia.edu/tag/0BDP (projection-formula paragraph)
and https://stacks.math.columbia.edu/tag/01E8, plus the Mathlib adjunction/mates source.
Searches run through msearch.py: leanfinder for base change on pulled-back objects,
loogle for CategoryTheory.Adjunction.unit, and grep for tensorPullback finite freeness.
The abstract-pullback instance was found by rg in the source library.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Scheme.picard_pullback_base_change_primal`
(node `lem-sc-picard-pullback-base-change-primal`). No sorry remains in this module.
Added zero holes and no new statements awaiting proof. This is a proof from the existing
finite-unit theorem, not a new decomposition. That imported theorem,
`AlgebraicGeometry.Scheme.isIso_tensorPullback_unit_of_finiteLocallyFree`
(node `lem-sc-finite-locally-free-tensor-unit`), is now proved in the repository, but its compiled axiom closure still contains
`sorryAx` from existing dependencies. The compiled primal theorem likewise contains
`sorryAx`; this delivery closes its own hole without claiming target acceptance.

## No longer needed

Removed `WeilConjectures.AlgebraicGeometry.Modules.Dual`: primal base change uses no dual,
invertible-module projection formula, or duality compatibility. The finite-unit module
remains needed, now as a private import. No existing proof-dependency node is pruned:
both finite-unit and module-base-change-map-open-restriction remain needed. Only the
latter module's definition and naturality are used; its open-restriction theorem is not
needed for this argument. No claim is made that Dual leaves the global target closure,
as other modules still need it. No blueprint-unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG's single step hid the compatibility of the canonical base-change morphism and
transport from a single to an iterated pullback. Those are now explicit, proved Lean
calculations. Finite local frames are needed only in the existing finite-unit theorem;
there is no additional frame calculation in the primal base-change proof. Removing Dual
also revealed that it supplied scheme pullback instances publicly, so the smaller
Mathlib Pullbacks import replaces that accidental dependency. No mathematical statement
or target definition was changed.


## Second reading by B2

1. Compared the sole delivered module and node against the repository with diff, and
   checked the existing theorem signature byte for byte by script: identical. No
   public definition or target statement changed. The import interface change is
   declared in `coord/changes/picard-primal-proof-imports.md`. Verdict: pass.
2. Compiled the module locally without errors or warnings. No sorry, axiom, unsafe,
   opaque, implemented_by, or extern appears in the delivered code. Printed axioms
   for all five private helpers and the public theorem in a scratch copy: the helpers
   use only propext, Classical.choice, Quot.sound; the theorem additionally uses
   sorryAx through the existing finite-unit dependency. The chosen adjunction is
   pinned by its sectionwise unit formula in exists_tensorPullbackAdjunction; it is
   not an arbitrary witness of an unconstrained existence statement. The square
   isomorphism is explicitly composed from existing concrete isomorphisms. Verdict: pass.
3. No statements were split off and no holes added. Read each proved helper: the
   base-change identity is precisely the composite-unit mates identity, transport
   uses a pushforward equivalence along a scheme isomorphism, and local freeness
   uses uniqueness of left adjoints. None adds rank, nonemptiness, or geometric
   hypotheses, so rank zero and empty schemes remain covered. Independent msearch
   grep for unit_conjugateEquiv_symm, isFiniteLocallyFree_pullback and
   isIso_app_iff_of_iso, plus rg in both library roots, found the underlying facts
   already used and no shorter ready-made primal theorem. Verdict: pass.
4. Read the reduction from the target downward. It applies the existing finite-unit
   result twice, pastes the squares, cancels isomorphisms in the proved canonical-map
   identity and transports along e. Both old proof dependencies remain used; there
   are no omitted pruned nodes. Dual is unused and removed, finite-unit and
   FiniteDescent are private proof imports, and scheme Pullbacks supplies instances
   in the unchanged public signature. Both unchanged direct importers compile in
   the scratch overlay. Read dag/units/sk-prop-av-cube.json: its realized fields are
   empty, and this reduction changes none of its statement or step routes. Verdict: pass.
5. Compared the node record: only proof and proof_origin change, proof_deps is the
   union of step uses and retains both existing dependencies. The four steps match
   the Lean reduction, including finite-local-freeness transport, square pasting,
   the unit equation and naturality. No new nodes need registration. Verdict: pass.

Second reading changed only this report: checked both direct importers and corrected
its stale claim that the finite-unit theorem itself still has a sorry. Its current
compiled closure, and hence the primal theorem, still use existing sorryAx. The Lean
proof, node and import change record needed no repair. Closed one named hole, added
zero; no proof-dependency node or globally unreachable module is claimed pruned.
