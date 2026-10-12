## What changed

Proved `AlgebraicGeometry.Etale.scheme_torsor_pullback_equivariant_hom_isIso` in
`Sheaf.AlgebraicGeometry.SchemeTorsorPullbackEquivariantHomIsIso`, with its statement
and docstring unchanged. The existing inverse-image clause of
`Sheaf.Torsor.etale_torsor_h1_functoriality` supplies a torsor T, an underlying sheaf
isomorphism e, and compatibility with the units. Transport f to q = e.inv ≫ f.
The simultaneous representative theorem gives a common covering sieve for a group
section and e.inv(x). The unit equations and naturality prove equivariance locally;
separatedness proves it globally. `Sheaf.Torsor.Iso.ofHom` makes q invertible, and
f = e.hom ≫ q finishes the proof.

Added proof imports `Sheaf.CategoryTheory.Sites.EtaleTorsorH1Functoriality` and
`Sheaf.AlgebraicGeometry.EtaleInverseImageJointRepresentatives`. Updated the item's
DAG proof, proof_deps and proof_origin to this argument. No definitions or statements
changed, and no new modules or nodes were introduced.

The two added nodes belong to the curve-estimates unit and are used as generic tools:
`lem-sc-etale-torsor-h1-functoriality` supplies only its general inverse-image torsor
construction clause, and `lem-sc-etale-inverse-image-joint-representatives` supplies
common local representatives. Neither replaces a unit statement or a step of the
proper-base-change unit. Both modules have complete proofs in the current source;
the delivery uses their interfaces and leaves their existing dependencies alone.

The proof handles empty objects by the covering-sieve and separatedness statements,
and does not assume a global torsor section. No finiteness argument or representative
for R is needed. Local representatives are used only in the proof; no definition
chooses data from an unproved existence theorem.

## Proved and sorry left

Closed the single hole:
`AlgebraicGeometry.Etale.scheme_torsor_pullback_equivariant_hom_isIso`
(node `lem-weil-pbc-scheme-torsor-pullback-equivariant-hom-is-iso`).
One of one holes closed; zero holes added or split off. No sorry remains in the
item's module. This is a proof from existing named declarations, not a claim that
their full transitive dependency closure is sorry-free.

Validation: the local single-file compiler accepted the complete proof without
warnings. The delivery dry run performs the final compiler and preflight checks.

## No longer needed

Removed proof imports:
- `Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`.
- `WeilConjectures.CategoryTheory.Sites.Torsor` (already public through the statement imports).
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (already public through the statement imports).

The item's proof no longer directly uses
`lem-weil-pbc-etale-inverse-image-algebraic-structures`; its preservation argument
is supplied through the two existing interfaces. This is removal of a direct
proof dependency, not a claim that its module is absent from the target closure.
The torsor and inverse-image definition nodes remain needed. No other planned
node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

The old DAG plan correctly describes the argument, but omits the now available
inverse-image construction and simultaneous-representative interfaces. Those
interfaces make the whole argument expressible without new intermediate holes.
No mathematical error was found; no statement was weakened or changed.

## Second reading by D2

1. **Unchanged interface — pass.** Compared the only delivered Lean module against
   the repository with `diff -u`, and checked its theorem signature and docstring
   byte for byte. Only the proof body and private proof imports change. No definitions,
   public imports, declaration signatures, or statement changes are delivered.
2. **Proof and axioms — pass with existing dependency holes.** Independently compiled
   the module with `lcompile.py`: clean, no warnings (4.6 seconds). Scanned the source:
   no sorry or forbidden declarations/options. A scratch copy with `#print axioms`
   reports precisely `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for
   the theorem. Both supporting theorem interfaces also report `sorryAx`; their
   source proof bodies are complete but their transitive dependencies remain open.
   This closes the item's local hole, not its entire axiom closure. No data definition
   is introduced: the existential torsor and representatives are eliminated inside
   a proposition proof, and no arbitrary witness is exported as a definition.
3. **Split statements — pass (none).** No new theorem, module, node, or lower hole
   is introduced. Read the inverse-image clause and simultaneous-representative
   interface actually used. Checked trivial coefficients and empty test schemes:
   the argument uses torsor local nonemptiness and sheaf separatedness over a covering
   sieve, never a global section or a nonempty test object.
4. **Route and pruning — pass.** Searched the local library and upstream torsor
   implementation using unit equivariance, inverse image, and pullback terminology.
   `Torsor.Iso.ofHom` is the existing final result and requires precisely the full
   equivariance proved here. `etale_torsor_unit_action_unique` already assumes two
   underlying isomorphisms, so cannot prove invertibility of the supplied morphism.
   The lifting-torsor interface requires extra short-exact-sequence data and gives
   no shorter direct application. The two private imports each supply a used theorem;
   the public imports support the original signature. The old proof dependency
   `lem-weil-pbc-etale-inverse-image-algebraic-structures` is the sole removed direct
   node dependency and is recorded above. No claim of target-closure module pruning
   is made. Read `dag/units/sk-thm-p1.json`'s `realized`: none of its statement or
   step nodes is bypassed or changed; this is a local torsor comparison argument.
5. **DAG agreement — pass.** The existing node changes only `proof`, `proof_deps`,
   and `proof_origin`. Its three steps match construction of T and e, local-to-global
   equivariance of q, and `Iso.ofHom` followed by composition. `proof_deps` is exactly
   the union of the steps' `uses`; the two new dependencies identify the existing
   declarations imported and applied in the proof. All remaining metadata is unchanged.

Second-reading changes: appended this audit and the explicit axiom-closure limitation
only. The Lean proof, imports, and node update required no repair.
