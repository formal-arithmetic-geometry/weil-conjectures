## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.exists_open_factorization_of_finite_constant_map`
by a compiling finite-free-cover argument. `Module.Finite.exists_fin'` supplies a
surjection from `Λ^(Fin n)` to `N`. Apply the new finite-free lifting lemma after
precomposing both maps with this surjection. Constant sheaf formation and open restriction
preserve epimorphisms. Their composite is a strong epimorphism in the abelian category of
module sheaves, so its lifting property against the restricted monomorphism descends the
free lift to `N`. The right triangle is precisely the original conclusion.

The original signature and docstring are unchanged. The only new proof imports are
`Mathlib.RingTheory.Finiteness.Cardinality` and
`Sheaf.AlgebraicGeometry.FiniteFreeConstantMapOpenFactorization`. A trial import of
`WeilConjectures.ConstructibleSheaf.Pullback` and a trial import of
`Mathlib.CategoryTheory.Abelian.Basic` proved unnecessary and were removed.
Both delivery modules compile without warnings under `lcompile.py --all`.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.exists_open_factorization_of_finite_constant_map`
(node `lem-weil-pbc-finite-constant-map-open-factorization`). The original module has no
remaining sorry.

Added: `AlgebraicGeometry.Scheme.exists_open_factorization_of_finite_free_constant_map`
(node `lem-weil-pbc-finite-free-constant-map-open-factorization`), in the new module
`Sheaf.AlgebraicGeometry.FiniteFreeConstantMapOpenFactorization`.
This is a decomposition: one upper hole closed, one strictly simpler free-source hole
added, net holes zero. The entire descent through possibly infinitely many relations is
proved. The remaining theorem concerns only lifting and descending finitely many free
basis vectors, with no relations to impose. It is not the original theorem renamed:
the source is restricted to a finite free module, and a genuine strong-epimorphism
argument extends it to arbitrary finitely generated modules.

Edge cases: `n=0`, a zero coefficient ring, and `N=0` are included. The free theorem's
proof in words specifies the zero map on all of X when its source is zero. The original
argument does not require a nontrivial source or a nonempty chosen basis. No finite
presentation of N, Noetherianity, irreducibility, or constancy of G was added.

## No longer needed

No original import was removed and no module is globally pruned. The old geometric
proof dependencies now belong to the new finite-free lifting node; they remain needed
there. They are no longer direct dependencies of the original node, whose proof now
uses the finite-free lifting node and the finite-free cover/strong-epi argument.
The old proof dependencies no longer used directly by the original node are
`def-weil-pbc-geometric-stalks`,
`lem-weil-pbc-constant-sheaf-maps-global-sections`,
`lem-weil-pbc-flat-lfp-open`, and
`lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`.
All four remain dependencies of the new free-source node, so none is globally pruned.
No blueprint unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The old plan's listed dependencies are infrastructure: cofiltered neighbourhoods,
openness, and the constant-sheaf adjunction. None states the finite-generator lifting
and descent step itself. The explicit remaining free-source theorem isolates that
step. The plan's final claim that monicity kills all relations has now been formalized
via the standard strong-epimorphism lifting property, avoiding a section-level
presentation of every relation. No statement was disputed or changed.

## New nodes

`lem-weil-pbc-finite-free-constant-map-open-factorization` states the open factorization
only for the standard finite free module. Its source is Stacks Tag 09BH (3), generator
lifting and descent, and its complete proof in words is in the module and node. Searches
used LeanFinder, Loogle, Mathlib grep, and both project roots; LeanSearch was unavailable.
The node retains the geometric dependencies of the original plan. No change record is
needed because no existing statement or definition changed.

## Second reading by S2

1. Compared the delivered original module with the repository using `diff`.
   The existing theorem signature and docstring are byte-for-byte unchanged;
   only its proof and two plain proof imports differ. No definition changes,
   additional hypotheses, weakened conclusions, or change records are present.
   Verdict: pass.
2. Compiled both delivery modules in import order with `lcompile.py --all`:
   no errors or warnings. Scanned both for forbidden declarations and holes.
   The only sorry is the named new finite-free theorem listed above; there are
   no definitions containing sorry. A scratch copy with `#print axioms` for
   both declarations compiled and reported only `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`. The last reflects the explicitly remaining
   finite-free lifting hole; this delivery is a decomposition, not a complete
   axiom-free proof of the original theorem. Verdict: pass with that hole.
3. Read the new finite-free statement, its complete docstring argument, and
   its node. Finitely many germ representatives admit a common refinement;
   monicity gives equality on the overlap, so descent to the open image works.
   The zero ring, n=0, zero sheaves and empty scheme cases introduce no exception
   (the last has no x). The new statement removes the relation-descent part and
   is strictly simpler; the original module proves that part by an actual
   strong-epi/mono diagonal lift. Independent LeanFinder search used sections
   lying in a subsheaf, grep searched local lifts and subsheaves, and Loogle
   checked StrongEpi. Also searched both project roots and inspected the old
   dependencies' Mathlib matches. No existing arbitrary-etale-module-sheaf
   theorem closes the finite-free hole in a few minutes. Verdict: pass.
4. Read the proof from the original theorem down. The finite free surjection,
   preservation of epimorphisms by constant sheaf formation and restriction,
   and StrongEpi lifting property give exactly the required right triangle.
   The added imports are plain and both used; the public imports serve the
   signatures. The old dependencies removed from the original node are now
   explicitly listed above; they remain in the free-source node. Checked
   `dag/units/sk-thm-p1.json`, including `realized`: this reduction is below
   the unit's route and bypasses none of its realized steps. Verdict: pass.
5. Checked both JSON nodes against the Lean declarations. The original node's
   proof and dependency union describe the finite-free reduction and diagonal
   lift; the new node has the source, creation, blueprint, search, Lean and
   proof fields required by the brief. Its recorded Lean statement matches
   the new declaration. No existing node statement changed. Verdict: pass.

Second reading changed report terminology from finite-free presentation to
finite-free cover (only finite generation is assumed), explicitly enumerated
all removed direct proof dependencies, made the corresponding proof-origin
wording correction, and corrected the new module's author group to S2.
The Lean proof and both theorem signatures required no repair.
