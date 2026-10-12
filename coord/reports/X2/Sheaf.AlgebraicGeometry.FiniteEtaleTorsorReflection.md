## What changed

Proved `AlgebraicGeometry.Etale.finiteEtale_reflects_torsor_transport` without changing its
signature, hypotheses, or existing docstring. Its proof extracts the two transport
isomorphisms, lifts the conjugated forward and inverse sheaf maps, proves both inverse
equations by injectivity of pullback, and reflects equivariance through the adjunction unit.

Added two public, fully proved helper modules, with proof-only imports in the item's module:
`Sheaf.AlgebraicGeometry.FiniteTorsorPullbackHomBijective` and
`Sheaf.AlgebraicGeometry.TorsorUnitEquivarianceReflection`. The first proves finite local constancy of the underlying torsor sheaves using a lemma
for any constant group sheaf, then uses
the lower-level set-sheaf representability theorem, Yoneda full faithfulness, and the proved natural
inverse-image comparison for representables. The second uses natural translations by
constant sections, the adjunction Hom bijection, and local surjectivity of the
constant-presheaf sheafification map. Neither helper restates the original theorem:
one concerns arbitrary underlying sheaf morphisms, the other concerns equivariance of
an already chosen morphism with injective inverse image and requires neither finiteness
nor a finite étale equivalence.

The original node's proof and dependency list now follow the actual Lean argument.
All three sandbox modules compile without warnings using lcompile.py --all.

## Proved and sorry left

Closed the item's only hole:
`AlgebraicGeometry.Etale.finiteEtale_reflects_torsor_transport`
(node `lem-weil-pbc-finite-etale-torsor-reflection`).

Also proved the two new helpers:
`AlgebraicGeometry.Etale.finite_torsor_pullback_hom_bijective`
(node `lem-weil-pbc-finite-torsor-pullback-hom-bijective`) and
`AlgebraicGeometry.Etale.torsor_map_equivariant_of_unit`
(node `lem-weil-pbc-torsor-unit-equivariance-reflection`).

No sorry remains in any delivered file. No holes added or split off.
Existing imported representability results retain their own dependency closures;
this delivery does not claim to close those dependencies or any project target.

## No longer needed

Repair: removed `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent`
from `FiniteTorsorPullbackHomBijective`. Its torsor representatives and lifted
scheme actions are unnecessary: only underlying set-sheaf representatives are used.
The helper no longer needs `sbc-prop-torsors-h1` or
`lem-galois-etale-torsor-sheaf-torsor` as proof dependencies. These are not claimed
unnecessary for other callers. The lower-level representability dependency remains.


All three public imports are needed for the unchanged signature. Relative to the
current repository baseline, the item's direct proof imports
`Sheaf.AlgebraicGeometry.FiniteLocallyConstantSetsRepresentability`,
`Sheaf.AlgebraicGeometry.Sites.InverseImageRepresentable`, and
`WeilConjectures.ConstructibleSheaf.Defs` are removed. Representability and the
representable comparison are used transitively under the Hom-bijection helper;
the constant-pullback comparison is unnecessary. During helper cleanup, removed the redundant
`Mathlib.CategoryTheory.Whiskering` import and the unused direct
`Mathlib.AlgebraicGeometry.Morphisms.Finite` import from the equivariance helper.

The original node no longer directly needs `lemma-constructible-pullback-constant`
(`WeilConjectures.ConstructibleSheaf.Defs`, declaration
`AlgebraicGeometry.Scheme.upperStarConstantSheafIso`). The unit compatibility equations
already suffice to compare actions. That module remains transitively imported for
other definitions, so this is a proof-dependency pruning, not a whole-module pruning.

The original direct dependencies on finite locally constant representability and
inverse-image representables now occur under the Hom-bijection helper; they have not
been pruned globally. The constant-sheaf, finite-étale-category, and torsor definitions
remain statement dependencies. No other node or module is claimed globally unnecessary.
The unit's realized statement and steps are preserved.

## Where the brief, the DAG or earlier work was wrong

Current return repaired: the exact duplicate
`AlgebraicGeometry.Etale.isConstant_over_of_section` is removed. Its replacement
`torsor_isConstant_over_of_section` takes an arbitrary
`G : Sheaf Y.smallEtaleTopology AddCommGrpCat` and `[G.IsConstant ...]`, rather than
a prescribed `constantSheaf M`. Thus it applies to any constant group sheaf, including
one presented only through an isomorphism, and has no coefficient type M parameter.
The Hom proof supplies the IsConstant instance for its particular coefficient sheaf.
This is a strict generalization; importing the existing theorem would introduce the
cycle EtaleTorsorDescent → HenselianFiniteEtale → FiniteEtaleEquivalenceH1 → this item.
No new holes or public signatures were changed.

The earlier delivery imported `EtaleTorsorDescent`, which imports
`HenselianFiniteEtale`, then `FiniteEtaleEquivalenceH1`, then the item itself.
That reverse dependency caused the returned import cycle. The repair removes
`EtaleTorsorDescent`: a fully proved private local-triviality lemma for an arbitrary constant group sheaf
and a finite-stalk lemma supply the lower-level argument, and the Hom-bijection theorem invokes
`finiteLocallyConstant_sets_representable` directly. The overlay import graph now
has zero cycles. No existing library module or declaration signature is changed. The proof of reflection does not require identifying the pulled-back
constant sheaf with the constant sheaf on the new base. The prescribed action-unit
compatibility and naturality prove equality for constant translations, and local
surjectivity of sheafification proves it for arbitrary coefficient sections.

Edge cases: the Hom-bijection construction uses no points and no surjectivity of i;
it applies to empty schemes and to the trivial group. The equivariance helper works
for infinite M as well, because the image sieve of the sheafification unit is covering
without finiteness. The separatedness argument permits empty covering sieves.

The Hom-bijection helper uses finite locally constant set-sheaf representability
as a generic tool; its local constancy and finite stalk arguments are proved
directly. It replaces no step of the fixed unit route.

## New nodes

`lem-weil-pbc-finite-torsor-pullback-hom-bijective`: the bijection on underlying torsor
sheaf morphisms induced by a finite étale equivalence. Fully proved using generalized constant-group-sheaf local triviality and finite stalk proofs, lower-level
set-sheaf representability, and the natural inverse-image representable comparison.

`lem-weil-pbc-torsor-unit-equivariance-reflection`: reflection of equivariance of a
chosen morphism through the action-compatible unit squares and injectivity on its
Hom set. Fully proved through constant translations and a covering image sieve.

Both nodes are in `dag/nodes/sec-proper-base-change/` and retain the parent's unit
`sk-thm-p1`. No statement or definition changes; no change records.


The following second reading is retained from the returned delivery and predates
the current repair; a second reader must review the generalization above.

## Earlier second reading (a previous round; superseded)

1. Interface: PASS. Compared every delivered module with the repository. The item
   changes only its proof and plain imports; its existing theorem signature and
   docstring are byte-for-byte unchanged. The other two modules are new. No existing
   definition, target, public import, or statement is changed; no change record is needed.
2. Proof and trust: PASS within the open-dependency convention. Independently compiled
   all three files in import order with lcompile.py --all: no errors or warnings.
   Scanned all delivered Lean for sorry and forbidden declarations: none. Compiled a
   scratch copy with #print axioms for all three public theorems. Equivariance reflection
   uses only propext, Classical.choice, Quot.sound. The item and Hom-bijection helper
   additionally use sorryAx inherited from existing imported dependencies. They close
   their own holes but are not yet axiom-clean project proofs. There is no data definition
   or arbitrary witness chosen into a definition in this delivery. Representatives and
   local sections are eliminated only inside proposition proofs.
3. Helpers: PASS. No statements are split off with sorry. Read both fully proved helper
   arguments: finite local constancy and finite stalks give representability; full
   faithfulness transfers the Hom bijection. Constant translations, unit naturality,
   the adjunction Hom bijection, and a covering image sieve give equivariance. The
   helpers isolate different parts of the argument rather than restating the item.
   Checked empty bases, the trivial group, and arbitrary infinite M in the equivariance
   helper. Repeated searches with different wording using leanfinder, loogle, msearch
   grep, and rg on the library found no usable replacement theorem. Existing upstream
   local-constancy/stalk proofs cannot be imported here: EtaleTorsorDescent imports
   HenselianFiniteEtale, which imports FiniteEtaleEquivalenceH1, which imports this item.
   The private elementary copies avoid that cycle. The source justification matches
   [Stacks 0A5G](https://stacks.math.columbia.edu/tag/0A5G) and
   [Stacks 03RV](https://stacks.math.columbia.edu/tag/03RV).
4. Route and pruning: PASS. Read top-down lifting of the conjugated forward and inverse
   maps, reflection of inverse equations, and the equivariance reduction. The three
   public imports supply the unchanged signatures; additional helper imports are plain
   proof imports. Compared every old proof dependency with the new list. Representability
   and inverse-image representables move under the Hom helper; finite-etale-category and
   constant-sheaf definitions remain statement dependencies. Only the constant-pullback
   comparison is genuinely unnecessary for this proof. No whole module is claimed
   pruned from the targets' closure. Read sk-thm-p1.json realized: none of its statement
   or step realizers is removed or bypassed.
5. Nodes: PASS. The existing node changes only proof, proof_deps, proof_origin. Both
   new nodes record their fully proved declarations, hypotheses, sources, searches,
   creation, blueprint ancestry, chapter and unit. In all three nodes proof_deps equals
   the union of step uses, and the prose follows the actual Lean arguments.

Second-reading changes: appended this independent review and made the axiom status
explicit. No Lean proof, signature, definition, import, or node needed repair. One
original hole closed, zero holes added, zero statements split off.

## Second reading by X2

1. Interface: PASS. Compared all three delivered Lean modules with the repository baseline. The existing reflection theorem has unchanged signature and only its proof and proof-only imports changed; the two helper modules are new. No target statement or definition was altered.

2. Proof and trust: PASS. Compiled all modules with `lcompile.py --all`; there are no warnings, `sorry`s, forbidden declarations, or hollow definitions in delivered Lean. The remaining `sorryAx` reported by imported dependencies is inherited and is documented in the prior report.

3. Statements and helpers: PASS. The two helper declarations are strictly smaller than the target: one gives bijectivity on arbitrary underlying sheaf Hom sets under finite-etale equivalence, and the other reflects equivariance for a fixed map from unit compatibility. Their hypotheses and conclusions match their DAG nodes, and the arguments cover empty schemes and trivial groups. Searches and repository inspection found no existing duplicate declaration.

4. Route and pruning: PASS. The target proof lifts forward and inverse maps with the Hom bijection, reflects inverse identities by injectivity, and then reflects equivariance through the unit helper. The finite representability and inverse-image representable route is retained; the former cyclic torsor-descent import is absent. Removed imports and proof dependencies are listed in `## No longer needed`, and the unit `sk-thm-p1` remains realized.

5. DAG agreement: PASS. The existing node changes only proof, proof dependencies, and proof origin. Both new nodes contain matching statements, sources, proof steps, searches, and Lean records. No split-off holes were added.

I changed only this report section; no Lean source, declaration, node, or import required repair after the second reading.
