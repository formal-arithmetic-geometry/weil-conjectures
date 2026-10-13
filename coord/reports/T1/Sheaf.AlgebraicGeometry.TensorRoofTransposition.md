## What changed

Reduced `AlgebraicGeometry.Scheme.tensor_roof_transposition` to the new natural
adjunction theorem in `Sheaf.AlgebraicGeometry.TensorModelRestrictionAdjunction`.
The original signature, universes and visibility are unchanged. Its proof constructs
`c = Q(rightUnitor P) ≪≫ eA`, takes the restricted unit equivalence by precomposition
with `R(c).inv`, and takes gamma to be the global transpose of xi.

The augmentation's invertibility is proved, rather than split off. Naturality
conjugates precomposition by `R(Q(u))` to precomposition by the localized tensor map.
The former is bijective because `R(Q(u))` is invertible. Surjectivity into `R(B J)`
gives an inverse on one side; injectivity into `R(B T)` proves the other inverse
identity. Thus the proof requires no conservativity or fullness of restriction.
Four proved private categorical helpers handle these tests and unit cancellation.

The new theorem supplies global and restricted equivalences for every second
complex J and every E, with naturality for arbitrary chain maps J → J' and
compatibility with restriction. It contains no tensor unit, augmentation,
invertibility hypothesis, representative section equation, or lifted-roof conclusion.
It isolates the model-level adjunction construction (original steps 1, 2 and 4),
while the main module proves the unit calculation, invertibility and combination.
No data definition is added or chosen from a mere existence theorem.

The declaration-local transparency and heartbeat options permit elaboration of
concrete derived functors. Generic categorical cancellation avoids expensive
rewrites through the sheaf instances. The declaration-local unused-variable linter
setting preserves the original, unnecessary-in-this-reduction hypothesis hJ.
Both modules compile within the single-file limit, with no warnings.

## Proved and sorry left

Closed the direct hole in `AlgebraicGeometry.Scheme.tensor_roof_transposition`
(node `lem-sc-tensor-roof-transposition`); its combining proof contains no sorry.

Added exactly one direct hole:
`AlgebraicGeometry.Scheme.exists_tensorModel_restriction_adjunction`
(node `lem-sc-tensor-model-restriction-adjunction`), in its own new module. Its
entire proof is `:= by sorry`, and its docstring records the source and complete
construction/naturality argument. This is a decomposition: one hole closed and
one added, net zero direct holes. The theorem still rests on this unproved
adjunction construction; no claim of an axiom-free completed proof is made.
The four private categorical helpers are completely proved.

## No longer needed

Removed the five direct proof imports from the original module:
`Sheaf.AlgebraicGeometry.DerivedInternalHomAdjunction`,
`Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom`,
`Sheaf.AlgebraicGeometry.OpenRestrictionKFlatModel`,
`Sheaf.Algebra.Homology.HomComplexRestrictOpen`, and
`Sheaf.Paper.DerivedInternalHomRestrictOpen`.
They remain needed by the new adjunction item's proof plan and remain imported
there. This is relocation of dependencies, not pruning from the target closure.
No node or module is claimed globally unnecessary. The original node now depends
only on `lem-sc-tensor-model-restriction-adjunction`; that node records the retained
original dependencies and the K-flat/total-tensor comparison tools it needs.

## Where the brief, the DAG or earlier work was wrong

The planned restriction identity does not follow just by applying the existing
object-isomorphism statements. `derivedInternalHom_restrict_open` and
`homComplex_restrict_open` expose `Nonempty` isomorphisms without an evaluation
compatibility equation. The new node states this missing simultaneous naturality
and morphism-level compatibility explicitly; it does not change either interface.

The existing restriction/K-flat and canonical tensor-Hom declarations were read,
along with their node signatures. Mathlib searches found ordinary categorical Hom
transport and Yoneda tests, but no complete model-level restriction adjunction.
LeanSearch returned HTTP 500, recorded as unavailable. LeanFinder, Loogle and grep
ran and are recorded in the sandbox search log. Blueprint searches for tensor Hom
restriction and the three Stacks tags found no exact imported blueprint statement.

The local checkout omits the Stacks source files. The corresponding authoritative
pages were read directly: https://stacks.math.columbia.edu/tag/08DJ,
https://stacks.math.columbia.edu/tag/08DL, and
https://stacks.math.columbia.edu/tag/08EH. The new statement is the representative
adjunction/naturality part of 08DJ and 08DL, not the perfect-roof existence of 08EH.

Edge cases checked mathematically: P=0 gives zero sources and RHom(0,E)=0;
J=0 gives zero source and total tensor; empty U gives the unique Hom maps on zero
objects. Arbitrary, unbounded J is allowed because P alone is K-flat. The main
argument uses two actual targets in the image of restriction, so it remains valid
without essential surjectivity of restriction. The unit record has no realized
nodes for this item; no unit or chapter statement or prescribed step was changed.

## New nodes

`lem-sc-tensor-model-restriction-adjunction` records the global/restricted
transposition families and their two exact compatibility equations. Its proof
uses the original canonical adjunction and Hom restriction nodes, plus the existing
K-flat natural comparison and open total-tensor comparison. The blueprint ancestor
and route are inherited from the original node. No change record is needed:
no existing definition or statement interface changed, and no module was adapted.

## Second reading by T1

1. PASS: compared the delivered original module with the repository by diff and
   extracted its complete theorem signature. The signature is byte-for-byte
   identical, including universes, all derived-category instances, hP, hJ, eA,
   the representative equation, and the exact chain formula for beta. No existing
   definition, declaration visibility, public import or target statement changed.
2. PASS as a decomposition: compiled both modules in import order with lcompile.py
   (16.7 and 30.2 seconds; no warnings). Separate scratch copies with #print axioms
   for both public theorems reported only propext, Classical.choice, Quot.sound
   and sorryAx. Inspected all four private helpers: each is proved and the
   invertibility test constructs both inverse equations in the correct order.
   The only direct sorry is the listed new public adjunction theorem; there are
   no definitions added, prohibited declarations, or choices of data in a public
   definition from an unproved existence assertion. Existential elimination inside
   the roof theorem's proof is ordinary propositional reasoning.
3. PASS: the new statement is tensor-model adjunction with restriction compatibility
   and naturality, not the same roof statement under a new name. It has no tensor
   unit, augmentation, invertibility or roof conclusion. The remaining unit
   cancellation and the two inverse tests are real, fully proved reductions.
   Checked zero P, zero J, empty U, U=top, and non-K-flat/unbounded J: K-flatness
   of P alone makes Hom(P,I) K-injective and computes the total tensor. Read the
   cited Stacks proofs at https://stacks.math.columbia.edu/tag/08DJ and
   https://stacks.math.columbia.edu/tag/08DL. Read all eight recorded dependency
   declarations. Independent searches used LeanFinder for "derived sheaf internal
   hom evaluation natural under restriction open immersion", Loogle for
   "CategoryTheory.Adjunction.homEquiv_naturality_left", grep for
   "homEquiv.*naturality|evaluation.*restrict|restrict.*adjunction", and rg in
   lean/Sheaf and lean/WeilConjectures. Generic adjunction naturality exists;
   no complete restriction-compatible tensor-model family was found. The
   object-isomorphism declarations alone do not establish the displayed morphism
   compatibility. Closing that construction is not a few-minute categorical repair.
4. PASS: the roof proof uses the new theorem once, then purely categorical
   transport and cancellation. Public imports support its signature; the new
   import is proof-only. The eight proof imports of the split module retain its
   documented construction plan. All five old proof_deps are listed in
   "No longer needed" via their module names and retained by the new node, so
   there is no claimed pruning from the target closure. Read
   dag/units/sk-thm-picard-duality.json: its realized statement and step lists
   are empty; no prescribed unit step or chapter route was bypassed or changed.
5. PASS: the original node's three proof steps match the definition of e and
   gamma, the two inverse tests, and the final naturality equation. Its sole
   proof_dep is the new adjunction node. Checked both nodes' proof_deps equal
   the union of step uses, all dependency declarations exist, and both Lean
   records contain their signatures verbatim. The new node has source, searches,
   creation, blueprint, chapter, unit and Lean fields required by the brief.

Second reading changed only the new theorem's proof docstring and matching new
node proof step: explicitly explained K-injectivity of Hom(P,I), representation
of arbitrary derived morphisms by chain maps modulo homotopy, and descent of
uncurrying. This closes a gap in the written argument for arbitrary J; the Lean
statements and proof terms are unchanged. One direct hole closed and one added:
net zero, decomposition only; zero of the one original holes proved without
remaining sorry dependencies. No module pruned from the target closure.
