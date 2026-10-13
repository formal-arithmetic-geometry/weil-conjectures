## What changed

Replaced the sole sorry of Sheaf.AlgebraicGeometry.ComplexLiftClassProjective with a
compiled reduction following Stacks Tag 0BCA. The proof chooses the supplied model,
constructs an acyclic cone through a new intermediate theorem, applies the existing
CochainComplex.exists_acyclic_lift_mod_ideal, and applies a separate module-level
splitting theorem in each degree. Mathlib's triangleOfSES supplies the derived
isomorphism; commShiftIso and shift cancellation supply the complex reduction
isomorphism. All existing signatures and public imports are unchanged. The second reader
added the proof-only Mathlib KProjective import to the new cone module, as its
DAG proof dependency requires, and removed its redundant Additive import.

Two new modules isolate the unfinished cone/dotted-arrow/cokernel construction and
the module-level reduced-splitting argument. Their whole proofs are named public
sorries with source, complete proof in words, and matching new DAG nodes. Updated
the original node's proof, proof_deps and proof_origin to match the Lean reduction.

## Proved and sorry left

Closed AlgebraicGeometry.complex_lift_class_projective
(lem-sc-complex-lift-class-projective), from the existing acyclic-lift theorem and
two new intermediate statements. This is a decomposition, not a sorry-free proof.
One original hole closed, two holes added; net minus one.

Added and left sorry:

- AlgebraicGeometry.exists_complex_lift_acyclic_enlargement
  (lem-sc-complex-lift-acyclic-enlargement), in
  Sheaf.AlgebraicGeometry.ComplexLiftAcyclicEnlargement.
- AlgebraicGeometry.projective_class_reduced_splitting
  (lem-sc-projective-class-reduced-splitting), in
  Sheaf.AlgebraicGeometry.ProjectiveClassReducedSplitting.

No sorry remains in the assigned module. The existing imported
CochainComplex.exists_acyclic_lift_mod_ideal remains a dependency, untouched.
The main proof, including the short exact sequence triangle and both shift
comparisons, compiles. The new statements were checked for the empty-class case
(their term-membership assumptions exclude it), I = bottom, I = top, and zero
complexes. In the splitting statement, I = top and the surjectivity condition
force class members to be zero. The cone statement has no surjectivity condition:
for I = top its reduced complexes vanish, and the zero map K0 -> A with cokernel
A gives the required right-exact sequence without asserting injectivity. They require no selection of
arbitrary data inside definitions; all existential constructions remain theorems.

## No longer needed

The second reader removed the redundant direct import
Mathlib.Algebra.Homology.Additive from the new cone module; it is already publicly
imported by HomologicalComplexAbelian, which its statement requires.

Removed proof imports Sheaf.Algebra.Homology.BoundedFlatKFlat and
Sheaf.Algebra.Homology.DerivedChangeOfRings. Their nodes
lem-pc-module-bounded-flat-kflat and lem-pur-derived-change-of-rings are not needed
on this branch: hK already includes the exact derived reduction isomorphism used
by the argument. This does not claim they are globally unreachable.

Sheaf.Algebra.Homology.AcyclicLift and
lem-sc-complex-lift-acyclic-projective are retained and used explicitly.
lem-pc-ring-derived-map-representative moves to the cone intermediate's proof
plan; it remains needed there. No other original proof nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof plan redundantly recomputes derived reduction even though the
Lean hypothesis hK supplies that comparison. No change of statement is necessary.
The local literature/stacks-project/more-algebra.tex file is absent; the complete
source proof was read at https://stacks.math.columbia.edu/tag/0BCA and its acyclic
lifting input at https://stacks.math.columbia.edu/tag/0BC9. LeanSearch returned
Internal Server Error; LeanFinder, Loogle and source searches were used instead.

The reduced-splitting argument only proves that the last term belongs to the
class. An identification with the particular supplied lift P3 is unnecessary and
is not asserted by the new statement. The enlargement does not assert injectivity
before reduction; the separate splitting argument provides it.

## New nodes

lem-sc-complex-lift-acyclic-enlargement:
lean/Sheaf/AlgebraicGeometry/ComplexLiftAcyclicEnlargement.lean. This states the
cone preparation and the right-exact cokernel diagram for any supplied acyclic
lift. It leaves application of the existing acyclic-lift theorem, module-level
splitting and the derived/complex shift conclusion to the assigned module.

lem-sc-projective-class-reduced-splitting:
lean/Sheaf/AlgebraicGeometry/ProjectiveClassReducedSplitting.lean. This is solely
the module-theoretic final paragraph of Tag 0BCA. It contains no complex or derived
category hypothesis. No change records or forced adaptations are needed.

## Second reading by Q4

1. PASS: Compared every delivered Lean file with the repository. The two helper
   modules are new; the existing module changes only plain proof imports and the
   theorem body. The entire existing theorem signature, docstring, visibility,
   universes, and public imports are byte-for-byte unchanged. No definition or
   statement change, change record, or forced adaptation is needed.
2. PASS: Compiled all three modules in dependency order with lcompile.py, then
   compiled scratch copies with #print axioms for all three declarations. Each
   lists only propext, Classical.choice, Quot.sound, and sorryAx. The latter comes
   from the two reported helper holes and the retained existing AcyclicLift hole.
   There are exactly two direct sorries, both whole proofs of public named
   theorems with sources, complete docstring arguments, and matching nodes; no
   forbidden declaration or hollow definition. The degreewise sequence, its
   derived connecting isomorphism, the -1 shift and shifted upper bound are
   checked by the compiled proof. This closes one hole by adding two, a
   decomposition with net -1, not a sorry-free proof.
3. PASS: Read https://stacks.math.columbia.edu/tag/0BCA in full and its acyclic
   lifting input https://stacks.math.columbia.edu/tag/0BC9. The cone lemma omits
   hsurj and asserts only right exactness over R; it does not assume or conclude
   the original lifting theorem. The second lemma is entirely about modules,
   with no complex or derived-category hypothesis. Its projection onto ker(g)
   does not require g composed with the first arrow to vanish. The projection
   becomes invertible modulo I; hsurj and projectivity split it; its kernel has
   zero reduction and hsurj applied from zero annihilates that kernel. Class
   membership of the actual cokernel follows from the resulting split sequence,
   without claiming that it equals the supplied module lift. The closure iff
   implies zero membership and isomorphism invariance once a class member exists.
   Checked empty class, zero modules and complexes, I = bottom, and I = top as
   explained above. All choices occur inside existential theorem proofs, with
   no data selected by an unproved mere-existence theorem inside a definition.
   Repeated searches with different wording using msearch.py LeanFinder, Loogle
   and grep, and rg on Sheaf, WeilConjectures and the relevant Mathlib sources.
   Found projective lifting/splitting APIs and isKProjective_of_projective, but
   no exact helper statement. Neither helper can be closed in a few minutes
   using a matching existing declaration.
4. PASS: The reduction uses the supplied derived comparison in hK, the existing
   acyclic lifting declaration, degreewise splitting, and Mathlib triangleOfSES;
   no derived tensor recomputation is needed. Every old proof dependency removed
   from the main node is accounted for: BoundedFlatKFlat and DerivedChangeOfRings
   are pruned on this branch, and the Mathlib derived-map representative leaf
   moves to the cone node. AcyclicLift remains explicitly used. The unit
   sk-prop-av-cube and its realized fields are unchanged (its current statement
   and step arrays are empty); this is a refinement below the unit level and
   leaves its general cube-theorem route intact. All new imports used only for
   proofs are plain imports.
5. PASS: Read the original node, both new nodes and the Mathlib representative
   leaf. The original proof/proof_deps/proof_origin match the actual reduction;
   the new nodes include self-contained statements, sources, full proof steps,
   dependency unions, origin, actual logged searches, split status, created
   records, blueprint ancestry, chapter, unit and verbatim Lean signatures.
   The cone node retains the representative leaf, while the module splitting
   node has only elementary module-theoretic steps and no proof dependencies.

Changed on second reading: added the missing plain import
Mathlib.Algebra.Homology.DerivedCategory.KProjective to the cone module so its
planned Mathlib dependency is available; removed the redundant direct Additive
import from that new module; corrected the report's I = top explanation for the
cone statement, which has no hsurj hypothesis. No proof or statement was rewritten.
