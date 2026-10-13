## What changed

The signature of AlgebraicGeometry.Scheme.exists_perfect_map_lift_of_isAffine is
unchanged. Its proof now takes a K-flat resolution of a Q representative of A,
constructs A' as Q of the total tensor with J, and supplies the witnesses in
IsDerivedTensorAugmentation explicitly. Existing perfect_derivedTensor proves
perfectness. A new proved pointwise stalk lemma proves the support clause.

The remaining Koszul section lifting and compatible transposition are isolated in
Sheaf.AlgebraicGeometry.AffinePerfectTensorRoof. This is a strict part of the argument:
it gives a chain augmentation and maps for a fixed K-flat P, but does not assert
perfectness of the total tensor, the augmentation predicate, or any support clause.
Those parts are established in the assigned theorem, with the support helper proved
in Sheaf.AlgebraicGeometry.DerivedTensorStalkVanishing.

The original node's proof and dependencies now describe this construction. No
existing signature, definition, public import, or other module is changed.
The unit route is retained: the RHom, Koszul representability and tensor-Hom steps
remain in the roof helper, and tensor perfectness remains in the assigned proof.
The unit record has no realized statement or step entries for this node.

Validation: all three modules compile cleanly with lcompile.py --all. The new
statements were checked on empty U, zero A, zero J, empty schemes, and zero stalks.
The Koszul construction permits empty principal families. The support theorem
needs only J K-flat, since its stalk tensors an acyclic P_x; P need not be K-flat.
No object is defined by choosing data from an unproved existence theorem.

Sources checked: https://stacks.math.columbia.edu/tag/08EH and
https://stacks.math.columbia.edu/tag/06YB. The local literature checkout contains
only its index files on this machine; the published Stacks pages were read.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.Scheme.exists_perfect_map_lift_of_isAffine
(node lem-sc-affine-perfect-map-lift); no sorry remains in the assigned module.

Added and proved AlgebraicGeometry.Scheme.derived_tensor_stalk_vanishing
(node lem-sc-derived-tensor-stalk-vanishing). Its proof uses the existing K-flat
stalk criterion, stalk tensor comparison, sheaf forgetful colimit preservation,
and Mathlib homology comparisons. It has no sorry of its own.

Added one hole, the complete proof of the public theorem
AlgebraicGeometry.Scheme.exists_affine_perfect_tensor_roof
(node lem-sc-affine-perfect-tensor-roof). This is a decomposition, not a completed
proof of the full affine map-lifting argument. Its docstring gives the complete
Koszul/RHom construction and compatibility argument. The original hole is closed
and one lower hole is added: net zero before any further dependency-closure changes.
The existing imported theorem perfect_derivedTensor still has its original hole;
this delivery does not change it or any other dependency's holes.

## No longer needed

Removed direct proof imports from the assigned module:
Sheaf.Algebra.Homology.RhomGlobalSections,
Sheaf.AlgebraicGeometry.AffinePerfectOpenRepresentCohomology,
Sheaf.AlgebraicGeometry.PerfectDerivedTensorHom,
Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherent,
Sheaf.Paper.DerivedInternalHomRestrictOpen.
All five remain needed by the roof construction and are imported there. Consequently
none of their nodes or modules is pruned from the target closure. No other node or
module is declared unnecessary. PerfectDerivedTensor is retained and actually applied.

## Where the brief, the DAG or earlier work was wrong

The declared plan lacks the glue transporting a general affine X and compact U to
Spec and a finite principal-open Koszul system. Represent-cohomology is stated only
for that system. Tensor-Hom is stated in the derived monoidal tensor, whereas the
augmentation and tensor-perfectness interfaces use representative total tensors.
The new roof theorem names that remaining transport and compatibility work.

The support clause need not rely on the docstring's assertion that zero cohomology
stalks make the object zero near the point. The proof works pointwise, using the
K-flat stalk criterion and exact stalk homology comparison, without needing any
neighbourhood-vanishing statement. No original statement was disputed or changed.

## New nodes

lem-sc-affine-perfect-tensor-roof: Sheaf.AlgebraicGeometry.AffinePerfectTensorRoof;
the Koszul augmented K-flat complex and compatible maps for a fixed source model,
with its sole named theorem still sorry. Its proof retains the original RHom and
Koszul dependencies and the bounded-above flat K-flat criterion.

lem-sc-derived-tensor-stalk-vanishing:
Sheaf.AlgebraicGeometry.DerivedTensorStalkVanishing; proved pointwise cohomological
vanishing under tensor with a K-flat complex. Unlike map lifting, it needs neither
affineness, a perfect source, a compact open, nor a closed subset.

No change records or forced adaptations are needed.


## Second reading by G1

1. Compared the complete assigned module with the repository using diff and a
   byte-for-byte signature comparison. The existing theorem's binders and conclusion,
   visibility, public imports, and all definitions are unchanged. The existing node
   changes only proof, proof_deps, and proof_origin. Verdict: pass.
2. Independently compiled all three delivered modules with lcompile.py --all, then
   compiled scratch copies with #print axioms for all three declarations. The original
   theorem and the roof theorem use only propext, Classical.choice, Quot.sound and
   sorryAx; the pointwise stalk theorem uses exactly the three permitted axioms and
   no sorryAx. The only direct hole is exists_affine_perfect_tensor_roof, whose entire
   proof is by sorry. There are no definitions, forbidden declaration forms, or hidden
   holes in these files. Existential witnesses are eliminated inside theorem proofs;
   no definition chooses arbitrary data from an unproved existence theorem. Verdict: pass.
3. Read the roof theorem and its node in full against Stacks Tag 08EH, and read
   Tag 06YB for the stalk argument. The roof fixes P and gives the canonical chain
   augmentation and compatible lifted morphism; it does not assert tensor perfectness,
   the augmentation predicate, or support. Those are separately established in the
   original proof, so this is a genuine decomposition with one hole closed and one
   added, not a completed map-lifting proof. For empty U choose J=0 and gamma=0;
   for zero A the source tensor is acyclic, and for empty X all stalk requirements
   are vacuous. For U=X the unit augmentation works. A zero J is allowed only when
   its resulting restriction can be isomorphic to A|U, as the conclusion requires.
   The stalk theorem needs only J K-flat: exact stalk homology makes P_x acyclic,
   then stalk K-flatness and the total-tensor comparison prove the conclusion.
   Independently searched with LeanFinder (extend derived morphism using finite
   Koszul complexes on principal open cover), Loogle (HomologicalComplex.Acyclic),
   and grep (mapHomologyIso|isKFlat_iff_stalk), and searched repository sources for
   roof/map-lift and stalk/tensor alternatives. Results supplied general fractions,
   acyclicity and homology comparison tools, but no replacement for either helper.
   The assigned module has no upstream proof in the available source tree. Verdict: pass.
4. Read the imported stalk criterion, stalk tensor comparison, tensor perfectness,
   and affine Koszul representability interfaces. The original proof genuinely applies
   perfect_derivedTensor and constructs IsDerivedTensorAugmentation's witnesses,
   while its support clause uses the proved stalk helper. No shorter complete lifting
   route was found. Proof imports are private; public imports supply signature types.
   All old proof dependencies except tensor perfectness move into the roof helper,
   rather than disappearing from the closure; No longer needed lists every such
   direct import and correctly claims no pruned module. The unit's realized arrays
   contain no entry for this node, and the RHom/Koszul/tensor-Hom route is retained
   under the roof node. Verdict: pass.
5. Matched each proof step and used declaration to all three nodes' proof_deps.
   The original node cites resolution, roof, tensor perfectness and stalk vanishing;
   the stalk node cites exactly the three project lemmas used by its compiled proof;
   the roof node retains the construction's RHom/Koszul dependencies and the
   bounded-above flat criterion. Both new nodes have complete creation, source,
   search, blueprint, chapter, unit and verbatim Lean statement records. Verdict: pass.

Changes by the second reader: appended this independent review and its axiom/search
results. No Lean proof, signature, import or node repair was necessary. The remaining
roof construction cannot be closed in a few minutes from the current interfaces.
