## What changed

Proved `RingTensorCohomology.affineTensorCohomology_additive_parts` without changing its
signature, definitions, universes or visibility. Added three proved private helpers:
`resolution_kFlat`, `restrictedExtension_quasiIso_of_kFlat`, and
`resolution_homology_additive`. The first two reuse the corresponding proved arguments
in `AffineTensorCohomologyScalarParts`, without importing that module.

The generic helper applies the existing resolving-class theorem to K-flat homotopy
objects. Its derived functor is exact and therefore additive. Augmentation, derived
counit and homology factorization provide three explicit natural-isomorphism transports.
Specialize to extension for source and restriction followed by extension for target.
The tensor generator formulas establish naturality of the arrow isomorphism used to
verify the second specialization's quasi-isomorphism preservation.

Added proof-only imports of `KFlatScalarExtensionDerivedIso` (with `all` to access its
proved scalar-extension helper), `BaseTensorOrdinaryIso`,
`LeftDerivedFunctor.Defs`, and `LeftDerivedFromResolvingClass`.
The existing public import of `RingTensorCohomology` is unchanged. Updated only
`proof`, `proof_deps`, and `proof_origin` in the item's DAG node.

`lem-pur-left-derived-from-kflat-class` is used as a general tool from another unit.
It implements exactly the resolving-class argument of Tag 06Y6, which explicitly
invokes Tag 06XN; no realized step of the item's unit is bypassed (its `realized`
statement and step lists are empty). The specialized base-derived-extension theorem
has no counit computation clause on the specific chosen K-flat resolutions; the
general tool supplies it directly for both module functors.

Validation: local compilation succeeds with no warnings. No flatness or boundedness
assumptions are introduced. Zero complexes and zero coefficient rings are included:
resolution, quasi-isomorphism, natural-isomorphism transport and tensor induction
use the same arguments. All private helpers are proved; no new statements are left open.

Sources read: the cited local Stacks TeX files are absent on this remote machine;
checked [06Y6](https://stacks.math.columbia.edu/tag/06Y6),
[06XN](https://stacks.math.columbia.edu/tag/06XN),
[05SE](https://stacks.math.columbia.edu/tag/05SE), and
[0DJ8](https://stacks.math.columbia.edu/tag/0DJ8) on the Stacks website.
Searches actually run through `msearch.py`: LeanFinder for additivity of cohomology
of functorial flat resolutions (derived-category additive instances), Loogle for
`CategoryTheory.Functor.additive_of_iso` (exact transport lemma), and grep for
`leftDerivedFunctor.*Additive|additive_of_iso` (transport infrastructure).

## Proved and sorry left

Closed: `RingTensorCohomology.affineTensorCohomology_additive_parts`
(node `lem-pc-affine-tensor-cohomology-additive-parts`), the sole original hole.
Added holes: none. Sorries remaining in the delivered module: none.
This is a proof from existing library declarations, not a new decomposition.
Independent second-reader axiom checks confirm that the theorem and all three private
helpers depend only on `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`
is reachable from these declarations.

## No longer needed

Removed the planned dependency `lem-pc-base-derived-extension-linear` and avoided its
module `Sheaf.Algebra.Homology.BaseDerivedExtensionLinear`. No import of this module
was present in the original item, so no original import was removed. The scalar
compatibility theorem and the specialized extension construction are unnecessary
for this additivity proof. Their descendants are not required through this dependency;
other target paths may still need them.

The exploratory import of `AffineTensorCohomologyScalarParts` was removed. Its scalar
transport theorem and `Mathlib.Algebra.Homology.ShortComplex.Linear` are unnecessary.
The exploratory `HomotopyCategory.Braided` import was also removed. All remaining
proof imports supply declarations used by the completed proof.

## Where the brief, the DAG or earlier work was wrong

The original DAG did not name the resolving-class counit computation needed for the
chosen models. Its proof-dependency list named the additive derived extension result,
whose public statement does not assert counit invertibility on these resolutions.
The updated route names the existing general resolving-class theorem and the actual
mixed-tensor quasi-isomorphism input instead. No mathematical statement was changed.

A raw homotopy-category K-flat predicate initially caused a monoidal-instance
elaboration failure. Describing the resolving class as homotopy objects represented
by K-flat complexes avoids that failure and is exactly the class required by the
argument; no definition or interface adaptation was necessary.


## Second reading by G4

1. PASS. Compared the sole delivered Lean module and its node against the repository
   with `diff -u`, then checked the existing theorem signature and docstring byte for
   byte. Its universes, hypotheses, conclusion, visibility, and public import are
   unchanged. No existing definitions changed; no change record is needed.
2. PASS. Independently compiled the module with `lcompile.py` (8.6 seconds, no errors
   or warnings). A scratch copy with `#print axioms` for the main theorem and all three
   private helpers compiled in 10.3 seconds: each uses only `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The delivered file has no
   sorry, axiom, unsafe, opaque, implemented_by, extern, or kernel-check bypass.
   No data definition or arbitrary witness from an unproved existence theorem was
   introduced. The existential derived pair is eliminated inside a theorem proof;
   its source theorem is proved and its pair is universal.
3. PASS. There are no split-off statements, new public declarations, or new nodes.
   Read each proved private helper: resolution K-flatness uses the existing flat
   resolution theorem; the tensor arrow square follows on generators; the generic
   helper transports additivity through three natural isomorphisms. Zero complexes,
   zero rings, identity maps, and arbitrary unbounded complexes require no additional
   hypothesis. In particular, restriction is not assumed to preserve K-flatness:
   the target uses tensor associativity with extension over A instead.
4. PASS. Read the imported scalar-extension helper, ordinary tensor isomorphism,
   resolving-class theorem, upstream derived-functor definitions, source/target
   definitions, and the unit record `sk-thm-picard-semicon`. Independently searched
   Lean with `rg` for resolution additivity and K-flat preservation, and used
   `msearch.py` Loogle for `CategoryTheory.Functor.IsTriangulated`, confirming the
   existing exact-to-additive instance. Mathlib's derived-functor files supply no
   direct additive instance eliminating the computation and transport argument;
   the specialized upstream counit alone does not supply derived additivity.
   The proof reuses the existing tools rather than adding open intermediates.
   Each added import supplies a used declaration and is proof-only. The old
   dependency `lem-pc-base-derived-extension-linear` is the only removed node and
   is already listed under No longer needed; no original import was removed.
   The resolving-class theorem is a general tool, not a replacement unit step;
   the unit's realized statement and step lists are empty and unchanged. Checked
   the route against Stacks [06Y6](https://stacks.math.columbia.edu/tag/06Y6),
   [06XN](https://stacks.math.columbia.edu/tag/06XN), and
   [05SE](https://stacks.math.columbia.edu/tag/05SE).
5. PASS. Node edits are confined to `proof`, `proof_deps`, and `proof_origin`.
   Its four proof steps match the preservation helper, resolving-class application,
   natural-isomorphism transports, and two specializations. `proof_deps` equals the
   union of the steps' `uses`; the original mathematical statement and Lean record
   are unchanged. There are no new nodes to validate.

Changed by this reading: clarified the axiom status in Proved and sorry left and
added this independent review. No Lean or DAG repair was necessary.
