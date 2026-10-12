## What changed

Proved `AlgebraicGeometry.Scheme.lisse_on_stratum_interiors` in
`Sheaf.AlgebraicGeometry.LisseStratumInteriors`, preserving its signature and docstring.
Added two proved private helpers: `finiteLisse_of_iso` and `finiteLisse_of_range_subset`.
The latter implements the fibre-product descent argument, preserving actual finite
stalks throughout. The main proof uses the existing interior open cover, descends
abelian local constancy, and transports finite stalks at lifted geometric points.
Updated the node `lem-weil-pbc-lisse-stratum-interiors` to describe this implementation.

Added the proof-only import `Sheaf.AlgebraicGeometry.FiniteLocalAbelianForget`.
Retained the proof-only imports `Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`
and `Sheaf.AlgebraicGeometry.PullbackFiniteLocallyConstant`. Public imports are unchanged.

Validation: the final module compiles locally without warnings (approximately 3 seconds).
The empty scheme/empty cover case is handled by the same proof; no nonemptiness,
Noetherianity, or assumption that an interior factors through its stratum is introduced.

## Proved and sorry left

Closed the only original hole:
`AlgebraicGeometry.Scheme.lisse_on_stratum_interiors`
(node `lem-weil-pbc-lisse-stratum-interiors`). Both private helpers are fully proved.
No `sorry` remains in the delivered module. No holes or new modules were added.
This is a proof from existing declarations, not a decomposition into new statements.

The proof uses the already stated `AlgebraicGeometry.Scheme.finite_local_abelian_forget_iff`
(node `lem-weil-pbc-finite-local-abelian-forget`), whose proof remains `sorry` in the
library. That existing declaration is not modified or duplicated by this delivery.
Other imported declarations can likewise retain their pre-existing transitive holes;
this delivery does not claim an unconditional axiom-free proof of the entire dependency
closure.

## No longer needed

Removed these proof-only imports:

- `Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance`:
  node `thm-weil-pbc-universal-homeomorphism-invariance` is not used directly;
  the proved abelian `IsLocallyConstantSheaf.of_upperStar` suffices.
- `Sheaf.Paper.InverseImageStalkGerm`:
  node `lem-weil-pbc-inverse-image-stalk-germ` is unnecessary; only the existing
  stalk isomorphism `lemma-openclosed-stalk-upperstar` is needed, with no germ formula.
- `WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism`:
  its closed surjective immersion instance is available through the public
  `GenericConstancy` import; the node
  `lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism` is still used.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  node `lem-weil-pbc-etale-inverse-image-restriction` is not needed directly;
  `GenericConstancy` already provides the proved abelian gluing theorem.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  composition isomorphisms remain used through existing public imports, so
  `lem-weil-pbc-inverse-image-composition` stays in the DAG.

No claim is made that these modules become globally unreachable from every target;
this lists the direct dependencies pruned from this item. The unit has no realized
statement/step nodes recorded, and the fibre-product/descent/open-cover argument is kept.

## Where the brief, the DAG or earlier work was wrong

The existing source generic-constancy theorem is not an exact substitute: its abelian
`IsFiniteSheaf` means finitely generated stalks, whereas this theorem requires finite
underlying sets at algebraically closed points. The proof uses the existing finite
abelian/set comparison lemma to separate local constancy from finiteness, so it never
confuses those two conditions. The original mathematical statement is unchanged.

The broad universal-homeomorphism invariance theorem and the germ-compatible stalk
comparison in the original dependency plan are stronger than needed. Existing proved
abelian local-constancy descent and plain stalk isomorphisms give the required argument.
The finite abelian/set comparison is an existing tool from another unit; it changes
neither the unit route nor this statement and is reported here for the maintainer's
cross-unit tool bookkeeping.

## Second reading by C2

1. Compared the delivered module and node against the read-only repository with `diff`.
   The existing theorem signature is byte-for-byte identical (also checked mechanically),
   its docstring and both public imports are unchanged, and no definition was changed.
   Verdict: pass; no statement change record is needed.
2. Compiled the delivered file locally without errors or warnings. A scratch copy printed
   axioms for both private helpers and the main theorem. The isomorphism helper uses only
   `propext`, `Classical.choice`, and `Quot.sound`; the range helper and main theorem also
   use `sorryAx` through existing imported statements. No prohibited declaration, explicit
   axiom, local sorry, or hollow definition occurs. Verdict: pass with the existing
   dependency holes already disclosed above.
3. No statement was split off and no hole was added. Read the existing finite abelian/set
   comparison and pullback statements and the point-lifting hypotheses. The closed
   immersion supplies stalk surjectivity for lifting over the same field. Checked empty
   interiors, the empty union/cover, and arbitrary immersed scheme structures: the proof
   never assumes an actual factorization through the stratum. The helper for isomorphisms
   duplicates the pattern of an inaccessible private helper in PullbackFiniteLocallyConstant,
   not an available public result. Verdict: pass.
4. Read GenericConstancy, Refinement, and UniversalHomeomorphism and searched the nearby
   Sheaf files for the isomorphism, range-containment, and open-cover routes. Their abelian
   finite-generation results cannot replace actual finite set stalks. The selected route
   uses their proved local-constancy results and transports actual finiteness separately.
   Removing each of the three retained proof-only imports in scratch copies fails with
   the corresponding unknown theorem, so each is needed. Every removed old proof dependency
   is listed in `No longer needed`; retained geometry and composition nodes are distinguished
   there from removed direct imports. The unit's `realized` statement and steps are empty,
   and the fibre-product/descent/interior-cover route is preserved. Verdict: pass.
5. Checked the node's proof steps against the Lean proof, all dependency node declarations,
   and that `proof_deps` is exactly the union of the steps' `uses`. Changes to the existing
   node are confined to `proof`, `proof_deps`, and `proof_origin`. No new nodes are present.
   Verdict: pass.

Second reading changed only this report by adding the review and verification evidence.
The Lean proof and node required no repair.
