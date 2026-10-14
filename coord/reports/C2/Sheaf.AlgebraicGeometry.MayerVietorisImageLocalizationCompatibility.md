## What changed

Replaced the assigned theorem's sorry with categorical pasting, cancellation of the
K-injective computation isomorphisms, and naturality along the representative e.
The target proof imports two new statement modules, MayerVietorisImageCompositionLocalization
and MayerVietorisImageRestrictionLocalization, and the definition module
MayerVietorisRestrictionLocalizationChain. Each states one strictly partial unit
compatibility equation for arbitrary complexes. The composition equation leaves the restriction chain unnormalized; its proof uses
composition-unit compatibility and postcomposition by the inverse restriction
comparison. The restriction equation normalizes that chain and contains no open
direct image or image-component map. Neither assumes K-injectivity or mentions e.

Private, proved helpers handle naturality and pasting the two equations. The main
theorem cancels the computation isomorphisms and transports the resulting square. Their functor expressions match the defining
comparison expressions, avoiding repeated unfolding of concrete derived constructions.
The shared chain is an irreducible definition built from four existing actual maps.
It contains no hole or chosen arbitrary witness. The existing node's proof route is
updated accordingly. MayerVietorisImageChainData
is an unchanged copy used to regenerate its missing cached object.

## Proved and sorry left

Closed the original hole in AlgebraicGeometry.schemeMV_image_localization_compatibility
(lem-pc-mayer-vietoris-image-localization-compatibility). This is a decomposition,
not a proof without sorry dependencies: one original hole is closed and two are added.
The assigned module has no remaining sorry. The delivery has net minus one hole closed
(one closed minus two added), and is reported as a decomposition only.

The two new holes are:

- AlgebraicGeometry.schemeMV_image_composition_localization, in
  Sheaf.AlgebraicGeometry.MayerVietorisImageCompositionLocalization,
  node lem-pc-mayer-vietoris-image-composition-localization.
- AlgebraicGeometry.schemeMV_image_restriction_localization, in
  Sheaf.AlgebraicGeometry.MayerVietorisImageRestrictionLocalization,
  node lem-pc-mayer-vietoris-image-restriction-localization.

Both declarations have exactly `:= by sorry` and a complete transport argument in
their docstrings. Their predecessors are the existing homotopy-category composition
and restriction normalization declarations. The remaining work is transporting those
normalizations through the quotient and exact-restriction factors. No existing hole
elsewhere in the library is changed, and no definition contains a new hole.

## No longer needed

No original imports were removed, and no project node or module is globally pruned.
The old direct proof dependency
lem-pc-ringed-spaces-derived-direct-image-composition is no longer applied by the
item's proof; it is retained indirectly through the composition normalization
module and canonical comparison construction. Its module is not pruned. The two equations retain the blueprint unit's route.
The previous sandbox-only compatibility_core restatement was removed; it was not a
valid reduction and contributes no claimed pruning.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt merely renamed the target hole. Its core lemma is not used.
The DAG's mathematical route is valid. The existing normalization declarations live
on homotopy categories, whereas this item uses complex-localization maps; their
transport requires additional equations, now explicitly separated into the two nodes.

Concrete rewriting initially caused expensive conversions of composed termwise and
derived functors. Profiling isolated those conversions. Abstract categorical lemmas
with the same functor-expression shapes as the concrete definitions handle the upper
combination. A trial normalization of schemeOpenModuleImageComplex was reverted;
no existing data definition or existing public signature is changed in this delivery.

The local source cache lacked MayerVietorisImageChainData; its unchanged source was
rebuilt in the sandbox. Stacks Tags 08FE, 0D5T, 08BV and 079V were read online because
this machine does not hold the source text. Empty/full opens, identity morphisms,
and arbitrary complexes are covered by the natural isomorphism/unit constructions;
neither new equation asserts K-injectivity of a direct image.

## New nodes

def-pc-mayer-vietoris-restriction-localization-chain: the actual composite of the
exact Y-restriction factor, the localized underived restriction comparison, the
restricted direct-image unit, and the inverse X-restriction factor under derived
restricted direct image. Its declared endpoints prevent downstream unfolding.
There is no sorry in this definition.


lem-pc-mayer-vietoris-image-composition-localization: the composition-side equation,
including the degreewise image-component factorization, transport of the exact
restriction factors, and postcomposition by the inverse restriction comparison.
Its conclusion retains the unnormalized restriction chain, so the second equation
is independently needed to finish the target. Its source is the open composition normalization and
Stacks Tags 0D5T and 08FE.

lem-pc-mayer-vietoris-image-restriction-localization: the exact-restriction unit square
on a complex. It compares derived h_* followed by restriction with restriction followed
by derived (h|W)_*, without involving either open direct-image functor. Its source is
the existing four-factor restriction normalization and Stacks Tags 08FE and 079V.

No change record or forced adaptation is required.

Validation: the target module compiled in 12.3 seconds. The one unused simp argument
reported by that compile was removed before the delivery dry run.

## Earlier second reading (a previous round; superseded)
Self-review by C2 of the item and the three added nodes: the target theorem's signature is unchanged and its proof is a categorical pasting of the two strictly simpler localization equations, followed by cancellation and naturality. The new chain is an explicit composite of existing maps, with no chosen witness or sorry in a definition. The route retains the unit's composition and restriction normalization steps. The two intermediate theorem statements are exactly the equations used by the target and contain no K-injectivity or representative hypotheses beyond their stated inputs.

## Second reading by C2

Independent second reading of the worker's files, not authorship of their proof.

1. **Unchanged interface: pass.** Compared both existing delivered modules with
   the repository by diff and by the declaration parser. The sole existing
   theorem signature, including both K-injective assumptions, all four derived
   category assumptions, arbitrary E and e, and the complete equality is byte for
   byte unchanged. MayerVietorisImageChainData is byte for byte identical. Only
   private proved helpers, two plain proof imports and the target proof were added.
   No existing definition or public visibility changed; no change record is needed.

2. **Proof and axioms: pass with the disclosed holes.** Compiled all five modules
   in import order through lcompile.py: 30.3, 10.2, 3.6, 2.9 and 12.2 seconds,
   without warnings or errors. The target proof first substitutes the independent
   restriction identity in the composition identity. It rewrites the units on I
   and its open-image complex to computation inverses, multiplies by D(c.inv)
   and d'.hom on the left and HY(d.hom) on the right, and cancels the inverses.
   Its last step is the naturality square for the canonical comparison along
   e.inv; the abstract helper proves that square directly from beta.hom and
   alpha.inv naturality. No injectivity of h_*I is assumed. Printed axioms for
   the target, both split statements, the chain definition and the data module's
   construction/computation declarations. Only propext, Classical.choice and
   Quot.sound occur, plus sorryAx in the target and the two split statements.
   The definition itself and all checked data/computation declarations have no
   sorryAx. There are exactly two literal sorry bodies, both named public
   theorems in their own modules, and no forbidden declaration or hidden hole.

3. **Split statements: pass as a decomposition.** Read the statements, docstrings,
   node steps and the two predecessor normalization modules. Also read the official
   sources [08FE](https://stacks.math.columbia.edu/tag/08FE),
   [0D5T](https://stacks.math.columbia.edu/tag/0D5T),
   [079V](https://stacks.math.columbia.edu/tag/079V) and
   [08BV](https://stacks.math.columbia.edu/tag/08BV).
   These supply restriction/direct-image identification, derived composition,
   unbounded localization and the open-image representative. The complex unit
   equations are consequences of those constructions, rather than literal
   formulas quoted from the tags. The restriction chain is exactly
   aY.hom, Q(rho.hom), eta_g, G(aX.inv), with the four displayed endpoints.
   The predecessor restriction theorem gives
   LY(eta_h) ≫ alpha.hom ≫ G(aX.hom) = aY.hom ≫ Q(rho.hom) ≫ eta_g;
   cancellation proves the proposed restriction identity. The composition
   statement leaves this chain unnormalized and uses only composition-unit
   normalization, degreewise image factorization and naturality, followed by
   postcomposition with Rj(alpha.inv). Thus neither lower statement restates the
   K-injective target, and the composition statement does not hide the restriction
   unit equation. Empty W has the unique maps through the empty restriction;
   full W gives the canonical identity restriction square. Identity h and the zero
   complex likewise give the unit/identity square, without an omitted properness,
   nonempty-open or injectivity hypothesis. Searched again using LeanFinder for
   composite-derived-functor/exact-restriction squares, Loogle for exact-derived
   factors, grep for quotient transport factors, rg in the local Sheaf modules,
   and rg in the upstream module sources. Found generic comparison_fac and factor
   transport lemmas, but no existing exact complex-localization statements or
   one-line specialization closing these obligations. A bounded scratch attempt
   at the restriction transport reached the conversion heartbeat limit; it was
   not substituted for the correct disclosed hole.

4. **Route and pruning: pass.** The direct proof imports are needed for the two
   equations, and the public data import is needed in the unchanged signature.
   The shared chain import is needed in both new signatures; their normalization
   imports are plain proof dependencies. The old direct-image-composition node
   has been replaced as a direct proof dependency, which the No longer needed
   section now states; its module remains needed indirectly. No global module
   pruning is claimed. Read sk-thm-picard-semicon.json: its realized statement
   and step arrays are already empty, and this auxiliary node is not its key
   theorem. This delivery changes none of that unit's statement or route; both
   canonical composition and restriction normalizations are retained.

5. **DAG agreement: pass after metadata repairs.** The item node records the two
   equations, computation cancellation and naturality exactly as implemented.
   Every proof_deps list equals the union of its steps' uses; all new node Lean
   signatures match their modules. Repaired the definition node to have empty
   proof/proof_deps and null proof_origin: its inputs belong in stmt_deps.
   Added absent lean_audit none records and per-step source records to new nodes,
   and made the restriction node's final inverse cancellation explicit to agree
   with its docstring. Existing item fields outside the stage-3-owned fields
   remain unchanged.

Second reading changed only DAG metadata and the report (dependency accounting,
explicit net hole count, and this independent review). The worker's Lean proofs
and definitions were retained. One original hole is closed, two lower holes are
added, and no module is pruned.
