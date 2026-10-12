## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.AffineDerivedHomEvaluationCounit` with a complete proof from the
existing affine derived sheaf-Hom adjunction and two new intermediate statements.
The declaration's statement and its public imports are unchanged.

The private `affineScalarLocalizationIso` uses the existing scalar-restriction exactness
instances, the proved exact-functor/right-derived comparison, and fully faithful
precomposition with Q. The private `transportEvaluation` proves the naturality calculation
that transports evaluation both across the left-functor isomorphism and from a complex
representative to an arbitrary derived object. Both helpers are completely proved.

Added proof imports of `DerivedInternalHomUnitIso`, `AffineDerivedHomLocalizedEvaluation`
and the source library's `RightDerivedFunctor.MapDerivedCategory` module. Updated the
assigned DAG node's proof, proof_deps and proof_origin to match the implementation.

## Proved and sorry left

Closed the body of `AlgebraicGeometry.exists_affine_derivedHom_evaluation_counit`
(the item's one original sorry), by reduction to existing declarations and two intermediate
theorems. This is a decomposition: one hole closed and two holes added, net -1; it is not
a sorry-free proof of the result.
No sorry remains in the assigned module.

The delivery adds exactly these two named public sorries:

- `AlgebraicGeometry.derivedInternalHom_unit_iso`, node
  `lem-sc-derived-internal-hom-unit-iso`, in `DerivedInternalHomUnitIso.lean`.
- `AlgebraicGeometry.affine_derivedHom_localized_evaluation`, node
  `lem-sc-affine-derived-hom-localized-evaluation`, in
  `AffineDerivedHomLocalizedEvaluation.lean`.

The first is only the unit-Hom natural isomorphism. The second constructs neither the
adjunction nor that isomorphism: it assumes the underived and derived adjunction data and
their sectionwise and chain-level counit formulas, and establishes comparison only on
complex representatives. The main proof genuinely combines these with the existing
adjunction theorem and proves the two transport operations.

All three modules compile locally. Delivery dry-run validation is the final check.

## No longer needed

None of the original imports or their modules can be removed: the affine
adjunction is used directly, the algebra-derived module supplies scalar exactness, and
DerivedInternalHom supplies the shared functor. The old direct proof edge to
`def-pur-derived-internal-hom` is replaced by the two new lemmas, which retain that
dependency; its module is still needed for the statement and is not pruned. The two additional comparison clauses
returned by exists_affine_derivedSheafHom_adjunction are unused; no separate module is
imported for them. No unit-level statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was corrected. The existing derived adjunction interface gives
an unspecified underlying-Hom isomorphism and a chain-level derived counit formula, but
no theorem connecting that isomorphism to precomposition by the unit. A compatible
localization comparison is therefore needed separately; the existing arbitrary
isomorphism alone cannot prove the evaluation identity.

Read Stacks Tags 0BUZ, 0BV0 and 0AX3 at their official pages. The local literature tex is
absent on this machine. LeanFinder and Loogle supplied only underived unit-Hom formulas;
grep found no derived unit/evaluation identity. LeanSearch returned an internal server
error and is recorded as unavailable, not as a negative search result.

Checked the new statements on zero objects and arbitrary shifts: evaluation is degreewise
and the argument uses unbounded K-injective resolutions. The localized comparison permits
any unit-Hom isomorphism: relative to canonical evaluation j, adjust d by RHom(A, alpha),
where alpha = iota.inv followed by j.hom. Naturality cancels j.inv followed by iota followed
by alpha, so the choice introduces no extra hypothesis. The arbitrary-derived-object
transport is formal and was checked by Lean.

Blueprint searches for derived internal Hom and evaluation at one found no blueprint
statement matching either intermediate theorem. The new nodes retain the assigned node's
ancestor and unit; its unit record has no realized statement/steps that this split bypasses.

## New nodes

`lem-sc-derived-internal-hom-unit-iso`:
`lean/Sheaf/AlgebraicGeometry/DerivedInternalHomUnitIso.lean`. Isolates step 3 of the
assigned plan. Its docstring gives evaluation and its inverse, the Hom-complex differential
calculation, and descent through Q.

`lem-sc-affine-derived-hom-localized-evaluation`:
`lean/Sheaf/AlgebraicGeometry/AffineDerivedHomLocalizedEvaluation.lean`. Isolates the
Hom comparison and evaluation compatibility on representatives (steps 2 and 4), with all
input adjunction data and both counit formulas explicit. Its docstring includes the
adjustment for an arbitrary iota. Both nodes have source, complete proof steps, actual
searches, and exact Lean signature records. No change record is needed because no existing
public signature or definition was changed.


## Second reading by X2

1. Compared the assigned module with the repository using diff and an exact substring
   comparison of the original theorem signature through `:= by`: byte for byte identical.
   Its existing docstring and public imports are unchanged. Both added modules are new;
   no existing public definition or statement was changed. Verdict: pass.
2. Compiled all three delivered modules in dependency order using lcompile.py: no errors
   or warnings. Scanned for forbidden declarations and attributes: none. The assigned
   module contains no sorry; exactly the two reported public theorems have sorry bodies.
   A scratch copy with #print axioms checked the main theorem, both private helpers and
   both new lemmas. Only propext, Classical.choice, Quot.sound and sorryAx occur.
   transportEvaluation has no sorryAx; scalar comparison still rests on existing open
   exactness/resolution results. The scratch file was removed. Verdict: pass as a
   decomposition, not a proof without open dependencies.
3. Read the two new statements, their docstring proofs, the definition of homComplex,
   derivedInternalHom and its comparison, and the full existing affine adjunction.
   The unit lemma is a separate natural-isomorphism assertion. The localization lemma
   assumes the adjunctions, the underived evaluation equation and the derived counit
   factorization; it establishes only the missing compatible comparison on complexes.
   Neither restates the original existence theorem. Zero complexes, the identity
   morphism, the empty scheme and arbitrary shifts give the expected unit/evaluation
   identities. For arbitrary iota, alpha = iota.inv followed by canonical_iota.hom is
   invertible; naturality gives F(alpha);p;iota = p;iota;alpha = p;canonical_iota.
   This confirms the adjustment in the proof and shows no normalization hypothesis is
   missing. Fresh LeanFinder queries used “tensor unit concentrated in degree zero” and
   “localizing an exact restriction of scalars adjunction”; results were only underived
   unit formulas and ModuleCat restriction/coextension counits. Loogle homObjUnitIso had
   no hit; rg found the upstream SheafOfModules.homObjUnitIso, which is underived and
   does not supply the Hom-complex/localization calculation. Neither new hole can be
   closed by that lemma alone in a few minutes. Verdict: true, needed, strictly separate
   parts of the argument, with no duplicate theorem found.
4. Read the proof top downward: the existing adjunction supplies the functors and counit;
   the exact-functor/localization API proves the scalar comparison; naturality proves
   transport to all derived objects. No shorter supplied theorem includes the needed
   evaluation compatibility. All proof-only additions use plain import. The existing
   RingedSpaceDerivedDirectImage import supplies the ringed-space Grothendieck instance
   needed for rightDerivedFunctor in the signature; PullbackFree supplies the unit map.
   Checked the old proof_deps against the new direct uses and corrected the report to
   distinguish a replaced direct DAG edge from a pruned module. The unit record
   sk-thm-picard-duality has empty realized statement/step lists; no realized node or
   unit route was replaced. Verdict: pass; no module pruned.
5. Read all three node files and checked each Lean declaration and its recorded
   signature. Existing-node changes are confined to the owned proof fields; new nodes
   contain sources, complete steps, searches, ancestry, unit/chapter and Lean records.
   Corrected the localized node's ordinary-composition notation from H composed with T
   to T composed with H, matching Lean's H followed by T. The main proof_deps are the
   two new lemmas, existing affine adjunction and scalar-exactness module. Verdict: pass.

Changes in this reading: corrected the report's decomposition accounting and replaced
proof-edge description; corrected the new node's composition notation; corrected the
new modules' author attribution to X2. No Lean proof or statement was altered.

Source check: read [Stacks 0BUZ](https://stacks.math.columbia.edu/tag/0BUZ) for the
underived adjunction, [0BV0](https://stacks.math.columbia.edu/tag/0BV0) for deriving it,
and [08J7](https://stacks.math.columbia.edu/tag/08J7) for the unbounded K-injective
internal-Hom construction. [0AX3](https://stacks.math.columbia.edu/tag/0AX3) discusses
trace compatibility for finite Noetherian morphisms on bounded-below quasi-coherent
objects; it is motivation for evaluation, not by itself a source for the full
unbounded affine assertion. The supplied degreewise argument provides that extension.
