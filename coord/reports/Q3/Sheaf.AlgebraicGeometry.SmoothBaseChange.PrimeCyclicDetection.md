## What changed

Replaced the sole hole in
`Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeCyclicDetection` by a compiling proof,
with its original signature unchanged. The proof chooses the constant module on the
geometric point, restricts coefficients to `ULift ℤ`, applies bounded torsion
prime-coefficient vanishing by contradiction, excludes units by scalar cancellation,
and identifies the prime-field quotient coefficient with the underlying cyclic group.
The prime quotient comparison is proved as a private helper in the original module.
No definition or existing statement was changed.

Added three modules, each with one public theorem and its own node:

- `GeometricPointModuleConstant`: module-valued constancy proved from the existing
  set-valued point theorem, `constantSheafAdj_counit_w`, reflection of isomorphisms,
  and the existing constant-sheaf pullback isomorphism.
- `CoefficientHigherDirectImageZero`: preservation and reflection of higher-direct-image
  vanishing proved from the existing restriction-of-scalars base-change comparison on
  an identity Cartesian square. Faithfulness and preservation of zero morphisms give
  reflection of zero objects. This uses a named existing dependency, as intended
  in stage 3; it does not add another coefficient-comparison hole.
- `TorsionConstantPrimeDevissage`: the remaining bounded torsion group argument, stated
  over integer coefficients with a complete sourced proof in words. It is strictly the
  primary decomposition / prime-power induction / filtered-union part of the argument:
  it has no geometric point, no original coefficient ring, no unit condition, and no
  base-change target. All transformations between it and the original theorem are
  implemented and compiled.

Updated only the existing node's proof, proof_deps and proof_origin, and added the
three corresponding nodes. The universal-datum unit's geometric-point cyclic reduction
route is kept; its other steps and all target statements are untouched.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.exists_prime_cyclic_higherDirectImage`
(node `lem-sbc-prime-cyclic-detection`). There are no holes left in the item's module.

The new theorems
`AlgebraicGeometry.Etale.exists_constant_module_upperStar_geometricPoint` and
`AlgebraicGeometry.Etale.isZero_higherDirectImage_restrictScalars_iff` are proved.
The private theorem `prime_cyclic_vanishing_in_integer_coefficients` is proved.

Exactly one hole is added:
`AlgebraicGeometry.Etale.isZero_higherDirectImage_constant_of_prime_vanishing`,
node `lem-sbc-torsion-constant-prime-devissage`, in the new module
`Sheaf.AlgebraicGeometry.SmoothBaseChange.TorsionConstantPrimeDevissage`.
Its proof is exactly `by sorry`. This delivery is a one-hole-to-one-hole decomposition,
with the geometric-point and coefficient comparison glue proved, not a claim that the
entire torsion argument or its imported open dependencies are now proved.

Local single-file and sandbox compilation pass. Separate scratch verification checks
cover annihilator 1 (the module is zero, so every image vanishes), negative degrees,
and the injectivity exclusion on ZMod 2 and ZMod 3. Mathematically the zero group and
empty primary sum satisfy the theorem; for a nonzero r-primary group multiplication
by r cannot be injective. Degree zero uses left-exact direct image and the same
middle-term exactness, so no q > 0 assumption is needed. These checks do not apply the
new open theorem and hence do not merely test its assumed conclusion.

## No longer needed

Removed these direct proof imports from the item's module:

- `Sheaf.AlgebraicGeometry.EtaleInverseImageExact`
- `Sheaf.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant`
- `Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit`

The explicit inverse-image exactness import is replaced here by the already-proved
`baseChangeTargetFunctorIso`; the node `prop-weil-pbc-inverse-image-exact` is no longer
a direct proof prerequisite of `lem-sbc-prime-cyclic-detection`.
`Sheaf.AlgebraicGeometry.InjectiveModuleDirectImageAcyclic` stays imported because it
realizes a step of the protected unit `sk-thm-p1`. This is the unit-route exception to
removing an import whose theorem is not applied directly in this proof. The theorem's
work is consumed here through the existing `restrictScalars_baseChange_comparison`.
No assertion is made that any removed direct import leaves every target's closure:
other users and the comparison's transitive proof dependencies can still need it.

The set-valued constancy import is retained in the new proved constancy module;
the long exact sequence and filtered colimit imports are retained in the new
open devissage module as its planned proof dependencies. Likewise
`lem-sc-coprime-torsion-decomposition` and
`lemma-weil-pbc-direct-image-filtered-colimit` remain below that node. These are
relocations below the reduction, not mathematical pruning of the torsion route.
`lem-weil-pbc-constant-module-sheaf-underlying` remains needed through its general
Mathlib match `constantCommuteCompose`, now applied to restriction of scalars.
No blueprint unit statement or step was bypassed.

For completeness, the old node's direct proof dependencies removed from the item are
`lem-sc-coprime-torsion-decomposition`, `lem-weil-pbc-derived-functor-long-exact`,
`lem-weil-pbc-injective-module-direct-image-acyclic`,
`lem-weil-pbc-spec-algebraically-closed-etale-sheaf-constant`,
`lemma-weil-pbc-direct-image-filtered-colimit`, and
`prop-weil-pbc-inverse-image-exact`. The first, second and fifth relocate below
torsion devissage; the fourth relocates below module constancy. The third remains
as a protected import rather than a directly applied theorem. The sixth is replaced
by the existing `baseChangeTargetFunctorIso`. Second reading also removed the planned
`lem-constructible-constant-exact` dependency of the new torsion node, using existing
general constant-sheaf exactness instances instead. None of this claims an entire
module pruned from the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The original node's first step cited a set-valued constancy theorem as though its
signature directly gave module-valued constancy. The delivery supplies and proves
that transfer using the counit comparison. Also the injective-module acyclicity
statement is encoded in smaller-ring-universe `SheafOfModules`, while the coefficient
ring here is in `Type (u+1)` and the sheaves are `Sheaf (ModuleCat Λ)`. The existing
restriction-of-scalars comparison fits the actual coefficient universe and avoids
repeating that interface conversion.

The existing filtered-colimit theorem's Lean signature quantifies `J : Type` (Type 0),
whereas a diagram of finitely generated subgroups of an arbitrary `M : Type (u+1)`
can be larger. The remaining node explicitly calls out this size obligation: use the
qcqs cohomology-colimit and sheafified-presheaf argument at the subgroup index universe;
do not silently pretend the Type 0 theorem covers it. This does not make the new
vanishing statement mathematically false. The worker taking it should generalize the
colimit interface as needed, or implement the sectionwise argument.

An overlay graph audit found the pre-existing cycle
`lem-weil-pbc-sheaf-algebraic-structures-objects` ->
`lem-weil-pbc-sheaf-algebraic-structures-abelian-component` ->
`lem-weil-pbc-sheaf-algebraic-structures-objects`. The corresponding two edges already
exist in the repository and are outside this item's ownership. They are reported for
maintainer repair rather than silently edited here.

The existing cyclic-reduction node
`lem-sbc-constant-module-higher-direct-image-cyclic-reduction` was inspected; it treats
only coefficients Λ/dΛ and all cyclic divisors, and does not supply vanishing for an
arbitrary constant group with injective primes excluded. The existing
`lem-weil-pbc-module-constant-of-set-pullback` was also inspected; it requires a connected
pullback scheme and does not directly apply to arbitrary Y here. Neither is duplicated
by the new statements.

The literature checkout on this machine contains citation lists but no Stacks tex
files. The source tags were read from the official Stacks pages instead:
https://stacks.math.columbia.edu/tag/0F08,
https://stacks.math.columbia.edu/tag/03FD,
https://stacks.math.columbia.edu/tag/0739,
https://stacks.math.columbia.edu/tag/03P5,
https://stacks.math.columbia.edu/tag/03Q1,
https://stacks.math.columbia.edu/tag/0A3H,
https://stacks.math.columbia.edu/tag/0D6J.
Actual LeanFinder, Loogle and Mathlib-source searches are recorded in the nodes.
LeanSearch returned Internal Server Error and is recorded as unavailable, not as
having established absence of a matching theorem.

## New nodes

`lem-sbc-geometric-point-module-constant` records the proved module-valued constancy
and pullback result. Its proof is assembled from the existing set-valued theorem and
Mathlib's coefficient/counit comparison; no new hole is introduced.

`lem-sbc-coefficient-higher-direct-image-zero` records the proved higher-direct-image
zero criterion under restriction of scalars. Its proof uses the existing coefficient
base-change comparison on an identity square and faithful reflection of zero objects.
No new hole is introduced. The current checkout proves the existing comparison;
its transitive dependencies still contribute sorryAx.

`lem-sbc-torsion-constant-prime-devissage` is the one remaining theorem: primary
components, finite cyclic prime powers, middle-term exactness, and filtered subgroup
unions. It is the strict torsion portion of the original plan and is independently
usable for arbitrary constant integer-module coefficients. There are no change records
because no existing definition or signature changes.


## Second reading by Q3

1. **Unchanged interfaces: pass.** Compared the item with the repository by diff.
   The signature of `exists_prime_cyclic_higherDirectImage` is byte for byte unchanged.
   There are no existing definitions changed and no change records required. The only
   existing node fields changed are `proof`, `proof_deps`, and `proof_origin`.
   New helper signatures also agree verbatim with their new nodes.
2. **Proof and trust checks: pass.** Compiled all four modules locally through
   `lcompile.py`, without errors or warnings. Read every proof, including the private
   quotient comparison. Scratch copies with `#print axioms` for all five declarations
   show only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. There is exactly
   one textual hole, the named public torsion devissage theorem; no definitions,
   private holes, new axioms, or forbidden implementation attributes were introduced.
   The two new proved public theorems still depend transitively on existing open proofs.
3. **Split statements: pass with a plan repair.** The sole remaining hole is the
   bounded torsion portion, strictly smaller than geometric-point cyclic detection.
   Checked zero modules, annihilator 1, absent primary components, negative degrees,
   and middle-term exactness in degree zero. Recompiled the scratch tests for n = 1,
   negative degrees and injectivity on ZMod 2/3, independently of the new hole.
   Fresh LeanFinder search for annihilator-based constant cohomology vanishing returned
   group cohomology statements, not this theorem. Fresh Loogle search found
   `Sheaf.isConstant_iff_forget`, an ingredient rather than the pullback statement.
   Read the existing cyclic reduction and module/abelian derived comparison; neither
   supplies this arbitrary-module prime vanishing statement directly. Checked the
   source cyclic reduction [Stacks 0F08](https://stacks.math.columbia.edu/tag/0F08)
   and colimit result [Stacks 0739](https://stacks.math.columbia.edu/tag/0739).
   The natural-language proof is complete; its large-index colimit interface obligation
   is explicitly recorded rather than silently supplied by the Type 0 theorem.
4. **Route and pruning: pass.** The Lean proof implements the geometric-point,
   coefficient, unit-exclusion and quotient conversions, and uses existing declarations
   for those conversions. No unit route was replaced. The universal-datum unit's
   `realized` arrays are empty in the repository, so they cannot certify a completed
   realization; the unit's written cyclic-coefficient step is retained. The protected
   `sk-thm-p1` acyclicity import stays by the unit-route exception. All six former direct
   proof dependencies removed from the item are accounted for:
   `lem-sc-coprime-torsion-decomposition`,
   `lem-weil-pbc-derived-functor-long-exact`,
   `lem-weil-pbc-injective-module-direct-image-acyclic`,
   `lem-weil-pbc-spec-algebraically-closed-etale-sheaf-constant`,
   `lemma-weil-pbc-direct-image-filtered-colimit`, and
   `prop-weil-pbc-inverse-image-exact`. The torsion and point dependencies relocate
   beneath the helpers; acyclicity is retained as a protected import and is used by
   the coefficient comparison route; inverse-image exactness is replaced by the
   existing comparison isomorphism. No whole module is claimed pruned from all targets.
5. **DAG agreement: pass after repair.** Read the four nodes against the declarations
   and checked their dependencies and creation/source/search records. Removed
   `lem-constructible-constant-exact` from the new torsion node's proof dependencies:
   its finite-ring signature cannot apply to integer coefficients. The already-proved
   `preservesFiniteLimits_constantSheaf` and `preservesFiniteColimits_constantSheaf`
   instances in `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver`
   give the needed exactness directly. Added that proof-only import, identified the
   instances in the new docstring and node, and compiled a scratch application of
   `ShortComplex.ShortExact.map_of_exact` over `ULift ℤ` without finiteness assumptions.

Second reading changed only the torsion helper's proof-plan import and documentation,
its node's exactness dependency, and this report (including stale wording about the
existing coefficient comparison). No existing signature or proof body was rewritten.
The delivery remains one hole closed and one hole added: a decomposition with net zero
holes, not an axiom-free proof of the target.
