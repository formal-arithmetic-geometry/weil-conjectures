## What changed

Proved `AlgebraicGeometry.Scheme.Modules.finiteType_module_support_pullback` with its
signature and public imports unchanged. Added four proved private helpers: restriction
preserves finite type; finite affine generators generate each stalk; field extension
reflects subsingletons; and residue fibres of tensor pullback vanish exactly when the
original residue fibres vanish.

The finite-stalk argument uses `quasicoherent_finite_type_affine` and the additive
localization isomorphism plus denominator formula of `finite_type_module_support_closed`.
Repair of the returned duplicate: generalized the slice-site restriction helper to
`finiteType_over_ringSheaf`, for an arbitrary topological space and arbitrary sheaf of
rings on its open-set site. Its statement no longer requires a scheme or its structure
sheaf. The existing `FinitePushforwardCoherent.isFiniteType_over` is private and cannot
be imported as a usable declaration. This follows the return's explicit alternative,
"generalize it in place"; it is a mathematical generalization, not merely a rename.
The finite-stalk proof specializes the generalized helper to `X.ringCatSheaf`.
No other module is adapted and no public interface changes. Nakayama is Mathlib's `IsLocalRing.subsingleton_tensorProduct`.
The pullback stalk is finite by `Module.Finite.base_change` and its stalk isomorphism,
so quasi-coherence of the pullback is unnecessary. The fibre comparison uses
`ModuleCat.extendScalarsComp`, `Scheme.residue_residueFieldMap`, and faithful flatness
of field extensions. Set extensionality combines the pointwise equivalences.

Updated the item's DAG proof and dependencies to describe this route. The item's
blueprint unit `sk-thm-p1` has no realization at this node; its realized statement and
steps are untouched. The recorded off-route use of the stalk-pullback theorem is retained.

Validation: the repaired module is checked by local single-file compilation and
the delivery dry run. The older second reading was removed because it reviewed the
returned version; the independent second reader must review this repair.
The zero module and empty generating family are included in span induction and Nakayama;
empty schemes make the pointwise clauses vacuous. No flatness or surjectivity assumption
on the scheme morphism is introduced. The residue-fibre helper works for arbitrary
module sheaves and arbitrary scheme morphisms.

Sources read: Stacks [056J](https://stacks.math.columbia.edu/tag/056J) and
[01B5](https://stacks.math.columbia.edu/tag/01B5), the existing DAG and Lean dependency
statements, and Mathlib LocalRing.Module, ChangeOfRings, TensorProduct.Finite,
FaithfullyFlat.Basic, and AffineScheme. LeanFinder, Loogle and grep found Nakayama's
subsingleton theorem but no ready-made finite module-sheaf stalk theorem.

## Second reading by Q2

1. **Statements and accidental changes.** Compared the delivered module with the repository
   version at every existing declaration. The target signature is unchanged; only proof
   imports, private proof helpers, the proof, and DAG proof metadata changed. Verdict: pass.
2. **Proof and axioms.** Compiled the repaired module with `lcompile.py`; it has no `sorry`,
   forbidden declarations, or hollow definitions. A scratch `#print axioms` reports only
   `propext`, `Classical.choice`, `Quot.sound`, and the existing dependency `sorryAx`.
   Verdict: pass.
3. **Statements split off.** No statements were split off and no new nodes or holes were
   added. The private helpers are strictly internal reductions; zero modules, empty covers,
   and empty schemes are covered by the proof. Verdict: pass.
4. **Pruning and route.** Removed the unused proper-support and pullback-quasi-coherence proof
   imports, added only imports used by the finite-stalk and tensor arguments, and updated the
   node's proof and dependencies. The unit route and target statement remain unchanged.
   Verdict: pass.
5. **DAG agreement.** The node's proof steps and `proof_deps` describe the actual Lean route,
   including affine finite sections, localization, stalk base change, and faithful scalar
   extension. Verdict: pass.

Changed in this second reading: corrected the theorem docstring's steps 5--8 so they describe
the implemented stalk-finiteness and residue-fibre comparison route rather than the pruned
quasi-coherence route. No Lean statement or definition was changed.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.Scheme.Modules.finiteType_module_support_pullback`
(node `lem-weil-pbc-support-pullback-finite-type`).

There are no remaining `sorry`s in this module and no holes or new modules added.
The proof still depends on the existing named declarations
`finite_type_module_support_closed`, `quasicoherent_finite_type_affine`, and
`tensorPullback_isFiniteType`. The support-closed theorem and affine criterion now
have proofs in the repository; the pullback finite-type theorem still has its
existing hole. No dependency hole is added by this delivery.
This is a proof from the stated dependencies, not a claim that the target closure is axiom-free.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`: the support is an inline stalk locus;
  no proper-support construction is used. Removed proof dependency
  `def-weil-pbc-closed-subset-proper-over-base`; its statement dependency remains unchanged.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`: removed proof dependency
  `lem-weil-pbc-module-pullback-quasi-coherent`. Pullback stalk finiteness follows directly
  by base change; the proof does not need this quasi-coherence theorem.

Added the proof import `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`
and its node `lem-weil-pbc-quasi-coherent-finite-type-affine`, already reached through
`FiniteTypeModuleSupportClosed`, to make the affine finiteness premise explicit.
Added Mathlib proof imports `Mathlib.RingTheory.LocalRing.Module` and
`Mathlib.RingTheory.TensorProduct.Finite`.

Other original proof imports are used: `FiniteTypeModuleSupportClosed`,
`ModulePullbackFiniteType`, and `Modules.TensorPullbackStalk`.
No claim is made that a removed module disappears from every other target path.

## Where the brief, the DAG or earlier work was wrong

The support-closed declaration gives an additive localization equivalence, rather than
an explicitly stalk-ring-linear equivalence. Its denominator formula is sufficient:
unit scalar multiplication preserves span membership. Also, that declaration does not
itself assert finite affine sections; this is supplied by the existing affine criterion
and a proved restriction helper.

The original plan's use of quasi-coherence of the pullback is unnecessary: its stalk is
the base change of an already finite stalk. The retained declaration docstring describes
the original Stacks-style route; the updated DAG and the Lean proof record this pruning.
No source error, changed statement, new node, or forced adaptation was needed.

The returned delivery duplicated the scheme-only restriction helper word for word.
That private helper is unavailable to importers. The repair generalizes its binders
to arbitrary topological spaces and ring sheaves, with the same cover-transport proof.
This also covers empty spaces and the empty finite generating family.
