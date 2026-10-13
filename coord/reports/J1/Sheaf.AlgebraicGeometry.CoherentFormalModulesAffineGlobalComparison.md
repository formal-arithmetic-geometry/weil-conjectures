## What changed

Proved `AlgebraicGeometry.coherentFormalModules_affine_global_comparison` in
`Sheaf.AlgebraicGeometry.CoherentFormalModulesAffineGlobalComparison` without changing
its signature, universes, visibility, or existing public imports.

The proof constructs chart transport directly from `exists_formalSystemsPullback`,
composes its inverse with the inverse of `coherentFormalModules_affine`, and constructs
both requested natural isomorphisms for that same equivalence. Added proof-only imports:

- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine`;
- `Sheaf.AlgebraicGeometry.FormalSystemsPullback`;
- `Sheaf.AlgebraicGeometry.ModulePullbackIdealPowerProductImage`;
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine`.

Private, fully proved helpers reconstruct the cokernel/pullback comparison and its
naturality from `FormalSystemsPullback`, generalizing its completion comparison to
any functor landing in quasi-coherent sheaves. This matters because a finite completed
module restricted to the original ring need not be finite over that ring. A second
private helper specializes the section comparison construction from
`CoherentFormalModuleAffineSpecTransport` directly to X instead of its top open subscheme.
No arbitrary object is chosen from a new existential theorem. The existing Spec
comparison supplies the system realization and universal limiting cones; the pullback
functors are specified by their underlying-system equations.

Updated the existing node's proof, proof dependencies and proof origin to match the
actual construction. No other modules, statements or definitions were adapted. Scoped
transparency options support categorical elaboration; the two longer declarations have
scoped heartbeat limits. Single-file compilation through `lcompile.py` succeeds without
warnings and within the 60-second file limit.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.coherentFormalModules_affine_global_comparison`
(node `lem-weil-pbc-affine-global-formal-comparison`).

No `sorry` remains anywhere in the delivered module. No holes were added or split off.
Every new private helper is fully proved. The imported existing declarations and any
holes in their dependency closure remain work for their own items; this delivery proves
the stated theorem from them, rather than claiming the entire target closure is closed.

The quotient comparison uses equality of multiplication images, preservation of
cokernels, and cancellation of quotient projections. The section-limit comparison's
naturality is explicitly proved by `limit.hom_ext` and the supplied cone equations.
Both comparisons use the same constructed equivalence. The formula works for I=0,
I=the unit ideal, the empty scheme and zero modules: no proper-ideal, nonzero-ring,
or finiteness-over-the-original-ring hypothesis was added.

## No longer needed

No existing import line was removed: all four original public imports support the
unchanged statement. All four added proof-only imports are used.

The original plan's two direct proof dependencies are unnecessary for this theorem:

- `lem-weil-pbc-formal-affine-spec-transport`, module
  `Sheaf.AlgebraicGeometry.CoherentFormalModuleAffineSpecTransport`;
- `lem-weil-pbc-affine-formal-quotient-comparison`, module
  `Sheaf.AlgebraicGeometry.AffineFormalQuotientComparison`.

Neither module is imported. The first is replaced by chart transport constructed directly
on X and a proved private section comparison. The second is replaced by the more general
pullback image/cokernel comparison. This is pruning of this theorem's direct route;
other targets or modules may still need either module. No unit realization is bypassed:
this node and these two dependencies are not among `sk-thm-p1.realized`.

## Where the brief, the DAG or earlier work was wrong

The original plan described composition with affine-open Spec transport, but its public
statement supplies only a section comparison, not the underlying pullback functor or
completion comparison needed for beta. Rather than strengthen that interface or adapt
other modules, the proof constructs the transport equivalence from the existing
underlying-system equations in `exists_formalSystemsPullback`.

Likewise, the levelwise affine quotient theorem is unnecessary once the actual Spec
inverse comparison is used: natural compatibility of completion with chart pullback
suffices. Restriction of a finite completed module to A cannot be assumed coherent;
all the local quotient-comparison helpers require only quasi-coherence.

Sources checked: [Stacks 087W](https://stacks.math.columbia.edu/tag/087W),
[01IB](https://stacks.math.columbia.edu/tag/01IB), and
[00MA](https://stacks.math.columbia.edu/tag/00MA). The proof follows the existing Spec
completion theorem rather than adding any new completion hypothesis or claim.

## Second reading by J1

1. **Interface: pass.** Compared the complete delivered module with the repository
   by `diff -u`, then checked the existing theorem signature byte for byte up to
   `:= by`. The universe, `[IsNoetherian X]`, `[IsAffine X]`, arbitrary ideal data J,
   finite completed-module category F, scalar restriction R, chart/tilde completion C,
   actual top-section diagram W, and both comparisons for the same E are unchanged.
   The four original public imports and existing docstrings are unchanged. The only
   added declarations are private proof helpers; all added imports are proof-only.
   There are no adapted modules or change records.
2. **Proof: pass.** Independently compiled the delivered file with `lcompile.py`:
   exit 0, no warnings, 50.4 seconds. Compiled a scratch copy with `#print axioms`
   for all six private helpers and the public theorem: exit 0, 40.9 seconds.
   Each helper uses only propext, Classical.choice and Quot.sound. The public theorem
   additionally uses sorryAx through existing imported proof dependencies; no sorry
   occurs in this delivery. No axiom, unsafe, opaque, implemented_by, extern, or
   hollow definition occurs. The quotient comparison is obtained from image equality,
   preservation of cokernels, and epimorphic projection cancellation. Its two
   naturality checks include both system transitions and module maps. Section-limit
   naturality follows from hn after composing with every limit projection.
   P and Q are fixed on objects and maps by their underlying-system equations through
   fully faithful inclusions; adjoints are unique and limit witnesses are universal.
   No definition selects an arbitrary object from unproved mere existence.
3. **Split statements: pass, none.** One existing hole is closed and no holes or
   public statements are added. The private helpers are fully proved. Checked zero
   and unit ideals, n=0 in the quotient helper, zero modules, and the empty scheme:
   cokernel/image constructions and scalar restriction introduce no exclusions.
   In particular the completion helper only assumes quasi-coherence, not finite
   generation over the original ring.
4. **Route and pruning: pass.** Read FormalSystemsPullback and the Spec affine
   equivalence in full and the affine transport construction. The existing transport
   statement provides its section comparison but not the underlying-system equation
   or completion comparison needed here; the direct construction avoids an interface
   change. Its existing completion helper is private and restricted to coherent
   sheaves, so cannot serve the restricted completed modules. Searched the project
   with completionPullbackIso, tensorPullback/moduleSpecΓFunctor and evaluation/isoSpec;
   searched Mathlib's algebraic-geometry sources for formal completion/equivalence.
   Loogle confirms PreservesCokernel.iso and iso_inv, already used in the proof.
   Found no shorter applicable public comparison. All added imports are used.
   The old proof_deps lose precisely the two nodes listed under No longer needed;
   the Spec equivalence remains used. Checked sk-thm-p1.realized and its unit steps:
   none of this item or the two bypassed nodes realizes a protected unit step.
5. **DAG: pass.** The only changed fields are proof, proof_deps and proof_origin.
   The proof_deps are exactly the union of the steps' uses. Checked their Lean
   records and the actual uses: affine comap formulas, tensor adjunction/identity/
   composition, formal-system pullback, Spec affine equivalence, and ideal-power
   product image equality. The five steps match the ideal transport, construction
   of P/Q and E, beta, section-diagram comparison, and gamma in the Lean proof.
   No new node is needed.

Second reading changed only this report by adding the independent checks above.
No correction to the Lean module or DAG was necessary.
