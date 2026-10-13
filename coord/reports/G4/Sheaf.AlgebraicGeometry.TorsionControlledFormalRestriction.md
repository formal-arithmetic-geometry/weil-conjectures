## What changed

Proved `AlgebraicGeometry.torsionControlled_formal_restriction` in
`Sheaf.AlgebraicGeometry.TorsionControlledFormalRestriction`, with its full signature,
visibility, original docstring and public imports unchanged.

The completion comparison is constructed from the two quotient universal properties.
Private proved helpers identify the restricted multiplication image, build the quotient
isomorphisms and their projection equations, and cancel quotient epimorphisms to assemble
the natural isomorphism. The equality `hH` is eliminated in a helper accepting an arbitrary
underlying local module, so the final projection equation contains exactly the required
`eqToHom hH.symm`.

The torsion argument uses quasi-coherence of component kernels and cokernels, exactness of
open restriction, and the existing ideal-power vanishing restriction theorem. Transport
along component isomorphisms uses the already proved `formalModuleQuotient_factor`:
the induced map of products is monic and its target is zero. No data is chosen from an
unproved existence theorem. The existential comparison is constructed by `NatIso.ofComponents`.

Added proof imports for `ModulePullbackIdealPowerProductImage` (using `import all` to reuse
its proved private power-subobject and product-inclusion comparisons),
`IdealPowerProductRestrictionZero`, `CoherentFiniteTypeLocallyNoetherian`,
and the source library's `Modules.QuasicoherentCokernel` (which publicly imports
`Modules.QuasicoherentKernel`).
The general tensor-pullback image theorem itself is not used; its two proved helpers are.
The single-product affine restriction theorem is visible through the `import all` dependency.
Updated the existing DAG node's proof, proof dependencies and proof origin to match.

Sources: [Stacks 0887](https://stacks.math.columbia.edu/tag/0887) for the quotient
pullback calculation and [Stacks 0888](https://stacks.math.columbia.edu/tag/0888)
for the component kernel/cokernel annihilation context. The local literature checkout
is absent on this machine, so these two sources were read online.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.torsionControlled_formal_restriction`
(node `lem-weil-pbc-torsion-controlled-formal-restriction`).
All newly introduced helpers are private and proved.
`#print axioms AlgebraicGeometry.torsionControlled_formal_restriction` reports exactly
`[propext, Classical.choice, Quot.sound]`, with no transitive sorry axiom.
No `sorry` remains in the item;
no holes were added in any module. This is a proof, not a decomposition.

Local single-file compilation passed with no warnings. The delivery dry run passed its
compilation, axiom probe and preflight checks, except for the second reading reserved
for the next worker; nothing was pushed.
The argument includes `t = 0`, quotient exponent zero in the helpers, empty opens,
zero modules and zero/unit ideals: all comparisons use universal properties and image
identities without positivity, nonemptiness or properness assumptions.

## No longer needed

Pruned planned dependency `lem-weil-pbc-formal-systems-pullback`, module
`Sheaf.AlgebraicGeometry.FormalSystemsPullback`, from this item's proof dependencies.
It was not imported by the original file and is not imported by the delivery.
The canonical quotient comparison is built directly, without invoking or choosing
any formal pullback functor. This does not assert the module is globally unreachable.

No original public import was removed. No other planned dependency was pruned.
The final reuse check retained `ModulePullbackIdealPowerProductImage` to reuse its
proved private comparison lemmas rather than duplicating their proofs locally.
The unit's realized statement and steps are preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The general `exists_formalSystemsPullback`
statement supplies a completion isomorphism but does not expose the quotient-projection
normalization required here; direct cokernel comparisons supply it. The original plan's
restriction and annihilator argument is retained, but the general formal-system pullback
dependency is unnecessary. No forced adaptations or interface changes were needed.

## Second reading by G4

1. PASS: compared the sole delivered module with the repository using `diff` and
   separately checked the existing theorem signature byte for byte. Its hypotheses,
   conclusion, visibility, original docstring and sole public import are unchanged.
   Only proved private helpers, a noncomputable section and proof imports were added;
   no definitions used in an existing signature changed and no change record is needed.
2. PASS: independently compiled the module using `lcompile.py`, without warnings.
   A scratch copy with `#print axioms AlgebraicGeometry.torsionControlled_formal_restriction`
   reports only `propext`, `Classical.choice`, `Quot.sound`. Inspected all helper bodies:
   no sorry, forbidden declaration or hollow definition. The quotient comparison uses
   explicit cokernel isomorphisms, not an arbitrary unproved existence witness.
3. PASS: no split-off statement or new node, and no new hole. Checked the component
   comparison direction, quotient projection equation, transition naturality, and
   annihilator transport. At t = 0 the same product-factor argument applies; empty
   opens, zero modules and zero/unit ideals require no extra hypotheses. Independent
   Loogle search for cokernel.mapIso confirmed the generic tool used; Lean Finder
   search for exact restriction of ideal-power cokernel systems returned module adic
   completion formulas, not a replacement for this sheaf-system comparison.
4. PASS: read FormalSystemsPullback and the reused ideal-power and restriction
   helpers. Its public existential comparison lacks the projection normalization,
   so the direct cokernel construction is appropriate. Library searches for
   restriction/completion and quotient comparisons found no shorter applicable public
   theorem. No longer needed lists the only old proof dependency removed:
   lem-weil-pbc-formal-systems-pullback. Read sk-thm-p1's realized statement and all
   realized steps: this local helper pruning bypasses none of them. Proof-only imports
   are private. Removed the redundant direct QuasicoherentKernel import, already
   publicly imported by QuasicoherentCokernel; retained both kernel and cokernel nodes
   because both theorems are used.
5. PASS: the node differs only in proof, proof_deps and proof_origin. The dependency
   list equals the union of proof-step uses. Read the corresponding Lean arguments:
   recursive-power/product inclusion comparisons, quotient naturality, coherent to
   quasi-coherent conversion, exact restriction, and zero-product transport all match.
   No new-node requirements apply.

Second reading changed only the redundant proof import and the report documenting
that removal and these checks. The mathematical proof required no repair.
