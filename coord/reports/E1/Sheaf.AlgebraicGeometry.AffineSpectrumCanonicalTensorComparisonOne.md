## What changed

Proved `AlgebraicGeometry.SingleComplexBaseChange.canonicalSpectrum_tensor_comparison_one`
in `Sheaf.AlgebraicGeometry.AffineSpectrumCanonicalTensorComparisonOne`, with its
statement and all public imports unchanged. Seven proved private helpers implement the
existing four-step plan: identify restriction with the tensor-stalk unit, compute the
composition mate on unit germs, compare the two routes, transport pure tensors, remove
restriction-of-scalars casts, and compute the two fixed complex comparisons degreewise.
The final proof composes these equalities and cancels the spectrum tensor-stalk map.

The composition helper uses Mathlib's `unit_conjugateEquiv_symm` and
`Adjunction.comp_unit_app`; the restriction helper uses
`Adjunction.unit_leftAdjointUniq_hom_app`. Both use the existing, proved germ specification
of `Scheme.Modules.exists_tensorPullback_stalk_iso`. Sources checked: Stacks Tags 0098
and 0096. No source-point, scalar-map, or choice of chain coordinates was changed.

Broad rewriting of the composite map caused a 60-second timeout. Explicit `congrArg`
and equality composition avoid unfolding its comparison constructions; the full proof
compiled in approximately 30 seconds before formatting cleanup. No definition was changed.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.SingleComplexBaseChange.canonicalSpectrum_tensor_comparison_one`
(node `lem-pc-affine-spectrum-canonical-tensor-comparison-one`).

Proved 1 of 1 original sorries; added 0 holes and split off 0 statements. No `sorry`
remains in the delivered module. All seven private helper theorems are proved.

## No longer needed

None. All original imports and planned proof dependencies are used. The existing unit
route and the node's four proof steps are retained; no node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error was found. The chain-coordinate dependency initially
lacked a compiled local artifact; the next green build and library refresh resolved this.
The general composition and restriction calculations were proved directly rather than
left as new statements.

## Second reading by E1

1. Interface: PASS. Diffed the complete delivered module against the repository.
   The sole existing theorem signature is byte-for-byte identical, as are its
   docstring, namespace, section variables and four public imports. The only Lean
   additions are seven private proved helpers and proof-local heartbeat settings;
   the original `sorry` is replaced by a proof. No definition or public statement
   changed, so no interface change record is required.
2. Proof and trust: PASS. Compiled the module with lcompile.py, cleanly in 30.7 s.
   Compiled a scratch copy with `#print axioms` for the public theorem and every
   private helper, cleanly in 34.0 s. Each lists exactly propext, Classical.choice
   and Quot.sound; none lists sorryAx. No sorry, axiom, unsafe, opaque,
   implemented_by, extern or kernel-check bypass occurs in the delivered module.
   No data definition or arbitrary existence-witness construction was added.
3. Split statements and small cases: PASS. There are no split-off statements,
   new public declarations or new holes. Read all private helper statements and
   proofs: the two cast lemmas reduce by equality elimination; the germ lemmas
   use the specified adjunction units, not independently chosen comparisons.
   Zero modules and zero scalar rings satisfy the same equations; empty schemes
   have no point to supply; every integer degree is covered without a boundedness
   assumption. The existing chosen tensor-stalk isomorphisms and tensor maps are
   pinned by their generating germ and restriction formulas.
4. Route and pruning: PASS. Read the imported comparison definitions and the
   tensor-stalk component specification. The final proof successively applies
   tensorStalkIso_one, additive_one, square_one, the canonical chain-coordinate
   formula, and inverse-isomorphism cancellation, implementing all four node
   steps. Searched Sheaf, the source library, and Mathlib using unit/germ/mate
   terminology; checked related open-restriction calculations and used msearch
   Loogle for unit_conjugateEquiv_symm. Existing Mathlib adjunction lemmas are
   already used; no shorter applicable comparison theorem was found. All four
   public imports provide declarations occurring in the original signature.
   Every old proof dependency is used, so `No longer needed: None` is complete.
   Read dag/units/sk-thm-picard-semicon.json: its realized fields are unchanged
   (currently empty), and this local calculation bypasses no unit step.
5. DAG correspondence: PASS after provenance correction. The node's statement,
   four proof steps and five proof dependencies match the actual Lean argument.
   No new nodes are needed for the proved private elementary calculations.
   Updated proof_origin from the original N4 statement-plan provenance to E1,
   naming the Mathlib unit identities and tensor-stalk component equations used
   by the actual proof; retained the source citation and all dependencies.

Second reading changed only the node's proof_origin and this report. No Lean
repair was needed. Verified net holes: one original hole closed, zero added;
one of one proved, zero split off, no nodes or modules pruned.
