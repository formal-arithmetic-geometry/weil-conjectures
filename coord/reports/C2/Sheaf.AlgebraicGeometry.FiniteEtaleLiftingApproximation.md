## What changed

The original theorem `AlgebraicGeometry.Scheme.exists_finiteEtale_lift_of_henselianPair_of_isGRing`
now has a complete Lean proof from a finite presentation completion-stage theorem and an
algebra-map approximation theorem. Its signature and all existing definitions are unchanged.
The construction of the map Y → Y_R, equality of its closed-fibre restriction with k,
finite/étale base-change instances, and the Over Y₀ isomorphism obtained by pullback pasting
are proved directly. The original node now records this four-step reduction.

The new module `Sheaf.RingTheory.HenselianApproximationAlgHom` is proved: choose
`Algebra.FinitePresentation.out`, enumerate its kernel generators, apply
`henselian_pair_approximation` at N = 1, descend evaluation with `AlgHom.liftOfSurjective`,
and prove equality modulo I using `AdicCompletion.ker_evalOneₐ_eq_map` and
`evalOneₐ_comp_algebraMap_eq_mk`. The final equality is checked on variables, then on all
polynomials, then on R using surjectivity. No further sorry was needed for this algebra glue.

The completion and finite-stage descent steps (original steps 1–4, and the corresponding
closed-fibre identification) are stated in `Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage`.
They do not assume a henselian pair or a G-ring: they only produce a model over an algebra
mapping into the completion, not a lift over A. The named theorem has the source and a
complete proof in words; it uses the existing complete-case, spreading-out, finite descent
and étale descent statements in its recorded argument.

All three modules compile cleanly with the prescribed lcompile.py. Searches ran via msearch.py:
LeanFinder found morphism-property and inverse-limit facts, Loogle found the completion
projection and `Algebra.FinitePresentation.out`, and grep found no ready-made approximation
lifting theorem. LeanSearch returned HTTP Internal Server Error; this is recorded as unavailable.
The general source-library lifting theorem cannot be used: its imports already depend on this
item through essential surjectivity, so that would introduce an import cycle.

## Proved and sorry left

Proved in the item:
`AlgebraicGeometry.Scheme.exists_finiteEtale_lift_of_henselianPair_of_isGRing`
(node `lem-weil-pbc-finite-etale-lifting-approximation`).

Proved in a new module:
`exists_algHom_approximation_mod_ideal`
(node `lem-weil-pbc-henselian-approximation-alg-hom`).

Exactly one direct sorry remains in the delivery:
`AlgebraicGeometry.Scheme.exists_finiteEtale_completion_stage`
(node `lem-weil-pbc-finite-etale-completion-stage`). Its proof is exactly `by sorry`.
The two proved declarations still depend transitively on unproved existing/new theorems;
this is a stage-3 reduction, not a claim that their final axiom lists are sorry-free.

Edge cases checked: the finite presentation proof permits zero variables and zero relations
(the corresponding Fin types are empty). For R = A, the identity map supplies the expected
approximation. For I = 0, the completion-stage assertion reduces to the cover itself after
canonical identifications; for I = A its closed fibre is empty and it may descend over the zero
stage algebra. Empty covers are allowed. The completion-stage assertion requires no map back
to A, which would be false without approximation. All rings and schemes remain in universe u.

## No longer needed

Removed from the item's direct imports:
`Sheaf.AlgebraicGeometry.DescendFinite`,
`Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent`,
`Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete`,
`Sheaf.RingTheory.AdicCompletionNoetherian`,
`Sheaf.RingTheory.HenselianPairApproximation`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`.
These modules remain required through the two new helper modules; they are not globally pruned.
The other original proof dependencies likewise remain in the completion-stage node except
`lem-weil-pbc-complete-pair-henselian`, which is no longer needed on this route.
The current complete-case theorem has no henselian hypothesis, so the completion's henselian
instance is unnecessary. No unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The old item's completion step supplied henselianity solely for an earlier version of the
complete-case statement. The current `exists_finiteEtale_lift_of_isAdicComplete` requires only
Noetherianity and adic completeness. That redundant dependency is removed from the new route.
No existing statement or definition was changed.

The repository copy does not contain literature/stacks-project/pione.tex. The source paragraph
was read on the official Stacks Project page https://stacks.math.columbia.edu/tag/0GS2,
“Essential surjectivity when (A, I) is a henselian pair and A is a Noetherian G-ring”.
The node records retain the project's canonical literature path and label. The source does not
use G-ring approximation until after the completion-stage model is constructed.

## New nodes

`lem-weil-pbc-finite-etale-completion-stage` carries the completion/descent half of the
argument, with its closed-fibre compatibility. It is strictly smaller than the original theorem:
it does not produce a cover over Y and assumes only A Noetherian. Its module is
lean/Sheaf/AlgebraicGeometry/FiniteEtaleCompletionStage.lean.

`lem-weil-pbc-henselian-approximation-alg-hom` records the proved algebraic glue that turns
polynomial approximation into a map from a finitely presented algebra. It involves no schemes
or covers. Its module is lean/Sheaf/RingTheory/HenselianApproximationAlgHom.lean.

Blueprint searches for “completion finite etale”, “approximation algebra map”, and
“finite presentation stage” found no matching blueprint statement. The broader search
“finitely presented algebra” found scheme conventions and filtered-colimit descent nodes,
which do not assert either new result. Both new nodes serve the essential-surjectivity proof
of thm-weil-pbc-finite-etale-lifting through the original item. No change record is needed.

## Second reading by C2

1. **Statements unchanged.** Compared the delivered item module with the repository version; the
existing theorem signature is byte-for-byte unchanged. The two added declarations are new split
lemmas with statements matching their DAG nodes.

2. **Proof and axioms.** Compiled all three modules with `lcompile.py --all`; there are no errors,
forbidden declarations, or unsanctioned `sorry`s. The only remaining `sorry` is the named
`exists_finiteEtale_completion_stage`, and its source, proof sketch, and node are recorded.

3. **Split statements.** Checked the approximation lemma on zero variables and relations, the
identity stage, and degenerate ideals; it is true and strictly smaller than the target. The
completion-stage lemma has weaker assumptions than the target and does not restate it. Searches
found no existing equivalent declarations.

4. **Route and pruning.** The final proof uses the completion-stage reduction, algebra-map
approximation, and pullback pasting. Removed imports and the obsolete complete-pair dependency
are listed above; the unit route and realized steps remain represented in the completion-stage
node.

5. **DAG agreement.** Checked the item and both new node records against the Lean declarations;
proof steps and `proof_deps` follow the imports and actual route, with the remaining split theorem
marked by its node.

I changed only the report by adding this second-reading record; no Lean proof or statement needed
repair after compilation.
