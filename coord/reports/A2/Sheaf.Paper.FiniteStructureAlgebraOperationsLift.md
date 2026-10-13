## What changed

Marked AlgebraicGeometry.finite_structure_algebra_operations_lift as
STATEMENT-DISPUTED, immediately before its existing docstring. Its signature, proof,
visibility, and imports are unchanged. No new theorem, axiom, definition, or hole is
introduced. This is a disputed-statement delivery, not a proof or decomposition.

The obstruction is in hc: Classical.choice is applied to
Scheme.Modules.nonempty_tensorPullbackComp, whose result is only Nonempty of a
natural module isomorphism. It does not specify compatibility with the canonical
adjunction selected by exists_tensorPullbackAdjunction, used in the conclusion.
The source implementation constructs an isomorphism by uniqueness of adjoints, but
its theorem returns a proposition that forgets this witness and its normalization.
Proof irrelevance means choosing from that proposition cannot recover the constructed
witness by unfolding its proof.

Searched via leanfinder for coherent algebra lifting, via loogle for
CategoryTheory.Adjunction.homEquiv_unit, and via grep for algebra lifting and
leftAdjointUniq unit formulas. Read the original node, all its dependency statements
and Lean records, CommAlgebraSheaf, GrothendieckExistence, TensorPullback,
TensorPullbackAdjunction, TensorPullbackStructureSheaf, ModuleBaseChangeMapAlgebra,
AffinePushforwardBaseChange, ThickeningSystemPushforward, and the downstream
FiniteStructureAlgebraLift and AlgebraizeFiniteStructureAlgebra. Read Mathlib's
Adjunction.Unique and the source's scheme module pushforward implementation.
No existing theorem pins the chosen Nonempty composition comparison to the
canonical adjunction. The unit route sk-thm-p1 is unchanged.

## Proved and sorry left

Closed zero of one holes; added zero holes. The original sorry remains:
AlgebraicGeometry.finite_structure_algebra_operations_lift
(lem-weil-pbc-finite-structure-algebra-operations-lift).

A scratch file, scratchpad/SignObstruction.lean, compiles through lcompile.py.
It is outside lean/ and is not delivered as a library module. Its checks prove:

1. Choosing from Nonempty containing a witness a is definitionally equal to choosing
   from Nonempty containing another witness b of the same type.
2. Negation and identity are distinct isomorphisms of the integer module.
3. Choice from Nonempty cannot recover every supplied module-isomorphism witness.
4. If unital ring homomorphisms a and b to the integers satisfy b(x) = -a(x)
   for every x, evaluating at 1 is a contradiction.
5. Consequently an additive identification with the integers cannot make both
   identity and negative identity into unital ring homomorphisms.

These are checks of the obstruction, not a full Lean counterexample to the exact
scheme theorem with its fixed global Classical.choice. No claim is made to have
proved its negation. The dispute concerns the unjustified canonical normalization;
it must be resolved before claiming an algebra-operation reduction is true.

## No longer needed

None. No imports, modules, or nodes are pruned. The original plan remains recorded;
no unit statement or step is bypassed. No node copy is needed because no proof route
or Lean record changed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the node calls c the canonical composition comparison, while the
Lean hypothesis fixes it to a Classical.choice of a bare Nonempty isomorphism type.
There is no unit-normalization equation. The docstring and node step 2 assert that
this comparison commutes with units, but neither the signature nor the return type
of nonempty_tensorPullbackComp supplies that fact. Likewise step 4 cannot identify
the adjoints of hpsi with the required section transition without that equation.

The intended source uses the canonical completion functor and its canonical
comparisons: Stacks https://stacks.math.columbia.edu/tag/09ZT, multiplication
paragraph, and https://stacks.math.columbia.edu/tag/088E. The local coherent.tex
source is absent, so these pages were read online. No source error is alleged.

To see why normalization matters, specialize the intended geometry to I = 0,
X = Spec(Z), f the identity, and all finite covers and transitions the identity,
up to the canonical pullback identifications. Tensor pullback identifies with the
identity functor. A natural composition isomorphism may be multiplied by -1. If
its component is negative identity, module comparisons psi_n can alternate sign,
satisfying the module compatibility equation. The displayed adjoints would then
alternate sign as maps on sections, whereas all the b_n are required to be unital
ring maps and to commute with identity transitions. This is impossible, as the
scratch integer calculation verifies. This is a countermodel for the unnormalized
comparison interface; it is not an assertion that Lean's fixed choice computes to
that particular sign on this scheme.

A suitable repair is a transparent, explicitly constructed tensor-pullback
composition isomorphism built from the canonical adjunctions, with its unit
compatibility theorem proved. Alternatively return an existential isomorphism with
that equation and choose from this constrained existence statement. The supporting
adjunctions must be the ones pinned by exists_tensorPullbackAdjunction. Then use
this comparison in hc and in the upstream system dictionary. The unit and tensor
normalizations must be verified, rather than assumed from natural invertibility.

This repair reaches beyond the assigned module (in particular the shared
TensorPullback interface and GrothendieckExistence). It has not been attempted by
changing unheld interfaces or weakening a conclusion. The independent reader should
resolve the normalization issue before accepting a new algebra-lifting hole as true.

## Second reading by A2

1. **Interface preservation — passes.** Compared the complete delivered module with
   the repository using `diff -u`. The only six added lines are the dispute comment
   before the docstring. The theorem signature, original docstring, `:= by sorry`
   body, imports, visibility, notation and options are byte for byte unchanged.
   No statement or definition change record is necessary.

2. **Proof and trust checks — passes as a dispute, not as a proof.** Independently
   compiled the delivered module and `scratchpad/SignObstruction.lean` through
   lcompile.py. Both compile without errors. Compiled a scratch copy of the entire
   module with `#print axioms AlgebraicGeometry.finite_structure_algebra_operations_lift`.
   Its reported axioms are `propext`, `Classical.choice`, `Quot.sound` and
   `sorryAx`, as expected for the unchanged named hole.
   There are no new holes, definitions, axioms or forbidden implementation escapes
   in the delivered module. The scratch calculation is valid: proof irrelevance
   makes the two choices from `Nonempty` definitionally equal, negative identity
   differs from identity over the integers, and unitality rules out sign-opposite
   ring maps. These checks do not prove the negation of the fixed scheme theorem.

3. **Split statements and shortest available repair — passes; none split.** There
   are no new library statements or nodes to validate. Independently searched with
   grep for `tensorPullbackComp`, `leftAdjointUniq_hom_app` and
   `unit_leftAdjointUniq`; with Loogle for an adjoint-uniqueness application formula;
   and with Lean Finder for composition comparisons compatible with adjunction
   units. Read Mathlib `Adjunction.Unique` and `Adjunction.CompositionIso`, and the
   repository's `TensorPullback`, `TensorPullbackAdjunction` and `ModulePullbackTensor`.
   Mathlib's `unit_leftAdjointUniq_hom_app` and `leftAdjointCompIso` provide the
   appropriate formulas for explicitly constructed comparisons. They give no
   equation identifying the bare `Classical.choice` in hc with such a comparison.
   The theorem returning Nonempty loses both its constructed witness and any unit
   normalization. The constrained existential adjunction in the conclusion does
   retain its sectionwise unit formula. Thus the disputed inference is real;
   replacing hc with a normalized comparison requires a shared interface repair,
   rather than adding an unproved normalization theorem here.

4. **Top-down route, imports and pruning — passes unchanged.** The sole original
   hole remains open and is explicitly reported. No route has been replaced by
   another hole or a restatement. No imports have been added or removed; the
   statement-needed public imports and proof-only imports keep their original
   visibility. `No longer needed` correctly says none: no old proof dependency
   has been made unnecessary by this comment-only delivery. Read the node's unit,
   `dag/units/sk-thm-p1.json`, including `realized`; its statements and steps are
   unaffected. No mathematical error in the unit or cited Stacks argument is
   claimed.

5. **DAG agreement — passes as an unresolved dispute.** Read
   lem-weil-pbc-finite-structure-algebra-operations-lift and its proof steps,
   proof_deps, proof_origin and Lean record. The node and docstring describe a
   canonical comparison, but the actual interface specifies only the choice from
   Nonempty. This discrepancy is precisely what the comment and report flag.
   Since no proof was changed, retaining the original proof plan and node records
   is correct; the dispute must be resolved before that plan can be implemented.

Second reading changed only this report, adding the independent checks and the
Mathlib route for a normalized interface repair. Accepted the existing dispute
marker with its stated limitation; no proof closure or decomposition is claimed.
