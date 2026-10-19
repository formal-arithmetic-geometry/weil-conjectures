## What changed

Marked `WeilConjectures.coefTowerNaturalCurrying` in
`lean/Sheaf/SixFunctors/CoefTowerNaturalCurrying.lean` as STATEMENT-DISPUTED.
The file's local `Elab.async` option is restored to `true`; the full source
compiled in 37.3 seconds. Every declaration, signature, definition, visibility,
import, proof body and existing docstring is unchanged. The scheduling change
and transitive consumers are recorded in
`coord/changes/F2-coef-currying-elaboration-scheduling.md`.
No consumer adaptation or timeout increase is made.

Read the complete module, its node `lem-coef-tower-natural-currying`, the unit
record, the seven proof steps, and the declarations of the pairing,
coaugmentation, finite mapping adjunction, scalar adjunction, diagram-site,
closed-monoidal and evaluation dependencies. The original module compiled with
the prescribed remote wrapper in 34.6 seconds. Short-route searches used
LeanFinder for constant-input tower internal Hom, Loogle for
`CategoryTheory.MonoidalClosed.curry`, and repository searches. They found generic
currying infrastructure, not a theorem repairing the missing normalization.

The defect is in the hypotheses of the requested invertibility conclusion, not
the presence of unproved dependency declarations. The prescribed declarations
may be used even when they contain holes; none can make an arbitrary
non-dualizing trace into a duality pairing.

## Proved and sorry left

Original holes: 1. Closed: 0. Added: 0. Split off: 0.
The remaining hole is `WeilConjectures.coefTowerNaturalCurrying`, node
`lem-coef-tower-natural-currying`, with its original complete proof-plan docstring.
No proof of the theorem or formal refutation of its entire Lean signature is
claimed. The delivery is a disputed-statement report, not proof progress.

A separate sandbox scratch calculation `traceShearCounterexample` checks the
underlying algebra: over any nonzero commutative ring, the linear equivalence
`(x,y) -> (x-y,y)` changes the addition trace to first projection, and the
resulting second-component curried pairing is noninjective. The geometric
specialization and its applicability to all model witnesses are the mathematical
argument below; they are not claimed to be kernel-checked by that calculation.
The scratch calculation is outside `lean/` and is not a delivered library module.
It compiled without warnings in 1.4 seconds; `#print axioms` lists only
`propext` and `Quot.sound`.

## No longer needed

None. No imports, nodes or modules were pruned. The canonical source argument
still needs the declared dependencies after its trace comparison is normalized.
No alternative proof route or new node is proposed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the Lean hypothesis `eTrace` is an arbitrary R-linear
isomorphism of compact-support section objects. It is not required to be the
canonical comparison induced by `eQ`, finite compact support and
`finiteDualizingOrigin`. The sole condition `_ht` says that `t` is the counit
after this arbitrary comparison. The conclusion's factorization
`M.omegaEvaluation n ≫ M.omegaOrigin n = eTrace n` fixes that same arbitrary
comparison, rather than supplying the missing normalization.

Here is a concrete counterexample to the intended mathematical assertion.
Take two distinct primes p and l, E = Q_l, and the allowed algebraically closed
finite-field datum of characteristic p. Put s = Spec(k) and X = s disjoint-union s.
The structure morphism is finite etale, proper and separated, with dimension 0.
Use the canonical quotient dualizing tower Q, equal to A_n on each component in
degree zero, with its usual quotient transitions and canonical eQ. Take d = 0
and a0 = b0 = 0. Let T be the actual compact-support reduction tower, with its
canonical evaluation comparisons. All hypotheses on Q and T are then satisfied.

At every positive level its dualizing compact-support sections are A_n × A_n.
The exceptional adjunction is direct sum left adjoint to the diagonal functor,
so the exceptional counit is epsilon_n(x,y) = x+y. Let e_can,n be the actual
comparison from evaluation of the strict dualizing tower to this presentation.
Define S_n(x,y) = (x-y,y), with inverse (x,y) -> (x+y,y), and put

    eTrace_n = e_can,n followed by S_n,
    t_n(x,y) = x.

All these formulas are R-linear and commute with every quotient map. Thus t is
an actual morphism of strict towers, not an attempted lift inferred from
unrelated derived maps. The equation epsilon_n(S_n(x,y)) = x is precisely `_ht`,
including the canonical identification of the coefficient target. Even adding
transition compatibility for eTrace would not exclude this example.

Take K to be R in degree zero on the second component and zero on the first.
It is derived complete, constructible, and its reductions have Tor amplitude
[0,0], so it belongs to the full input subcategory. Its compact-support sections
are C = R and C_n = A_n. The Hom tower has value A_n, and its ordinary evaluation
pairing into the dualizing compact-support tower has the form

    (h,c) -> (0,hc).

Composing with first projection gives zero. Hence its transpose Gamma_K is zero,
whereas its source and target both evaluate to the nonzero A_n[0]. It cannot be
an isomorphism. Failure already occurs for n = 0, the quotient of exponent 1.
There is no issue involving inverse limits, negative degrees or a Tor bound.

The existential choices of M do not remove the obstruction. The formula for
`CoefPairingSystem.beta` is natural in its second argument Q: it is made from
functorial projection mates, the source-sections counit, internal evaluation,
and the natural isomorphism `compactSections`. Let v be the projector of Q onto
the first open-and-closed component. Internal Hom from second-component K to
the first-component summand is zero, so Hom(K,v) is zero. Naturality in Q gives

    beta_(K,Q) followed by B(v)
      = (Hom(K,v) tensor identity) followed by beta_(K,Q) = 0.

Tensor with a fixed object is a left adjoint, so it preserves zero objects and
zero morphisms here. Since B(v) followed by t equals t, beta followed by t is
zero for every such choice of adjunction/frame comparisons. Inserting eta
does not change zero. The normalization of the reduction models and their
representative Hom computations identifies the input with the same
second-component object; it does not allow transferring it to the first
component. Finally the transpose bijection is inverse to composition with its
evaluation, so the transpose of zero is zero. Thus arbitrary frame witnesses
or Hom-model comparisons cannot turn this map into an invertible one.

The exact failed inference is DAG step 3, where the evaluated fixed trace is
used as *the* exceptional counit in the same presentation as finite evaluation.
Step 4 then invokes finite mapping adjunction for that pairing, and step 5
concludes invertibility. `_ht` alone gives the counit only after the unrelated
eTrace. `omegaOrigin` has no condition identifying it with the canonical
finite exceptional comparison. The stage-2 review's claim that this field is
pinned by eTrace does not pin it to the comparison required by adjunction.

The source paragraph 2 and final paragraph of
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/prop-coef-integral-dualizing.proof.md`
use the comparisons defined by their counits and the specified natural maps.
They do not authorize an arbitrary automorphism of the finite compact-support
sections. This is a formal statement/interface defect, not a claimed error in
the source proof or the unit route.

A repair should first construct the actual finite comparison induced by eQ,
finite compact support and `finiteDualizingOrigin`, with its resolution/
localization normalization, and use that comparison in the trace hypothesis.
Equivalently eTrace must be required to equal that construction. Merely asking
for compatible eTrace, or factorizing it through an unrestricted omegaOrigin,
does not suffice. This delivery does not silently add that hypothesis or replace
the theorem by a weaker one; it flags the false statement for independent review
as required by AGENTS.md section 5 and the stage-3 brief.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
