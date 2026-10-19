## Worker report

The module `Sheaf.TraceFormula.NodeAlgebraicallyClosedExtension` states the node as
`AlgebraicGeometry.node_algebraically_closed_extension`.  It binds an algebraically
closed field `k`, a scheme `C` and structure morphism `f` locally of finite type, the
pointwise nodal completed-local-ring hypothesis `hC`, and an algebraically closed field
extension `Ω` via `[Algebra k Ω]`.  The conclusion quantifies over every point of the
scheme-theoretic pullback and assumes exactly that no open neighbourhood is smooth;
it returns a `Nonempty` ring equivalence from the maximal-ideal-adic completion of the
stalk to `MvPowerSeries (Fin 2) Ω` modulo the product of the two coordinate variables.
Thus the equivalence is a ring equivalence (`≃+*`), with no k-algebra condition.

The hypothesis `hC` renders “at each nonsmooth point of C” as
`∀ x : C, (¬ ∃ U : C.Opens, x ∈ U ∧ Smooth (U.ι ≫ f)) → ...`; its completion is
`AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x)) (C.presheaf.stalk x)`
and its node ring is the displayed quotient over `k`.  The field-extension hypothesis
is `[Algebra k Ω]`, and the base change is
`Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))`.  The conclusion's
nonsmooth clause and completed stalk use the corresponding pullback expressions.
The empty scheme is covered vacuously; smooth schemes have no points satisfying the
premise; and the power-series index is `Fin 2`, so the two-variable node is retained in
all characteristics, including characteristic two.

Dependency declarations used: `Algebra` from `Mathlib.Algebra.Algebra.Defs` (the
field-extension structure); `AlgebraicGeometry.LocallyOfFiniteType` from
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType`; `AlgebraicGeometry.Smooth` from
`Mathlib.AlgebraicGeometry.Morphisms.Smooth`; `AdicCompletion` from
`Mathlib.RingTheory.AdicCompletion.Algebra`; `MvPowerSeries` from
`Mathlib.RingTheory.MvPowerSeries.Basic`; and `CategoryTheory.Limits.pullback` from
`Mathlib.AlgebraicGeometry.Fiber`/pullback infrastructure.  Algebraic closedness is
Mathlib's `IsAlgClosed` class.  No project declaration was duplicated.

Searches made: `msearch.py leanfinder` for “a node of a curve remains a node after
extension of algebraically closed fields” (Weierstrass base-change hits only;
no completed-local-ring statement); `msearch.py loogle` for “node field extension
completed local ring” (no result); Mathlib grep for nodal or ordinary-double-point
completed-local-ring base change (no result); project `rg` for the same terms and for
this item id (no existing declaration); and `tools/blueprint_refs.py`/DAG grep for
an existing node carrying the statement (none).

No statement correction or new node was needed.  `STATEMENT-DISPUTED:` none.

## Second reading by Q05

I independently reread the copied node, its source statement, and the Lean module.
The base field, local-finite-type morphism, pointwise nonsmooth hypothesis, ring-only
completed-local-ring equivalence, algebraically closed extension, and pullback
conclusion all occur with the same quantifiers and clauses.  The Lean uses no
Noetherian, separated, quasi-compact, dimension, or universe-equality assumptions.
The only repair from the returned delivery was replacing the stage-1-only packet by
this stage-2 module and adding its `lean` record; the node's statement, proof,
proof_deps, and split_report remain byte-for-byte unchanged.
