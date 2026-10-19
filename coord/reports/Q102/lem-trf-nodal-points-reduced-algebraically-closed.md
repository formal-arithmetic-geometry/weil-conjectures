## Worker report

The delivery states `AlgebraicGeometry.isReduced_of_nodal_closed_points` in
`Sheaf.AlgebraicGeometry.NodalClosedPointsReduced`. Its sole proof is `sorry`.
The existing Q44 review concerns the stage-1 split, not a Lean statement: the base node
has no `lean` record. Its reviewed six-step proof is preserved, including the explicit
axis-kernel and fraction calculations, and rendered in the theorem docstring. No node
statement, dependency list, proof, or stage-1 review is changed.

Clause-by-clause correspondence:

- The algebraically closed field F is `(F : Type u) [Field F] [IsAlgClosed F]`.
- A scheme C over F is `(C : Scheme.{u}) (f : C ⟶ Spec (.of F))`.
  The explicit structure morphism is needed in the smooth-neighbourhood condition.
- Locally of finite type is `[LocallyOfFiniteType f]`. There is no `QuasiCompact f`.
- Every closed point is `∀ x : C, x ∈ closedPoints C → ...`.
- Having no open neighbourhood smooth over F is exactly
  `¬ ∃ U : C.Opens, x ∈ U ∧ Smooth (U.ι ≫ f)`.
  This does not assert failure of global smoothness of C and does not require an
  affine or quasi-compact neighbourhood.
- The completed local ring is
  `AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x)) (C.presheaf.stalk x)`.
  The ring structure comes from Mathlib's completion Algebra module. No Noetherian
  assumption is added to the signature; local Noetherianity belongs to the proof.
- Isomorphic as a ring is `Nonempty (... ≃+* ...)`. No F-algebra compatibility is
  required or silently imposed.
- `F[[u,v]]/(uv)` is `MvPowerSeries (Fin 2) F ⧸ Ideal.span
  {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) F) * MvPowerSeries.X 1}`.
  `Fin 2` supplies exactly two distinct variables and the ideal is principal.
- The conclusion is `AlgebraicGeometry.IsReduced C`, equivalent to reducedness of
  every local ring, exactly the recorded reduced-scheme dependency.
- No dimension, connectedness, nonemptiness, quasi-compactness, separatedness or
  properness hypothesis occurs. All variables and the universe are explicitly bound.
  There is no quantification over test extensions with an independently smaller
  universe; F and C use the standard scheme universe.

Dependency declarations read and reused (all statement dependencies):

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs; a commutative division ring,
  including nontriviality, exactly the field notion.
- `def-weil-algebraic-closure`: `IsAlgClosed`, Mathlib.FieldTheory.IsAlgClosed.Basic;
  its docstring and `exists_root`/`of_exists_root` identify the polynomial-root form.
  This item needs algebraic closedness, not a choice of an algebraic closure.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType.
- `def-weil-closed-points`: `closedPoints`, Mathlib.Topology.JacobsonSpace;
  its definition is `Set.ofPred (IsClosed {·})`.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth, on the restricted structure map.
- `def-weil-pbc-adic-completion`: `AdicCompletion`,
  Mathlib.RingTheory.AdicCompletion.Basic, and its ring instance in .Algebra;
  it is the compatible family in the quotients by powers of the ideal.
- `def-weil-pbc-multivariate-power-series`: `MvPowerSeries` and `MvPowerSeries.X`,
  Mathlib.RingTheory.MvPowerSeries.Basic, coefficient families with Cauchy product.
- `def-pc-reduced-scheme`: `AlgebraicGeometry.IsReduced`,
  Mathlib.AlgebraicGeometry.Properties; also read `isReduced_of_isReduced_stalk`
  and `isReduced_stalk_of_isReduced` for the equivalent local-ring formulation.

Proof-dependency modules are imported non-publicly: Mathlib's Noetherian,
AffineScheme, Localization.AtPrime.Basic, Localization.Submodule,
AdicCompletion.AsTensorProduct, AdicCompletion.LocalRing,
Flat.FaithfullyFlat.Algebra, MvPowerSeries.NoZeroDivisors, and upstream
WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced (read the
`Smooth.geometricallyReduced` declaration and docstring). The other proof
interfaces are supplied by the public statement imports. No missing node,
private definition, or dependency repair was needed.

Source and edge checks: read Stacks curves.tex, `lemma-facts-about-nodal-curves`
(Tag 0E37), especially its final reduced-completion paragraph. Its pure-dimension-one
hypothesis is not used in the node's extracted argument and is not added to this
statement. The empty scheme has vacuous point hypotheses and is reduced. `Spec F`
and smooth affine spaces of any dimension satisfy the hypothesis vacuously;
this confirms no hidden dimension-one restriction. A node with completion
F[[u,v]]/(uv) is included even with only a ring isomorphism. Infinite disjoint
unions of smooth schemes are allowed. The dual-number point Spec F[e]/(e²)
fails the premise: its completed ring is nonreduced, whereas the nodal model
embeds into the product of the two power-series domains. The argument and
signature do not exclude positive characteristic, including characteristic two.

Searches (required launcher msearch.py, group Q102, this item):

- LeanFinder: "A scheme locally of finite type over an algebraically closed field
  is reduced if each nonsmooth closed point has completed local ring F[[u,v]]/(uv)".
  Eight results included IsReduced, isReduced_of_isReduced_stalk,
  isReduced_of_isIntegral and Algebra.FormallyUnramified.isReduced_of_field;
  none treats the nodal-completion closed-point hypothesis. The unramified
  theorem has an additional assumption that fails for nodes.
- Loogle: `IsReduced, AdicCompletion`: zero results.
- Mathlib grep: `nodal|isReduced.*[Cc]ompletion|IsReduced.*AdicCompletion`:
  five hits, all Lagrange-interpolation nodes and unrelated.
- LeanSearch: "A locally finite type scheme over an algebraically closed field
  whose nonsmooth closed points have nodal completed local rings is reduced":
  eight results, reduced-scheme definitions, stalk/open-cover criteria,
  integral implies reduced, and unrelated Scheme.mk; no matching theorem.
- Direct rg in upstream WeilConjectures and project lean/Sheaf for nodal,
  Nodal, completion, and reduced/nodal combinations; exact item-id search in
  upstream; and declaration-name search in dag/lean_names_upstream.json:
  no declaration of this statement. Read
  `Sheaf.SixFunctors.TraceFormula.NodalGeometricFibresReduced` in full:
  its theorem assumes a locally finite type quasi-compact structure morphism,
  pure dimension one for each nonempty algebraically closed base change, and
  scalar-compatible nodal isomorphisms at the nonsmooth closed points of every
  algebraically closed base change. It concludes geometric reducedness; it is
  not this one-field closed-point
  ring-isomorphism assertion and cannot replace it without extra hypotheses.

Validation: scompile.py compiled both sandbox and library module checks cleanly
(3.3 s and 3.1 s). All Lean lines have length at most 96. No statement fault or
dispute was found. No new nodes and no dependency modules are delivered.

## Second reading by Q102

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
