## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousQuotientKrullDimension`
states `AlgebraicGeometry.topologicalKrullDim_homogeneousQuotient`, with one `sorry`
and no definitions. It renders the unchanged DAG statement, including finiteness and
nonnegativity of all three dimensions. No statement correction, new node, or dependency
repair is needed.

Source read: Milne, Algebraic Groups (2017), the local PDF, printed pp.104–105
(PDF pp.116–117), Definition 5.20, Proposition 5.23 (the dimension equality),
Propositions 5.24–5.25 (torsor identity and faithful flatness), and Theorem 5.28
(existence). The node's five-step proof is reproduced in the theorem docstring,
including its nonreduced local-dimension argument through Stacks 02FY, 06FE and 0AFE.

Hypothesis and clause correspondence:

- A field k: `(k : Type u) [Field k]`.
- k-group schemes A and L: `(A L : Over (Spec (.of k))) [GrpObj A] [GrpObj L]`.
  The Over objects contain their actual structure morphisms.
- A separated and finite type: `[IsSeparated A.hom]`,
  `[LocallyOfFiniteType A.hom] [QuasiCompact A.hom]`. No properness assumption occurs.
- Closed subgroup inclusion: `(j : L ⟶ A) [IsClosedSubgroupScheme j]`.
  This upstream class includes the group homomorphism, pointwise injectivity and
  closed immersion, so no second subgroup notion is introduced.
- The represented separated finite-type quotient and its k-morphism:
  `(X : Over (Spec (.of k))) (q : A ⟶ X)`, with `[IsSeparated X.hom]`,
  `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom]`.
- “With its quotient morphism as in lem-sfb-algebraic-group-homogeneous-quotient”:
  the supplied quotient's properties are passed as arguments, exactly the witnesses
  in `exists_homogeneousQuotient`. They are `[Flat q.left] [Surjective q.left]`,
  `[LocallyOfFinitePresentation q.left] [QuasiCompact q.left] [QuasiSeparated q.left]`,
  together with `hcoset` and `hlift`. This states the result for any supplied
  representing quotient, not only a choice of witness from an existence proof.
- The test-scheme coset criterion is `hcoset`, for every k-scheme `T` and its two
  points `a b : T ⟶ A`, with `a⁻¹ * b` in the range of postcomposition with j.
- Local surjectivity as an fpqc sheaf is `hlift`, with exactly the dependency's
  `Scheme.fpqcPrecoverage` covering family and the commuting local lifts.
  These two clauses characterize the represented fpqc coset quotient without
  requiring a normal subgroup or a group structure on X.
- The dimension formula is the first conjunct,
  `topologicalKrullDim A.left = topologicalKrullDim L.left + topologicalKrullDim X.left`.
- All three dimensions finite and nonnegative is the second conjunct:
  `∃ a l x : ℕ`, with each topological dimension equal to the corresponding natural
  number cast into `WithBot ℕ∞`. Thus neither minus infinity nor infinity is allowed;
  zero is included. There is no use of a local-ring dimension or natural subtraction.
- No smoothness, reducedness, connectedness, normality or affineness assumption is
  present, and the field is arbitrary (including imperfect and positive-characteristic).

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`, exported through the scheme dependencies.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` on Over schemes;
  its real multiplication, unit and inverse structure supplies the test-point groups.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsClosedSubgroupScheme` (extends `IsSubgroupScheme`, which extends
  `IsMonHom`, and supplies `IsClosedImmersion j.left`). The recorded declaration
  `IsSubgroupScheme` and the closed variant's full docstrings and signatures were read.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` / `Separated`:
  `AlgebraicGeometry.IsSeparated` (the separated clause of def-weil-proper-morphism).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` / `QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`.
- `Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousQuotient`:
  `AlgebraicGeometry.exists_homogeneousQuotient`. Its full signature and proof docstring
  were read; our X, q and quotient hypotheses are its conclusion with G renamed A.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim : WithBot ℕ∞`, defined as
  `Order.krullDim (IrreducibleCloseds T)`; this is precisely the required dimension.

The recorded modules of stated proof dependencies are imported privately: local
Krull dimension, pullbacks, scheme fibres, finite presentation, closed immersions,
field-extension dimension, finite-type dimension bounds, surjective-flat global
dimension, fibre dimension after base change, finite-type and Noetherian affine
rings, prime spectra and Noetherian schemes. Finite-type composition and base-change
instances are in the already imported finite-type and quasi-compact modules.
`lem-sfb-field-groupoid-constant-local-dimension` has no Lean record or Mathlib match
in the read clone, so no module can currently be imported for this proof-only
prerequisite; its use remains explicitly documented in proof step 3. It is not a
statement prerequisite and supplies no object needed to type the present theorem.

Edge cases checked before drafting:

- L is the trivial subgroup: dim L = 0, the quotient is A, so the formula reduces
  to dim A = 0 + dim A.
- L = A: X is Spec k with dimension 0; no normality or connectedness restriction
  has been introduced.
- A is the trivial group: all three dimensions are 0; natural-number witnesses
  allow this case, and no positivity hypothesis occurs.
- Nonreduced finite group schemes, e.g. alpha_p in characteristic p, have topological
  dimension 0 and are not excluded. The coset condition uses full schemes, not
  reduced schemes or geometric points only.
- Nonaffine groups, e.g. abelian varieties, and disconnected groups remain allowed.
- An empty group scheme over a field cannot carry the group-object unit from Spec k.
  Hence excluding minus-infinity dimensions is a conclusion, not an extra assumption.
  The image of its identity likewise makes X nonempty.
- All variables and universes are explicit, with `autoImplicit false`; arbitrary
  small test k-schemes and fpqc covers use the same universe as the recorded quotient
  interface. No hypothesis identifying two independent universes was added.

Searches actually run on 2026-10-24:

- `msearch.py ... leanfinder`: “For a finite type group scheme G over a field and a
  closed subgroup H, dim G equals dim H plus dim of the homogeneous quotient G/H”.
  Eight hits: fixed-field ranks, abstract group rank, module and ideal quotient
  finranks; no scheme quotient dimension formula.
- `msearch.py ... loogle`: `topologicalKrullDim, AlgebraicGeometry.Scheme`.
  One hit, `AlgebraicGeometry.IsLocallyArtinian.of_topologicalKrullDim_le_zero`,
  which is not the requested statement.
- `msearch.py ... grep`: `homogeneous|quotient.*[Dd]im|[Dd]im.*quotient`,
  subdirectory `AlgebraicGeometry/Group`: zero hits.
- `msearch.py ... leansearch`: “Krull dimension of an algebraic group equals the
  dimension of a closed subgroup plus the dimension of its homogeneous quotient”.
  Eight hits: `topologicalKrullDim` and ideal quotient dimension inequalities or
  regular-element dimension drops; none gives homogeneous quotient dimension.
- `rg` in the read clone's `lean/WeilConjectures` and `lean/Sheaf` for homogeneous
  quotient and quotient-dimension names: homogeneous quotient existence and smooth
  quotient geometry are present, as are Proj quotients and ring quotient dimensions;
  no exact statement. `grep -rn` for this item's id in `lean/WeilConjectures` was empty.
- Exact proposed-name searches in Mathlib, `lean/WeilConjectures`, and `lean/Sheaf`
  for `topologicalKrullDim_homogeneousQuotient` and its reversed-name variant were empty.

No `STATEMENT-DISPUTED` issue was found. Validation: `scompile.py N5 lem-sfb-homogeneous-quotient-krull-dimension` compiled
the module successfully both as a sandbox module and at its library module path,
with exit code 0 and no errors or unexpected warnings. `deliver2.py N5 lem-sfb-homogeneous-quotient-krull-dimension --no-push`
also printed OK: the complete three-file packet passes preflight and compiles.

## Second reading by N5

A separate second pass by the same dispatcher-started worker (no other agent was
started) read the node and finished Lean side by side. The maintainer supplies the
independent review. The field and group binders, separated finite-type assumptions
on A, closed subgroup class, and arbitrary represented quotient X are present.
I compared the supplied quotient arguments term by term with the conclusion of
`exists_homogeneousQuotient`: separatedness, local finite type, quasi-compactness of X;
flatness, surjectivity, local finite presentation, quasi-compactness and quasi-separatedness
of q; and both universally quantified coset and fpqc lifting clauses agree. No group
structure is required on X, and no normality of L is used. The formula has the correct
order dim A = dim L + dim X, and the three natural-number witnesses assert exactly
finite nonnegative dimensions without excluding zero. The full nonreduced schemes
are used throughout. No mismatch was found and no mathematical statement was changed.
