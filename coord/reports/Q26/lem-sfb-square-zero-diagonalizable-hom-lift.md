## Worker report

The module Sheaf.AlgebraicGeometry.SquareZeroDiagonalizableHomLift states
AlgebraicGeometry.squareZero_diagonalizable_hom_lift. Its only theorem has proof `by sorry`.
No new definition or theorem is proved. The original mathematical statement and proof plan
are preserved. The existing, landed node def-sfb-ring-diagonalizable-group is added to
stmt_deps so this delivery uses the project's one arbitrary-ring construction of D_A(M).
No new nodes or dependency repairs are needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The arbitrary commutative ring A is `(A : Type u) [CommRing A]`. It has no nontriviality,
  locality, Noetherian, completeness, field, characteristic, or reducedness assumptions.
- The ideal J and J^2 = 0 are `(J : Ideal A) (hJ : J ^ 2 = ⊥)`.
  Its quotient A_0 is literally `A ⧸ J`, inferred as the target of `Ideal.Quotient.mk J`.
  The base S is `Spec (.of A)` and S_0 is the spectrum of that quotient.
- The finitely generated additive abelian group is
  `(M : Type u) [AddCommGroup M] [AddGroup.FG M]`. Finite generation is as a group,
  rather than finiteness of its underlying set. There is no torsion-free assumption.
- The finitely supported free group algebra, its basis, product, unit, coproduct, counit,
  and antipode are the existing `AddMonoidAlgebra A M` Hopf structure used by
  `ringDiagonalizableGroup A M`. Its definition is `hopfSpec` of this Hopf algebra.
- An S-group scheme is `Grp (Over (Spec (.of A)))`, hence an actual scheme over S
  with Mathlib's group-object multiplication, identity and inverse and their laws.
  `G` has precisely this type. `[Smooth G.X.hom]` and `[IsAffineHom G.X.hom]`
  render smooth and affine over S. Because S is affine, the latter is equivalent
  to affineness of the total scheme. No separatedness or finite-presentation binder
  beyond what smoothness already means is added.
- Reduction is the existing functor
  `(Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).mapGrp`.
  It sends G to its group-scheme fibre product with Spec(A/J), with the induced
  operations. `u₀` is a morphism in the category of group objects over S_0, and
  therefore preserves multiplication and identity; preservation of inverse follows
  from Mathlib's `GrpObj.inv_hom` for every such morphism.
- The source of `u₀` is the same pullback applied to `ringDiagonalizableGroup A M`.
  This is D_(A/J)(M) in the node, expressed as the chosen pullback: coefficient
  reduction identifies (A/J) tensor_A A[M] with (A/J)[M] by e_m to e_m, and respects
  all three Hopf maps. This is an equivalent presentation with no extra choice,
  comparison hypothesis, or arbitrary map. It includes every prescribed u₀ from
  D_(A/J)(M), transported by this canonical identification.
- `∃ u : ringDiagonalizableGroup A M ⟶ G` asserts an actual S-group homomorphism.
  The equality `...mapGrp.map u = u₀` is equality of its prescribed base change
  with u₀, not just isomorphism, pointwise agreement over fields, or existence of
  an unspecified reduced homomorphism. No uniqueness assertion is added.

Dependencies read and used:

- def-weil-affine-spectrum: Mathlib.AlgebraicGeometry.Scheme,
  AlgebraicGeometry.Spec and AlgebraicGeometry.Spec.map; full definitions read.
- def-pc-base-change: WeilConjectures.AlgebraicGeometry.BaseChangeConventions,
  AlgebraicGeometry.baseChange_morphism_projections and its module documentation:
  scheme and morphism base change are the existing CategoryTheory.Over.pullback.
  The module's moduleBaseChange concerns module sheaves and is not misused as
  scheme base change. The Grp functor uses the same Over.pullback on objects/maps.
- def-sbc-smooth-morphisms: Mathlib.AlgebraicGeometry.Morphisms.Smooth,
  AlgebraicGeometry.Smooth, its full affine-local class signature and documentation.
- Added landed def-sfb-ring-diagonalizable-group:
  Sheaf.AlgebraicGeometry.RingDiagonalizableGroup,
  AlgebraicGeometry.ringDiagonalizableGroup. Read the full module, including the
  quotient-character map declaration, and Mathlib's hopfSpec and group-algebra
  Hopf instance. It works over all commutative rings, not only fields.
- Mathlib.GroupTheory.Finiteness supplies AddGroup.FG. Mathlib's Grp, mapGrp,
  GrpObj.inv_hom and Over group-pullback interfaces were read in their source.

The proof-dependency nodes lem-sfb-square-zero-hom-regular-defect and
lem-sfb-diagonalizable-regular-two-cocycle have no recorded Lean modules yet.
They are not needed to state this theorem, so no nonexistent proof imports were
invented. Their full statements and the four accepted proof steps were read;
the theorem docstring carries the complete four-step natural-language proof.

Edge cases checked before writing: J = 0 gives lifting across the identity
base change; the zero ring A is permitted (empty spectrum); M = 0 gives the
trivial group; a finite torsion M in characteristic dividing its order is
permitted, even though D_A(M) is then nonsmooth. Only G is assumed smooth.
Nonreduced A and nonprincipal J are permitted. No assumption on the residue
characteristic, no local base, and no uniqueness requirement occurs. The common
universe is the project's ringDiagonalizableGroup convention: any pair of sizes
can be raised to their maximum, and finite generation does not bound M's
cardinality or impose a positive rank.

Searches made on 2026-10-24:

- msearch.py leanfinder: "Homomorphisms from split diagonalizable group schemes
  to smooth affine group schemes lift across square zero ideals". Eight hits,
  including Algebra.FormallySmooth.exists_lift, .lift and .of_split, concern
  algebra-map lifts only; none imposes or corrects group multiplicativity.
- msearch.py loogle: "HopfAlgebra, Algebra.FormallySmooth". Zero hits.
- msearch.py grep: "Diagonalizable|diagonalizable|groupScheme|GrpObj" in
  AlgebraicGeometry. Seventeen hits include the existing affine Hopf-spectrum
  and group-object pullback APIs; none is the requested homomorphism lift.
- msearch.py leansearch: "A group scheme homomorphism from a diagonalizable group
  to a smooth affine group lifts across square zero thickenings". Eight hits,
  including scheme liftQuotient and formal-smooth algebra lifts, no exact match.
- rg in lean/WeilConjectures and lean/Sheaf for group schemes, diagonalizable,
  Hopf, and the exact item id. Found the arbitrary-ring RingDiagonalizableGroup
  construction and CompleteLocalSplitTorusHomLift (a different result with a
  complete Noetherian local base), plus field-based group-scheme APIs. No exact
  square-zero homomorphism-lifting theorem exists.
- The exact item id was searched in dag/lean_names_upstream.json, with no match.
  The existing diagonalizable definition node was read and reused; no second
  construction is introduced.

Source checked directly:
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf,
printed p.287 (PDF page 287), Corollary B.2.6: the obstruction is necessary and
sufficient for a homomorphism lift, and is zero for multiplicative-type H.
Printed p.285, Remark B.2.4 explains vanishing through the degree-zero summand
of an M-graded module. This confirms the arbitrary-base and torsion cases.
The item is a supporting node, not a blueprint unit statement. No statement
correction or STATEMENT-DISPUTED issue was found.

Validation: scompile.py Q26 lem-sfb-square-zero-diagonalizable-hom-lift compiled
this file both as sandbox and as its actual library module against the live
published build, with exit code 0 and no diagnostics (25.3 s and 10.6 s).

## Second reading by Q26

Solo second pass with the original JSON and completed Lean file open; this is
not a claim of an independent worker review. The dispatch brief forbids starting
other agents and assigns the independent review to the maintainer.

Rechecked A/CommRing, J/Ideal and square-zero, M/AddCommGroup/AddGroup.FG,
G/Grp over Spec A, smoothness and affineness against each node hypothesis.
Rechecked the quotient's Spec.map orientation and both source and target of u₀:
Over.pullback along Spec(A/J) → Spec A gives group objects over exactly Spec(A/J).
The source is the canonical reduction of Spec A[M], which represents exactly
Spec (A/J)[M], without restricting u₀. The conclusion quantifies an actual
homomorphism u and identifies its base-change morphism with this exact u₀.
Group morphisms preserve the inverse as well as the monoid operations.
No locality, completeness, torsion-free or reducedness binder appears. The proof
is sorry only; its docstring follows all four DAG steps. All variables and the
universe are explicit. No mismatch was found and no revision was needed.
The only metadata change besides lean is citing the landed diagonalizable-group
node that supplies the existing definition already used in the original text.
