## Worker report

The module `Sheaf.AlgebraicGeometry.DiagonalizableNilpotentTriviality` states
`AlgebraicGeometry.diagonalizable_nilpotent_triviality`, with proof `sorry`.
No definitions are introduced and the mathematical statement is unchanged.
The existing, landed `def-sfb-ring-diagonalizable-group` is added to `stmt_deps`
under brief-stage2 §5 (stmt_deps may gain landed nodes).

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A commutative ring: `(A : Type u) [CommRing A]`. This permits the zero ring.
- An ideal J and an exponent N ≥ 1 with J^N = 0: `(J : Ideal A) (N : ℕ)` with
  `(hN : 1 ≤ N) (hJ : J ^ N = ⊥)`. Natural-number exponents with N ≥ 1 are exactly
  the positive integers in the node; bottom is the zero ideal.
- S = Spec A is `Spec (.of A)`. S₀ = Spec(A/J) and its canonical inclusion are the
  source and morphism of `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))`.
- A finitely generated additive abelian group M: `(M : Type u) [AddCommGroup M]
  [AddGroup.FG M]`. The shared universe is the established ringDiagonalizableGroup
  convention, without restricting cardinalities: a finitely generated abelian
  group is countable and has a representative in every ring universe.
- A[M] and all its displayed Hopf operations: the recorded
  `(ringDiagonalizableGroup A M).X` uses `AddMonoidAlgebra A M`, the finitely
  supported free module, with Mathlib's group-algebra Hopf structure. Its
  multiplication, unit, coproduct, counit and antipode are precisely those of the
  node. The source and its group structure are fixed, not arbitrary parameters.
- An arbitrary S-group scheme G: `(G : Over (Spec (.of A))) [GrpObj G]`.
  The internal group-object axioms are the multiplication, identity, inverse,
  associativity and unit/inverse diagrams in the cartesian category of S-schemes.
  There are no extra geometric hypotheses on G, including no commutativity.
- An S-group homomorphism: `f : (ringDiagonalizableGroup A M).X ⟶ G` and
  `[IsMonHom f]`. A morphism in Over is over S; IsMonHom preserves multiplication
  and identity, and for groups thereby preserves inverses.
- e_G followed after p: `toUnit (ringDiagonalizableGroup A M).X ≫ η[G]` in Over S.
  The monoidal unit in Over S is the identity S-scheme. Thus this composite is
  the identity-valued map of the node, and its underlying structure map is p.
- Reduction f₀ = e_(G₀) p₀: `hf` applies the same canonical `Over.pullback` functor
  along Spec(A/J) → Spec A to f and to that identity-valued map. This is exactly
  the morphism base change from def-pc-base-change. Pullback preserves the group
  identity section and the terminal structure map, so the right side is the
  identity-valued morphism on the base-changed source, without any choice of maps.
- Conclusion f = e_G p: the theorem's displayed equality in Over S. Equality
  of Over morphisms is equality of the underlying S-scheme morphisms.

Dependencies read and reused:

- def-weil-affine-spectrum and def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`, `Spec.map`, `Scheme`, and `Scheme.Hom`; read their
  definitions and docstrings in the pinned Mathlib.
- def-pc-base-change: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`,
  `AlgebraicGeometry.baseChange_morphism_projections`, and its documented use of
  `CategoryTheory.Over.pullback`. Read the full signature of that functor in
  Mathlib.CategoryTheory.Comma.Over.Pullback: object pullback and induced map.
- def-sfb-ring-diagonalizable-group: `Sheaf.AlgebraicGeometry.RingDiagonalizableGroup`,
  `AlgebraicGeometry.ringDiagonalizableGroup`; read its signature and docstring,
  `hopfSpec` and the group-algebra Hopf structure. The existing field-only
  diagonalizableGroup would be too specialized and is not used.
- Mathlib `CategoryTheory.GrpObj` and `CategoryTheory.IsMonHom`: read the full
  class signatures in CategoryTheory.Monoidal.Grp and CategoryTheory.Monoidal.Mon.
  No additional definition of an S-group scheme is needed.

The stated proof-dependency modules are imported privately: Thickening,
TensorProduct.Maps, Modules.Differentials, the upstream Modules.Tilde,
SchemeZariskiEtaleQuasiCoherentEquivalence, Mathlib Modules.Tilde,
FlatCohomologyAffineSections, and LinearAlgebra.TensorProduct.Basic.
The three proof nodes lem-sfb-space-square-zero-lift-linearization,
lem-sfb-group-space-square-zero-difference-additive and
lem-sfb-scheme-etale-relative-differentials-comparison have no Lean record in
this checkout; they are not needed to type this statement and have no import.
Their full role remains in the six-step proof docstring.

Edge cases checked before writing: N = 1 forces J = 0 and the hypothesis is
already the desired equality; J = 0 for any positive N; the zero ring (empty
spectrum); M = 0 (trivial source); torsion in M, including μ_p in characteristic p;
characteristic 2, where i₀ = 2i₀ still gives i₀ = 0 by additive cancellation.
The target may be nonaffine, noncommutative, nonsmooth or nonseparated; none of
these cases is excluded. No counterexample or statement correction was found.

Source checked online: Conrad, Reductive group schemes,
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, Corollary B.2.7 on
printed p.287 (PDF page 286), explicitly allows an arbitrary S-group scheme G.
The source's nilpotence exponent convention also covers N = 1 by enlarging
an exponent. This is its split-diagonalizable case, as in the node.

Searches for an existing statement:

- msearch.py leanfinder: “A homomorphism from a split diagonalizable group scheme
  that is trivial modulo a nilpotent ideal is trivial”: eight results, all
  formally smooth or formally unramified algebra statements. In particular
  Algebra.FormallyUnramified.ext/lift_unique require an unramified target and do
  not apply to arbitrary G. No exact match.
- msearch.py loogle: `"GrpObj", "IsMonHom"`: zero results.
- msearch.py grep: `diagonali[sz]able|nilpotent.*[Tt]rivial` in AlgebraicGeometry:
  zero Mathlib results.
- msearch.py leansearch: “A homomorphism from a diagonalizable group scheme
  trivial modulo a nilpotent ideal is trivial”: inspected; no exact match.
- Project rg for `GroupScheme|group scheme|IsGroup|group hom`, then
  `diagonalizable|Diagonalizable` in the two project roots found the existing
  RingDiagonalizableGroup and the downstream SplitLocalSpecialKernelLifting,
  whose docstring cites this result but does not state it.
- rg for `diagonalizable_nilpotent_triviality` in Mathlib, both project roots
  and dag/lean_names_upstream.json: no declaration collision.
- grep -rn for the exact node id in lean/WeilConjectures: no result.
- The raw msearch results are in sandbox searches.jsonl.

Validation: scompile.py compiled this file in sandbox and library module modes
cleanly (5.5 s and 3.7 s respectively); no errors or warnings.

## Second reading by Q16

A separate sequential pass re-read the node and completed Lean file. This is
this worker's second pass, not a claim that another agent was started; the
dispatcher explicitly prohibits starting agents and supplies independent
maintainer review after delivery.

Checked all binders against the correspondence above: the nilpotence exponent
is positive; finite generation is present; the source is the specified Hopf
spectrum; the target has only GrpObj; f is over the base and preserves the group
law; hf uses the canonical quotient map; and the conclusion is equality of the
original morphisms, rather than equality on geometric points. In particular,
base changing the full trivial composite has exactly the meaning e_(G₀) p₀;
it does not assume an arbitrary comparison map or a lift. No statement mismatch
or correction was found. The only added DAG edge cites the landed definition
actually used. The natural-language proof includes the square-zero coordinate
argument, coefficient cancellation and induction through every ideal power.
