## Worker report

The module `Sheaf.RingTheory.MonomialIntegrality` states
`AddMonoidAlgebra.monomial_integrality`, with its whole proof `sorry`.
It gives the monomial criterion and the elementwise integral saturation extension
as the two conjuncts of one theorem. No new nodes, dependency repairs, or statement
correction are needed. Only the item's `lean` record changes.

Hypothesis and clause correspondence:

- A field k is `(k : Type u) [Field k]`.
- The arbitrary ambient abelian group is `(G : Type v) [AddCommGroup G]`;
  the independent universes admit every field/group size combination.
- Its arbitrary additive submonoid and element are `(P : AddSubmonoid G) (g : G)`.
  No finite generation, sharpness, saturation, torsion freeness, or group-algebra
  domain assumption appears.
- `AddMonoidAlgebra k G` is k[G], with finitely supported coefficient functions;
  `single g (1 : k)` is the basis monomial e^g. Convolution multiplication gives
  e^g e^h = e^(g+h), and its unit is e^0.
- For any additive submonoid Q, `(mapDomainAlgHom k k Q.subtype).range` is the
  embedded k[Q]. The map sends every finite sum of Q-indexed basis monomials to
  the same finite sum in G. The subtype inclusion is injective, so this range
  is precisely the subalgebra described by the node, including all scalars.
  This is an application of existing Mathlib constructions, not a new notion.
- Integrality over k[P] is
  `IsIntegral (mapDomainAlgHom k k P.subtype).range ...`. The range subalgebra's
  canonical algebra structure on k[G] is inclusion, so its polynomials have
  exactly the requested coefficients.
- The equivalence is the first conjunct, with the exact necessary and sufficient
  condition `∃ n : ℕ, 0 < n ∧ n • g ∈ P`. Positive integer witnesses are the
  same positive natural witnesses; negative and zero integers are excluded.
- Ambient saturation is the additive submonoid
  `Submonoid.toAddSubmonoid' (AlgebraicGeometry.FineFan.saturation P.toSubmonoid)`.
  The two type-tag conversions change additive notation to multiplicative and
  back without changing the ambient group. The recorded saturation is the
  submonoid closure of the positive-root subset. That subset is already a
  submonoid for every abelian G: zero has witness 1; witnesses a,b for h,h'
  give witness ab for h+h'. Thus this is exactly the node's ambient root set,
  even when G is larger than the group completion of P.
- The second conjunct quantifies `∀ x : AddMonoidAlgebra k G` and assumes
  membership in the range subalgebra of this saturation, then asserts
  `IsIntegral (mapDomainAlgHom k k P.subtype).range x`. It covers every element
  of k[P^sat], not just its basis elements or a finite set of generators.
  The consequent has no extra assumption on g; G always contains zero.

Dependency declarations read and used:

- `def-trf-fine-fan-blowup`: `AlgebraicGeometry.FineFan.saturation` in
  `Sheaf.AlgebraicGeometry.FineFanBlowup`, with full type
  `{G : Type u} [CommGroup G] (Q : Submonoid G) : Submonoid G` and body
  `Submonoid.closure {g | ∃ n : ℕ, 0 < n ∧ g ^ n ∈ Q}`.
  Both its local source and current `scompile.py --source` source were read.
- `def-weil-pbc-integral-closure` (also the sole proof dependency):
  `IsIntegral` and `integralClosure` from
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`. The former is a monic
  polynomial root under the algebra map; the latter is the subalgebra of those
  elements, closed under sums/products and containing the coefficient image.
  The recorded `IsIntegrallyClosedIn` was also inspected; that clause is not
  needed in this statement.
- Mathlib's `AddMonoidAlgebra.mapDomainAlgHom`, `AlgHom.range`, `single`, and
  `AddSubmonoid.toSubmonoid` / `Submonoid.toAddSubmonoid'` supply canonical
  constructions. Their source signatures and docstrings were read. No helper
  map, private copy, arbitrary algebra structure, or chosen object is introduced.

The theorem docstring carries all three DAG proof steps: coefficient extraction
from a monic relation, the explicit binomial converse, and closure under scalars
and finite sums in the integral-closure subring. Nothing is proved at this stage.
ILO VIII 3.1.17 (printed p.101) and 3.2.9 (printed p.104) were read in the local
PDF. They define root saturation and give the toric normalization argument.
As the node and stage-1 report explain, the coefficient proof is agent-supplied
supporting algebra, not a quotation of the ILO proof. This attribution is retained.

Edge cases checked before writing: g=0 has n=1; P=G has every exponent already
in P; P={0} in Z has only the zero integral basis exponent; P=2N in Z admits
g=1 via n=2 but excludes g=-1. P=N in Q includes g=1/2 in its ambient
saturation, so no replacement by saturation in P^gp is valid. A finite torsion
group with P={0} admits every exponent by its order, including in characteristic
dividing that order, when k[G] can have nilpotents. Infinitely generated P is
allowed: the coefficient argument uses only finite support. Zero elements and
empty sums in the saturation algebra are included. Fields of every
characteristic and the trivial ambient group are included.

Searches for an existing statement were made through the prescribed msearch.py:

- LeanFinder: “A monomial in a group algebra is integral over a submonoid algebra
  if and only if a positive multiple of its exponent belongs to the submonoid”.
  Returned IsIntegral, IsAlmostIntegral, power-basis facts, and general integrality
  criteria; none proves the necessary exponent-membership condition.
- Loogle: `"IsIntegral", "AddMonoidAlgebra"` returned
  `instIsIntegralAddMonoidAlgebraOfIsPushout`, whose inspected type changes
  coefficient rings with a fixed exponent monoid. It is not this criterion.
- Mathlib grep:
  `(MonoidAlgebra|AddMonoidAlgebra).*(integral|IsIntegral)|integral.*(MonoidAlgebra|AddMonoidAlgebra)`
  returned zero hits.
- LeanSearch: “A monomial of a group algebra is integral over a submonoid algebra
  exactly when a positive multiple of its exponent belongs to the submonoid”.
  Returned general IsIntegral and integralClosure, Subalgebra.isIntegral_iff,
  polynomial coefficient constructions, and localization lemmas. No exact match.
- Direct rg searches in upstream WeilConjectures and project lean/Sheaf for
  monomial/integrality and MonoidAlgebra/integrality found no declaration of the
  criterion. The item id was absent upstream. The chosen full theorem name was
  absent from Mathlib, upstream, project sources and dag/lean_names_upstream.json.
  Broader monomial searches found polynomial/Rees constructions and the fine-fan
  saturation dependency, not an existing criterion or saturation-integrality claim.

Compilation note: the recorded FineFanBlowup dependency is a legacy Lean file,
confirmed by the current-source wrapper. Lean rejects importing it from a
`module` file. This statement therefore uses the same legacy import format,
with globally visible declarations and explicit autoImplicit=false. No dependency
source or live artifact was changed. Final compilation and delivery checks are
recorded below when complete.

No STATEMENT-DISPUTED finding or mathematical node fault was found.

Validation: the prescribed `scompile.py Q59 lem-trf-monomial-integrality`
compiled both the sandbox probe and the actual library module with exit 0 and
no warnings or errors (2.9 s and 2.8 s respectively).

## Second reading by Q59

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
