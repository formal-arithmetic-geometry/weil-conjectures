## Worker report

The module `Sheaf.Paper.NearbyFiniteBaseDescent` states
`AlgebraicGeometry.Orgogozo.nearbyFiniteBaseDescent`; it does not prove the
statement.  The theorem uses the project’s `UniversalTruncatedComparison` for
`P_r` and `IsPsiGood`/`IsPsiGood`’s ordinary `baseChange` comparison.

The node’s hypotheses are rendered as follows.  `X S T : Scheme.{u}` and
`f : X ⟶ S` are explicit.  `[IsNoetherian S]` is the node’s Noetherian
(quasi-compact, locally Noetherian) base.  `[LocallyOfFiniteType f]` and
`[QuasiCompact f]` are exactly finite type.  `Λ : Type (u + 1)` has
`[CommRing Λ] [Finite Λ]`, and `[HasInvertibleExponent Λ S]` is the recorded
notion that a positive annihilating integer of `Λ` is invertible on `S`.
`K : EtaleDerived X Λ`, together with `hKb : IsBounded ... K` and `hKc`, is
`K ∈ D^b_c(X_et, Λ)`: `hKc` says that every cohomology sheaf, after the
oriented-site coefficient transport, is
`Scheme.IsConstructibleEtaleModuleSheaf`, while `hKb` gives a finite cohomological
interval.  The finite surjective base map is `p : T ⟶ S` with
`[IsFinite p] [Surjective p]`.

For the first conclusion clause, the expression
`((etaleModules (pullback.fst f p)).pull (Coeff Λ)).obj K` is the canonical
coefficient-module pullback `K_T`; its proof field is the canonical boundedness
transport `modulePull ... .bounded_mapDerivedCategory_obj hKb`.  Thus the
premise is exactly `UniversalTruncatedComparison (f_T) Λ K_T r`, and the first
conclusion is `UniversalTruncatedComparison f Λ ⟨K,hKb⟩ r`.  The second clause
is the corresponding implication from `IsPsiGood f_T Λ K_T` to
`IsPsiGood f Λ K`, with the same canonical `K_T`.  The integer `r : ℤ` is
unrestricted and appears on both `P_r` assertions.  No extra properness,
flatness, reducedness, or finiteness condition on a further test base change is
introduced.

The dependency declarations used are:

- `def-trf-orgogozo-induction-data`: `AlgebraicGeometry.Orgogozo.UniversalTruncatedComparison`
  from `Sheaf.Paper.OrgogozoInductionData`.
- `def-trf-oriented-nearby-cycles`: `AlgebraicGeometry.OrientedNearbyCycles.IsPsiGood`
  and the canonical `nearbyCycles`, `baseChange`, `etaleModules`, and `Coeff`
  declarations from `Sheaf.Paper.OrientedNearbyCycles`.
- `def-weil-finite-type-morphism`: Mathlib’s `LocallyOfFiniteType` and
  `QuasiCompact` classes.
- `def-weil-pbc-etale-constructible-sheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf` from
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`.
- `def-weil-finite-integral-morphism`: Mathlib’s `AlgebraicGeometry.IsFinite`.
- `pqf-def-locnoeth`: Mathlib’s `AlgebraicGeometry.IsNoetherian`.
- `def-weil-surjective-morphism`: Mathlib’s `AlgebraicGeometry.Surjective`.

The source read was Orgogozo, *Modifications et cycles proches sur une base
générale*, Lemma 2.6 and its Cech-nerve proof, pp. 4–5.  The proof plan in the
declaration records the six required stages: arbitrary preliminary and further
base changes; strict-local tube stalks; the Cech nerve of the pulled-back finite
cover; factorwise comparison cones; bounded-below column-cone descent; and
conservativity of oriented geometric points.  The final paragraph records the
composition of ordinary comparison maps, which gives full `Psi`-goodness.

Edge cases checked: the identity finite cover; empty schemes and empty fibres
(the universal quantifiers then have no geometric-point witnesses); `r = 0`
and negative `r`; zero complexes and zero coefficient modules; nonreduced
finite covers; arbitrary further base changes; and positive characteristic when
the annihilating integer is invertible.  No nonemptiness, properness, flatness,
or reducedness assumption is silently added.

Searches made:

- `msearch.py ... leanfinder "finite surjective descent of truncated nearby-cycle comparison and Psi-goodness"` returned eight unrelated general sheaf, limit, and homological-complex declarations; no nearby-cycle descent theorem.
- `msearch.py ... loogle "UniversalTruncatedComparison, IsPsiGood, IsFinite, Surjective"` returned zero hits (the project identifiers are unknown to Loogle).
- `msearch.py ... grep "nearby.*finite|UniversalTruncatedComparison|IsPsiGood" Sheaf` returned zero Mathlib hits.
- Direct `rg` over the project and the read-only `WeilConjectures` source found no
  `nearbyFiniteBaseDescent` declaration.  The only project occurrences of the
  node id are proof references in `OrgogozoGoodModification.lean`; there is no
  existing statement to attach.

No new definition node or dependency module was needed, and there is no
statement correction or `STATEMENT-DISPUTED` issue.

## Second reading by Q41

I reread the node, all seven statement dependencies and their recorded Lean
interfaces, and the module signature.  The Noetherian, finite-type, finite,
surjective, finite-coefficient, and invertible-exponent hypotheses are all
present.  The bounded-constructible object is represented by exactly the
project’s boundedness and cohomology-constructibility conditions.  Both the
truncated implication and the full `Psi`-goodness implication use the same
canonical pullback object, with no stronger conclusion or omitted integer case.
The module compiles cleanly through `scompile.py`.

## Maintainer review fix (cc review service, 2026-10-18)

The delivered conclusion parsed as `P_r(f_T,K_T) → (P_r(f,K) ∧ (Ψ(f_T,K_T) → Ψ(f,K)))`: the
full-`Ψ`-goodness implication sat under the hypothesis `P_r(f_T,K_T)`, which the node does not
assume (deriving it from `Ψ`-goodness of `f_T` is the composition argument of proof Step 7, not a
triviality). The fixed module states the two implications independently,
`(P_r(f_T,K_T) → P_r(f,K)) ∧ (Ψ(f_T,K_T) → Ψ(f,K))`, as the node and its citer
lem-trf-psi-proper-surjective-constructibility use them. The statement docstring now carries
the node's proof Steps 1--7 with their dependency references, and the unused import
`Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes` is replaced by the module actually used,
`Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`. Hypotheses are unchanged.
