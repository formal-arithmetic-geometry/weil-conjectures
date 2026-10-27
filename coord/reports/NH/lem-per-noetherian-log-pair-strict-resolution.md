## Worker report

The delivery states `AlgebraicGeometry.exists_noetherian_log_pair_strict_resolution`
in `Sheaf.AlgebraicGeometry.NoetherianLogPairStrictResolution`. It introduces no
new definition, adds no hypothesis, changes no natural-language statement, and has
one postponed theorem with its entire thirteen-step DAG proof in the docstring.
The node copy changes only `lean`.

Hypothesis and conclusion correspondence:

- An arbitrary integral scheme M: `(M : Scheme.{u}) [IsIntegral M]`. The integral
  class includes nonemptiness. No field, finite-type-over-a-field, separatedness
  of M, dimension bound, or characteristic assumption is imposed.
- Noetherian M: `[IsNoetherian M]`, the Mathlib class combining local
  Noetherianity with quasi-compactness, rather than just local Noetherianity.
- Excellent M: `hexc : ∀ V : M.affineOpens, IsExcellent Γ(M, V)`.
  This is excellence on every affine open, using the recorded ring predicate.
- B is a closed subset: `B : Closeds M`. Its nowhere density is
  `hB : DenseRange (Scheme.Opens.ι (X := M) B.compl)`. The range of that open
  inclusion is exactly the complement of B, so this is precisely density of
  the complement. The complement itself is not extra input.
- The log regular pair is `hlog : IsDivisorialFineSaturatedLogRegularPair M
  (Scheme.Opens.toScheme (X := M) B.compl)
  (Scheme.Opens.ι (X := M) B.compl) hB`. This is the dependency's actual
  divisorial fs log structure and its geometric-stalk regularity/dimension
  predicate, applied to the canonical complement inclusion.
- The objects R, e and A are existentially quantified as a scheme, its morphism
  to M and `R.IdealSheafData`, respectively. IdealSheafData specifies the closed
  subscheme boundary, rather than just its topological support.
- Integrality, Noetherianity, regularity and properness of the result are the
  conjuncts `IsIntegral R`, `IsNoetherian R`, `IsRegularScheme R` and
  `IsProper e`. In particular regularity includes local Noetherianity via the
  recorded scheme predicate.
- Birationality is explicit: a dense open `V : M.Opens` whose inverse image is
  dense in R and on which `e ∣_ V` is an isomorphism. These are dense open
  subschemes of the two integral schemes, and the isomorphism is induced by e.
  This is the usual dense-open meaning in the node (properness in particular
  implies separatedness, so a common dense-open isomorphism can be expressed
  as an isomorphism over a target open). No function-field proxy is used.
- A is strict normal crossings: `IsStrictNormalCrossingsBoundary A`, exactly
  the recorded effective-Cartier, radical, regular-component/intersection notion.
- Boundary containment: `e ⁻¹' (B : Set M) ⊆ A.support`. The stronger equality
  obtained in the proof plan is not required in the theorem.
- Every point x has a sufficiently small neighbourhood: `∀ x : R, ∃ W :
  R.affineOpens, ∃ hx : x ∈ W.1, ...`. Choosing an affine neighbourhood loses
  no generality because affine opens are a neighbourhood basis.
- The distinct components through x are enumerated by `C : Fin s → Closeds R`.
  `Function.Injective C` forbids repetition. The range equality says exactly
  that their underlying subsets are the images in R of the irreducible
  components of the subspace `A.support`, filtered by containment of x.
  Thus neither other divisors nor unlabelled etale branches are substituted.
- The equation of each reduced component on W is the equality
  `(Scheme.IdealSheafData.vanishingIdeal (C i)).ideal W = Ideal.span {t i}`,
  with actual functions `t : Fin s → Γ(R, W)` on that neighbourhood. The
  vanishing ideal gives the canonical reduced structure of the component;
  radicalness of A and its strict-boundary predicate give exactly this structure.
- These equations form part of regular parameters: their germs in order,
  `List.ofFn (fun i ↦ R.presheaf.germ W.1 x hx (t i))`, are a `Sublist` of p,
  and `IsLocalRing.IsRegularSystemOfParameters p` is the recorded definition.
  The existential `hN` is only the Noetherian instance needed to type that
  predicate for the stalk; it follows from the already asserted Noetherian R
  and imposes no extra condition on input data.
- The local equation of A is explicitly `A.ideal W = Ideal.span {∏ i, t i}`.
  This is equality of ideals on the neighbourhood, not just stalk equality or
  equality of zero sets. Together with the component equations it also removes
  components not passing through x by shrinking W.
- The empty boundary is included: `s = 0` has empty C and t, its germ list is
  the empty sublist, and its product is 1. The boundary ideal on W is then the
  unit ideal. No nonempty-boundary assumption occurs.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent`, which combines the actual
  quasi-excellent and universally catenary ring predicates.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`;
  `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsNoetherian`.
- `Sheaf.AlgebraicGeometry.LogRegularPair`:
  `AlgebraicGeometry.IsDivisorialFineSaturatedLogRegularPair`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`:
  `AlgebraicGeometry.IsRegularScheme` (local Noetherianity and the published
  stalkwise regular scheme class).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`:
  `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`.
- `WeilConjectures.RingTheory.IsRegularSystemOfParameters`:
  `IsLocalRing.IsRegularSystemOfParameters` (maximal-ideal generation and
  length equal to Krull dimension; no private replacement).
- Mathlib's canonical `Scheme.Opens.toScheme`, `Scheme.Opens.ι`, `Scheme.Hom`
  restriction, `Scheme.IdealSheafData.vanishingIdeal`, affine ideals, and germ
  maps express the remaining constructions directly.

All recorded statement-dependency modules are public imports. Every recorded
proof-dependency module is also imported; Mathlib-only facts use the already
imported Proper, Noetherian, and regular-local-ring modules plus
`Mathlib.RingTheory.LocalRing.Module` for Nakayama. The proof-only node
`lem-per-excellent-normalization-preparation` currently has no Lean record,
so there is no module of that node to import. Its result is not needed to type
this statement; the proof plan still cites it. No dependency module repair is
needed. No import cycle was found in the listed direct dependency imports.

Source check: read the current blueprint unit
`literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/_section.md`
and the cited ILO PDF, printed pp. 82--83, 117--119 and 134 (PDF pages 88--89,
123--125 and 140). VII 4.3 supplies the Noetherian regular birational resolution;
VIII 4.1.6--4.1.8 strictifies the boundary; VIII 4.2.2(i) identifies the regular
intersection criterion, and IX 2.4 explicitly uses the strict-boundary form.

Edge cases checked before writing: B empty (the complement is all of M), x away
from A (zero component equations), dimension-zero regular stalks (empty full
parameter list), one component (one equation), and arbitrarily many components
through a point (distinct labels and an actual parameter sublist). Empty M is
correctly excluded by the node's integrality assumption. No mixed/equal
characteristic or arbitrary-excellent-base case is excluded. The universe u is
explicit, with no auto-bound variables or independent smaller test universe.

Searches for an existing statement (all dated 2026-10-24):

- `msearch.py ... leanfinder`: "An excellent Noetherian log regular pair has a
  proper birational regular resolution with strict normal crossings boundary".
  Eight hits, all ordinary smoothness/standard-smoothness results; no such theorem.
- `msearch.py ... loogle`: "AlgebraicGeometry.IsProper,
  AlgebraicGeometry.IsIntegral". One hit, an unrelated commutative group-object
  result in `Mathlib.AlgebraicGeometry.Group.Abelian`.
- `msearch.py ... grep`: `resolution|[Ll]og[Rr]egular` in `AlgebraicGeometry`.
  Zero Mathlib hits.
- `msearch.py ... leansearch`: "An excellent Noetherian log regular scheme has
  a proper birational regular modification with strict normal crossings boundary".
  Eight hits (Noetherian/locally Noetherian basics, finite irreducible components,
  scheme and smoothness constructors); none states this result.
- `rg` in the prescribed upstream and Sheaf source roots and the upstream name
  index for the node id and `strict_resolution|log_pair.*resolution|
  log.*pair.*strict.*resolution`: no exact existing declaration. An earlier
  broad case-insensitive resolution search returned unrelated homological
  resolutions and existing monoidal-log-resolution infrastructure, which was
  narrowed to these names. `grep -rn` for the node id in WeilConjectures also
  found no match. Existing related strict-boundary and parameter declarations
  were opened and reused instead of copied.

Validation: scompile.py checked both the sandbox and the named library module
on the live server; successful run reported 2.6 s and 3.1 s respectively, with
no errors or unexpected warnings. The only elaboration repair was to write the
canonical complement inclusion and scheme using fully qualified Scheme.Opens
names: Closeds.compl otherwise resolves field notation in the topological
Opens namespace. This changes no mathematical data.

No statement dispute or correction is needed. No new nodes are introduced.
The worker delivers directly; the maintainer's independent review supplies the
independent mathematical reading required by the current dispatcher brief.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
