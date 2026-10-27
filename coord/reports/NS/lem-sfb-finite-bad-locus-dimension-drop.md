## Worker report

The module `Sheaf.SixFunctorsBasics.FiniteBadLocusDimensionDrop` states
`AlgebraicGeometry.finite_bad_locus_dimension_drop`. Its sole proof is `by sorry`.
There are no new definitions, new DAG nodes, dependency repairs, or statement changes.

Source read: de Jong, *Families of curves and alterations* (1997), publisher scan
https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf, printed p.615,
Lemma 5.7 proof. The first paragraph gives spreading on reduced irreducible closed
subschemes. The second identifies maximal points of the bad closure and the
finite-map dimension drop. The item's six-step abstraction supplies the detailed
Noetherian and incomparability argument; all six steps are in the theorem docstring.
Stacks `schemes.tex`, `lemma-reduced-closed-subscheme` and
`definition-reduced-induced-scheme` (01J3/01J4), were read for the closed structures.

Hypothesis and clause matching:

- `V : Scheme.{u}` is the Noetherian base. `[IsLocallyNoetherian V]` and
  `[CompactSpace V]` are precisely locally Noetherian and quasi compact as required.
  `hdimV : topologicalKrullDim V < ⊤` says finite topological dimension and allows
  bottom, hence allows the empty scheme. It does not require nonemptiness.
- `A : Set V` is an arbitrary subset, without constructibility or closedness.
- `hspread` quantifies over every closed immersion `i : T ⟶ V` from an integral
  scheme. `IsIntegral T` already implies reducedness and irreducibility and includes
  nonemptiness. `ξ : T` with `IsGenericPoint ξ Set.univ` is its generic point;
  `i ξ ∉ A` is the stated antecedent. `U : T.Opens`, `U ≠ ⊥`, and the pointwise
  condition on `i t` say there is a nonempty open of T disjoint from A.
- The first conclusion quantifies over `irreducibleComponents ↥(closure A)` and
  all their generic points in that subspace, and says their ambient points lie in A.
  This uses subspace generic points, not components of V. Because `closure A` is
  closed, the ambient and subspace generic-point descriptions agree.
- The second conclusion is `Set.Finite` of the set of all those generic points.
  The subtype embeds injectively into V, so this is exactly finiteness of the
  ambient set of component generic points, including no points if Z is empty.
- The remaining conclusions are universally quantified in W, a, and A_W, after
  the first two conclusions. Thus the first assertions require no finite morphism
  or auxiliary scheme to be supplied.
- `[IsLocallyNoetherian W] [CompactSpace W]` says W is Noetherian, and
  `a : W ⟶ V` with `[IsFinite a]` is the finite morphism. No assumption of
  flatness, surjectivity, generic etaleness, or integrality of W is present.
- `A_W : Set W` is arbitrary; the first arrow antecedent in the W clause is the
  identical spreading condition over closed integral subschemes of W.
- The next antecedent `A_W ⊆ a ⁻¹' A` is the stipulated containment.
- The last antecedent quantifies over exactly the old component generic points
  and asserts `A_W ∩ a ⁻¹' {s} = ∅`, with s coerced into V.
- `closure A_W ⊆ a ⁻¹' closure A` is the first displayed inclusion. The next
  clause replaces A_W by its closure in the same fibre-avoidance equality,
  giving the second displayed assertion.
- The reduced closed schemes Z and Z_W used in dimensions are the actual
  `Scheme.IdealSheafData.vanishingIdeal` closed subschemes of the respective
  closed sets. The recorded reduced-induced-structure theorem gives reducedness
  and identifies their images with the closures. Their underlying spaces are
  homeomorphic to the subspaces used for the point-set and chain clauses.
- For every `d : ℕ`, nonemptiness of the old closure and the equality of its
  reduced scheme's dimension with `(d : WithBot ℕ∞)` imply the three dimension
  conclusions. Finite dimension of V ensures such a natural d exists whenever
  Z is nonempty; no separate dimension bound or nonemptiness is imposed on W.
- A strict specialization chain of length n is a function
  `c : Fin (n + 1) → ↥(closure A_W)` with adjacent entries satisfying `⤳` and
  inequality. `Fin.castSucc j` and `Fin.succ j` are the adjacent indices. The
  conclusion `n < d` covers n = 0 as well as longer chains.
- `d = 0 → closure A_W = ∅` is precisely the zero-dimensional empty conclusion.
- If the new closure is nonempty, `topologicalKrullDim` of its reduced closed
  scheme is strictly below that of the old reduced closed scheme.
- Finally `closure A = ∅ → closure A_W = ∅` is independent of the natural-d
  clause and covers the empty old locus.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, and `Scheme.Opens`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`, whose affine-local
  finite-ring-map field is exactly the definition in the node. The related
  `IsIntegralHom` signature in `Morphisms.Integral` was also read.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`; its fields and the
  reduced/irreducible equivalence give precisely integral reduced test schemes.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`; open subschemes
  in the hypothesis are the canonical `T.Opens`, rather than arbitrary maps.
- `Mathlib.Topology.Sober`: `IsGenericPoint` is singleton-closure equality.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents` is maximal irreducible
  subsets, with the subspace argument supplied explicitly in the theorem.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, together with
  `CompactSpace` for quasi compactness.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim : WithBot ℕ∞`.
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme`; its full docstring
  and signature were read, including the image and uniqueness clauses. The
  statement uses the canonical vanishing ideal and its real subscheme data.
- The plain proof imports include `Mathlib.Topology.NoetherianSpace`,
  `Mathlib.AlgebraicGeometry.AffineScheme`,
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, and
  `Mathlib.RingTheory.Ideal.GoingUp`, which supply the recorded finite-component,
  affine-basis, finite-integral, and incomparability proof dependencies.

Edge cases checked: empty V (allowed by dimension < top), empty A or A_W,
empty W, zero-dimensional nonempty Z, n = 0 chains (one point), reducible Z,
finite nonflat closed immersions, nonsurjective maps and identity maps. For
n = 0 the adjacency condition is vacuous and the chain conclusion rules out
points when d = 0. Nilpotents of the ambient schemes are permitted; reducedness
is required only on the integral test schemes and built into the closed loci.
All scheme and test-scheme universes are explicitly u. Closed subschemes have
canonical representatives in this universe, so the test quantifier loses no
closed subscheme. No implicit universe or variable is introduced.

Searches actually run through msearch.py for this item:

- LeanFinder: `dimension drop for closure of bad locus under finite morphism`.
  Eight results: quasi-finite morphisms, finite global sections, Jacobson spaces,
  coborder constructions, vanishing-ideal pushforward and closed-point images.
  No result states the spreading bad-locus theorem.
- Loogle: `IsFinite topologicalKrullDim closure`. It returned zero hits and
  `Unknown identifier IsFinite`; this query was inconclusive, not an exact-match
  exclusion by itself.
- Grep: `bad_locus|dimension_drop` in Mathlib. Zero hits.
- LeanSearch: `A spreading subset of a Noetherian scheme contains the generic
  points of its closure and a finite morphism avoiding them decreases its dimension`.
  Eight results include `genericPoints`, Noetherian component finiteness,
  closed-point images and spreading of stalk maps. They give ingredients only.
- Direct rg searches in Mathlib, WeilConjectures, Sheaf and
  `dag/lean_names_upstream.json` for `finite_bad_locus_dimension_drop`,
  `finite_bad`, `bad_locus`, `dimension_drop`, `bad.?locus`, and `bad.?closure`
  found no existing statement. The item id occurs only in the DAG and its citer.
  Existing dimension-drop results concern nowhere dense closed subsets,
  coordinates or very ample divisors. Existing reduced-closure ideal wrappers
  were read; the theorem directly uses their underlying canonical vanishing
  ideal operation and adds no duplicate definition.

The final module compiled cleanly through scompile.py in both sandbox and
library modes (6.6 s and 6.7 s). Every compile used the prescribed wrapper.
There is no STATEMENT-DISPUTED flag or node fault.

## Second reading by NS

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
