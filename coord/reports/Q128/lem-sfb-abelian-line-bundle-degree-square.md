## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.LineBundleDegreeSquare` states
`AlgebraicGeometry.IsAbelianVariety.line_bundle_degree_square`, with a single `sorry`.
There are no new definitions, new nodes, dependency repairs, or statement changes.
Only the item's `lean` field changes. All written files are in the assigned sandbox.

Source read: Milne, Abelian Varieties, I Theorem 11.1(a),(b), printed p.54 (PDF p.60),
and the zero-degree convention preceding Theorem 10.9, printed p.46 (PDF p.52).
The former says degree(lambda_L) = chi(L)^2 and chi(L) = D^g/g! for an invertible
sheaf L = L(D), without an ampleness assumption. The accepted DAG proof translates
this into the existing coefficient-of-Euler-polynomial intersection convention.
The docstring reproduces all four steps, with their dependency IDs.

Hypothesis and clause correspondence:

- `k : Type u`, `[Field k]`, `[IsAlgClosed k]`: the algebraically closed base field.
  The explicitly bound universe `u` is arbitrary; no characteristic is restricted.
- `A : Over (Spec (.of k))`, `[GrpObj A]`, `[IsAbelianVariety A]`: the given abelian
  variety and its group scheme structure. The last class supplies properness,
  smoothness and connectedness. Nonemptiness and properness needed by the intersection
  definition are inferred from these existing structures, not additional hypotheses.
- `(g : ℕ) (_hg : 1 ≤ g)` and
  `hA : topologicalKrullDim A.left = ((g : ℕ∞) : WithBot ℕ∞)`:
  the positive integer dimension g and equality with the topological Krull dimension.
- `D : AbelianDualPoincareDatum A`: the normalized representing dual variety of the
  polarization-calculus dependency. This is its existing full universal Poincare datum,
  not an arbitrary abelian variety or an arbitrary map called a polarization.
- `N : A.left.Modules`, `[N.IsInvertible]`: every invertible sheaf N on A.
- `φ : A ⟶ D.dual`, `[IsMonHom φ]`,
  `_hφ : ClassifiesAbelianDifference D N φ`: exactly the homomorphism phi_N of the
  polarization-calculus dependency. The predicate identifies the pullback of the
  universal Poincare sheaf with the normalized translated-difference family.
  The dependency gives existence and uniqueness of such a homomorphism for N; these
  binders merely name that specified object without choosing data from an existence
  theorem or introducing another definition of it.
- The left side is `@ite ℚ (IsIsogeny φ) (Classical.propDecidable _)
  (isogenyDegree φ : ℚ) 0`. Thus the locally defined d(h) is rendered directly,
  using the existing isogeny degree on the isogeny branch and zero otherwise.
  `isogenyDegree φ` unfolds to `(GrpObj.ker φ).hom.finrankΓ`, the dimension of the
  coordinate algebra of the scheme-theoretic kernel, not the number of geometric points.
  The explicit classical decider supplies only a decision of the branch proposition.
- The right side uses `@Scheme.Modules.selfIntersectionNumber k _ A.left ⟨A.hom⟩
  (inferInstance : IsProper A.hom) A.left inferInstance (𝟙 A.left) inferInstance
  g hA N inferInstance`,
  divided by `(Nat.factorial g : ℚ)` and squared: the repeated-bundle intersection
  with Z = A and its identity closed immersion, divided by g! in Q and squared.
  The entire equation has type equality in Q.
- There is no ampleness, nondegeneracy, separability, finite-kernel or isogeny hypothesis.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field`, a commutative ring and division ring.
- Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed` (every polynomial splits,
  equivalently every nonconstant polynomial has a root). The algebraic-closure node's
  `mathlib_match` also records `AlgebraicClosure` and `IsAlgClosure`; this item needs
  the closedness predicate, not a chosen closure.
- WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs: `IsAbelianVariety`.
- Mathlib.Topology.KrullDimension: `topologicalKrullDim`, the Krull dimension of
  `IrreducibleCloseds`, with values in `WithBot ℕ∞`.
- WeilConjectures.AlgebraicGeometry.Modules.Invertible: `Scheme.Modules.IsInvertible`.
- Sheaf.AlgebraicGeometry.AbelianVariety.PolarizationCalculus:
  `IsAbelianVariety.exists_dual_polarization_calculus`; its public dependency
  Sheaf.AlgebraicGeometry.AbelianVariety.DualPoincareDatum supplies
  `AbelianDualPoincareDatum` and `ClassifiesAbelianDifference`. Their full source
  signatures and docstrings were read. The theorem's existence/uniqueness clause
  makes the classifying-map formulation the same phi_N as the node.
- Mathlib.CategoryTheory.Monoidal.Grp: `GrpObj` and `IsMonHom`, through the recorded
  group-scheme interface in WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Defs: `IsIsogeny` and `isogenyDegree`.
- Sheaf.AlgebraicGeometry.IntersectionNumber: `Scheme.Modules.intersectionNumber`
  and its repeated-bundle notation `Scheme.Modules.selfIntersectionNumber`.

The two direct public imports expose these statement notions. The two Euler proof
nodes have no recorded Lean declaration in the read clone, so there is no proof-only
module to import yet; the proof plan names both exactly. The intersection-number
proof dependency is already imported publicly because it is also a statement dependency.

Edge cases checked before writing: N = O_A in positive dimension gives phi_N = 0,
non-isogeny degree zero and top self-intersection zero. For an elliptic curve and any
line bundle of signed degree d, the formula is d^2, including d = 0 and d < 0. For a
pullback from one factor of E × E, the positive-dimensional kernel and vanishing top
self-intersection give zero on both sides. An anti-ample bundle can have a negative
Euler characteristic/top intersection when g is odd, but its square is still the
kernel degree. In positive characteristic a nonreduced finite kernel is measured
by its coordinate-algebra dimension; inseparability is not discarded. g = 0 is
excluded exactly as in the node, while g = 1 is included. The empty scheme cannot be
an abelian variety with this connected/group structure. No disputed statement found.

Searches actually run with the prescribed `msearch.py` wrapper:

- LeanFinder: "The degree of the homomorphism defined by any line bundle on an
  abelian variety is the square of top self intersection divided by dimension factorial".
  Eight hits, all WeierstrassCurve division-polynomial degree statements; no match.
- Loogle: `"isogeny"`. Zero hits.
- Mathlib grep, AlgebraicGeometry: `isogenyDegree|selfIntersectionNumber|riemannRoch|riemann_roch`.
  Zero hits.
- LeanSearch: "The degree of the line bundle homomorphism on an abelian variety
  equals its top intersection divided by factorial squared". Eight hits including
  polynomial-degree declarations, RatFunc.intDegree_mul and a HomComplex projection;
  none concerns the line-bundle homomorphism or abelian Riemann--Roch.
- Local rg over `lean/WeilConjectures` and `lean/Sheaf` for
  `isogenyDegree|IsIsogeny|exists_dual_polarization_calculus|intersectionNumber|selfIntersectionNumber|IsAbelianVariety`
  located the above existing interfaces and other intersection formulae, no copy of
  this identity. A separate search of both trees and `dag/lean_names_upstream.json`
  for the node id, `line_bundle_degree_square`, `isogenyDegree.*intersection`, and
  `intersection.*isogenyDegree` found no existing declaration. The node-id search
  over the upstream source also had no result.

## Second reading by Q128

I reread the node and the final signature clause by clause; no separate worker or
sub-agent was started, as the dispatcher explicitly forbids that. The maintainer's
independent review remains the independent reading. This section records my own
second check, without claiming an independent reviewer.

The signature retains algebraic closedness, the group scheme and abelian-variety
structure, the dimension equality and g >= 1, arbitrary invertible N, and the
specified difference-family homomorphism to the normalized dual. The conditional
is necessary: the upstream `isogenyDegree` definition is the kernel finrank for
all maps, without itself testing whether a map is an isogeny. The signature supplies
that missing zero convention explicitly. The intersection uses the identity of A,
not a divisor or a different closed subscheme. The factorial is cast before division,
and the equality is in Q. No additional geometric condition is imposed, and no clause
is dropped. No mismatch or node correction was required.

Compilation adjustment: the bundled over-scheme does not automatically expose the properness
instance through an inferred `A.left.Over` structure. The intersection application now
passes the actual structure map `⟨A.hom⟩` explicitly, so the existing
`IsProper A.hom` instance is used. This adds no hypothesis or new construction.
