# Strict normal crossings boundary parameter criterion

## Worker report

The delivery states `AlgebraicGeometry.isStrictNormalCrossingsBoundary_iff_parameters`
in `Sheaf.AlgebraicGeometry.SNCBoundaryParameterCriterion`. Its proof is `sorry`.
No definitions, helper nodes, or dependency repairs are needed. Only the item's `lean`
record changes. The prior Q82 delivery was the stage-1 split, not a stage-2 statement:
its report explicitly says no Lean source or compiler was used, and the current node has
neither `lean` nor `reviewed_lean`. Therefore this delivery does not repeat that work.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A scheme X: `(X : Scheme.{u})`, with an explicitly bound arbitrary universe `u`.
- Noetherian X: `[IsNoetherian X]`, Mathlib's locally Noetherian and quasi-compact
  scheme predicate. This also supplies Noetherianity of every stalk for the recorded
  parameter predicate. No separate assumption on the stalks is introduced.
- Regular X: `(_hX : IsRegularScheme X)`, exactly the recorded scheme notion.
- A closed subscheme H of X: `(H : X.IdealSheafData)`, the canonical quasi-coherent
  ideal representation used by the recorded boundary definition. Its closed subscheme
  is `H.subscheme` with closed immersion `H.subschemeι`; this ranges over arbitrary
  closed subschemes, with no Cartier or reduced hypothesis on H.
- H is a strict normal crossings boundary: `IsStrictNormalCrossingsBoundary H`,
  exactly the dependency declaration, on the left side of `↔`.
- If and only if at every point: `↔ ∀ x : X, ...`; both directions are retained.
- A regular system t_1,...,t_d of O_X,x: `t : List (X.presheaf.stalk x)` together
  with `IsLocalRing.IsRegularSystemOfParameters t`. The recorded definition says
  its entries generate the maximal ideal and its length is the ring Krull dimension.
- The integer 0 ≤ r ≤ d: `(r : ℕ)` and `r ≤ t.length`. Nonnegativity is intrinsic
  to naturals, while `t.length` is d by the parameter predicate.
- The stalk ideal is (t_1...t_r):
  `(H.ideal U).map (X.presheaf.germ U.1 x hx).hom = Ideal.span {(t.take r).prod}`.
  An affine neighbourhood `(U : X.affineOpens)` with `(hx : x ∈ U.1)` represents
  the ideal sheaf stalk by extension along the germ map. This is the existing
  representation in `IsNormalCrossingsDivisor`, not a new notion or additional
  geometric hypothesis. Every point has such a neighbourhood, and extension of a
  quasi-coherent ideal gives its stalk ideal independently of this choice.
- Empty product / points off H / empty boundary: `List.take 0 t = []` and
  `List.prod [] = 1`, so the right-hand ideal is the unit ideal. No membership in
  H.support is imposed on x. The case r=0 remains available everywhere.
- The final consequences are the actual clauses of the recorded boundary predicate:
  `H.IsInvertible` is the effective Cartier ideal predicate; `H.radical = H` is
  radicality/reducedness; the witnesses `n` and `C : Fin n → X.IdealSheafData`
  are finitely many distinct integral regular components, whose supports have union
  H.support; its `∀ s : Finset (Fin n), ∀ z, ...` clause states regularity of every
  scheme-theoretic intersection and the exact local dimension equality with `s.card`.
  Thus the reverse implication includes all the stated “in particular” assertions,
  rather than replacing them by an independent or weaker local boundary predicate.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`,
  locally Noetherian and the upstream stalkwise `AlgebraicGeometry.IsRegular`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (all ideals finitely
  generated). The scheme hypothesis uses `AlgebraicGeometry.IsNoetherian` and its
  stalk instance from `Mathlib.AlgebraicGeometry.Noetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`; ideal sheaf data represents its associated
  closed subscheme through Mathlib's `IdealSheafData.subscheme` construction.
- `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`:
  `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`, read in full including all
  intersection and dimension clauses.
- `Sheaf.RingTheory.IsRegularSystemOfParameters`:
  `IsLocalRing.IsRegularSystemOfParameters`, read in full including its empty list.

The statement modules are public imports. Stated proof-dependency modules are ordinary
imports: `RegularLocalQuotientKernelParameters`, `RegularLocalGeneratorsRegularSequence`,
`RegularLocalUFDBoundaryFactorization`, `Mathlib.RingTheory.LocalRing.Module`, and
`WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`. The cotangent-dimension and
Noetherian finite-components modules are already publicly imported through the statement
modules. The theorem docstring carries all four proof steps from the node, with their
named dependencies. There are no local instances, private notions, hidden let binders,
or auto-bound implicit variables.

Edge cases checked against the source and full boundary predicate:

- The empty scheme: the local condition is vacuous and the boundary has an empty
  component family.
- The empty boundary: H is the unit ideal; choose r=0 at all points.
- Dimension zero: t is empty and r=0 is the only permitted value. The whole nonempty
  zero-dimensional scheme is excluded, since its zero ideal is not the unit ideal.
- Coordinate axes V(xy) in the affine plane: r=2 at the origin, with two regular
  components and a regular codimension-two intersection.
- V(x²): excluded by radicality and by a product of distinct regular parameters.
- Tangent branches V(x(x-y²)): excluded because the two branch equations cannot
  be members of a single regular parameter system; their intersection has the
  wrong reduced regular structure.
- An irreducible nodal curve: an etale or completed splitting is insufficient.
  The statement requires parameters in the ordinary local ring itself, matching
  strict normal crossings and avoiding the weaker normal crossings notion.
- Non-equidimensional X and no base field: the statement imposes neither a global
  dimension nor smoothness nor a characteristic restriction; all dimensions are local.

Sources opened: `literature/stacks-project/etale.tex`,
`definition-strict-normal-crossings` and `lemma-strict-normal-crossings` (Tags 0BI9,
0BIA), including both directions of the proof. The source's condition at points on
H is extended to points off H using the node's regular ambient scheme and r=0,
exactly as the node specifies. No statement correction or dispute is required.

Searches for reuse (all msearch commands use group NX and this item):

- LeanFinder: “A closed subscheme of a regular Noetherian scheme is a strict normal
  crossings divisor if and only if its ideal at each stalk is generated by a product
  of distinct members of a regular system of parameters”. Eight hits concerned
  Weierstrass division, smooth loci, or reduced stalks; no matching theorem.
- Loogle: `IsStrictNormalCrossingsBoundary, IsRegularSystemOfParameters`.
  Zero hits; unknown identifier `IsStrictNormalCrossingsBoundary`.
- Mathlib grep: `StrictNormalCross|strict normal crossing|IsRegularSystemOfParameters`
  under AlgebraicGeometry. Zero hits.
- LeanSearch: “strict normal crossings divisor on a regular Noetherian scheme
  characterized by products of regular parameters in its local rings”. Eight hits,
  including schemes and Noetherian finite-components infrastructure; none the criterion.
- `rg` in upstream WeilConjectures: the node id and
  `strict.normal.cross|StrictNormalCross|IsRegularSystemOfParameters` give no matches.
- `rg` in the project's `lean/Sheaf` finds the exact boundary and parameter
  definitions and related normal-crossings charts, but no theorem of this iff.
  `NormalCrossingsDivisor` uses an etale neighbourhood and is strictly different;
  `RegularBoundaryDivisorialChart` assumes a boundary and supplies its log chart.
- The proposed declaration and module names were searched in the project,
  upstream source, and `dag/lean_names_upstream.json`; no collision was found.

Validation: the prescribed scompile.py compiled the file in both sandbox and library
contexts with no errors or warnings. The prescribed deliver2.py --no-push dry run returned OK at c5878214e4: the
commit passes the server preflight and compiles.

## Second reading by NX

I reread the unchanged node, Tags 0BI9/0BIA, the full recorded boundary definition,
and the delivered signature after compilation. Each point is universally quantified;
U and hx only present its actual stalk ideal. The parameter list is a full system,
not an arbitrary sequence, and the selected factors are its initial r terms with
r bounded by its length. Consequently no repeated factor or extra generator is allowed.
Both directions use the same ideal H. No reducedness or Cartier assumption is silently
placed on the right side; these conclusions follow through the left boundary predicate.
The finite family, integral components, support union, and all intersection clauses
are retained by referring to that exact predicate. r=0, dimension zero, and the empty
scheme remain included. The regular and Noetherian hypotheses are precisely the node's.
All variables and the universe are explicit, the single theorem has sorry, and no
statement, proof, dependency list, or maintainer field in the node was changed.
