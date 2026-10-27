## Worker report

The module `Sheaf.AlgebraicGeometry.ComponentProjectionWeightBounds` states
`AlgebraicGeometry.BoundedHilbertWeight.component_projection_weight_bounds`, with its entire
proof `sorry`. Its only helper is the fully written predicate `IsPolynomialRestriction`, which
specifies the existing restriction arrows by their chart values; it constructs no arbitrary map.
The additional module `Sheaf.AlgebraicGeometry.RationalNormalCurve` defines the missing rational
normal curve predicate with real data (a proposition), without any postponed construction.

The item statement, proof, sources, and proof dependencies are unchanged. Its only changes are
`lean` and addition of `def-sfb-rational-normal-curve` to `stmt_deps`. No dependency repairs,
statement corrections, or STATEMENT-DISPUTED flags are needed.

The exact correspondence of every hypothesis and clause is:

- An algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`. The ambient
  coordinate type is the recorded `HilbertPlucker.Coordinates n`, with `r = n + 2`. `hr` states
  `4 ≤ n + 2`; every allowed r is included. `d : ℕ`, `hd : 3 < d`, `c : ℤ`, and `hdr` render
  precisely the positive integral degree, integral constant, and rational inequality d/r < 8/7.
- The embedded connected closed scheme is `X`, `i`, `[IsClosedImmersion i]`, and
  `[ConnectedSpace X]`. The structure over k is induced by the displayed embedding and the
  ambient projection. The coordinate Hilbert polynomial is exactly `hP`, using the recorded
  predicate with polynomial `C d * X + C c`. No purity, linear normality, characteristic,
  reducedness, or semistability condition is added.
- `hnd` says the degree-one equations of `X.nilradical.subschemeι ≫ i` are bottom. The quotient
  by the nilradical is the canonical reduced support, including its scheme structure.
  `ProjectiveHilbertPolynomial.equations` is the linear kernel of restriction, given on each
  standard chart. Thus this is exactly that no nonzero linear form vanishes on X_red.
- A reduced irreducible component is represented by `[IsIntegral Y]`, a closed immersion `j`,
  and `hY : Set.range j ∈ irreducibleComponents X`. This gives the unique reduced structure
  on that component, rather than replacing a possibly nonreduced X by a reduced curve.
- `e : ℕ` with `he` fixes exactly its degree: `Scheme.Modules.degree k` of O(1) pulled back
  along `Y.fromNormalization ≫ j ≫ i`, using the explicit induced field structure on the
  canonical `Y.normalization`. This is the source's normalized-component degree. Degree
  positivity is a consequence of the geometric assumptions, not an extra hypothesis.
- The family `ρ` and `hρ : IsPolynomialRestriction i ρ` are the canonical polynomial
  restriction maps, with the same chart formula as the recorded bounded-weight theorem.
  Their target is the recorded `sections`, namely module-sheaf H⁰ of the pulled-back twist
  with scalars restricted along the structural map to Spec k. Chart characterization fixes
  the maps uniquely; it is not an arbitrary association of polynomials to sections.
- `b` is any compatible basis and natural weights `w` with `hw : ∀ l, w l ≤ 1` are exactly
  zero/one integral weights. `hF : flag b w 0 = equations ... (j ≫ i) 1` says its weight-zero
  space is W, the kernel of the restriction to Y. The weight-one quotient is consequently
  V/W. No basis or complement is fixed geometrically.
- `a : ℚ` and `ha` identify a_F by the exact convention `|weight (ρ m) b w - a*m²| ≤ A*m`
  for sufficiently large m, with the existing minimum monomial weight definition. These
  parameters describe the a_F already introduced by the item; they are not additional
  geometric hypotheses. The recorded bounded-weight theorem guarantees existence, its
  half-integrality, and flag independence. Any two such a agree by dividing their O(m)
  difference by m², so the universal formulation does not choose a different coefficient.
- In the first implication, `2 ≤ Module.length` of the X-stalk at `j (genericPoint Y)`
  is precisely the local length assumption. `coordinateDimension ... (j ≫ i) 1 ≤ e + 1`
  is s ≤ e+1: this dimension is literally that of V modulo its linear equation kernel.
  Its other conjunct is `2*(e:ℚ) + 1/2 ≤ a`.
- The second implication assumes reduced X-stalks at every point whose singleton closure
  is an irreducible component. These are exactly the generic points. This is generic
  reducedness, and still permits embedded nilpotents. Its next hypotheses are exactly
  `e ≤ 3` and `¬ IsRationalNormalCurve k (n+1) (j ≫ i) e`. The conclusion is s ≤ e and
  `(e:ℚ) + 1/2 ≤ a`. Both implications are conjoined for the same projection flag.

Dependency declarations read and used:

- Mathlib `Field`, `Scheme` and `Scheme.Hom`, `IsClosedImmersion`, `IsReduced`, and
  `ConnectedSpace`, with their docstrings and full structures; `Module.length` in
  `Mathlib.RingTheory.Length` is the extended-natural submodule-chain length. The instances
  on the ambient generic stalk make it its length as a module over itself.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`: `ProjectiveSpace.twist`.
- `WeilConjectures.Topology.RingedSpaceModuleCohomology`: `RingedSpace.moduleCohomology`,
  through the existing `sections` and `UniformProjectiveFibreVanishing.zeroSections`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`: `Scheme.Modules.degree`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`: `Scheme.normalization` and
  `Scheme.fromNormalization`, both for the specified integral component.
- `Sheaf.AlgebraicGeometry.BoundedHilbertWeightPolynomials`:
  `BoundedHilbertWeight.exists_uniform_bounded_hilbert_weights`, whose complete signature
  was read. Its public weighted-monomial definitions `LinearForms`, `sections`, `flag`,
  and `weight` are reused. The canonical chart normalization is verbatim its ρ clause.
- The publicly imported recorded coordinate-polynomial definitions in
  `Sheaf.AlgebraicGeometry.FlatProjectiveHilbertPolynomialLocality`: `equations`,
  `coordinateDimension`, and `IsCoordinatePolynomial`.
- The new rational-normal predicate is the only added independent notion. The two recorded
  Mathlib proof dependencies for finite type/Noetherianity and finite components are covered
  by the proof import `Mathlib.AlgebraicGeometry.Noetherian`. Ideal-sheaf powers and the closed
  immersion kernel are covered by `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`. Other geometric
  proof prerequisite nodes currently have no Lean record, so no unavailable imports were added.

Edge cases checked: r=4 and d=4 satisfy the intended lower endpoints; r<4 and d≤3 are excluded
exactly by the node. The empty scheme is excluded by ConnectedSpace and the positive Hilbert
slope. A zero-dimensional component cannot occur: it would be an isolated component in this
connected one-dimensional Noetherian scheme. Thus representing e as a natural number loses no
negative or zero degree case. W=0 is not explicitly excluded; the theorem applies to every
zero/one flag and the proof derives W≠0 in the asserted cases. Embedded points and generically
reduced nonreduced schemes remain allowed. The generic-multiplicity premise includes all lengths
at least two. A line, a conic and a twisted cubic satisfy the rational-normal definition; a smooth
or nodal plane cubic does not. A rational curve embedded by an incomplete higher-degree series
fails completeness, even if its underlying curve is P¹. The characteristic is unrestricted.
Universes are explicit; neither extra site-size identifications nor auto-implicit variables occur.

Searches actually performed through msearch.py (logged in the sandbox):

- LeanFinder: "Component projection leading Hilbert monomial weight lower bound for a multiple
  component of a projective curve" returned eight elliptic polynomial/degree hits, no match.
- Loogle: "Module.length, LinearMap.ker, AlgebraicGeometry.Scheme.normalization" returned zero
  hits and an unknown-normalization-identifier diagnostic; it did not validate an absence.
- Mathlib grep: `rationalNormal|RationalNormal|projection.*weight|component.*weight` returned
  18 unrelated weighted-limit and power-series hits.
- LeanSearch and LeanFinder for the rational-normal notion returned eight elliptic-projective
  and projectivization hits each; the algebraic-geometry grep returned no hits. The exact
  queries and actual logged results are in the new node's mathlib_searches.
- `rg` in upstream WeilConjectures, Sheaf, and upstream names found no component-projection
  bound or rational-normal definition. Whole-DAG exact-text searches found only the five
  theorem nodes using this notion, not a definition. `blueprint_refs.py search 'rational normal'`
  found zero blueprint nodes. The ancestor command reports the inherited null ancestor,
  retained in the new node, with the existing via chain extended by this item.

Sources read: Morrison's current arXiv PDF, §3.2, Theorem 8 steps (2)--(3), printed p.14
(https://arxiv.org/pdf/0810.2340); Gieseker's TIFR PDF, Proposition 1.0.3, printed pp.30--36
(https://mathweb.tifr.res.in/Documents/Publications/Lectures/tifr69.pdf), especially the
geometric monomial filtration estimate preceding the application of semistability. These are
read online; the read-only literature tree was not changed. The existing blueprint unit does
not independently state this supporting estimate.

Both delivered modules compiled separately in dependency order through scompile.py against
the published live library, with no error or disallowed warning. All declarations and universes
are explicit, all lines fit 100 columns, and the only theorem has the whole proof `by sorry`.

## New nodes

`def-sfb-rational-normal-curve` defines the independent notion missing from the DAG and library.
For a morphism Y→Pⁿ over k, it requires a closed immersion, positive e, a k-isomorphism P¹→Y,
the pulled-back hyperplane line O(e), and restricted linear-form dimension e+1. On P¹ the last
condition is exactly completeness of the degree-e system in the curve's own linear span.
It uses the existing field, scheme, closed-immersion, twist, and coordinate-dimension nodes;
it constructs no surrogate curve or map. The source is the definition specified in this item
and the companion span-rigidity node, used in Morrison Theorem 8 step (3). The LeanSearch,
LeanFinder, Mathlib grep, upstream/Sheaf rg, DAG and blueprint searches above found no existing
definition. There are no dependency modules.

## Second reading by Q38

This is the author's second reading with both node copies and both Lean modules open; the
maintainer provides the independent review, as prescribed by the dispatcher brief (no other
agent was started). The quantitative hypotheses, the two conditional conclusions, and their
shared flag were compared individually as above. In particular, `hnd` concerns X_red, not X;
`he` concerns normalized Y, not its arithmetic genus; and generic reducedness is a local
condition at all component generic points, not global reducedness. The minimum weight uses
H⁰ of the actual X, retaining all its nilpotent structure. The rational-normal definition
checks the isomorphism is over k and demands the complete linear system rather than merely
rationality. During the reading its ambient indexing was generalized to Pⁿ directly, so the
main theorem applies it with n+1; its imports were reduced to the recorded coordinate-polynomial
module. Both modules were then recompiled. No mismatch with either node remains.

Preflight schema repair: the current server requires `import_flags` on a new node
(tools/stage2_delivery.py, updated 2026-10-23). Added the empty list required by that schema;
the older field list in brief-stage2.md omits it. No import flags on the existing item changed.
