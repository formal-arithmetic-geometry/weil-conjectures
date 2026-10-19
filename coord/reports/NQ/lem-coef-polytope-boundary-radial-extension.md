## Worker report

The module `Sheaf.Topology.PolytopeBoundaryRadialExtension` states
`EuclideanGeometry.polytope_boundary_radial_extension`, with its sole proof `by sorry`.
It states the whole node: unique continuous radial coordinates on each punctured polytope,
and extension of every prescribed boundary homeomorphism by the given radial formula,
including the inverse formula and both centers. No definition, instance, auxiliary node,
or dependency repair is needed. The node copy changes only `lean`; its mathematical
statement, dependencies and twelve-step proof are unchanged. All variables and the two
index universes are explicit, and `autoImplicit` is false.

The previous BLOCKED conclusion confused stages. Q152's existing record is a stage-1
split and its independent mathematical review: `status: split`, `reviewed.result: pass`.
There was no `lean` or `reviewed_lean` record and no module for this item. Writing its
first Lean statement is precisely stage 2; this delivery does not re-split the node or
replace Q152's work. There was no repair note for the item in `coord/repair-notes`.

The hypothesis and clause correspondence is as follows. Set expressions in type positions
use the explicit subtype coercion `↥`; this retains the recorded induced topology.

| Node hypothesis or clause | Exact Lean rendering |
| --- | --- |
| Dimensions d,e at least 1 | `{d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e)` |
| Usual real Euclidean spaces | `EuclideanSpace ℝ (Fin d)` and `EuclideanSpace ℝ (Fin e)` from Mathlib; no custom topology |
| Finite inequality index sets J,K | `{J : Type u} {K : Type w} [Finite J] [Finite K]`; neither nonemptiness nor an enumeration is assumed |
| Real linear functionals ell_j,m_k | `ell : J → EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ` and the analogous `m` |
| Each functional nonzero | `hell : ∀ j : J, ell j ≠ 0` and `hm : ∀ k : K, m k ≠ 0` |
| Real thresholds a_j,b_k | `(a : J → ℝ) (b : K → ℝ)` |
| P,Q are exactly the sets defined by the inequalities | `hP : P = {x | ∀ j : J, ell j x ≤ a j}` and `hQ : Q = {y | ∀ k : K, m k y ≤ b k}` |
| Both sets bounded | `hPb : Bornology.IsBounded P` and `hQb : Bornology.IsBounded Q` |
| Centers c,v and every inequality strict there | Explicit Euclidean points `c,v`, `hc : ∀ j, ell j c < a j`, `hv : ∀ k, m k v < b k` |
| Subspace topologies on all subsets | The recorded `instTopologicalSpaceSubtype`, including both punctures, both boundaries, and P,Q themselves |
| Boundary means P minus its interior, similarly Q | Every occurrence is literally `↥(P \ interior P)` or `↥(Q \ interior Q)`; no silently substituted frontier |
| A boundary coordinate p and real coordinate r for every x in P other than c | The first existential functions `pP : ↥(P \ {c}) → ↥(P \ interior P)` and `rP : ↥(P \ {c}) → ℝ` |
| Both coordinates depend continuously on x | `Continuous pP ∧ Continuous rP` on the punctured subspace |
| 0 < r ≤ 1 and x=c+r(p-c) | For every `x`, `0 < rP x ∧ rP x ≤ 1 ∧ x.val = c + rP x • ((pP x).val - c)` |
| Coordinates unique | For every boundary `p` and real `r`, positivity, `r ≤ 1`, and the same representation imply `p = pP x ∧ r = rP x` |
| Analogous assertion for Q,v | The second existential with `pQ,rQ`, their two continuity clauses, the positive interval, representation, and uniqueness, with Q,v in every place |
| Every prescribed boundary homeomorphism psi | `∀ psi : ↥(P \ interior P) ≃ₜ ↥(Q \ interior Q)` |
| The specified extension is a homeomorphism P to Q | `∃ H : P ≃ₜ Q`, together with the following equations that determine its function on all points |
| H(c)=v | `∀ x : P, x.val = c → (H x).val = v` |
| H(c+r(p-c))=v+r(psi(p)-v) | For all boundary `p`, `r` with `0 < r ≤ 1`, and `x : P` with `x.val = c + r • (p.val - c)`, the conclusion is `(H x).val = v + r • ((psi p).val - v)` |
| H extends psi pointwise | `∀ p : ↥(P \ interior P), (H ⟨p.val, p.property.1⟩).val = (psi p).val` |
| Inverse sends v to c | `∀ y : Q, y.val = v → (H.symm y).val = c` |
| Inverse radial formula | For all boundary `q`, `r` with `0 < r ≤ 1`, and `y : Q` with `y.val = v + r • (q.val - v)`, `(H.symm y).val = c + r • ((psi.symm q).val - c)` |

The equalities `hP,hQ` merely name the two displayed inequality-defined sets; they do not
add restrictions. The strict inequalities already imply that c belongs to P and v belongs
to Q, so the center clauses are not vacuous. Their conditional presentation avoids putting
proof-producing terms in the signature. Similarly the radial clauses quantify an existing
subtype point and its ambient-coordinate equality, avoiding proof terms for ray membership.
The coordinate conclusions ensure that every noncenter point has exactly such a presentation.
Consequently those clauses and the center values determine the forward and inverse maps
everywhere; this is not an arbitrary homeomorphism with only its boundary restriction fixed.
`Homeomorph` supplies bijectivity and continuity in both directions, exactly as required.

### Dependencies and source reading

The only statement and proof dependency is `def-kun-subspace-topology`. I read its complete
statement and its `mathlib_match`/`lean` record, and then read
`Mathlib.Topology.Defs.Induced`, lines 60-78. Its declaration is
`instTopologicalSpaceSubtype {p : X → Prop} [t : TopologicalSpace X] :
TopologicalSpace (Subtype p) := induced (↑) t`.
The preceding documentation and actual `induced.IsOpen` field identify opens as preimages
of ambient opens. Thus this is exactly the subspace topology the node asks for. The module
imports that dependency directly with `public import`; it is also the only proof dependency.
The dependency's inherited Stacks tag 0055 describes Krull dimension rather than the basic
induced-topology definition. This pre-existing source-label fault does not affect the exact
Mathlib match and is not changed in this delivery.

The other two public imports provide the existing notions used in the signature:
`Mathlib.Analysis.InnerProductSpace.PiL2` gives `EuclideanSpace` (read its definition and
docstring at lines 107-114), the real linear algebra and metric boundedness;
`Mathlib.Topology.Homeomorph.Defs` gives `Homeomorph` and its canonical inverse.
No Euclidean space, boundary topology, coordinate structure or extension map is redefined.

I read the current node and all twelve proof steps, Q152's stage-1 report, its sole cited
definition, and step 12 of `lem-coef-realization-finite-limits`. I also read the current
blueprint source for `prop-coef-integral-exceptional-adjoint` proof paragraph 2. The latter
provides the ancestry/context, not this elementary Euclidean proof. The module's theorem
docstring carries all twelve steps, including the positivity, uniqueness, quantitative
coordinate continuity, radial inverse calculation, and separate center estimates.

I opened the Rochester Hovey PDF online and read printed p.79 (PDF page index 88), including
the paragraph after Proposition 3.2.2, and its continuation through Proposition 3.2.3.
It gives the simplex/disk and horn/cylinder pairs; the general prescribed-boundary extension
is explicitly the recorded agent supplement, not a theorem attributed to Hovey.
Source: https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/hovey-model-cats.pdf .
The theorem docstring preserves that distinction.

### Searches

All three prescribed search forms were run, with their raw results in sandbox
`searches.jsonl`; no unavailable response was treated as a negative result.

1. `msearch.py ... leanfinder "Every prescribed homeomorphism between boundaries of bounded
   convex polytopes extends by radial coordinates from interior points"`: eight hits.
   `exists_homeomorph_image_eq` and
   `exists_homeomorph_image_interior_closure_frontier_eq_unitBall` give existence of a
   particular ambient homeomorphism; the remaining hits are manifold models. None fixes
   an arbitrary prescribed boundary map or states the unique continuous coordinates.
2. `msearch.py ... loogle "Homeomorph, frontier"`: four hits,
   `Homeomorph.image_frontier`, `Homeomorph.preimage_frontier`, and the same two gauge
   existence theorems. The first two concern an already given ambient homeomorphism;
   the latter do not extend prescribed data. I read the pinned
   `Analysis/Convex/GaugeRescale.lean:128-197`, including the full signatures and docstrings.
   They do not state this node and cannot be used as an exact existing record.
3. `msearch.py ... grep "radial.*(extend|frontier)|extend.*homeomorph|homeomorph.*extend"
   Analysis`: two prose hits in the inverse function theorem module, unrelated to a
   prescribed map between polytope boundaries.
4. `rg` of `polytope|radialExtension|radial.*[Cc]oordinate|[Bb]oundary.*[Ee]xten` and a
   narrower case-insensitive radial/polytope search over the upstream `WeilConjectures`
   and side `lean/Sheaf` sources: no declaration stating this node. Searches for the
   exact item id and chosen full declaration name also gave no match. The upstream
   declaration index was searched for the same terms and name.
5. The existing cubical-open-box statement was opened: it gives a particular cube-pair
   homeomorphism, not this arbitrary-boundary extension. The DAG's convex-body-ball and
   horn-boundary-cylinder entries and Q152's recorded duplicate audit likewise concern
   a particular ambient homeomorphism or a particular boundary map. This node is their
   general radial extension input and is not already carried by another declaration.

### Edge cases and statement check

- The one-dimensional case is included. For P=[-2,3], c=1, the radial scalar is
  max((x-1)/2,(1-x)/3); p selects the appropriate endpoint. For Q=[-1,5], v=0 and
  the endpoint-reversing boundary map, H(x)=5(1-x)/3 when x≤1, and
  H(x)=-(x-1)/2 when x≥1. Both pieces meet at 0 and extend the swapped endpoints.
  The inverse is x=1-3y/5 for y≥0 and x=1-2y for y≤0, giving the asserted inverse rays.
- At the centers no boundary-coordinate limit is claimed: coordinates are continuous
  only on P minus {c} and Q minus {v}. H and its inverse are continuous on the whole
  bodies, including the centers, as the node requires.
- r=1 is included and gives the exact prescribed boundary value. r=0 is dealt with by
  the separate center clauses, so it cannot create spurious uniqueness of p.
- Empty J or K remains allowed syntactically. With positive dimension it makes the
  corresponding inequality set the unbounded whole space, contradicting the existing
  boundedness hypothesis. No unnecessary nonempty-index hypothesis was added.
- Empty polytopes and lower-dimensional bodies cannot satisfy all the strict inequalities
  at the displayed center. There is no extra nonemptiness, convexity, closedness, or
  full-dimensionality assumption: these follow from the node's actual hypotheses.
- Repeated and redundant nonzero constraints are allowed. For a centered square with
  an extra inequality x₁≤2 the maximum max(x₁,-x₁,x₂,-x₂,x₁/2) still gives the same
  coordinates, including edges and corners. Very thin polytopes only enlarge the
  finite Lipschitz constants, without invalidating the statement.
- d and e are independent, as are the universes of J and K. Only the final extension
  is conditional on a boundary homeomorphism; both coordinate assertions are independent
  of its existence. No equality of dimensions or orientation assumption was added.

No mathematical statement correction or STATEMENT-DISPUTED flag is needed.

### Validation

The prescribed `scompile.py` wrapper is used for the single delivered module. The initial
compile identified ambiguous coercion of compound set expressions to types; every such
type now uses `↥(P \ ...)` or `↥(Q \ ...)`. This is an elaboration repair only.
The repaired module compiled cleanly through `scompile.py`, both as the sandbox file and
as `Sheaf.Topology.PolytopeBoundaryRadialExtension` (1.5 seconds for each invocation).
There were no errors or warnings.

`deliver2.py NQ lem-coef-polytope-boundary-radial-extension --no-push` returned
`OK (dry run): commit 31a915aefb passes the preflight and compiles; nothing pushed`.
Only the report, the item node, and its single module were staged. The final delivery
command repeats these checks before pushing the reviewed packet for maintainer review.

## Second reading by NQ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
