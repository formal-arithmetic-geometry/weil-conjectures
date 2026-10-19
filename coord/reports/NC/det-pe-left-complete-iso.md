## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleLeftComplete` states
`AlgebraicGeometry.Scheme.ProEt.left_complete_quasiIso`. It says exactly that
for every complex of modules over an arbitrary ring sheaf on the small
pro-etale site, the specified canonical comparison to the shifted-cone limit
of the canonical lower truncations is a quasi-isomorphism. The node's text,
statement dependencies, proof and other fields are unchanged; only `lean` is
set in its sandbox copy.

The previously missing dependency `det-pe-milnor-sequence` has now landed as
`Sheaf.AlgebraicGeometry.ProEtaleMilnorSequence`, with primary declaration
`AlgebraicGeometry.Scheme.ProEt.milnor_sequence`. Its complete signature and
all its helper definitions were read. Thus the previous missing-dependency
report is resolved, without stating any other DAG node in this delivery.

Hypotheses and clauses, one by one:

- The scheme X and its small pro-etale site are `X : Scheme.{t}` and
  `topology X`, Mathlib's topology on `X.ProEt`. No quasi-compactness,
  quasi-separatedness, noetherianity, nonemptiness or smoothness assumption
  is imposed.
- The coefficient sheaf is `R : Sheaf (topology X) RingCat.{max u (t + 1)}`.
  It is an arbitrary sheaf of rings, including noncommutative rings; no
  constant-coefficient or commutativity restriction is introduced. The
  coefficient/module universe is at least t+1, as in the landed Milnor
  module. The small site's object and morphism universes remain different.
- Every unbounded complex K of R-modules is quantified by
  `K : CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ`.
  `ringedSiteModules` is the dependency's transparent abbreviation for
  Mathlib's `SheafOfModules`, not a new module category.
- The n-th canonical truncation is the existing `K.truncGE (-(n : ℤ))`;
  the quotient carrying k to its image is the existing
  `K.πTruncGE (-(n : ℤ))`. The indexing is all natural numbers, including 0.
- `postnikovStep K n` constructs the canonical transition. Apply truncGE at
  a=-(n+1) to `K.πTruncGE b`, b=-n, then invert the quotient of the already
  a-supported complex `K.truncGE b`. Naturality gives
  `K.πTruncGE a ≫ postnikovStep K n = K.πTruncGE b`.
  The inverse is of an actual canonical isomorphism; it chooses no arbitrary
  transition or cone lift. `postnikovTower` packages these successive maps
  with Mathlib's `Functor.ofOpSequence`, whose successor-map formula was read.
- The product and 1-T are the same as in the landed Milnor dependency:
  `towerTransitionEndomorphism` is identity minus `towerProductShift`, with
  n-th component pr_n minus pr_(n+1) followed by the transition. The target
  `WeilConjectures.integralOperationsRoos (postnikovTower K)` unfolds to
  `CochainComplex.mappingCocone` of this map, hence Cone(1-T)[-1].
- The source's specified iota, k |-> ((bar k_n),0), is the real definition
  `postnikovComparison K`. It is `mappingCocone.lift` applied to the product
  lift of the quotient maps and the literal zero degree-minus-one cochain.
  Mathlib's `lift_fst` and `lift_f_snd_v` show that these are exactly its two
  coordinates. Both definitions and the projection formulas were read.
  Under the source's identification (b,a) |-> (a,-b), the second coordinate
  remains zero. This is the specified chain map, not any compatible lift.
- The conclusion is `QuasiIso (postnikovComparison K)`, the dependency's
  usual cohomology-isomorphism criterion for every integer degree. It is a
  statement about the chain map itself, with no derived-category replacement
  or boundedness assumption.

Dependency declarations used:

- `sk-def-pe-site`: Mathlib `AlgebraicGeometry.Scheme.ProEt` and
  `AlgebraicGeometry.Scheme.ProEt.topology`, in
  `Mathlib.AlgebraicGeometry.Sites.Proetale` (public through the Milnor module).
- `def-weil-sheaf-of-modules-category`: `CategoryTheory.ringedSiteModules`,
  `Sheaf.CategoryTheory.RingedSiteModules` (public through the Milnor module).
  Its full declaration and underlying Mathlib definition were read.
- `def-weil-abstract-derived-category`: `DerivedCategory`,
  `HasDerivedCategory`, and `HomologicalComplex.QuasiIso`, via
  `Mathlib.Algebra.Homology.DerivedCategory.Basic` in the public import closure.
  This theorem only needs the complex and quasi-isomorphism portions of that
  composite definition, so it adds no localization-choice binder.
- `def-kun-truncations`: public import
  `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`. Its documentation
  explicitly reuses `CochainComplex.truncGE` and `πTruncGE` from Mathlib;
  these are used directly, with no private copy. The module's new homotopy
  colimit predicate is not relevant to this clause of the composite node.
- `det-pe-milnor-sequence`: public import
  `Sheaf.AlgebraicGeometry.ProEtaleMilnorSequence`, with the already existing
  strict construction `WeilConjectures.integralOperationsRoos` from
  `Sheaf.Paper.IntegralOperationsWellDefined`. Its target, signs and transitions
  are reused exactly, not reconstructed.
- Stated proof prerequisite `det-pe-products-derived` is imported without
  `public` as `Sheaf.AlgebraicGeometry.ProEtaleProductsDerived`.
  The proof prerequisites `lem-sf-derived-homology-long-exact` and
  `det-pe-left-complete-truncation-tower` currently have no Lean record and
  are therefore not imported or restated; the maintainer can add their proof
  imports after they land. They are not statement prerequisites of this item.

The same-node helpers implement the canonical map that this node explicitly
mentions. They introduce no independent mathematical notion and state no
other DAG node. There are two postponed proofs, both tagged with the item's
blueprint id and supplied with full source-based proof docstrings:
`postnikovComparison_condition` is exactly the first proof paragraph's
assertion that (quotient family,0) is a map of complexes; the primary theorem
is the quasi-isomorphism assertion, with all three recorded DAG proof steps
in its docstring. The condition is a named proof used by the definition;
all definition data are actual Mathlib constructions, never sorry or a
choice from undetermined existence.

Edge cases checked mathematically before writing:

- K=0 and R=0: all quotient-family maps have zero coordinates and the
  statement is the expected quasi-isomorphism of zero complexes.
- The empty scheme is allowed and imposes no extra binder.
- n=0 is truncation at degree 0; its incoming transition is from cutoff -1.
  The proof of a<=b is the ordinary successor inequality and has no
  positivity restriction or off-by-one omission.
- For q<0 the cohomology tower is zero until n>=-q, then has the cohomology
  of K. For q=0 and q>0 the relevant cohomology already stabilizes at n=0.
  These cover the transition across the boundary and every cohomological
  degree, including unbounded K.
- Bounded-below and degree-zero complexes remain included. No assumption
  that any individual quotient K->tau_(>=-n)K is a quasi-isomorphism is made.
- The helper chain-map condition holds in every abelian category with
  countable products, even without exact products; exactness is used only
  for convergence on the pro-etale site.

Searches (2026-10-16, using the prescribed msearch.py wrapper):

- LeanFinder query: "For every complex of module sheaves on the pro-etale
  site the canonical map to the derived inverse limit of its good lower
  truncations is a quasi-isomorphism". Eight hits: individual truncation
  quasi-isomorphism criteria and a representation resolution. No exact
  inverse-limit convergence theorem.
- Loogle query: `"CochainComplex", "truncGE"`. Twelve hits, including
  `truncGE`, `πTruncGE`, `truncGEMap`, boundary-object isomorphisms and
  individual-truncation quasi-isomorphism criteria. None is this theorem.
  Their source signatures were inspected, including `isStrictlyGE_of_ge`.
- Mathlib grep query: `left.?complete|Postnikov|homotopy.?limit`, restricted
  to the existing `Algebra/Homology` directory. Zero hits.
- LeanSearch query: "A complex of sheaves of modules on the pro-etale site
  is quasi-isomorphic to the derived inverse limit of its canonical lower
  truncations". Eight hits: finite-truncation criteria, module-sheaf limits,
  and a profinite limit isomorphism. No exact convergence theorem.
- Direct rg of the upstream WeilConjectures source for
  `left.?complete|Postnikov|homotopy.?limit` found general homotopy-limit and
  adic completeness APIs, not Postnikov convergence; the required
  `grep -rn 'det-pe-left-complete-iso'` found nothing.
- Direct rg of `lean/Sheaf` for `postnikov|Postnikov|leftComplete|left_complete`
  found no existing declaration. Broader truncation/limit searches found
  ringed-site or ringed-space theorems with local cohomological-bound
  hypotheses or conclusions only about triangles in a derived category.
  They do not state this strict canonical chain-map theorem.
- Exact-name rg over Mathlib, upstream WeilConjectures, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` found no occurrences of the five new names.

Validation: `scompile.py NC det-pe-left-complete-iso` compiled the module
separately in both sandbox and library context, with exit 0 and no warnings
(the compiler suppresses expected sorry warnings). The initial elaboration
issue in `Functor.ofOpSequence` was repaired by explicitly specifying its
object family. No other delivery file requires compilation.

No STATEMENT-DISPUTED issue, statement correction, new node or dependency
module is needed. Only the authorized sandbox was written; source trees
were read and the prescribed wrappers handled compilation and delivery
bookkeeping.

## Second reading by NC

Independent second reading, 2026-10-17. I read the node and its three proof steps,
the blueprint statement, proof and unit `_section.md`, and Stacks
`sites-cohomology.tex`, Tag 0947 (`proposition-enough-weakly-contractibles`),
including its hypotheses and the proofs of (2), (4)--(7). Stacks assumes a basis
of weakly contractible objects on a general site. Here the site is specifically
the small pro-etale site, where the product-exactness prerequisites supply that
consequence; it introduces no extra geometric assumption on X. No repair note
exists for this item. The sandbox node differs from the shared node only in
`lean`; there is no statement correction, new node or dependency module.

My inventory of the mathematical statement and its exact Lean rendering is:

1. Arbitrary scheme X and its small pro-etale site: `X : Scheme.{t}` and
   `topology X`. I opened Mathlib's `Scheme.ProEt` (weakly etale schemes over X)
   and its topology. These are the recorded `sk-def-pe-site` objects. Verdict:
   same site; no qcqs, separatedness, nonemptiness or noetherianity assumption.
2. Arbitrary sheaf of rings R: `R : Sheaf (topology X)
   RingCat.{max u (t + 1)}`. Neither commutativity nor constant coefficients is
   assumed. Verdict: exact coefficient object in the site's size convention.
3. Every unbounded cochain complex of left R-modules:
   `K : CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ`.
   I read `ringedSiteModules` in `Sheaf.CategoryTheory.RingedSiteModules` and
   Mathlib's underlying `SheafOfModules` structure and morphisms. It is a
   transparent abbreviation for the recorded module-sheaf category, with its
   actual Mathlib abelian instance. Verdict: exact category and quantification;
   no bound, resolution, derived-category choice or extra instance is assumed.
4. The natural-number tower of good lower truncations:
   `postnikovTower K` has objects `K.truncGE (-(n : ℤ))`. I read the composite
   `def-kun-truncations` node and its module, and Mathlib's `truncGE`,
   `πTruncGE`, `truncGEMap`, `πTruncGE_naturality`, and strict-support API.
   `postnikovStep K n` applies the truncation functor at a=-(n+1) to the
   quotient at b=-n, then inverts the further quotient of the b-truncated
   complex. Since a<=b, that further quotient is an actual isomorphism.
   Naturality gives `π_a ≫ postnikovStep K n = π_b`. This characterizes the
   canonical transition (the quotient is epic), without an arbitrary choice.
   I read `Functor.ofOpSequence` and its successor-map formula; its transitions
   are exactly these steps. Verdict: correct truncations, direction and cutoff.
5. Product P, endomorphism 1-T, and Cone(1-T)[-1]:
   `WeilConjectures.integralOperationsRoos (postnikovTower K)` reuses the
   landed Milnor module's construction. I read its complete signature and
   helpers, and the definitions `integralOperationsTowerStep`,
   `integralOperationsRoos`, `towerProductShift`, and
   `towerTransitionEndomorphism`. The last two live in the shared side clone's
   `lean/WeilConjectures/CategoryTheory/Limits/TowerTransitionEndomorphism.lean`:
   their nth projections are pr_(n+1) followed by t_n, and pr_n minus that.
   Mathlib's `mappingCocone` is literally `(mappingCone φ)⟦(-1 : ℤ)⟧`.
   Verdict: same strict shifted cone and termwise product as the node.
6. The specified map iota, with coordinates (quotient family,0):
   `postnikovComparison K` uses `mappingCocone.lift` with
   `Pi.lift (fun n ↦ K.πTruncGE (-(n : ℤ)))` and the literal zero cochain.
   I read `lift`, `lift_fst`, and `lift_f_snd_v`: the first projection is
   exactly the quotient family and the second coordinate is zero. Thus this
   is the node's prescribed map, not merely a compatible existential lift.
   The signs in Mathlib's shifted cone only change the sign of coordinates;
   the quotient-family/zero map has exactly the source's (x,y) coordinates
   under its specified identification. `postnikovComparison_condition` is
   precisely the chain-map condition for these data, a named theorem with
   the elementary proof paragraph in its docstring. Verdict: correct map.
7. Conclusion for that map in every degree: `QuasiIso (postnikovComparison K)`.
   I opened Mathlib's `HomologicalComplex.QuasiIso` and its homology-map
   criterion, as used by `def-weil-abstract-derived-category`. Verdict:
   exactly quasi-isomorphism of this chain map, with all integer degrees
   and the quantifier order X, R, K; neither weaker nor stronger.

Edge cases: the fixed tower index is ℕ, so no arbitrary empty-index family is
introduced or excluded. At n=0 the cutoff is 0 and the successor transition
comes from cutoff -1; `Nat.le_succ 0` applies. For q<0 the boundary n=-q is
included; for q>=0 cohomology already stabilizes from n=0. Zero complexes,
the zero ring sheaf, the empty scheme, degree-zero complexes and complexes
unbounded in both directions are all allowed. There is no characteristic,
field or finiteness restriction. Site objects live in universe t+1 and
morphisms in t; these are not equated. The free u permits coefficients and
modules in any containing universe `max u (t+1)`, exactly as the landed
Milnor dependency; no hidden lower coefficient universe is assumed. Every
variable and universe used in signatures is explicitly bound. The helper
constructions are polymorphic in both object and morphism universes of the
abelian category, with no equality between them.

Independent searches, using terms different from the first reader:

- LeanFinder through msearch.py: "In an abelian category with exact countable
  products the map from a complex to the mapping fibre of one minus shift on
  its lower canonical truncations is a quasi-isomorphism". Eight hits were
  finite truncation or ordinary homology-sequence results, including
  `HomologicalComplex.quasiIsoAt_πTruncGE`; none states convergence.
- Loogle through msearch.py: `"truncGE", "limit"`. One hit,
  `HomologicalComplex.truncGE'.isLimitKernelFork`; I checked the result's
  signature, which constructs a boundary kernel fork, not an inverse limit.
- LeanSearch through msearch.py: "Every complex of sheaves on a site with
  exact products is quasi-isomorphic to the mapping fibre of one minus shift
  on the product of its connective truncations". Eight hits concerned
  mapping cones, shifts, truncation and composition of quasi-isomorphisms;
  none is this theorem.
- Direct rg in Mathlib's `Algebra/Homology`, upstream `WeilConjectures`, and
  shared `lean/Sheaf` for `left.?complet|postnikov|quasiIso.*(lim|roos)` and
  quasi-isomorphism/inverse-limit and truncGE/limit patterns found no match.
  I opened the nearby
  `HomologicalComplex.quasiIsoAt_π_of_isLimit_of_isEventuallyConstantTo`:
  it concerns projections from an ordinary limit, with eventual constancy
  in three degrees, not the canonical map into the shifted cone.
- I also opened `CategoryTheory.site_truncation_isDerivedLimitTriangle`,
  `RingedSpace.pointwise_truncation_limit_exists`, and
  `CategoryTheory.isZero_firstDerivedLimit_of_eventually_isIso`. Their
  signatures concern respectively a derived-category triangle with a local
  bound and commutative coefficients, an existential derived-category lift,
  and derived limits of abelian-group towers. None gives this strict map
  theorem or these canonical chain-level helper constructions. The existing
  lower-truncation kernel module accepts a transition as an argument rather
  than constructing it. No duplicate definition needs dropping.
- Exact-name rg for all five new declaration names in Mathlib, upstream,
  `lean/Sheaf`, and `dag/lean_names_upstream.json` found no collision.

Mismatch found and repaired: the worker report treated
`lem-sf-derived-homology-long-exact` as unavailable because it lacks `lean`,
but its `mathlib_match` already supplies `DerivedCategory.HomologySequence`
in `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`. I read
`δ`, `exact₁`, `exact₂`, and `exact₃` and added that module as a non-public
proof import, as required by stage 2 rule 7. This supersedes the worker
report's assertion that this proof prerequisite is not imported. The
truncation-tower proof prerequisite still has neither a Lean record nor a
Mathlib match, and does not need an import to state this item. There is no
mathematical mismatch requiring a definition, node or signature change.

Both theorem proofs remain exactly `sorry`. All three definitions contain
real construction data; only the named chain-map-condition proof is postponed.
The main theorem docstring carries all three DAG proof steps, including the
projection-compatible cone calculation and both uses of truncation-tower
stabilization. Every declaration is listed in `lean.declarations`, has its
source and blueprint docstring, and no line exceeds 100 characters. I checked
that `lean.statement` is verbatim equal to the main signature in the file.

Second-reader validation: the final module, including the added proof import,
passed `scompile.py NC det-pe-left-complete-iso
lean/Sheaf/AlgebraicGeometry/ProEtaleLeftComplete.lean` in both sandbox and
library contexts (3.2 s and 3.0 s), with exit 0 and no diagnostics. Every
supplied Lean file has been compiled individually through the prescribed
wrapper under its default 60-second limit.
