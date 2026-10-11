## Worker report

The delivery adds `Sheaf.AlgebraicGeometry.DivisorModule`, whose entry point is
`AlgebraicGeometry.Scheme.Divisor.moduleOfSmoothConnectedCurve`. It reuses the five
existing divisor definitions in `WeilConjectures.AlgebraicGeometry.Curve.Divisor`;
none is copied. The node has a mixed lean record listing these existing declarations
alongside the new associated module and its section definition. No statement correction,
new definition node, or dependency replacement is needed.

Clause-by-clause correspondence:

- Algebraically closed field: `(k : Type u) [Field k] [IsAlgClosed k]`.
- Smooth connected curve over that field: `(C : Scheme.{u})
  (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]`. The recorded
  `IsConnectedCurve` extends the recorded `IsCurve`, including separatedness,
  finite type, dimension exactly one and nonempty connected underlying space.
- Finite sums of closed points with integer coefficients and their free abelian
  group: the existing `Scheme.Divisor C = closedPoints C →₀ ℤ`.
- Nonzero rational functions: the existing `Scheme.div C` has domain
  `Additive C.functionFieldˣ`. `C.functionField` is the generic stalk, exactly
  the integral-scheme clause of the recorded `def-sc-function-field` (not a
  replacement for its general component-product declaration).
- Principal divisor coefficients: the existing `Scheme.div` has coefficient
  `C.ord (f.toMul : C.functionField) P`. For the smooth connected curve's
  closed points this order is the normalized DVR order; regularity is supplied
  by `IsRegular.of_smooth` and the DVR input is the recorded
  `IsRegularLocalRing.isDiscreteValuationRing`.
- Finite support: the existing `Scheme.div` directly invokes the dependency
  `Scheme.finite_setOf_ord_ne_zero`. No additional finite-support datum is assumed.
- Class group: the existing `Scheme.principalDivisors C = (Scheme.div C).range`
  and `Scheme.DivisorClassGroup C = C.Divisor ⧸ C.principalDivisors`.
- Constant sheaf of the function field: `divisorConstantSheaf` uses the recorded
  `(CategoryTheory.constantSheaf (Opens.grothendieckTopology C) CommRingCat).obj
  C.functionField`. The section construction uses its ordinary topological
  model: locally constant functions `U → C.functionField`.
- Nonempty-open formula for O_C(D): `Divisor.sectionCondition` is local
  constancy together with, at every `x : U` whose singleton in C is closed,
  `s x = 0 ∨ 0 ≤ C.ord (s x) x.val + D ⟨x.val, hx⟩`.
  Every nonempty open of an integral scheme is irreducible, so every such
  locally constant function is a single rational function. Thus this is exactly
  the node's `{0} ∪ {f ≠ 0 | v_P(f) + n_P ≥ 0 for every closed P in U}`,
  without applying an order bound to the junk value for the zero function.
- Sub-O_C-module: `sectionModule` is an explicit `Submodule Γ(C,U)
  (U → C.functionField)` with precisely that carrier. `divisorScalarMap` takes
  a regular scalar's germ at each point followed by its map to the generic
  stalk. `restrictSection` is pointwise restriction along inclusions;
  `modulePresheaf` assembles these same modules and maps; `associatedModule`
  bundles that presheaf with its named sheaf-condition theorem. No module data
  is chosen from an existence theorem or hidden behind `sorry`.
- Empty open: there is only one function from the empty type to the function
  field. The conditions are vacuous, so its section submodule is the zero
  module, including with an empty covering family.
- Invertibility and identification with Pic: neither is asserted in this
  module, as the node explicitly leaves them to a separate theorem.
- Degree: the existing `Scheme.Divisor.degree` is
  `Finsupp.liftAddHom (fun _ ↦ AddMonoidHom.id ℤ)`, the sum of coefficients.
- Disconnected smooth curves: apply the same definitions to each connected
  component. The construction is general for regular integral Noetherian
  schemes, so it also applies to zero-dimensional components with the
  existing `ord = 0`; no one-dimensional component is silently discarded.
  The node requests componentwise application, rather than a further bundled
  gluing functor, and no additional definition of divisors is introduced.

The generic construction uses `IsIntegral`, `IsNoetherian`, and `IsRegular`
instances. The entry point has none of these as added hypotheses: it derives
Noetherianity by `isNoetherian_of_locallyOfFiniteType f`, connectedness by
`IsConnectedCurve.connectedSpace' f`, regularity by `IsRegular.of_smooth f`,
and integrality by `IsRegular.isIntegral C`. These are actual library terms.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FunctionField`: `Scheme.functionFieldOfComponents`
  was read; for the integral case we use its explicitly recorded existing
  Mathlib `Scheme.functionField` generic-stalk clause. The product model and
  single generic stalk are canonically isomorphic, not definitionally equal.
- `WeilConjectures.AlgebraicGeometry.Regular`: `IsRegular.of_smooth` and
  `IsRegular.isIntegral` (regularity/integrality of the smooth connected curve).
- `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`:
  `IsRegularLocalRing.isDiscreteValuationRing` (normalization of the order at
  closed points; imported transitively through Regular).
- `WeilConjectures.AlgebraicGeometry.Curve`: `IsCurve`, `IsConnectedCurve`,
  and `IsConnectedCurve.connectedSpace'`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `WeilConjectures.AlgebraicGeometry.Curve.Divisor`:
  `Scheme.finite_setOf_ord_ne_zero` and all five reused divisor definitions.

All nine outstanding proofs are named theorems in this module, with source,
node tag and complete natural-language argument in their docstrings:
`Divisor.sectionCondition_zero`, `Divisor.sectionCondition_add`,
`Divisor.sectionCondition_smul`, `Divisor.sectionCondition_restrict`,
`Divisor.restrictSection_add`, `Divisor.restrictSection_smul`,
`Divisor.restrictSection_id`, `Divisor.restrictSection_comp`, and
`Divisor.modulePresheaf_isSheaf`. Each supplies a proof field for explicit
section/restriction data and belongs to this definition node. Their proofs
are all `sorry`; no theorem is proved at stage 2.

Edge cases checked: D=0 gives regular rational functions on the smooth curve;
the zero rational function is included independently of D; 1 satisfies the
bound exactly when the relevant coefficients are nonnegative; positive D
allows poles of bounded order, negative D forces zeros; empty opens have one
section; opens avoiding the support impose ordinary regularity at all their
closed points; disconnected curves are handled per component; no properness
is required and no field characteristic is excluded. Universes and variables
are explicitly bound; `autoImplicit` is disabled in the file.

Searches (the remote tools recorded their actual results in searches.jsonl):

- LeanSearch, `divisor associated sheaf of rational functions with orders bounded
  below`: unavailable, Internal Server Error (no mathematical verdict).
- LeanFinder, `divisor associated invertible sheaf on smooth curve sections
  rational functions valuation`: eight hits on elliptic-curve fractional ideals,
  rational-function valuations and the generic-stalk field instance; none
  defines the scheme module O_C(D).
- Loogle, `"Divisor"`: twelve substring hits on zero-divisors and unrelated
  arithmetic; none is a scheme divisor module.
- msearch grep, `divisor|divisorial`, AlgebraicGeometry: twenty-five hits,
  principally zero-divisors and elliptic-curve material; none is O_C(D).
- Source `rg` for `divisorModule|divisorSheaf|ofDivisor|divisor.*Module|
  ord.*Submodule|associated.*divisor|divisorial`, and node-id search:
  five existing definitions in Curve/Divisor.lean; Curve/Picard.lean explicitly
  says the associated subsheaf construction is missing. No exact full match.
- The same concept/name searches in `lean/Sheaf` and the upstream-name index:
  meromorphic modules and associated modules of a general module exist, but
  not the valuation-bounded subsheaf. All new full names were checked for
  collisions. The actual integral function-field and constant-sheaf signatures
  and docstrings were read in the pinned Mathlib checkout.

Source note: the blueprint markdown is absent in this machine's literature
checkout, as already reported by stage 1. The current DAG statement, the prior
stage-1 report and the full source divisor definitions were read. The blueprint markdown was successfully read over SSH on the server. It
gives the same sums, quotient, valuation-bounded submodule and degree, and
explicitly leaves invertibility to a separate theorem; its broader introductory
wording was already corrected by stage 1. No further change to the node
statement was made.

Validation: clean server single-file compilation, including the exact
smooth-connected-curve entry point and ambient constant-sheaf definition.
The final deliver2 dry run performs the preflight and repeats that compile;
its second-reading section is deliberately reserved for the independent reader.


## Second reading by E1

I independently opened the delivered node, its whole Lean module, all six statement
dependency nodes, their recorded declarations, Mathlib's function-field and order
declarations, and the source blueprint markdown on the server. The source is the
blueprint file named by the node, not a Stacks definition of the whole construction.
Its valuation formula requires smoothness; the stage-1 node already makes this explicit
and treats zero and empty opens correctly. This delivery makes no statement correction.
There are no new nodes or dependency modules to review.

Object/hypothesis/clause inventory and correspondence (all mathematical verdicts: pass):

1. Algebraically closed field k: `k : Type u`, `[Field k]`, `[IsAlgClosed k]`
   in `Divisor.moduleOfSmoothConnectedCurve`. There is no characteristic restriction.
2. Smooth connected curve C over k: `C : Scheme.{u}`, `f : C ⟶ Spec (.of k)`,
   `[IsConnectedCurve f]`, `[Smooth f]`. I read `IsCurve` and `IsConnectedCurve`:
   these include separatedness, finite type, nonempty connected space, and dimension
   exactly one, exactly the dependency node's connected-curve notion. No properness
   is assumed. The explicit f is accepted for this recorded curve declaration.
3. Finite integer sums of closed points and their free abelian group:
   existing `Scheme.Divisor` is `closedPoints C →₀ ℤ`; the closed-point subtype
   and finitely supported integer functions give exactly these objects.
4. Function field and its nonzero elements: existing `Scheme.functionField` is
   the generic stalk. I read `functionFieldOfComponents` and its node: the integral
   case expressly uses this generic stalk. Regularity plus connectedness makes C
   integral. `Additive C.functionFieldˣ` in existing `Scheme.div` is exactly the
   multiplicative group of nonzero field elements, with additive group notation.
5. Normalized orders and principal divisor: `Scheme.div` evaluates at each closed
   P to `C.ord (f.toMul : C.functionField) P`. `ordHom` uses `Ring.ordFrac`
   of the stalk, the length order, which on a DVR is its normalized valuation.
   The recorded regularity theorem is `IsRegular.of_smooth`; the recorded DVR
   theorem is `IsRegularLocalRing.isDiscreteValuationRing R (h : ringKrullDim R = 1)`.
   Closed points of the smooth integral one-dimensional finite-type curve have
   codimension one, so the non-codimension-one junk branch is not used there.
6. Finite support: the body of `Scheme.div` supplies it with the recorded
   `finite_setOf_ord_ne_zero f.toMul.ne_zero`; it is not a new hypothesis.
7. Class group: existing `principalDivisors C` is the range of `div C`, and
   `DivisorClassGroup C` is `C.Divisor ⧸ C.principalDivisors`.
8. Ambient constant sheaf: `divisorConstantSheaf` uses the recorded
   `CategoryTheory.constantSheaf`, whose body is the sheafification of the constant
   presheaf. Locally constant functions are its usual topological section model.
   The constructed module uses that section model, not arbitrary functions:
   `sectionCondition` explicitly requires `IsLocallyConstant s`.
9. For every nonempty open U, the section formula: `sectionCondition` further
   requires for each `x : U` and `hx : IsClosed ({x.val} : Set C)` that
   `s x = 0 ∨ 0 ≤ C.ord (s x) x.val + D ⟨x.val, hx⟩`.
   Every nonempty open of integral C is irreducible, so a locally constant s is
   a single rational function. The formula is therefore precisely zero together
   with the nonzero functions satisfying every closed-point bound in U. Closedness
   is in C, as the coefficients of D require, not a different subtype of points.
10. Sub-O_C-module, restrictions, and sheaf: `sectionModule` has exactly this
    carrier as a `Submodule Γ(C,U) (U → C.functionField)`. `divisorScalarMap`
    sends regular sections through their germ and the canonical generic-stalk map;
    I read `algebraMap_germ_eq_germToFunctionField`, which identifies this with
    the same rational scalar at every point. `restrictSection` precomposes the
    inclusion. `modulePresheaf` and `associatedModule` retain these explicit data.
    Only named proof theorems are postponed, not any underlying module data.
11. Empty open: its function type is a singleton and both conditions are vacuous,
    giving exactly the zero section module; the empty cover glues uniquely.
12. Invertibility and Cl-to-Pic identification: no such theorem or hypothesis is
    asserted here, as the node expressly reserves them for a separate theorem.
13. Degree: existing `Divisor.degree` is `Finsupp.liftAddHom` of the identity on
    integers; I read `degree_apply`, identifying it with the coefficient sum.
14. Disconnected smooth curves: the node specifies componentwise use rather than
    a new bundled global construction. The generic `associatedModule` accepts
    each regular integral Noetherian component, including dimension zero. The
    existing divisor, quotient and degree definitions apply on each component.
    Smooth finite-type components are disjoint open and closed; on zero-dimensional
    components the existing order is zero. This clause imposes no connected-curve
    hypothesis on those zero-dimensional components.

Edge cases: zero divisors and the empty support are permitted by Finsupp. The zero
rational function is admitted even for negative coefficients (the explicit disjunct
avoids `ord 0`'s junk value). Positive coefficients allow poles and negative coefficients
force zeros, with the source's sign. D=0 imposes ordinary regularity on the smooth curve.
Opens missing the support still impose order >= 0 at their closed points. Empty opens
and empty covering families have one section. The empty scheme is excluded by the
connected-curve hypothesis exactly where the node excludes it; its componentwise
clause has no components to construct. There is no natural-number parameter or n=0
exception. Universe u is arbitrary and all binders are explicit with autoImplicit false;
a common universe for k and C follows the recorded Scheme API and can be enlarged.

Independent H4 searches, using different concept words from the worker:

- LeanFinder via msearch: `Riemann Roch space sections sheaf bounded poles effective
  divisor on a scheme`: eight hits, on localization of sections and
  `ModuleCat.Tilde.sectionsSubmodule`; none defines these divisor bounds.
- Loogle via msearch: `"divisor"`: twelve substring hits on zero-divisors and
  bit-vector division, no associated scheme module.
- Mathlib grep via msearch: `bounded.?pole|divisorial|riemann.?roch|divisor.*[Ss]heaf|
  [Ss]heaf.*divisor` in AlgebraicGeometry: zero hits.
- Direct rg of Mathlib AlgebraicGeometry, source WeilConjectures, and lean/Sheaf
  for Riemann-Roch, bounded poles, divisorial, divisorSheaf, divisorModule and
  ofDivisor: source Riemann-Roch/Picard constructions and project determinant
  modules, no valuation-bounded module. I opened Curve/Picard.lean: it explicitly
  says the subsheaf construction is missing, and its `Divisor.toPic` uses ideal
  sheaf dual classes instead. It cannot replace O_C(D)'s section definition.
- Direct rg of the upstream name index and project Lean for the node and new
  entry point, associated-module and section-condition names: no collision.
  Existing Divisor.lean's five definitions were read and reused, not duplicated.

Mismatches/changes: the mathematics and recorded entry-point signature need no repair.
The module header omitted the required main-definitions list for a module with several
declarations; I added that list only. No Lean declaration, node statement, dependency,
or proof was changed. All nine postponed theorems have source-tagged docstrings and
natural-language proofs; every theorem body is sorry. Def/instance data and structural
proof fields are explicit or use these named theorems. The namespace, imports, line
widths and explicitly bound variables were checked. The record's `lean.statement`
 reproduces the entry-point signature verbatim from `def` through its return type.

Validation: the unchanged definitions compiled cleanly on the server during this reading.
The final header-only revision is compiled again by the delivery dry run and delivery;
there are no sibling imports. The delivery dry run must pass before pushing.
