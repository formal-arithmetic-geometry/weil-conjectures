## Worker report

The module `lean/Sheaf/AlgebraicGeometry/RationalSectionOrder.lean` states
`AlgebraicGeometry.Scheme.Modules.rational_section_order`, with its proof `sorry`.
It states both clauses of the node, without defining an order, choosing generators,
or introducing a new notion. The node changes only in `lean`.

Hypotheses and objects, matched individually:

- Algebraically closed field k: `(k : Type u) [Field k] [IsAlgClosed k]`.
- Smooth connected curve C over k: `(C : Scheme.{u})` and its structural morphism
  `(f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]`. The recorded class
  `IsConnectedCurve` includes nonemptiness, connectedness, dimension exactly one,
  separatedness and finite type. Properness is not assumed.
- Noetherian integral scheme: `hC` is chosen from
  `C.smooth_connected_curve_local_rings k f`; `letI := hC` enables the integral-scheme
  definitions. The theorem's `choose_spec`, bound as `h`, supplies Noetherianity and
  all the other local-ring facts. These are consequences, not added assumptions.
- Generic point eta: `let η := genericPoint C`. Function field: `C.functionField`,
  the existing integral-scheme generic stalk, with Mathlib's field instance. This is
  the integral clause of `def-sc-function-field`, not a private product-field definition.
- Closed point P: `{P : C // P ∈ closedPoints C}` in clause 1; membership in
  `closedPoints C` is included in the set of clause 2.
- Normalized valuation v_P: `v P` is chosen from the final clause of the recorded
  local-rings theorem, projected by `h.2.2.2.2.2.2.2.2 P.val P.property` and then `.2.2`.
  That clause asserts the DVR and fraction-field facts and existence of a surjective
  homomorphism `C.functionFieldˣ →* Multiplicative ℤ` characterized by the integer
  exponent in unit-times-uniformizer factorization. `Multiplicative.toAdd` returns
  its integer order. These characterizations uniquely determine the normalized valuation,
  so this choice does not restrict which normalized valuation the node means.
- Invertible module: `(L : C.Modules) [L.IsInvertible]`, using the dependency's class.
- Local stalk L_x and generic stalk L_eta: `TopCat.Presheaf.stalk L.val.presheaf x`
  and the same expression at eta, with Mathlib's module instances.
- Germ map lambda_x: `lam x` is `TopCat.Presheaf.stalkSpecializes L.val.presheaf`
  for the specialization from the generic point to x, exactly the map used in
  `invertible_module_generic_stalk`. Its germ compatibility gives the map in the node.
- Nonzero rational section: `∀ (s : ↑(TopCat.Presheaf.stalk L.val.presheaf η)), s ≠ 0 →`.

Conclusions, matched individually:

1. For every closed P and generators e,e': the first universally quantified clause
   uses the closed-point subtype, stalk elements `e e'`, and the two hypotheses
   `Submodule.span (C.presheaf.stalk P.val) {e} = ⊤` and the corresponding formula for e'.
   This is precisely generation by one element. The same rendering is used in the
   recorded generic-stalk theorem.
2. The nonzero coefficients g,g' are `C.functionFieldˣ`. The equations
   `s = (g : C.functionField) • lam P.val e` and its primed version render both
   representations. The conclusion is equality of their integer valuations.
3. The second conjunct is `Set.Finite` of the set of closed P admitting a generator
   e and a unit coefficient g representing s with nonzero integer valuation.
   The generic-stalk theorem gives existence and uniqueness of this coefficient for
   each generator; clause 1 makes nonzero order independent of the generator.
   Thus existential quantification defines exactly the support in the node, without
   choosing a family of generators or silently excluding a point with no representation.

Dependency declarations read and used (including full signatures and docstrings):

- `WeilConjectures.AlgebraicGeometry.Curve`: `AlgebraicGeometry.IsCurve` and
  `AlgebraicGeometry.IsConnectedCurve` (via the local-rings module).
- `Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings`:
  `AlgebraicGeometry.Scheme.smooth_connected_curve_local_rings`, used explicitly
  to obtain integrality and normalized valuations.
- `Sheaf.AlgebraicGeometry.FunctionField`: the record explains its integral clause
  reuses `AlgebraicGeometry.Scheme.functionField` from
  `Mathlib.AlgebraicGeometry.FunctionField`; that abbreviation and its field and
  stalk-algebra instances were read. Imported transitively through the local-rings module.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, imported through the generic-stalk module.
- `Mathlib.Algebra.Category.ModuleCat.Stalk`: the stalk-module instances and
  `PresheafOfModules.germ_ringCat_smul`; `Mathlib.Topology.Sheaves.Stalks`:
  `TopCat.Presheaf.stalk`, `stalkSpecializes`, and `germ_stalkSpecializes`.
- `Sheaf.AlgebraicGeometry.InvertibleModuleGenericStalk`:
  `AlgebraicGeometry.Scheme.Modules.invertible_module_generic_stalk`. Its stalk,
  generator, generic field and lambda expressions are reused exactly. Its conclusions
  justify the existential-support rendering; no additional freeness assumptions occur.

Edge cases checked before writing: empty schemes and zero-dimensional points are
excluded by the node's connected-curve hypothesis, not by additional binders; s=0
is explicitly excluded; a nowhere vanishing section has empty (therefore finite)
support; negative orders (poles) are included because the codomain is ℤ, not ℕ;
nonproper curves and every characteristic are included; no finiteness of all closed
points or choice of global trivialization is assumed. Universes are explicitly bound.
Local generators cannot be zero because the local stalk is free rank one over a
nonzero local ring. The generic point is not inadvertently counted as a closed point.

Searches made:

- `msearch.py ... leansearch "A nonzero rational section of a line bundle on a smooth
  curve has finite support of orders of vanishing"`: unavailable, Internal Server Error.
- `msearch.py ... leanfinder "A rational section of an invertible sheaf on a smooth
  integral curve has finitely many nonzero orders and order is independent of the local
  generator"`: eight hits, including the function-field field instance, affine germs,
  and `Ring.ordFrac_eq_div`; no rational-section/order-independence/finite-support theorem.
- `msearch.py ... loogle "IsDiscreteValuationRing, valuation"`: zero hits, unknown
  identifier `valuation`.
- `msearch.py ... grep "rationalSection|rational.section|divisor" AlgebraicGeometry`:
  25 hits concerning zero divisors and elliptic-curve division polynomials; no match.
- `rg` on the source `WeilConjectures` and `lean/Sheaf` for rational-section and
  section-order names, and the item id: only surrounding Picard/Riemann-Roch docstrings;
  they explicitly describe rational sections as unavailable there. No duplicate statement.
- `rg rational_section_order` across Mathlib, the source, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no existing declaration of this name.

Source checked: the local Stacks TeX is absent on this machine, so the source places
were opened directly at [Section 02SE](https://stacks.math.columbia.edu/tag/02SE) and
[Lemma 02SG](https://stacks.math.columbia.edu/tag/02SG). The former supplies comparison
by a local unit; the latter supplies a generating open and containment of support
in its complement. The curve specialization in the DAG supplies global finiteness.
No statement correction, disputed statement, new nodes or dependency repairs are needed.

Validation: `scompile.py F1 lem-sc-rational-section-order` compiled the module on the
server in 2.1 seconds with exit code 0 and no warnings. Delivery dry run follows;
the independent second reading is reserved for the next worker.

## Second reading by F1

I independently read the node copy, RationalSectionOrder.lean, all six statement
 dependency nodes and the declarations they record. I also read the Stacks TeX at
`section-c1`, the paragraph before `definition-order-vanishing-meromorphic`, and
`lemma-divisor-meromorphic-locally-finite` with its proof. Since literature contains
no local Stacks checkout, I fetched the upstream `divisors.tex` into the sandbox's
scratchpad and checked it against [02SE](https://stacks.math.columbia.edu/tag/02SE)
and [02SG](https://stacks.math.columbia.edu/tag/02SG). The source assumes locally
Noetherian integrality; the node specializes this to a smooth connected finite-type
curve and obtains global finiteness. Both specializations are valid.

My inventory and correspondence, in the node's order:

1. An algebraically closed field k: `(k : Type u) [Field k] [IsAlgClosed k]`.
   Exact, including arbitrary characteristic.
2. A smooth connected curve C over k: `(C : Scheme.{u})`, its structure morphism
   `f : C ⟶ Spec (.of k)`, `[IsConnectedCurve f] [Smooth f]`. I opened Curve.lean:
   IsConnectedCurve extends IsCurve (separated, locally finite type, quasi-compact,
   dimension at most one), adding connected nonemptiness and dimension exactly one.
   Exact; there is no properness hypothesis.
3. Consequent Noetherian integrality, generic point and function field: `hC` is
   `Classical.choose (C.smooth_connected_curve_local_rings k f)`, registered by
   `letI := hC`; `h` is its choose_spec; `η := genericPoint C`; `C.functionField`
   is Mathlib's generic structure-sheaf stalk. The function-field dependency explicitly
   reuses that declaration in its integral-scheme clause. Exact; no extra instance
   is demanded of the caller, and no product-field copy is introduced.
4. Closed P and its normalized integer valuation: the subtype
   `{P : C // P ∈ closedPoints C}` and `v P`, chosen from
   `((h.2.2.2.2.2.2.2.2 P.val P.property).2.2)`. I counted the conjunction projections:
   eight `.2` select the closed-stalk clause, and two more select the valuation witness.
   Its signature characterizes the value as the unique unit-times-uniformizer exponent
   for every uniformizer. Thus the choice is exactly the normalized valuation, not an
   arbitrary surjective homomorphism. `Multiplicative.toAdd` renders its integer value.
5. An invertible O_C-module L: `(L : C.Modules) [L.IsInvertible]` uses the recorded
   Scheme.Modules class. I read its local unit-isomorphism field; it is local freeness
   of rank one, which also entails quasi-coherence. Exact, with no global triviality.
6. Local and generic stalks and their germ map: `TopCat.Presheaf.stalk L.val.presheaf`
   at x and η; `lam x` uses the generic-point specialization. I read
   `stalkSpecializes` and `germ_stalkSpecializes`: its direction is L_x to L_eta,
   and it sends a local germ to the same section's generic germ. The module-stalk
   instance and `germ_ringCat_smul` supply exactly the prescribed scalar action.
7. A nonzero rational section: `∀ (s : ↑(TopCat.Presheaf.stalk L.val.presheaf η)),
   s ≠ 0 → ...`. Exact; no requirement that s extend globally as a regular section.
8. First conclusion, for every closed P and every pair of local generators:
   the first conjunct universally quantifies P, e, e'; singleton span equal to top
   expresses generation. It then quantifies `g g' : C.functionFieldˣ`, assumes both
   displayed representations of s using `lam`, and concludes equality of integer
   values. This has precisely the node's quantifier order and hypotheses.
9. Second conclusion, only finitely many closed P have nonzero order:
   `Set.Finite {P : C | ∃ hP : P ∈ closedPoints C, ∃ e, ... ∃ g, ...}`.
   The generic-stalk dependency says a local generator maps to a singleton basis;
   hence every generator has a unique nonzero coefficient for s. The first conjunct
   makes its valuation independent of generator. The existential set therefore is
   exactly the support in the node, with no omitted points or weaker interpretation.

Edge cases: an empty support is covered by Set.Finite; a zero section is explicitly
excluded by the node. Empty schemes and dimension-zero schemes are excluded by
IsConnectedCurve itself. The zero sheaf cannot satisfy invertibility on this nonempty
curve. Negative valuations and valuation zero are covered by integer values; there
is no natural-number restriction. Nonproper curves, all characteristics, arbitrary
universe u, infinitely many closed points, and nontrivial line bundles remain covered.
There is no index set or tensor-power n to restrict. The two appearances of the
valuation choice use the same witness h; proof irrelevance removes any dependence
on the membership proof hP. Choosing the integral instance changes no underlying data.

Independent searches used different phrases from the worker:

- LeanFinder via msearch: "Changing a basis of an invertible sheaf stalk preserves
  valuation of a rational section and its zeros and poles form a finite set".
  Eight results about affine germs, local fractions and evaluation; no match.
- Loogle via msearch: `Ring.ordFrac`. Twelve results about orders of scalar fractions,
  including `ordFrac_of_isUnit` and DVR comparisons; no line-bundle section theorem.
- rg on Mathlib/AlgebraicGeometry, WeilConjectures, lean/Sheaf and the upstream-name
  table for zeros/poles, order with section/generator, and vanishing with sheaf/section.
  I opened Curve/Divisor.lean's `Scheme.finite_setOf_ord_ne_zero`: it is for a single
  rational function, without L, local generators or the first conclusion. It is a
  possible proof tool, not this node's statement. The other hits concern ample
  nonvanishing loci or cohomology and do not duplicate this statement. No existing
  declaration `rational_section_order` was found.

No mismatch was found; the Lean and node record were left unchanged. No new nodes,
dependency modules or statement correction are present or needed. Both imports serve
notions in the signature. All variables and universe u are bound explicitly. The
module and theorem docstrings name the source and blueprint id; the theorem docstring
follows all three proof steps (local-unit comparison, affine principal-open generating
locus, finite zero-dimensional complement) and names their dependencies. There are no
definitions with postponed data and no proved auxiliary results: only the named theorem
has a sorry proof. I checked that lean.statement is verbatim the theorem signature.

Validation: the independent scompile invocation with the sandbox module's absolute
path returned exit code 0, compiled in 2.3 seconds, and emitted no warnings.
