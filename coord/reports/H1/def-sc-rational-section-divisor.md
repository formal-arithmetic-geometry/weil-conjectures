## Worker report

The module `Sheaf.AlgebraicGeometry.RationalSectionDivisor` defines rational sections,
the order of a nonzero rational section at a closed point, and its divisor. No new
statement or dependency node is needed. The item is unchanged outside `lean`.
No `sorry` occurs in the delivered module, and no theorem is proved.

Clause-by-clause correspondence:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- The smooth connected curve is `(C : Scheme.{u}) (f : C ⟶ Spec (.of k))`
  with `[IsConnectedCurve f] [Smooth f]`. `IsConnectedCurve` includes separatedness,
  finite type, nonemptiness, connectedness and dimension exactly one.
- Integrality is obtained, not imposed: every definition uses the integral instance
  `Classical.choose (C.smooth_connected_curve_local_rings k f)`. This is the
  identical instance chosen by the recorded finite-order theorem.
- The generic point is `genericPoint C`, and the function field used for coefficients
  is `C.functionField`, Mathlib's structure-sheaf stalk there. This uses the
  integral-scheme clause of def-sc-function-field, not its component product.
- The invertible module is `(L : C.Modules) [L.IsInvertible]` in the order and
  divisor definitions. `rationalSection` itself returns the actual generic stalk
  `↑(TopCat.Presheaf.stalk L.val.presheaf (genericPoint C))`. The type abbreviation
  also works for other modules, without restricting its use for invertible modules.
- A rational section is an element of that stalk; the nonzero input to order/divisor
  is the subtype `{s : rationalSection k C f L // s ≠ 0}`. The stalk retains its
  existing additive group and function-field module structures. Its dimension one
  is the second clause of `invertible_module_generic_stalk`, already a dependency.
- Closed points are `P : closedPoints C`, the very indexing type in `C.Divisor`.
- A local generator `e` is expressed by
  `Submodule.span (C.presheaf.stalk P.val) {e} = ⊤` in the actual module stalk.
- The map λ_P is `TopCat.Presheaf.stalkSpecializes L.val.presheaf` using
  `(genericPoint_spec C).specializes (Set.mem_univ P.val)`, exactly as in both
  generic-stalk and rational-section-order dependency declarations.
- The nonzero coefficient is `g : C.functionFieldˣ`, with equation
  `s.val = (g : C.functionField) • lam e`.
- The normalized valuation is the chosen monoid homomorphism supplied at P by
  `smooth_connected_curve_local_rings`; it is the identical choice used by
  `rational_section_order`. `Multiplicative.toAdd (v g)` is its integer value.
- `rationalSectionOrder` uses `Classical.epsilon` on integers satisfying the above
  generator/coefficient equation and `Multiplicative.toAdd (v g) = n`. This is a
  fully specified data definition, not a proof placeholder. There is such an integer:
  the generic-stalk theorem supplies a local singleton basis and a generic basis
  from its generator; a nonzero section has a nonzero coordinate in that basis.
  Every admissible integer is equal by clause 1 of `rational_section_order`.
  Consequently this choice is precisely the order in the node, independent of e.
- Clause 2 of `rational_section_order`, applied to `s.val` and `s.property`, gives
  the finite set of underlying closed points admitting a coefficient with nonzero
  valuation. Its `toFinset` is used in `rationalSectionDivisor`. Each summand is
  `Finsupp.single ⟨P, hP⟩ (rationalSectionOrder ... ⟨P, hP⟩)`. This is
  ∑ ord_P(s)[P] in the existing free abelian group `C.Divisor`. The closed-point
  conditional only supplies the subtype proof; every point in this finite set is
  closed by the predicate defining it. Points outside it have order zero by the
  same existence and independence facts, so the finite sum is the required sum.
- For L = O_C and generator 1, λ_P(1) = 1 and its coefficient is the rational
  function itself; the normalized DVR order equals `Scheme.ord`. Thus this sum
  is the principal divisor defined by `Scheme.div`. This compatibility is explained
  in the declaration docstring; it introduces no second principal-divisor map.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.Curve`: `AlgebraicGeometry.IsConnectedCurve`
  (specialization of the recorded `IsCurve`).
- `Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings`:
  `AlgebraicGeometry.Scheme.smooth_connected_curve_local_rings`.
- `Mathlib.AlgebraicGeometry.FunctionField`:
  `AlgebraicGeometry.Scheme.functionField` (the integral clause of
  `Sheaf.AlgebraicGeometry.FunctionField` / def-sc-function-field).
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `Mathlib.Topology.Sheaves.Stalks`: `TopCat.Presheaf.stalk`, `stalkSpecializes`;
  `Mathlib.Algebra.Category.ModuleCat.Stalk`: the module-stalk instance and
  `PresheafOfModules.germ_ringCat_smul` (def-weil-pbc-module-stalk's mathlib_match).
- `Sheaf.AlgebraicGeometry.InvertibleModuleGenericStalk`:
  `AlgebraicGeometry.Scheme.Modules.invertible_module_generic_stalk`.
- `Sheaf.AlgebraicGeometry.RationalSectionOrder`:
  `AlgebraicGeometry.Scheme.Modules.rational_section_order`.
- `WeilConjectures.AlgebraicGeometry.Curve.Divisor`:
  `AlgebraicGeometry.Scheme.Divisor`, `Scheme.div`. These are the existing entries
  explicitly named in def-sc-divisor's mixed record; its `DivisorModule` module adds
  the associated O_C(D), which this definition does not use.

The two direct imports supply the order theorem and the existing divisor type.
All other required modules come through these imports.

Edge cases checked before writing: the empty scheme and dimension-zero connected
schemes are excluded by the node's connected-curve hypothesis itself; the zero
section remains a rational section but is excluded only from order and divisor;
a nowhere-vanishing section has empty finite support and produces zero; negative
orders are integer coefficients and produce poles; no properness, affine hypothesis,
or characteristic restriction is introduced. The universe is the scheme/field/module
universe u, with no finite-cardinality restriction on points or sections.

Searches made:

- msearch.py leanfinder: `divisor of nonzero rational section of invertible sheaf on
  a smooth algebraic curve` returned eight results on elliptic coordinate/function
  fields and analytic meromorphic divisors, none defining this notion.
- msearch.py loogle: `Scheme.Divisor, stalk` returned no hits (unknown identifier
  Scheme.Divisor in Mathlib).
- msearch.py grep in AlgebraicGeometry: `RationalSection|rational.section|divisor.*section`
  returned no hits. These searches are logged by the tool in searches.jsonl.
- rg in upstream WeilConjectures and lean/Sheaf for `RationalSection|rationalSection|rational.section`
  found Picard/RiemannRoch commentary and the dependency RationalSectionOrder;
  no rational-section or divisor definition. Picard.lean explicitly says rational
  sections of line bundles are unavailable there.
- grep -rn for `def-sc-rational-section-divisor` in upstream returned no match.
- rg for the proposed names `rationalSectionDivisor|rationalSectionOrder|abbrev rationalSection`
  in dag/lean_names_upstream.json, upstream, Mathlib and lean/Sheaf returned no match.

Source checked directly: Stacks Tags [01X5 (2)](https://stacks.math.columbia.edu/tag/01X5),
[02SF](https://stacks.math.columbia.edu/tag/02SF) and
[0BE6 (1)](https://stacks.math.columbia.edu/tag/0BE6). Local literature contains lists
but not the Stacks text, so the tag pages were read online. No statement fault or
STATEMENT-DISPUTED issue was found.

## Second reading by H1

I read the item node, its eight statement dependencies and their recorded source
signatures, and the delivered Lean independently. No mathematical mismatch was
found; the Lean and node record are unchanged. This reading adds only this report.
There are no new nodes, dependency modules or statement corrections to review.

Source check: the local literature tree has no Stacks checkout. I obtained
`divisors.tex` from the official stacks/stacks-project repository into this item's
scratchpad and read `lemma-meromorphic-functions-integral-scheme` (01X5), the
section preceding `definition-order-vanishing-meromorphic` (02SF), that definition,
and `definition-divisor-invertible-sheaf` (0BE6). The standing assumption is locally
Noetherian integral, not proper. The section explicitly identifies regular
meromorphic sections with nonzero meromorphic sections on an integral scheme.
01X5(2) applies to quasi-coherent modules; local freeness of rank one ensures this
for the invertible modules here. The curve specialization obtains Noetherianity
and integrality from the recorded local-rings theorem. Prime divisors of this
one-dimensional integral curve are precisely closed points. I also read
[02MD](https://stacks.math.columbia.edu/tag/02MD), whose length-based order is the
normalized valuation in the DVR case. Source pages:
[01X5](https://stacks.math.columbia.edu/tag/01X5),
[02SF](https://stacks.math.columbia.edu/tag/02SF),
[0BE6](https://stacks.math.columbia.edu/tag/0BE6).

My object/hypothesis/clause checklist and correspondence:

1. Algebraically closed field k: `(k : Type u) [Field k] [IsAlgClosed k]`.
   PASS; no characteristic restriction.
2. Smooth connected curve C over k: `(C : Scheme.{u})
   (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]`.
   PASS. I read `IsCurve` and `IsConnectedCurve` in upstream Curve.lean:
   separated, locally finite type, quasi-compact, connected and dimension one
   are exactly the dependency node's connected-curve notion. The explicit f
   is also the argument of the recorded local-rings and order declarations.
3. Integral C, generic point eta and field k(C): every definition installs
   `Classical.choose (C.smooth_connected_curve_local_rings k f)` and uses
   `genericPoint C` and `C.functionField`. PASS. This is a conclusion-derived
   integral instance, not an extra hypothesis. Mathlib FunctionField.lean
   defines the field as the structure-sheaf stalk at this generic point.
   The function-field dependency explicitly retains this integral-scheme clause;
   its component-product addition is unnecessary here.
4. Invertible O_C-module L: `(L : C.Modules) [L.IsInvertible]` in order and
   divisor. PASS. Upstream `Scheme.Modules.IsInvertible` means local isomorphism
   with the structure sheaf, hence rank-one locally free and quasi-coherent.
   `rationalSection` permits arbitrary modules but specializes to this exact
   notion; its generality does not change any definition for invertible L.
5. Rational sections are elements of L_eta, including zero:
   `rationalSection` is an abbreviation for the actual generic module stalk.
   PASS. The additive structure and field action are the existing Mathlib stalk
   instances, not replacement structures. The rank-one assertion is clause two
   of `invertible_module_generic_stalk`, read in its module.
6. Nonzero section s and closed point P: the subtype
   `{s : rationalSection k C f L // s ≠ 0}` and `P : closedPoints C`.
   PASS. Nonzero is imposed only where the source imposes it.
7. Local generator e_P: `e` in the actual stalk at P, satisfying
   `Submodule.span (C.presheaf.stalk P.val) {e} = ⊤`. PASS. This means exactly
   generator of that rank-one local module. The dependency's singleton-basis
   clause ensures generators exist.
8. Germ map lambda_P: `TopCat.Presheaf.stalkSpecializes` applied to specialization
   from eta to P. PASS. I read its signature: it maps the stalk at the specialized
   point to the stalk at its generalization, so the direction is L_P to L_eta.
   It is the same map as in the two recorded generic-stalk/order dependencies.
9. Nonzero coefficient g_P and order v_P(g_P): `g : C.functionFieldˣ`,
   `s.val = (g : C.functionField) • lam e`, and
   `Multiplicative.toAdd (v g) = n` inside `Classical.epsilon`. PASS. The chosen v
   is exactly the normalized homomorphism in the local-rings theorem, with the
   same integral instance and projections as the order theorem. A local basis
   exists, its generic image is a field basis by `invertible_module_generic_stalk`,
   and the coordinate of nonzero s is nonzero, hence a unit. Thus the epsilon
   predicate is inhabited. Clause one of `rational_section_order` says every
   satisfying integer agrees. No arbitrary fallback value is used mathematically.
10. Independence of generator and finitely many nonzero orders: respectively
    clauses one and two of `rational_section_order`. PASS. The latter's set
    records existence of a generator and a nonzero-valued coefficient. Existence
    and independence just checked make this exactly the support of the order,
    not merely a set related to that support.
11. Divisor equals sum of orders times [P] in Div(C): `hfin.toFinset.sum`, each
    closed-point term `Finsupp.single` with coefficient `rationalSectionOrder`.
    PASS. The predicate for hfin includes closedness, so the conditional's else
    branch is never used on its indexing set. Outside that set the unique order
    is zero. Upstream Divisor.lean defines `C.Divisor = closedPoints C →₀ ℤ`,
    the recorded dependency's free abelian group; no private divisor type appears.
12. Structure-sheaf specialization is the principal divisor: PASS. For the unit
    module, its stalk is canonically the ring stalk, generator 1 has generic
    image 1, and the coefficient is s itself. The order is therefore its DVR
    order, namely the `Scheme.ord` coefficient in upstream `Scheme.div` (whose
    definition I opened). The last docstring explains this compatibility;
    no second principal-divisor definition or extra axiom is introduced.

Edge cases: the node itself excludes the empty scheme and dimension-zero schemes
by its connected-curve hypothesis, as does IsConnectedCurve. The zero rational
section exists in the abbreviation, and is excluded only from order/divisor.
Empty support gives the empty sum, hence zero; a section with no zeros or poles
therefore has zero divisor. Orders take values in integers, so poles are retained.
No properness, affineness, extra Noetherian instance or restriction on positive
characteristic appears. All point sets may be infinite; only the derived support
is finite. The arbitrary universe u matches the recorded Scheme.Modules universe;
field and scheme can be placed in a common universe. Every binder and universe
is explicit (`autoImplicit false`); no extra smallness hypothesis appears.

Independent H4 searches (different wording from the first worker):

- msearch leanfinder: `generic fiber of a line bundle meromorphic section order
  vanishing divisor` returned analytic `MeromorphicOn.divisor`, its evaluation
  lemmas and `meromorphicOrderAt`; these concern normed fields and functions,
  not algebraic invertible modules.
- msearch loogle: `TopCat.Presheaf.stalkSpecializes` returned the existing
  specialization/germ machinery. I opened it and reused its meaning; none of
  these declarations defines the rational-section divisor.
- msearch grep: `meromorphic|generic.*section|section.*valuation` returned analytic
  and number-theoretic material, not this notion.
- Direct rg for `meromorphic|rational.?section|divisor.*section|section.*divisor`
  in Mathlib/AlgebraicGeometry, upstream WeilConjectures and this project's
  lean/Sheaf found the order dependency, divisor modules and upstream commentary
  that rational sections were missing. I additionally inspected the project's
  MeromorphicModule signatures: it defines the sheaf of localized sections on
  an arbitrary scheme, not the generic-stalk abbreviation, its normalized local
  order or its divisor. It therefore does not replace this node's definitions.

H5/H6/H8/H9: all three declarations have concrete data bodies, no sorry, no new
axiom and no theorem proved. Source and blueprint markers are present on each
and on the module. This is a definition node with empty proof, so no theorem
proof narrative is missing. Both imports are used; declarations have no Sheaf
namespace prefix and every Lean line is within 100 characters. The node's recorded
main signature equals the declaration signature (starting at `def`, excluding
`noncomputable`, as required by the project's signature reader).

Verification: `scompile.py H1 def-sc-rational-section-divisor` on the absolute
sandbox Lean path compiled successfully in 2.2 seconds with no warnings or errors.
The first invocation used a relative path from the read-only repository and
could not find the sandbox file; rerunning with its absolute path resolved this
invocation error without changing any tool or file.
