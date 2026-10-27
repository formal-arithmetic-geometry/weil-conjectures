## Worker report

The module `Sheaf.GroupTheory.IntegralSharpeningGroupExactness` states
`AlgebraicGeometry.FineFan.integral_sharpening_group_exactness`, with its sole proof
`sorry`. No new definition, dependency repair, or statement correction is needed.
Only the item's `lean` field changes. The five proof steps appear in the docstring.

The statement uses multiplicative notation, following the recorded dependency
interfaces (and the already landed FineMonoidUnitSplitting consumer). Products,
quotients, and the identity translate the node's sums, differences, and zero.

Clause-by-clause rendering:

- Commutative monoid P: `(P : Type u) [CommMonoid P]`, with explicit universe u.
- Integral, defined by injectivity of P to its completion G:
  `hP : Function.Injective (Algebra.GrothendieckGroup.of (M := P))`.
  No finite generation, saturation, or torsion-free hypothesis is added.
- G is the actual `Algebra.GrothendieckGroup P`. Its canonical `of` identifies P
  with its image using hP; no separate ambient group or arbitrary embedding occurs.
- Units U are a subgroup of G: `∃ U : Subgroup (Algebra.GrothendieckGroup P)`
  and the exact carrier equation
  `(U : Set _) = Algebra.GrothendieckGroup.of '' {p : P | IsUnit p}`.
  In an integral commutative monoid, these are exactly the elements whose inverse
  is also in P. Thus this existential specifies the unit subset exactly; it does
  not replace the desired subgroup by an arbitrary one or its larger group closure.
- B and q are Mathlib's `Associates P` and `Associates.mkMonoidHom`.
  `Associates` is explicitly the quotient by the relation x*u=y for a unit u.
- The canonical map B to G/U is the existential monoid homomorphism i, with
  `∀ p, i (Associates.mk p) = QuotientGroup.mk' U (Algebra.GrothendieckGroup.of p)`.
  This pins i on every quotient representative; `Function.Injective i` is the
  asserted embedding, with no extra hypothesis on a freely chosen map.
- Integrality of B is `Function.Injective
  (Algebra.GrothendieckGroup.of (M := Associates P))`.
- H is the actual `Algebra.GrothendieckGroup (Associates P)`. The canonical pi is
  `Algebra.GrothendieckGroup.lift (Algebra.GrothendieckGroup.of.comp
  (Associates.mkMonoidHom : P →* Associates P))`. Mathlib's lift is the extension
  equivalence, inverse to composition with `of`; hence on of(p)/of(p') it is
  of(q(p))/of(q(p')), exactly the node's specified map. Its `Function.Surjective`
  clause and `.ker = U` give both remaining exactness assertions.
- The finite list is arbitrary `(d : ℕ) (a : Fin d → P)`. Its generation premise
  is `Submonoid.closure (Set.range a) = ⊤`. The two conclusions are respectively
  the monoid closure of `fun k ↦ Associates.mk (a k)` equal to top and the subgroup
  closure of `fun k ↦ Algebra.GrothendieckGroup.of (Associates.mk (a k))` equal
  to top. They assert generation by this same list, not merely finite generation.

Dependency declarations and source reading:

- `Sheaf.AlgebraicGeometry.FineFanBlowup`: read `IsFine`, `IsSharp`, `sharpenMap`,
  `sharpPresheaf` and `sharpSheaf`. In particular `sharpenMap : (P →* Q) →
  (Associates P →* Associates Q)` and the sectionwise quotient use precisely
  `Associates`, so the present statement uses that same quotient. IsFine contains
  both Monoid.FG and injectivity; this theorem correctly uses only its integral
  part, since the node assumes no finiteness until its final conditional clause.
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: read the recorded module and
  its group-completion/characteristic uses; it imports the actual Mathlib
  `Algebra.GrothendieckGroup` construction through LogRegularPair. Both recorded
  statement/proof dependency modules are public imports.
- `Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup`: read the full
  signatures and documentation of `GrothendieckGroup`, `of`, `of_injective`,
  `lift`, and `lift_apply`. The universal completion is localization at top.
- `Mathlib.Algebra.GroupWithZero.Associated`: read `Associates`, `mk`,
  `mk_eq_mk_iff_associated`, and `mkMonoidHom`.
- `Mathlib.GroupTheory.QuotientGroup.Defs`: `QuotientGroup.mk'` is the canonical
  quotient homomorphism; commutativity supplies normality for every subgroup.

Source checked: extracted PDF pages 104--106, printed pp.98--100, of
`literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf`.
VIII 3.1.1 defines sharpening as quotient by invertibles; 3.1.2 identifies integral
localization within the completion; 3.1.11 discusses sharpening and completion.
The exactness and generator clauses are the node's explicit algebraic refinement.

Edge cases checked before writing:

- d=0: closure of the empty set is the trivial monoid. Its being top forces P
  trivial, and both conclusions are trivial. No Nonempty list hypothesis appears.
- Trivial P: U, G, B, H and both maps are trivial, satisfying every clause.
- P an abelian group: all elements are units, U=G, B and H are trivial; the
  embedding into G/U and the kernel assertion remain correct, including torsion.
- P a sharp integral monoid: U is trivial and the completion map is an isomorphism;
  the statement imposes no unnecessary torsion restriction.
- Non-finitely-generated integral P: all exactness clauses still apply; the final
  conditional does not assume such a generating list exists.
- Every construction stays in Type u. Explicit binders and autoImplicit=false
  exclude accidental auto-bound variables. No file-local notation or let occurs.

Searches performed with the prescribed msearch.py wrapper:

- leanfinder: "For an integral commutative monoid the group completion of its
  sharpening is the quotient of its group completion by units, with surjectivity
  kernel units and induced finite generators". Eight hits: GrothendieckGroup,
  GrothendieckAddGroup, of, lift_apply, group structures and instFG; none states
  sharpening exactness or this list of conclusions.
- loogle: `"GrothendieckGroup", "Associates"`. Zero hits.
- grep: `Grothendieck.*Associates|Associates.*Grothendieck|sharpen.*(kernel|inject|quotient)`.
  Two irrelevant Grothendieck-topology hits in Coverage.lean.
- leansearch: "The sharpening of an integral commutative monoid embeds into its
  group completion modulo units and the induced map of group completions is
  surjective with kernel exactly the units". Eight hits, of_injective/lift and
  additive or multiplicative completion definitions/instances; no exact match.
- Local rg on lean/Sheaf and lean/WeilConjectures for the completion/Associates
  combination and this node id found FineMonoidUnitSplitting, logarithmic
  differential maps and characteristic-group constructions. None states the
  present general integral-monoid theorem. Read FineMonoidUnitSplitting: it assumes
  finiteness and two torsion-free completions, and concludes a product splitting;
  it is not this theorem. FsFaceSharpening is specialized to fs face localization,
  also not this theorem. The upstream grep for this item's id returned no hit.
- Full-name collision rg on dag/lean_names_upstream.json, Mathlib,
  WeilConjectures and Sheaf found no occurrence of the chosen theorem name.

The requested CompactObject example was opened: the current module contains only
"Withdrawn: no declarations remain". The current module-mode brief and existing
FineMonoidUnitSplitting module provide the applicable header and namespace pattern.

Validation: prescribed scompile.py compiled both its sandbox check and the library
module cleanly (26.9 seconds and 5.9 seconds respectively); no warnings were printed.
No disputed statement or source fault was found.

## Second reading by Q28

A separate self-review pass reopened the node and the completed module. It checked
that the hypothesis is injectivity alone, U is fixed by its exact carrier rather
than closure, i has the representative formula and injectivity, B is integral,
pi is the actual universal extension with the correct domain and codomain and has
both surjectivity and exact kernel, and the final conditional preserves each
specified generator with monoid versus subgroup closure used in the right places.
The empty-list and all-units cases remain included. No mismatch was found and no
statement changed. This is a self-review, not a claim of independent agent review:
the dispatcher explicitly prohibits starting another agent, and the maintainer's
independent review reads the delivery.
