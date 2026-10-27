## Worker report

The module `Sheaf.AlgebraicGeometry.Morphisms.SeparatedLocalIsoGenericInjectivity`
states `AlgebraicGeometry.isOpenImmersion_of_separated_of_generic_injOn`, with its
whole proof `by sorry`. No definitions, helper statements, dependency repairs or
statement corrections are introduced. The original node is unchanged except for
its `lean` record.

I read the statement and proof at `literature/stacks-project/varieties.tex`,
lines 8890–8909, Tag 09NG, label `lemma-characterize-open-immersion`, and the
application at lines 9004–9008 in Tag 09NI. Renaming the source's X,Y to Y,X
matches the node. The declaration docstring expands all five DAG proof steps,
including the base change of the closed diagonal; no reducedness assumption or
agreement-of-morphisms argument is used.

Hypothesis and conclusion correspondence:

- Arbitrary schemes and their morphism: `{Y X : Scheme.{u}} (g : Y ⟶ X)`.
- Separatedness: `[IsSeparated g]`, whose sole defining condition is that
  `pullback.diagonal g` is a closed immersion. The proper-morphism dependency
  records this declaration as well as `IsProper`; properness is not assumed.
- The generic points Y⁰: Mathlib's `genericPoints Y`, defined in
  `Mathlib.Topology.Sober` by `{η | closure {η} ∈ irreducibleComponents Y}`.
  Since `IsGenericPoint η C` means `closure {η} = C`, this is exactly the set
  of generic points of irreducible components specified by the two DAG nodes.
  It introduces no alternative definition of either notion.
- Indexed open subsets: `{I : Type v} (V : I → Y.Opens)`. Both universe variables
  are explicit; the index universe is independent and the index type need not
  be inhabited, finite or countable.
- The union is Y: `hcover : ∀ y : Y, ∃ i : I, y ∈ V i`. This is precisely
  pointwise coverage, equivalent to the union of these open subsets being Y.
- Each restriction is an open immersion:
  `hlocal : ∀ i : I, IsOpenImmersion ((V i).ι ≫ g)`, using the canonical open
  subscheme inclusion `Scheme.Opens.ι` from `Mathlib.AlgebraicGeometry.Restrict`.
- Distinct generic points have distinct images:
  `hgeneric : Set.InjOn g (genericPoints Y)`. Injectivity on this subset says
  equal images imply equal points; its contrapositive is the node's clause.
- Conclusion: `IsOpenImmersion g`, with no additional conclusion.
- The final sentence of the node is respected: no quasi-compactness,
  finite-component, reducedness or generic-image-containment hypothesis occurs.

Statement dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`; open subschemes use `Scheme.Opens.toScheme`
  and `Scheme.Opens.ι` from `Mathlib.AlgebraicGeometry.Restrict`.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsSeparated`, whose full
  signature and defining closed-diagonal field are in
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`; the recorded dependency
  module `Mathlib.AlgebraicGeometry.Morphisms.Proper` is publicly imported.
- `def-sc-generic-point`: `IsGenericPoint`, `Mathlib.Topology.Sober`;
  its standard aggregate `genericPoints` renders Y⁰.
- `def-weil-irreducible-components`: the recorded Mathlib match
  `irreducibleComponents`, `Mathlib.Topology.Irreducible`, whose definition is
  `{s | Maximal IsIrreducible s}`. This Mathlib node requires no lean repair.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`, the exact recorded declaration.

All modules of the statement dependencies are public imports. The already
stated proof dependencies are imported without `public`: the component-cover
lemmas are supplied by the topology import; sobriety of schemes by
`Mathlib.AlgebraicGeometry.Properties`; `CategoryTheory.Limits.pullback` by
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`; closed immersion
and its base-change stability by
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`; and
`AlgebraicGeometry.IsOpenImmersion.of_forall_source_exists` by
`Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion`. Shared statement/proof
modules retain public visibility. There are no omitted proof imports or cycles.

Edge cases checked against the mathematical statement:

- Empty Y is allowed, including the empty indexed cover. Both pointwise
  coverage and generic-point injectivity are then vacuous and the conclusion
  is the valid open immersion of the empty scheme.
- For nonempty Y an empty index type cannot satisfy `hcover`; this is exactly
  the source condition rather than an extra nonemptiness binder.
- Empty cover members, arbitrary infinite covers and infinitely many
  irreducible components are allowed. No irreducibility assumption is imposed.
- The identity on any scheme, including nonreduced schemes, satisfies the
  assumptions; no reduction or singleton generic point was substituted.
- Two disjoint copies of the same nonempty integral scheme mapping identically
  to that scheme fail generic injectivity, as required.
- The doubled-origin line mapping to the affine line fails separatedness;
  it is excluded by precisely the hypothesis needed in proof step 4.
- No generic-image-containment condition is supplied: the signature only tests
  generic points of Y, and neither binds a map Y⁰ → X⁰ nor prescribes their images.

Searches performed through the prescribed msearch.py wrapper (Q43 and this item):

- LeanFinder: `A separated local isomorphism of schemes injective on generic
  points of irreducible components is an open immersion`. Eight hits, including
  `IsOpenImmersion.of_forall_source_exists`, `IsLocalIso.exists_isOpenImmersion`
  and `isLocalIso_iff`; none includes the generic-point/separatedness argument.
- Loogle: `AlgebraicGeometry.IsSeparated, AlgebraicGeometry.IsOpenImmersion`.
  Two normalization/Zariski-main-theorem hits, both about a different morphism
  with additional finiteness hypotheses, not this assertion.
- Mathlib grep: `generic.*[Ii]nject|[Ii]nject.*generic|of_forall_source_exists|IsLocalIso`
  in `AlgebraicGeometry/Morphisms`. Thirteen hits, chiefly local-isomorphism
  APIs and the criterion assuming injectivity on all points. No exact theorem.
- LeanSearch: `A separated local isomorphism of schemes injective on generic
  points is an open immersion`. Eight hits, comprising open-immersion and local
  isomorphism APIs; none proves the missing generic-to-global implication.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for
  `generic.*[Ii]nject|[Ii]nject.*generic|separated.*[Ll]ocal[Ii]so|isOpenImmersion_of.*generic`
  found unrelated generic algebra/cohomology statements and no exact result.
  `grep -rn` of the item id in `lean/WeilConjectures` returned no match.
- Direct Mathlib source searches found the existing `genericPoints` definition,
  `IsGenericPoint`, `irreducibleComponents`, `IsSeparated` and `IsOpenImmersion`.
  The full new declaration name was searched in Mathlib, both project source
  roots and `dag/lean_names_upstream.json`, with no occurrence.

Validation: the prescribed scompile.py compiled this file both as a sandbox
module and under its library module name, with no errors or unexpected warnings.
No disputed statement or node fault was found.

## Second reading by Q43

This section records a separate pass by the writer, not an independent agent:
the dispatcher's explicit instruction forbids starting other agents, and the
maintainer independently reviews the delivery. With the node and final module
open, I checked the two scheme binders, the separatedness instance, every cover
member and the pointwise union condition, and the restriction `(V i).ι ≫ g`.
I unfolded `genericPoints` and read `IsGenericPoint` and `irreducibleComponents`
to verify that `Set.InjOn` quantifies over precisely Y⁰. Its codomain is all of X,
not X⁰. The conclusion is exactly an open immersion. The proof plan uses
separatedness only through its closed diagonal and supports arbitrary components,
including the empty source. No mismatch or subsequent statement change was found.
