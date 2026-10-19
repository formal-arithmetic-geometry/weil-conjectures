## Worker report

The module [lean/Sheaf/AlgebraicGeometry/PurityAffineLineComponents.lean](/home/ubuntu/weil-newtargets-stage2-sandbox/Q10/lem-pur-a1-components/lean/Sheaf/AlgebraicGeometry/PurityAffineLineComponents.lean) states `AlgebraicGeometry.affineLine_connectedComponents`.

The `PurityFiniteSetting` parameter renders the fixed purity conventions and supplies the base
field `P.field.k`; `b : B ⟶ Spec (.of P.field.k)` is the structure morphism. `[Nonempty B]`
renders nonemptiness. `[IsSeparated b]`, `[LocallyOfFiniteType b]`, and `[QuasiCompact b]`
render separatedness and finite type. The affine line is
`AffineSpace (ULift (Fin 1)) B`, with projection
`(AffineSpace (ULift (Fin 1)) B ↘ B)`. The open complement is represented by
`j : G ⟶ A1` with `[IsOpenImmersion j]` and `hj` identifying its base range with the
complement of the zero-section range. `i₁` and `hi₁` render the unit section and its
factorization through `G`.

The first conjunct states, pointwise, that each connected component of the affine line is
exactly the inverse image of the connected component of `B` containing its projection. The
second conjunct states the same equality for `G` using `j` followed by the affine-line
projection. The third conjunct says every affine-line component intersects the open
complement; the fourth says every affine-line component intersects the image of the unit
section; the fifth says every component of `G` intersects the image of `i₁`. These are the
three clauses of the node (with clause 1 expressed by the two component equalities and
clauses 2--3 by the three nonempty intersections).

Dependencies used in the statement: `def-pur-conventions` via
`WeilConjectures.PurityFiniteSetting` in `Sheaf.Paper.PurityFiniteSetting`;
`def-sbc-affine-space` via `AlgebraicGeometry.AffineSpace` in
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace`; `def-weil-proper-morphism` via
`AlgebraicGeometry.IsSeparated` in `Mathlib.AlgebraicGeometry.Morphisms.Proper`;
`def-weil-finite-type-morphism` via `AlgebraicGeometry.LocallyOfFiniteType` and
`AlgebraicGeometry.QuasiCompact` in `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
`Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`; `def-weil-affine-spectrum` via
`AlgebraicGeometry.Spec` in `Mathlib.AlgebraicGeometry.Scheme`;
`def-weil-closed-immersion` via `AlgebraicGeometry.IsClosedImmersion` in
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`; and
`def-weil-connected-scheme` via Mathlib `IsConnected`/`connectedComponent` in
`Mathlib.Topology.Connected.Basic`.

Edge cases checked: `Nonempty B` excludes the empty base as required; `connectedComponent`
is a maximal connected set containing a point, so source components are nonempty. The index
`ULift (Fin 1)` is nonempty, so the affine line and its zero/unit sections are the intended
one-dimensional objects. The formulation allows arbitrary (including empty) `G` only subject
to the stated open-complement range equality; no extra smoothness, flatness, finite
presentation, or connectedness hypothesis is added.

Searches made: `msearch.py leanfinder` for affine-line connected components and the unit
section (no exact theorem); `msearch.py loogle` for `AlgebraicGeometry.AffineSpace,
connectedComponent` (no exact theorem); `msearch.py grep` for connected-component
preimages/fibres (generic topology results only); `rg` in the source and project for
`lem-pur-a1-components`, `connectedComponent`, `zeroSection`, and `oneSection` (no existing
statement). The exact Mathlib/upstream declarations used above were opened and checked.

The file compiles cleanly with `scompile.py`; the theorem proof is intentionally `sorry`.


## Second reading by Q10

I independently read the delivered node and module, every statement dependency's node and
recorded signature, the corresponding Lean definitions, and the primary blueprint source
`sec-smooth-purity/sk-prop-a1-inv/lem-pur-a1-components.md`. I also read the local Stacks
TeX: `morphisms.tex`, `lemma-fppf-open` (01UA); `constructions.tex`,
`definition-affine-n-space` (01M0) and its base-change formula; and `topology.tex`,
`definition-connected-components` (004S) and both connected-fibres lemmas (0377, 0378).
Tag 01UA supplies openness, rather than the whole geometric statement. It assumes exactly
flatness and local finite presentation, with no extra global hypothesis. The blueprint
supplies the fixed setting and the separated, finite-type, nonempty base; the DAG's more
explicit relative-spectrum description agrees with 01M0. No statement correction is needed.

The object/hypothesis/conclusion checklist, written before evaluating the signature, is:

1. Fixed purity conventions, including their field k: `P :
   WeilConjectures.PurityFiniteSetting.{u}` and `P.field.k`. Pass. I opened the
   structure in `Sheaf.Paper.PurityFiniteSetting` and `FiniteFieldDatum` in
   `Sheaf.Paper.FiniteFieldFiber`: the latter supplies the finite field, its algebraic
   closure k, and actual field instances. The positive coefficient level and coefficient
   data come from the node's fixed setting; they impose no new geometric hypothesis.
2. A nonempty k-scheme B and its structure morphism: `{B : Scheme.{u}}`,
   `b : B ⟶ Spec (.of P.field.k)`, `[Nonempty B]`. Pass. An explicit structure map is
   appropriate for the finite-type and separatedness predicates. `Spec` is the recorded
   Mathlib spectrum, whose underlying space is PrimeSpectrum, not an alternative object.
3. The structure morphism is separated and of finite type: `[IsSeparated b]`,
   `[LocallyOfFiniteType b]`, `[QuasiCompact b]`. Pass. I opened the Mathlib classes;
   IsSeparated asks for a closed diagonal, and the latter two together are precisely
   finite type as recorded by def-weil-finite-type-morphism. There is no added properness,
   smoothness, finite presentation, connectedness, or Noetherian instance.
4. The relative affine line and its first projection: `AffineSpace (ULift.{u} (Fin 1)) B`
   and `(AffineSpace (ULift.{u} (Fin 1)) B ↘ B)`. Pass. I opened Mathlib's definition,
   the `over` instance, and its affine-base interpretation recorded by def-sbc-affine-space:
   it is the pullback of Spec Z[t] over Spec Z, with `pullback.fst` as projection.
   The coordinate type has exactly one element and the base's universe.
5. The zero section, closed immersion defined by t=0:
   `AffineSpace.zeroSection (ULift.{u} (Fin 1)) B`. Pass. The upstream definition is
   `homOfVector (𝟙 B) 0`, and its projection identity and coordinate formula are exactly
   those of the zero section. I also opened the general upstream instance
   `AffineSpace.isClosedImmersion_zeroSection`; no separate closedness hypothesis or
   duplicate zero-section definition is needed.
6. The open complement G_m,B: `{G : Scheme.{u}}`, `j : G ⟶ AffineSpace ... B`,
   `[IsOpenImmersion j]`, and `hj` identifying `Set.range j.base` with the complement
   of the zero-section range. Pass. An open immersion identifies G as a scheme with
   that open subscheme, not just a set with arbitrary topology. Thus this allows any
   isomorphic presentation of the canonical complement and assumes no extra property.
7. The unit section t=1 and its factorization through the complement:
   `AffineSpace.oneSection ... B`, `i₁ : B ⟶ G`, and
   `hi₁ : i₁ ≫ j = AffineSpace.oneSection ... B`. Pass. I opened the upstream definition
   `homOfVector (𝟙 B) 1` and `oneSection_comp_over`. The factorization is the very one
   named in the node, and is unique because j is an open immersion. The projections of
   both unit sections are the identity, so both source-to-base maps are surjective.
8. Every affine-line component is exactly the inverse image of a base component:
   the first conjunct, `∀ x : AffineSpace ..., connectedComponent x = p.base ⁻¹'
   connectedComponent (p.base x)`. Pass. Mathlib's connectedComponent is the union of
   all preconnected sets through x; I checked `isConnected_connectedComponent` and
   `IsPreconnected.subset_connectedComponent`, which give the node's maximal nonempty
   connected subset. Conversely, every base component contains y, and its inverse image
   occurs at the unit-section point over y by the equality. The pointwise wording
   therefore expresses both directions of “exactly”, with no component lost.
9. The analogous component assertion for G_m,B: the second conjunct uses
   `(j ≫ (AffineSpace ... B ↘ B)).base`. Pass. It is the actual restricted projection;
   the same argument using i₁ over each y gives every base component in this formula.
10. Every affine-line component meets G_m,B: the third conjunct,
    `(connectedComponent x ∩ Set.range j.base).Nonempty`. Pass. It asserts an
    intersection with the specified open complement in the affine line.
11. Every affine-line component meets the unit-section image: the fourth conjunct,
    `(connectedComponent x ∩ Set.range (AffineSpace.oneSection ... B).base).Nonempty`.
    Pass. This is the image in the affine line, rather than the factorization's image
    in the different space G.
12. Every G_m,B component meets the unit-section image there: the fifth conjunct,
    `(connectedComponent x ∩ Set.range i₁.base).Nonempty` for `x : G`. Pass. The use of
    i₁ places both sets in G, with the prescribed factorization to the affine line.

All objects are introduced before their uses, all quantified points are in the intended
source space, and all hypotheses precede the conjunction. The pointwise indexing does not
add a chosen component, a finiteness assumption on components, or a new quantifier order.

Edge cases: the empty base is explicitly excluded exactly as in the node. Every point's
component is nonempty by Mathlib, not a possibly empty preconnected set. An empty G cannot
satisfy the factorization from nonempty B; the canonical complement does satisfy it because
1 and 0 differ in each residue field. This works also in characteristic 2; the fixed
setting's characteristic and ell-not-p condition are inherited and no extra condition on
characteristic is introduced. There is no arbitrary index family or zero-object parameter.
The geometric dimension is fixed to one, so n=0 is not a case of this node; the coefficient
level is positive as prescribed by the conventions. `u` is explicitly bound, the lift of
Fin 1 lies in Type u, and B, G and the field lie in the shared scheme universe required by
the recorded affine-space interface. No unrelated site/coefficient universes or equality
of independent universes are imposed, and autoImplicit is false.

Independent duplicate searches used different wording from the worker:

- `msearch.py leanfinder`: “Relative affine line punctured at the origin has the same
  connected components as its base and every component contains the point with coordinate
  one”. Eight results concerned real normed spaces and convex rays, with no match.
- `msearch.py loogle`: `"connectedComponent", "AffineSpace"`. Zero results.
- `msearch.py grep`: `(AffineSpace|affineLine|punctured|multiplicative).*(connected|Connected)|
  connectedComponent.*(section|Section)`. One unrelated order-connected-section result.
- `msearch.py leansearch`: “Each connected component of a relative affine line and its
  zero-section complement is the inverse image of a connected component of the base
  scheme”. The service returned Internal Server Error and was recorded as unavailable.
- Direct `rg` with the geometric words, `affineLine_connectedComponents`, and the node id
  in upstream WeilConjectures, Mathlib's AlgebraicGeometry tree, the project's lean/Sheaf,
  and dag/lean_names_upstream.json: no exact statement. The hits were punctured principal
  slices, punctured curves, root covers and a smooth-trait section theorem. I opened
  `SmoothTraitSectionComponents.lean`: it compares sections over a DVR and is not this
  affine-line statement. Generic quotient-map component lemmas are proof ingredients,
  not an existing geometric theorem with all of this node's clauses.

Repairs: H3 found no signature mismatch and the signature was preserved verbatim. H8 found
that the original six-line proof summary did not carry the node's ten steps. I replaced it
with all ten steps, including fibre base change, the polynomial-domain/dense-prime argument,
connectedness of the open punctured fibre, the restricted quotient topology, maximality,
exhaustion of components, and all three section intersections. I corrected the source
attribution in both docstrings to name the primary blueprint and the relevant Stacks tags;
01UA alone is only the openness ingredient. I added non-public imports for the stated proof
dependencies: upstream Smooth and SmoothFiber, and Mathlib UniversallyOpen, Fiber,
Pullback.HasPullback, Polynomial.Basic, Field.Defs, and Connected.Clopen. I opened the
recorded smoothness, smooth-criterion, flat-lfp openness, and quotient-preimage connectedness
signatures and verified their hypotheses against the steps. Other proof-dependency modules
are already imported publicly or provided by the public statement-dependency imports.
No new node, dependency repair module, or statement_change was required. There is exactly
one named theorem with proof `by sorry`, carrying this node's id and full proof docstring;
there is no definition, private notation, local instance, hollow data, or proved theorem.
The Lean record's statement is byte-for-byte the file signature. All lines in the Lean
module are at most 100 characters, and every variable and universe is explicitly bound.

Validation: `scompile.py Q10 lem-pur-a1-components` compiled the sole delivered module
cleanly after the repairs, both sandbox and library checks (4.9 seconds each), with no
errors or warnings. The sole theorem intentionally retains `sorry` for stage 3.
