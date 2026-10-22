## Worker report

Delivered module: `Sheaf.AlgebraicGeometry.GaloisComponentPresentation`.
Declaration: `AlgebraicGeometry.exists_galois_component_presentation`.
This is stage 2: the sole theorem has proof `by sorry`; there are no new definitions,
new nodes, dependency repairs, or statement changes. All variables and the universe
`u` are explicitly bound; `autoImplicit` is false.

I read the full node and its ten proof steps, every statement dependency and its
recorded interface, and the relevant declarations/docstrings in the read-only Lean
sources. I read ILO Expose X, 2.3 Steps 1--2, printed p.150 (PDF p.156), directly
with pdftotext. Step 1 supplies properness, irreducibility, geometric reducedness,
Cartier boundary and normality; Step 2 chooses the finite Galois extension, component
and decomposition subgroup and states transitivity on components. The expanded
DAG proof supplies the finite etale orbit and faithfulness assertions. Its ten
steps, references and dependencies are carried into the theorem docstring.

Hypothesis-by-hypothesis correspondence:

- The field e is `(e : Type u) [Field e]`. The e-scheme is `(B : Scheme.{u})`
  with named structure morphism `b : B ⟶ Spec (.of e)`.
- Nonempty and integral are `[IsIntegral B]`; Mathlib's class includes `Nonempty B`
  and is equivalent to nonempty, reduced and irreducible. No empty B is admitted.
- Normality is `hBnormal : ∀ x : B, IsDomain (B.presheaf.stalk x) ∧
  IsIntegrallyClosed (B.presheaf.stalk x)`, exactly the local-ring convention in
  the node. This is not geometric normality or smoothness.
- Proper finite type is `[IsProper b]`. Its fields give separated, universally
  closed and locally finite type; universally closed implies quasi-compact,
  so this includes the entire finite-type hypothesis. Separate finite-type
  instance parameters were removed after the overlapping-instances warning;
  the hypothesis is mathematically unchanged.
- Geometrically reduced is `[GeometricallyReduced b]`, the dependency's recorded
  Mathlib notion, quantifying over field-valued base changes.

Conclusion-by-conclusion correspondence (the theorem uses L for e_0, U.toScheme
for X, and writes u as `U.ι ≫ pullback.fst b (Spec.map ... )`):

- `IsNoetherian B` is the Noetherian conclusion. Mathlib's documented
  `isNoetherian_iff_of_finite_iSup_eq_top` identifies it with the finite affine
  cover by Noetherian rings specified in the node.
- `∃ (L : Type u) (_ : Field L) (_ : Algebra e L), Module.Finite e L ∧
  IsGalois e L ∧ ...` chooses a finite Galois field extension. `L ≃ₐ[e] L` is
  exactly its group A; it is not an arbitrary finite group or a chosen subgroup.
- `U : (pullback b (Spec.map (CommRingCat.ofHom (algebraMap e L)))).Opens`
  defines X as the actual open subscheme of B_L. `IsClosed (U : Set ...)` makes
  it clopen; membership in `irreducibleComponents` makes it an actual component.
  `IsIntegral U.toScheme`, the same local normality assertion on its stalks,
  `IsProper (U.ι ≫ pullback.snd ...)`, and `GeometricallyIntegral` of that same
  map give integral, normal, proper and geometrically integral over L.
- `a : (L ≃ₐ[e] L) →* Aut (pullback b ...)` is the scheme action. The two
  projection equalities uniquely specify `id_B × Spec(g⁻¹)`: it fixes the first
  projection, and acts on the second by `Spec.map ... g.symm.toRingHom`.
  Thus no arbitrary or unspecified action replaces the canonical action.
  A monoid homomorphism to `Aut` includes the action laws.
- For every irreducible component Z, `∃ g, (a g).hom '' U = Z` says that the
  orbit of U is all components. Automorphisms permute irreducible components,
  so this is precisely transitivity of A on the components.
- `H : Subgroup (L ≃ₐ[e] L)` with `∀ g, g ∈ H ↔ (a g).hom '' U = U` is exactly
  the stabilizer, not a subgroup contained in it. Its action on L is evaluation
  of its underlying algebra automorphism. That action is faithful by subtype
  inclusion and extensionality of algebra automorphisms; no extra premise is
  needed. `r : H →* Aut U.toScheme` with `(r h).hom ≫ U.ι = U.ι ≫ (a h.val).hom`
  specifies the restricted action. Together with the second projection law this
  is precisely semilinear compatibility with X → Spec L, using the same inverse
  scalar convention. `Function.Injective r` asserts faithfulness on X as a
  scheme (not merely on its topological point set).
- `IsFinite u ∧ Etale u ∧ Surjective u` gives the three map properties;
  `∀ h, (r h).hom ≫ u = u` gives H-invariance.
- The geometric-fibre orbit clause quantifies over every algebraically closed
  `Ω : Type u` and maps `x y : Spec (.of Ω) ⟶ U.toScheme` with `x ≫ u = y ≫ u`;
  it concludes `∃ h : H, x ≫ (r h).hom = y`. By the pullback universal property,
  these are Ω-valued lifts over the same geometric base point. Since u is finite
  etale, its geometric fibre is a finite disjoint union of copies of Spec Ω:
  each fibre point determines exactly one such lift, with its residue-field
  embedding retained. This is exactly transitivity on points of the geometric
  fibre `pullback u bΩ` from def-weil-geometric-fibre, and not the weaker orbit
  assertion on underlying points of X. Surjectivity and finite etaleness ensure
  that every such geometric fibre is nonempty.
- An input Cartier support C is rendered by arbitrary `I : B.IdealSheafData`
  with `I.IsInvertible`, and C = I.support. The conclusion supplies
  `J : U.toScheme.IdealSheafData`, `J.IsInvertible`, equality of J.support with
  `u ⁻¹' I.support`, and `∀ h, J.comap (r h).hom = J`. This is stability of the
  effective Cartier divisor itself, including multiplicities, not merely its
  closed support. Quantifying over all Cartier ideals represents the node's
  conditional statement for every such C; the presentation is chosen before I.

Dependency declarations used:

- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs.
- def-pc-integral-scheme: `AlgebraicGeometry.IsIntegral`,
  Mathlib.AlgebraicGeometry.Properties.
- def-weil-proper-morphism: `AlgebraicGeometry.IsProper`,
  Mathlib.AlgebraicGeometry.Morphisms.Proper.
- def-weil-finite-type-morphism: `LocallyOfFiniteType` and `QuasiCompact`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType and .QuasiCompact; supplied
  by the properness instance rather than redundant binders.
- def-pc-geometrically-irreducible: `GeometricallyReduced` and
  `GeometricallyIntegral`, Mathlib.AlgebraicGeometry.Geometrically.Integral.
- def-pc-field-extension: `Algebra`, Mathlib.Algebra.Algebra.Defs.
- def-pc-field-tower: imports Sheaf.FieldTheory.FieldTower and uses the
  `Module.Finite` encoding of finite extension documented there; no second
  degree or finite-extension definition is introduced.
- def-pc-fibre-product and def-weil-geometric-fibre: `pullback`, `pullback.fst`,
  `pullback.snd`, Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback.
  The orbit clause is the equivalent field-valued-lift expression explained above.
- def-weil-pbc-noetherian-ring: `IsNoetherianRing`,
  Mathlib.RingTheory.Noetherian.Defs, through `IsNoetherian` of
  Mathlib.AlgebraicGeometry.Noetherian and its finite-affine-cover equivalence.
- def-weil-finite-integral-morphism: `IsFinite`,
  Mathlib.AlgebraicGeometry.Morphisms.Finite.
- def-weil-etale-morphism: `Etale`, Mathlib.AlgebraicGeometry.Morphisms.Etale.
- def-weil-surjective-morphism: `Surjective`,
  Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap.
- def-nagata-effective-cartier-ideal:
  `Scheme.IdealSheafData.IsInvertible`,
  WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible.

Statement dependencies are public imports, directly or through their recorded
public dependency modules. The stated proof dependencies are private imports,
including GenericComponentsSplit, FiniteGaloisReceivingSeparableExtensions,
EtaleNormalComponents and FiniteGaloisTensorDecomposition, plus the Mathlib modules
for the morphism and residue-field tools. The flat Cartier-pullback declaration
`Scheme.IdealSheafData.IsInvertible.comap_of_flat` is in the same module that
publicly supplies the Cartier definition. No downstream model theorem is imported.

Edge cases checked before writing:

- B empty: correctly excluded by IsIntegral, as the node requires nonempty B.
- B already geometrically integral: L = e, the only component is all of B and
  the stabilizer can be trivial; u is the identity up to the pullback isomorphism.
- B = Spec K for finite separable K/e: choose a Galois closure L; X = Spec L,
  H = Aut_K(L), and each geometric fibre is the corresponding embedding orbit.
- A scalar automorphism acts trivially on the one-point space Spec L but can
  act nontrivially on its scheme. Faithfulness therefore uses Aut of schemes,
  not an action on topological points alone.
- Imperfect e and positive characteristic: only geometric reducedness and the
  separable component-splitting extension are used; no perfectness assumption.
- Empty Cartier divisor: the unit ideal is IsInvertible, its support is empty,
  and its pullback remains the unit ideal. No nonempty-boundary assumption.
- Trivial H and identity extension are allowed. There is no freeness, torsor
  uniqueness, projectivity or geometric normality conclusion added.
- Universe u is shared by the base field, scheme and test fields, exactly as in
  the recorded geometric-property interfaces. Every finite extension and every
  algebraic closure of a residue field has a representative in this universe.
  No independent smaller universe can make the test-field quantifier vacuous.

Searches for an existing statement (2026-10-22):

- msearch.py leanfinder: “A normal geometrically reduced proper variety has a
  finite Galois extension with a geometrically integral clopen component and
  decomposition group transitive on geometric fibres”. Eight hits, including
  IsGaloisGroup fraction-ring criteria, abstract Galois-category objects and
  Ideal.isPretransitive_of_isGalois; none states the scheme presentation.
- msearch.py loogle: `"GeometricallyIntegral", "IsGalois"`: zero hits.
- msearch.py grep: `Galois.*[Cc]omponent|galois.*[Cc]omponent|[Cc]omponent.*[Gg]alois`
  in Mathlib/AlgebraicGeometry: zero hits.
- msearch.py leansearch: “A normal geometrically reduced proper integral variety
  admits a finite Galois scalar extension with a geometrically integral clopen
  component whose stabilizer is transitive on geometric fibres”. Eight hits on
  ring geometric reducedness, Galois normality and invariant integral closures;
  none is this result. Raw tool queries and results are in searches.jsonl.
- rg with the same component/Galois pattern in lean/WeilConjectures and lean/Sheaf:
  unrelated field-torsor components and abstract Galois-category material;
  EquivariantSmoothGaloisModel cites this result in its proof but does not state it.
  rg for the exact node id in lean/WeilConjectures: no match. I opened the
  parent model statement and the component-splitting and normal-component modules.

No STATEMENT-DISPUTED flag or node fault was found.

## Second reading by NL

Author's second pass; the maintainer's independent review follows delivery, as
specified by this worker brief. I reopened the node and the complete module and
checked the field, integral/nonempty, proper finite type, geometric reducedness,
and stalk normality assumptions against the signature. I checked the chosen
extension and literal pullback, clopen component membership, normality, properness,
geometric integrality, both canonical-action projection laws, component transitivity,
exact stabilizer, restriction equation, scheme faithfulness, finite etale surjectivity,
invariance, genuine geometric-fibre lifts and ideal-level Cartier stability against
each conclusion. The correspondence is detailed above. I specifically checked that
inversion on scalars agrees with categorical Aut multiplication and Spec
contravariance; field faithfulness follows from the exact subgroup representation.
The only implementation corrections were the explicit point-space coercion `↥`
for pullback schemes in topological expressions and removal of redundant finite-type
instance binders implied by properness. Neither changes the mathematical statement.
