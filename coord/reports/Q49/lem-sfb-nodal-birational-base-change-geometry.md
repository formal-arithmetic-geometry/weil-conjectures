## Worker report

The delivery states `AlgebraicGeometry.nodal_birational_base_change_geometry` in
`Sheaf.AlgebraicGeometry.NodalBirationalBaseChangeGeometry`. Its only theorem proof is
`sorry`. There are no new definitions, new nodes, dependency repairs, statement corrections,
or disputed statements. Only the item's `lean` field changes.

Hypothesis correspondence, in the order of the node:

- The field is `(F : Type u) [Field F]`. All schemes have universe `u`.
- The finite-type integral F-scheme S is `(p : S ⟶ Spec (.of F)) [IsIntegral S]`,
  `[LocallyOfFiniteType p] [QuasiCompact p]`. The explicit structure map is used because
  the statement involves the base-change diagram and semilinear actions.
- The named family is `f : T ⟶ S`; `hf : IsProjectiveBundle f` is exactly the recorded
  projective-bundle convention, with a finite-type quasi-coherent module, not necessarily
  locally free. It is not replaced by H-projectivity.
- Flatness is `[Flat f]`. Finite presentation is `[LocallyOfFinitePresentation f]`,
  `[QuasiCompact f]`, and `[QuasiSeparated f]`.
- `hnodal : HasNodalGeometricFibres f` tests all algebraically closed fields in the scheme
  universe, and includes nonemptiness, connectedness, topological dimension one, and
  the specified completed local rings at nonsmooth points. `[GeometricallyReduced f]`
  supplies the separately stated reducedness. Reducedness of all field-valued fibres is
  equivalent to reducedness of all algebraically closed geometric fibres by faithfully
  flat field extension; no integrality of special fibres is assumed.
- `hgeneric` supplies a generic point eta of S, smoothness and geometric integrality of
  `f.fiberToSpecResidueField eta`. This is the ordinary generic fibre with its structural
  map, not the geometric fibre substituted for it.
- `D : Closeds S` is an arbitrary closed subset. `hsmooth` is smoothness of `f ∣_ U`
  for the open complement U of D.
- `i : M ⟶ T` is a closed immersion. The marking is recorded by `n : ℕ`, sections
  `s : Fin n → (S ⟶ T)`, their section equations `hs`, the scheme isomorphism
  `eM : (∐ fun _ : Fin n ↦ S) ≅ M`, and `hM` identifying every coproduct inclusion
  followed by `eM.hom ≫ i` with its named section. Since i is a closed immersion, this
  really is a disjoint union of sections as a closed subscheme. `hmark` puts each section
  image in the relative smooth locus. There is no condition `0 < n`.
- `t : S₀ ⟶ S`, `ht : IsProjectiveBundle t`, `[Surjective t]`, `[IsIntegral S₀]`, and
  `[Smooth (t ≫ p)]` give exactly the base modification and its smooth F-structure.
- `hbirational` supplies dense open subschemes of S and S0 and an isomorphism commuting
  with t. Since both schemes are integral, it identifies their function fields; the
  node's equal-function-fields clause is part of this geometric characterization, not
  an unrelated abstract field isomorphism.

Conclusion correspondence:

- W is the actual scheme `pullback (C := Scheme.{u}) f t`, with
  `g = pullback.snd f t`, `q = pullback.fst f t` throughout. There is no substitute
  model or chosen comparison map.
- The four `IsNoetherian` conjuncts give locally Noetherian and quasi-compact, exactly
  Mathlib's `IsNoetherian`. Four pairs of `LocallyOfFiniteType` and `QuasiCompact`
  give finite type over F for p, t followed by p, f followed by p, and g followed by
  t followed by p. The already-assumed S clause is retained because the node lists all
  four schemes in this conclusion.
- `IsIntegral T` and `IsIntegral W` give the two asserted integral total spaces.
- Each of g and q has both `IsProjectiveBundle` and `IsProper` conjuncts.
- The g conjuncts are flatness; local finite presentation, quasi-compactness and
  quasi-separatedness (finite presentation); `HasNodalGeometricFibres`; and
  `GeometricallyReduced`. The smooth-restriction conjunct uses precisely the complement
  of `t ⁻¹' D`. The existential eta0 conjunct gives a smooth geometrically integral
  generic fibre over S0.
- M0 is `pullback i (pullback.fst f t)` with its closed immersion
  `pullback.snd i (pullback.fst f t)` into W. `e₀` identifies M0 with the finite
  coproduct of S0, and the equations for its inclusions identify them with the canonical
  sections `f.baseChangeSection (s j) (hs j) t`. The following conjuncts state their
  section equations, pairwise disjointness and relative smooth-locus containment.
  Thus both the scheme structure of M0 and the actual base-changed sections are retained.
- The two universal open-set conjuncts state the inverse-image density assertions for
  f and g. The following dense-open isomorphism commutes with q and gives its birationality
  and identification of function fields; `Surjective (pullback.fst f t)` gives surjectivity.
- The last conjunct is conditional on an arbitrary finite group `J : Type v`, with
  actions `aF`, `aS`, `aT`, `a₀`. The equation involving `Spec.map (aF j⁻¹)` expresses
  semilinearity for S. The f and t equivariance equations imply the same compatibility
  for T and S0 with their displayed structure maps. No field action is required trivial
  or faithful. The next two assumptions are preservation of D and M.
- The action `aW : J →* Aut W` satisfies both projection equations. The pullback universal
  property uniquely determines every `aW j` from these equations, so this is precisely
  the diagonal action, not an arbitrary action. The last two conclusions are preservation
  of the pulled-back marking and of its union with `g ⁻¹' (t ⁻¹' D)`.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and `Morphisms.QuasiCompact`, `QuasiCompact`.
- `def-trf-projective-bundle-morphism`: `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`,
  `AlgebraicGeometry.IsProjectiveBundle`.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `AlgebraicGeometry.Flat`.
- `def-sbc-locally-finite-presentation`: `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`, with `QuasiCompact` and `QuasiSeparated`
  for the finite-presentation comparison clause.
- `def-trf-nodal-geometric-fibres`: `Sheaf.AlgebraicGeometry.NodalGeometricFibres`,
  `AlgebraicGeometry.HasNodalGeometricFibres`, read in full, including its universe and
  completed-local-ring test.
- `def-weil-geometric-fibre` and `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`; `Mathlib.AlgebraicGeometry.Fiber`
  supplies `Scheme.Hom.fiberToSpecResidueField` for the generic fibre.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth` and `Scheme.Hom.smoothLocus`.
- `def-pc-geometrically-irreducible`: `Mathlib.AlgebraicGeometry.Geometrically.Integral`
  and its imported Reduced module, `GeometricallyIntegral` and `GeometricallyReduced`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian` and `IsNoetherian`.

Other existing canonical constructions are `Sigma.ι` and the scheme coproduct from
`Mathlib.AlgebraicGeometry.Limits`, `CategoryTheory.Aut`, and
`AlgebraicGeometry.Scheme.Hom.baseChangeSection` from
`WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChangeSection` (its implementation
is `pullback.lift (b ≫ s) (𝟙 B')` with the section equation). No private copy is introduced.

Proof-only imports retain the available plan: `ProjectiveBundleBaseChange`,
`Sheaf.TraceFormula.ProjectiveBundleProper`, `BirationalGenericIsomorphismOpen`,
`WeilConjectures.AlgebraicGeometry.AffineFibreSectionsTensor`, Mathlib
`Morphisms.UniversallyOpen` and `RingTheory.Flat.TorsionFree`. The remaining proof leaves
are provided by the already imported Mathlib modules for finite type, Noetherianity,
flatness, finite presentation, properness, pullbacks and closed immersions. No import cycle
is introduced.

Edge cases checked: n = 0 gives the empty coproduct and empty M, and e0 asserts the same
for M0. D can be empty or the whole base; its complement then gives respectively the
whole-base or empty smooth restriction. The integral bases are nonempty as required by the
node; no empty case the node allows is excluded. No restriction on characteristic, perfectness
of F, faithfulness or triviality of actions, dimension of the base, or smoothness of special
fibres was added. In particular, nodal reducible special fibres remain permitted. The group
universe v is independent; geometric-fibre tests use exactly the recorded scheme universe u.

Sources checked: ILO PDF, printed pp.149–150 (PDF pages 155–156), especially the last paragraph
on p.149 describing successive equivariant projective modifications of marked nodal curves;
the current blueprint's direct-images proof; and the node's nine expanded geometry steps.
No source-based statement correction was needed. This item is an auxiliary geometry lemma,
not the blueprint unit's statement.

Searches for an existing statement (Q49, this item, via msearch.py):

- LeanFinder: `A flat projective nodal curve with smooth geometrically integral generic fibre
  remains integral under a projective birational base change`. Eight hits concerned
  Weierstrass integral models or integral morphisms; none is this statement.
- Loogle: `AlgebraicGeometry.Flat, AlgebraicGeometry.IsIntegral`. Four hits included
  `GeometricallyIntegral.isIntegral_of_isLocallyNoetherian` and its pullback instances.
  They assume all fibres geometrically integral, so cannot replace this result.
- Mathlib grep: `integral.*generic|generic.*integral|birational` in AlgebraicGeometry.
  Nine hits concerned rational maps, scheme birationality and generic-point function-field
  lemmas; no marked nodal base-change package.
- LeanSearch: `flat nodal curve integral generic fibre birational base change integral total
  space`. Eight hits concerned Weierstrass models and integral morphisms; no match.
- Direct project searches: `nodal.*birational|birational.*nodal` in `lean/Sheaf` and
  `lean/WeilConjectures` found the finite-birational-map-to-a-nodal-curve lemma, a different
  result. The exact item id has no match in `lean/WeilConjectures`. Searches for the
  declaration name in Mathlib, the two project source trees and `dag/lean_names_upstream.json`
  found no existing declaration. Searches for markings and base-changed sections led to
  the recorded nodal predicate and the upstream canonical `baseChangeSection`, which are reused.

Validation: scompile.py typechecked the theorem after adding explicit `C := Scheme.{u}`
to pullbacks used as underlying spaces (otherwise Lean inferred the category of types).
The subsequent compile's sole style warning was a 103-character line; that line was wrapped
before the final dry run. No mathematical signature change was needed.

## Second reading by Q49

This is a second pass by the same dispatcher-started worker; no independent agent was
started, as required by the launcher brief. Independent mathematical review is the
maintainer's delivery review.

Reopened the node and Lean file and checked the correspondence above clause by clause:
field, finite-type integral base; projective-bundle flat finitely presented family; nonempty
connected reduced dimension-one nodal geometric fibres; smooth geometrically integral generic
fibre; closed boundary and smooth complement; actual closed marking as a finite disjoint
coproduct of sections in the smooth locus; projective birational surjective smooth integral
base modification. All appear in the binders. Checked that the marking isomorphism commutes
with each section, so it encodes the subscheme and not just equality of supports.

Checked every output: all four Noetherian/finite-type assertions; both total spaces integral;
both projections projective and proper; all fibre, finite-presentation and smoothness clauses
for g; the actual pullback marking and its canonical sections; both density clauses;
birationality and surjectivity of q; compatible arbitrary finite semilinear group actions;
both projection equations and both invariance clauses. Parentheses enclose the whole action
implication and boundary union. Empty n and D are admitted. Dense-open isomorphisms commute
with t and q, respectively, so their function-field identifications are the induced ones.
No added assumptions or missing clauses were found. The only repairs during this pass were
the category annotation at underlying pullback spaces and the line wrap noted above.
