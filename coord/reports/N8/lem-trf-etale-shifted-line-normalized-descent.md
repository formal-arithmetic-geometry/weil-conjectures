## Worker report

The delivery states `lem-trf-etale-shifted-line-normalized-descent` without changing
its mathematical statement or dependencies. The module is
`Sheaf.AlgebraicGeometry.EtaleShiftedLineNormalizedDescent`, in namespace
`AlgebraicGeometry.Etale.AffineLineNormalizedDescent`. Its two postponed theorems
are `sheaf_rigidity` (the node's first paragraph) and `normalized_descent`
(the remaining paragraphs). Each carries the corresponding complete proof plan.
Nothing is proved in this stage-2 module.

Four same-node helper definitions make the prescribed maps legible. `lineBaseChange`
is the composite of the inverse-image compositors for q followed by a and for a_T
followed by b; the equality is Mathlib's `AffineSpace.map_over`. `Normalized` is the
literal equality i_1*(kappa) followed by the section compositor = theta.
`LocallyNormalized` uses the existing `sectionRestrictionIso` and asks that it equal
the identity; expanding it cancels the identification i_1'^*q*F = b*i_1*F and b*theta,
so this is exactly the stated local normalization. `comparisonRestriction` conjugates
a restricted local comparison by the two prescribed compositors. All these definitions
have real bodies and require no existence choices or postponed auxiliary assertions.
They are the maps and conditions of this very statement, not independent new notions.

Hypotheses and clauses, matched individually:

| Node text | Lean rendering |
| --- | --- |
| Arbitrary scheme S | `(S : Scheme.{u})`, without geometric hypotheses |
| Finite commutative ring A | `(A : Type (u + 1)) [CommRing A] [Finite A]` |
| X = A^1_S and its projection a | `AffineSpace (ULift.{u} (Fin 1)) S` and its `↘ S` map |
| Unit section t=1 | `AffineSpace.oneSection (ULift.{u} (Fin 1)) S` |
| Small etale sites and ordinary constant-A module inverse images | `Sheaf S.smallEtaleTopology (ModuleCat.{u+1} A)` and `Etale.upperStar` |
| Unbounded derived categories | `DerivedCategoryModule A S`, the recorded upstream abbreviation |
| Locally constant free rank-one L | `Scheme.IsLisseRankOneSheaf L`, whose definition is an etale cover on which L is isomorphic to the constant sheaf with value `ModuleCat.of A A` |
| Automorphism of a*L | `v : (upperStar ... a).obj L ≅ (upperStar ... a).obj L` |
| Its restriction at one is the identity | `hv : (upperStar ... i_1).map v.hom = 𝟙 _`; conjugating by the canonical i_1*a* = id identification leaves the identity fixed, so this is exactly i_1*v = 1_L |
| Rigidity conclusion | `v = Iso.refl _` in `sheaf_rigidity` |
| Arbitrary integer m | `(m : ℤ)` |
| C and F shifted by -m are rank-one sheaves in degree zero | `hC` and `hF` each existentially quantify a sheaf with `IsLisseRankOneSheaf` and `Nonempty (K⟦-m⟧ ≅ (DerivedCategory.singleFunctor _ 0).obj ...)` |
| Specified theta, not a chosen comparison | Explicit isomorphism parameter `θ : i_1*F ≅ C` |
| Given jointly surjective etale cover | `cover : Scheme.Cover.{u} Scheme.etalePrecoverage S` |
| X_i = A^1_{S_i} | `AffineSpace (ULift.{u} (Fin 1)) (cover.X i)` |
| Given local comparisons lambda_i | `localIso i : q_i*F ≅ a_i*((cover.f i)*C)`, with `q_i = AffineSpace.map ... (cover.f i)` |
| Normalization under inverse-image compositors | `hlocal : ∀ i, LocallyNormalized A (cover.f i) θ (localIso i)` |
| Agreement on every overlap | First conclusion: equality of `comparisonRestriction` on `pullback q_i q_j`; `pullback.condition` supplies the common composite. These are actual X_i times_X X_j, canonically the stated affine lines over S_i times_S S_j. `lineBaseChange.symm` places both targets in the restriction of a*C before comparing them. |
| Their inverses agree | Second conclusion explicitly equates `.inv` of those same restricted comparisons |
| Global isomorphism kappa exists | `∃ κ : F ≅ a*C` |
| i_1*kappa = theta | First conjunct `Normalized A S θ κ` |
| It restricts to each lambda_i | Second conjunct: `q_i*.mapIso κ ≪≫ lineBaseChange A (cover.f i) C = localIso i` |
| Uniqueness among every normalized global comparison | Third conjunct quantifies every `κ' : F ≅ a*C` and assumes only `Normalized A S θ κ'`, then concludes `κ' = κ` |
| Independence of normalized local comparisons and cover | Last conjunct quantifies every etale `b : T ⟶ S` and every normalized comparison `μ` over its affine line, and identifies it with the canonical restriction of κ. Applying this to any other cover gives the stated independence; no relation with the given cover is assumed. |

The `.leftDerivedFunctor` used on derived categories is the existing exact inverse
image, canonically identified with `.mapDerivedCategory` by
`Etale.leftDerivedUpperStarIsoMapDerivedCategory`. It introduces no new coefficient
encoding, derived category, or additional exactness assumption.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme` (publicly imported through AffineSpace).
- `def-sbc-affine-space`: its Mathlib match `AlgebraicGeometry.AffineSpace`, its projection,
  `AffineSpace.map`, `AffineSpace.map_over`, and `isPullback_map`, in
  `Mathlib.AlgebraicGeometry.AffineSpace`; the source extension
  `WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace` supplies `oneSection`,
  `oneSection_comp_over` and `oneSection_comp_map`.
- `def-weil-pbc-derived-categories`: recorded module
  `WeilConjectures.AlgebraicGeometry.DerivedCategories`; its imported
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients` defines
  `AlgebraicGeometry.Etale.DerivedCategoryModule` as the unbounded derived category
  of precisely the ordinary module-valued small-etale sheaves used here.
- `prop-weil-pbc-inverse-image-modules-exact`: recorded declaration
  `AlgebraicGeometry.etaleInverseImageModulesExact` in
  `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`, imported for proof.
  Its entire signature and docstring were read, including the canonical constant-ring
  comparison, linear action transport, exactness, adjunction and unit/counit clauses.
  The concrete fixed-coefficient inverse image in the signature here is the existing
  `Etale.upperStar` from `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`;
  no replacement interface is needed.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`, used in covers and independence.
- Proof dependency `new-lem-pur-etale-a1-pullback-full`:
  `AlgebraicGeometry.etale_a1_pullback_full`,
  `Sheaf.AlgebraicGeometry.EtaleAffineLinePullbackFull`.
- Proof dependency `lem-amb-etale-sheaf-hom-family-gluing`:
  `AlgebraicGeometry.Etale.existsUnique_etaleSheafHom_of_family`,
  `Sheaf.AlgebraicGeometry.EtaleSheafHomFamilyGluing`.
- Proof dependency `lem-sf-exact-functor-derived-triangulated`: Mathlib match
  `CategoryTheory.Functor.mapDerivedCategory` and `mapDerivedCategorySingleFunctor`,
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- Proof dependency `lem-weil-pbc-derived-single-fully-faithful`: Mathlib matches
  `DerivedCategory.instFullSingleFunctor` and `instFaithfulSingleFunctor`,
  `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`.
- Proof dependency `lem-weil-pbc-etale-covering-base-change`: its Mathlib precoverage
  base-change instance in `Mathlib.AlgebraicGeometry.Sites.MorphismProperty`.
- Canonical derived comparisons used directly: `Etale.leftDerivedUpperStarComp`,
  `leftDerivedUpperStarCompSectionIso` and `sectionRestrictionIso` in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence` and its imports.
- Existing rank-one predicate: `AlgebraicGeometry.Scheme.IsLisseRankOneSheaf`,
  `WeilConjectures.ConstructibleSheaf.LisseRankOne`. Its full definition and docstring
  were read; no finite generation, field, nonzero-ring, connectedness or Noetherian
  condition is hidden in this predicate.

Edge cases checked before writing and on rereading: S empty (the cover type can be
empty and all overlap quantifiers can be empty); arbitrary nonreduced S; zero ring
A (no Nontrivial instance, no basis-cardinality rank definition excluding zero);
m=0, positive and negative m; disconnected and non-quasi-compact bases; repeated
cover members; the identity etale map and a cover containing the identity. All schemes
use arbitrary universe u, with ordinary coefficient and sheaf universes u+1 as in the
recorded derived-category dependency. No independent smaller test universe appears.

Searches actually run using the prescribed msearch.py wrapper:

- LeanFinder: `Shifted rank one ordinary etale sheaves on affine line have unique descent
  isomorphism normalized at t equals one`. Eight hits, including StandardEtalePair
  algebra statements and `AffineSpace.homOverEquiv`; no normalized-descent statement.
- Loogle: `AlgebraicGeometry.AffineSpace.homOfVector, CategoryTheory.Functor.mapDerivedCategory`.
  Zero hits.
- Mathlib grep: `normalized.*descent|shifted.*line|[Ll]ocally[Ff]ree.*[Rr]ank[Oo]ne`.
  Two unrelated hits: `ShiftedHom.map_smul` and a Lie-weight-space shift.
- Direct rg in both `lean/WeilConjectures` and `lean/Sheaf` for shifted-line,
  normalized-descent, rank-one and affine-line-fullness patterns found the existing
  rank-one predicate, the fullness theorem, and a specialized finite-ring smooth-section
  deformation module. That module's `IsShiftedLine` uses only shift -2d and its
  `existsUnique_normalized` concerns a particular dualizing deformation with Noetherian,
  smoothness and invertibility hypotheses; it does not state this node's arbitrary
  base and arbitrary integer-shift assertion. It is not imported, avoiding a downstream
  dependency. An item-id search in `lean/WeilConjectures` found no declaration. The
  upstream-name record was also searched for this item and the intended names.

Source read: the complete current sk-thm-dnc proof, especially its opening paragraph
and Gluing. Also read the local Stacks sources for `lemma-sections-upstairs` (0A3H),
`lemma-right-derived-exact-functor` (015F), `lemma-negative-exts` (06XS), and
`lemma-glue-maps` (04TQ), matching the node's proof. No statement correction, disputed
statement, new DAG node, dependency repair or proof-import cycle is needed.

Compilation: the first pass caught Lean's reserved lambda token being used as a
binder; it was renamed to `localIso`. The final module compiled cleanly through
scompile.py under both the sandbox and actual module name, with no error or warning
(the stage-2 sorry proofs are expected). No global build or direct compiler was run.

## Second reading by N8

The dispatcher forbids starting another agent. This is a second clause-by-clause
reading in the same worker session; the maintainer supplies the independent review.
I reopened the node, both theorem signatures and all four helper bodies. In
`sheaf_rigidity`, the identity condition on the pulled-back endomorphism is equivalent
to the node's identity after the specified section identification, by conjugation.
In `normalized_descent`, hC and hF use the same arbitrary integer shift -m, theta is
specified, and the cover and its local isomorphisms remain input data. Expanding
`LocallyNormalized` shows precisely i_1*localIso = theta restricted to the cover,
with all section identifications supplied by `sectionRestrictionIso`. Expanding
`lineBaseChange` gives the stated a_i*(C|S_i) target, rather than an arbitrary comparison.
On overlaps both branches use the same composite to X, via `pullback.condition`,
and the separate inverse clause has matching endpoints. The global-uniqueness
quantifier has only normalization as its hypothesis: it does not assume agreement
with localIso. The final universally quantified normalized local comparison gives
independence for every other cover. No missing clause or extra mathematical
hypothesis was found. No definitions contain sorry; the only sorries are the two
named assertions of the same node, both with their proof docstrings. The mathematical
node fields are unchanged, and all six module declarations are recorded.
