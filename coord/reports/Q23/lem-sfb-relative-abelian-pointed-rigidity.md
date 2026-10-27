## Worker report

Item: `lem-sfb-relative-abelian-pointed-rigidity`; group Q23; 2026-10-24 UTC.
Module: `Sheaf.AlgebraicGeometry.RelativeAbelianPointedRigidity`.

The module states the two conclusions of the node, with `sorry` as each theorem's
entire proof. It also defines the actual base-change map needed to express their
base-change clauses. This helper constructs a map using the existing fibre-product
pairing, projection, and terminal-base equality; it does not choose a map or a group
structure. Its only nontrivial proof obligation is the already recorded terminal-base
uniqueness theorem `Poincare.baseMap_eq`. That theorem determines an equality, not
unconstrained data. The module contains no new postponed auxiliary theorem.

The main declaration is
`AlgebraicGeometry.AlgebraicSpace.relativeAbelian_pointed_rigidity`.
The other conclusion is
`AlgebraicGeometry.AlgebraicSpace.relativeAbelian_two_axis_vanishing`.
The helper is `AlgebraicGeometry.AlgebraicSpace.relativeAbelianBaseChangeMap`.
All three declarations carry this item's blueprint id and source docstrings.

Hypothesis and clause correspondence:

- The base is `(S : Scheme.{u}) [IsLocallyNoetherian S]`. These are the recorded
  declarations of `def-pc-scheme` and `pqf-def-locnoeth`.
- The objects are `(A B : AlgebraicSpace S)`, with `C` in the two-axis theorem.
  This is exactly the full subcategory of fppf sheaves with representable diagonal
  and an etale surjective scheme atlas, from `def-trf-algebraic-space`. A morphism
  `a : A ⟶ B` is an arbitrary natural transformation, not a group homomorphism
  supplied in advance. Similarly `v` is an arbitrary map from the sheaf product.
- The specified commutative group operations are `(g : CommutativeSpaceGroup A)`
  and `(h : CommutativeSpaceGroup B)`, and `k` for `C`. This existing structure is
  a commutative group law on each scheme-test value with natural restriction.
  It supplies multiplication, inverse, and the identity section. The convention is
  multiplicative Lean notation for the additive group laws in the node.
- `hA : IsAbelianFamily (groupSpaceProjection A)` and `hB`, and `hC` for the other
  theorem, impose exactly properness, smoothness, finite presentation, and abelian
  geometric scheme fibres. Unfolding the recorded predicate gives `MapIsProper`,
  `MapIsLocally (@Smooth)`, `MapIsLocallyOfFinitePresentation`, and `HasAbelianFibres`.
  `MapIsProper` is separated, finite type, and universally closed, exactly as the
  node spells out; `MapIsLocally` tests every compatible pair of etale scheme charts.
  Properness includes quasi-compactness and separatedness; hence local finite
  presentation here gives finite presentation, including quasi-separatedness, as
  explicitly specified in the owning definition node. `HasAbelianFibres` quantifies
  over algebraically closed fields in the scheme universe and actual pullback
  squares represented by `Z : Over (Spec K)` with `IsAbelianVariety Z`. The latter
  is proper, smooth, connected; the given natural group law is inherited by the
  represented fibre. Over an algebraically closed field this is the requested
  geometrically connected group scheme. No representability of the whole family
  by a scheme is assumed.
- `ha : g.identity ≫ a = h.identity` is exactly `u ∘ e_A = e_B`.
- The first conclusion `IsHom g h a` asserts preservation of identity and
  multiplication on every scheme test, for those same specified group laws.
- The second conclusion is the requested morphism equality
  `addition A g ≫ a = productMap ... a a ≫ addition B h`.
  `addition` is the actual natural multiplication map on the existing sheaf product;
  `productMap` is its canonical product map. Thus this is exactly
  `u ∘ m_A = m_B ∘ (u ×_S u)`.
- The final main conjunct quantifies over every `(T : Over S)` with
  `[IsLocallyNoetherian T.left]`. It equates the actual base-change maps of both
  composites. The helper sends the source coordinate through the given map and
  leaves the `T` coordinate unchanged. Its domain and codomain are the existing
  sheaf fibre products with `h_T → h_S`, so this is precisely the pulled-back
  identity over `T`. In particular `T` may be nonreduced; no flatness or etaleness
  of `T → S` is imposed. The theorem itself is uniform in `S`, also covering every
  locally Noetherian base directly.
- For the last clause of the node, `v` has source
  `product (groupSpaceProjection A) (groupSpaceProjection B)`, exactly `A ×_S B`.
  `hvA` restricts along `rightAxis (pointedGroup A g) (pointedGroup B h)`, namely
  `(1,e_B)`, and `hvB` along `leftAxis ...`, namely `(e_A,1)`. Their right sides
  are respectively `groupSpaceProjection A ≫ k.identity` and
  `groupSpaceProjection B ≫ k.identity`: both are the genuine zero morphisms.
  The conclusion equates `v` to the product's structure map followed by
  `k.identity`, exactly `v = 0`. Its second conjunct gives the actual base change
  of this same equality for every locally Noetherian `T`.
- There is no reducedness hypothesis on any base. Equalities of full natural
  transformations retain nilpotent information; equality only on geometric points
  would be insufficient and is not used as a replacement statement.

Dependency declarations used:

1. `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
   Read the full structure declarations and docstrings.
2. `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
   Read the class: all affine open coordinate rings are Noetherian, equivalent to
   the affine-cover definition as the dependency's record explains.
3. `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`;
   read its complete definition and `IsAlgebraicSpace`, `IsRepresentableWith`, and
   the morphism conventions from the full subcategory.
4. `Sheaf.AlgebraicGeometry.AbelianSpacePoincareData`, namespace
   `AlgebraicGeometry.AlgebraicSpace.Poincare`: `IsAbelianFamily`, `HasAbelianFibres`,
   `product`, `fst`, `snd`, `pair`, `pointedGroup`, `addition`, `IsHom`, `productMap`,
   `baseMap_eq`, `leftAxis`, and `rightAxis`. Read their signatures, bodies, and
   docstrings. Their owning node `def-sfb-abelian-space-poincare-data` already
   landed and is added to `stmt_deps`, as authorized for a landed notion. Its
   dependencies provide `CommutativeSpaceGroup`, `groupSpaceProjection`,
   `groupSpaceBase`, `groupSchemeMap`, and `CommutativeSpaceGroup.identity` in
   `Sheaf.AlgebraicGeometry.RegularGroupSpace`; read those full definitions too.
   Read the chartwise proper/smooth/lfp definitions in
   `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties` and the upstream
   `IsAbelianVariety` in `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`.

Plain proof imports cover all currently stated proof dependencies:
`Mathlib.AlgebraicGeometry.Morphisms.Smooth` (smooth-flat),
`WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic` (geometric integrality),
`WeilConjectures.AlgebraicGeometry.AbelianVariety.Rigidity` (field rigidity), and
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality` (base-change locality).
The algebraic-space definition is already public. At this reading,
`lem-sfb-rigidified-space-picard`, `lem-sfb-proper-space-finite-image-neighbourhood`,
and `lem-sfb-space-affine-target-global-functions` have no recorded Lean declarations;
these are proof prerequisites, not notions needed to state this item, so there is
no corresponding proof import yet. Their uses are retained in the proof docstring.

Edge cases checked before writing:

- The empty base is allowed. There is no `Nonempty S` or field assumption on `S`.
  Over an empty base the assertions are equalities in the corresponding terminal
  sheaf situation. Empty fibres over a genuine geometric point are excluded by
  the group identity and by `IsAbelianVariety`, as in the source.
- Zero-dimensional abelian varieties, the trivial group family, identity maps,
  and zero maps are included. No positivity of dimension or polarization is assumed.
- Both axes are required; a projection followed by a nonzero map can vanish on
  only one axis. The Lean statement therefore retains each independent restriction.
- Nonreduced locally Noetherian bases, including dual-number bases, satisfy the
  binder without additional reduction. Positive and zero characteristic are both
  allowed; no invertibility or characteristic restriction appears.
- Scheme and field tests use the same explicit `u` as `Scheme.{u}`, following the
  recorded framework. No independent smaller test universe makes the fibre or
  base-change quantification vacuous. The base-change scheme need not be affine,
  flat over the base, finite type over it, or etale over it.

Searches for an existing statement or notion (2026-10-24):

- `msearch.py ... leanfinder`: “Every identity preserving morphism of proper smooth
  commutative group algebraic spaces with abelian variety geometric fibres is a
  group homomorphism”. Eight hits: smooth dimension-zero multiplicativity,
  `CommGrpCat` trivial morphisms/identities, and affine-space maps. No match.
- `msearch.py ... loogle`: `"rigidity", "AlgebraicGeometry"`. Zero hits.
- `msearch.py ... leansearch`: “A pointed morphism of abelian schemes is a
  homomorphism over an arbitrary base”. Eight hits: `Pointed.Hom` constructors,
  base-point preservation, and affine-scheme morphisms. No relative rigidity.
- `msearch.py ... grep`: `rigidity|AbelianScheme|abelian_scheme`. Four hits in
  intermediate-value and complex-manifold files; no algebraic-space assertion.
- `rg` of `lean/WeilConjectures` for rigidity and abelian/pointed names found
  the field rigidity theorem `exists_eq_snd_comp`, not this relative theorem.
  Searching the item's id there returned no occurrences.
- `rg` of `lean/Sheaf` found the downstream Poincare-calculus docstring citing
  this node, and, crucially, the landed `AbelianSpacePoincareData` notions. Those
  definitions are reused. `rg` in Mathlib, `WeilConjectures`, `Sheaf`, and
  `dag/lean_names_upstream.json` found no collision for any delivered name.
- `tools/blueprint_refs.py search 'pointed morphisms'`: zero blueprint matches.
  DAG searches identify this exact item and its Poincare-calculus consumer; the
  landed Poincare data node carries all required notions. No new definition node
  or dependency replacement is needed.

Source reading: read Milne I Theorem 1.1 and Corollary 1.2 in the supplied PDF,
printed pp.8--9. The theorem is the two-axis collapse and the corollary uses the
additivity defect. The relative argument in the node explicitly strengthens the
field argument with universal functions and finite-image neighbourhoods; it is
copied step by step into the theorem docstring, not replaced by equality on
geometric fibres. The node labels GIT Proposition 6.1 WANTED; no claim is made to
have read that unavailable reference. The latest blueprint pointer is the
2026-10-24 snapshot; no blueprint unit statement is being changed.

No statement correction, disputed statement, new node, or dependency-module repair.
The only item changes are `lean` and addition of the already landed Poincare data
node to `stmt_deps`. Every theorem body is `by sorry`; the helper has real data.

Validation: `scompile.py Q23 lem-sfb-relative-abelian-pointed-rigidity <module>`
compiled both sandbox and library module names cleanly, 1.9 s each; no errors or
warnings were reported. All variables and universes are explicitly bound with
`autoImplicit false` and `relaxedAutoImplicit false`.

## Second reading by Q23

I reopened the node and the complete delivered module for a separate second pass.
The main theorem's group laws belong to the same `A` and `B` as its abelian-family
hypotheses; its input map is arbitrary, and pointedness is its only map condition.
`IsHom` is a conclusion, not an assumption. The displayed equality uses the
published addition and product map for those very laws. In the other theorem the
axis named `rightAxis` actually has source `A`, while `leftAxis` has source `B`;
I checked the definitions to ensure the two zero restrictions use the correct
source structural maps. The zero on the product is the first projection followed
by the base map and the given `C` identity, so it is a genuine constant morphism.
The base-change helper's second coordinate is exactly `snd`, and its first is
exactly `fst ≫ f`; the terminal-base proof supplies only their compatibility.
Thus its equalities are the real pulled-back equalities. Each base-change binder
allows every locally Noetherian scheme over `S`, including identity and iterated
base changes. Properness already supplies the missing global parts of finite
presentation; no extra finite-presentation hypothesis is needed or dropped.
No mismatch found and no statement change made. This is a second pass by the same
worker; the dispatcher's instructions prohibit starting another agent. The
maintainer's independent review remains the independent reading of this delivery.
