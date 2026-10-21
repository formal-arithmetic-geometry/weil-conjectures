## Worker report

Item: `lem-weil-pbc-kinjective-fiber-triangle-comparison`, group Q110, stage 2.
Module: `Sheaf.CategoryTheory.KInjectiveFiberTriangleComparison`.
The node is unchanged except for `lean`. No dependency repair or new node is needed.
All three theorem proofs are `sorry`; the six auxiliary definitions have real data.
Their declarations are all recorded in `lean.declarations`.

The statement is rendered by three declarations, all in `CategoryTheory`:
`existsUnique_unitNormalizedKInjectiveShift`, `kInjectiveFiberTriangle_comparison`,
and `kInjectiveFiberTriangle_comparison_naturality`. The main recorded declaration
is the second. Each theorem retains the initial hypotheses of the node; the second
and third use the shift furnished by the first. The final theorem takes the
K-injectivity proofs of the two fibres furnished by the second.

Hypothesis and clause audit:

- Abelian categories A and B: `{A : Type uA} [Category.{vA} A] [Abelian A]`
  and the corresponding B binders. Object, morphism, and derived-localization
  universes are explicit and independent on the two sides.
- Ordinary unbounded derived categories and their localization functors:
  `[HasDerivedCategory.{wA} A]`, `[HasDerivedCategory.{wB} B]`,
  `DerivedCategory A`, `DerivedCategory B`, and `DerivedCategory.Q`.
  Complexes are `CochainComplex A ℤ`; no boundedness is imposed.
- Every A-complex has a K-injective resolution: `hA` is exactly
  `∀ K, ∃ J i, J.IsKInjective ∧ QuasiIso i`. Mathlib's `IsKInjective`
  is literally the null-homotopy condition for maps from acyclic complexes.
- The additive functor is `(G : A ⥤ B) [G.Additive]`.
  Preservation of K-injectives is `hG`, with the termwise functor
  `G.mapHomologicalComplex (ComplexShape.up ℤ)`.
- The fixed derived functor is `RG : DerivedCategory A ⥤ DerivedCategory B`.
  The unit `η` has source the termwise G followed by Q_B, and target Q_A
  followed by RG. `hUniversal` is exactly bijectivity of composition with
  this unit for natural transformations from RG to every functor F.
  `hη` asserts invertibility at every K-injective complex.
  This is the complex-level form of the recorded dependency's homotopy-level
  unit: use `G.mapHomotopyCategoryFactors` and `DerivedCategory.quotientCompQhIso`.
  Precomposition with the homotopy quotient gives a bijection on these natural
  transformations, since every object has a complex representative and quotient
  morphisms are chain maps modulo homotopy. Thus neither the fixed unit nor its
  universal property is replaced by additional data or an extra hypothesis.
- The unique natural shift is an actual natural isomorphism
  `σ : shiftFunctor (DerivedCategory A) 1 ⋙ RG ≅ RG ⋙ shiftFunctor (DerivedCategory B) 1`.
  `∃! σ, IsUnitNormalizedKInjectiveShift G RG η σ` asserts existence and uniqueness.
  This predicate writes the normalization for EVERY complex K, spelling out
  the termwise G-shift comparison and the Q_A/Q_B shift identifications.
  When K and K[1] are K-injective, cancellation of their invertible units
  identifies σ with the termwise shift comparison under the unit isomorphisms.
- P, P' and their K-injectivity: `P`, `P'`, `hP`, `hP'`.
  Endomorphisms: `u : P ⟶ P`, `u' : P' ⟶ P'`.
  The fixed chain isomorphism: `c : (G.mapHomologicalComplex _).obj P ≅ P'`.
  Its endomorphism square is `hc : G(u) ≫ c.hom = c.hom ≫ u'`, the node's
  `c G(u) = u' c` in Lean's left-to-right composition convention.
- `kInjectiveFiberTriangle u` is the inverse rotation of
  `CochainComplex.mappingCone.triangle u`. Its objects are exactly
  `Cone(u)[-1]`, P, P, so H is not replaced by an abstract cone object.
  Mathlib's cone uses the opposite order of the two summands: its shifted
  coordinates are `(x,y)`. Reordering to the node's `(y,x)` gives
  `H^r = P^(r-1) ⊕ P^r`, differential `(-dy-ux,dx)`.
  The inverse rotation cancels the negative cone projection, yielding
  `r(y,x)=x`; the connecting map is the cone inclusion `b(z)=(z,0)` with
  the canonical `Cone(u)[-1][1] ≅ Cone(u)` identification. The same applies
  with primes. We reuse this existing construction rather than define a
  second coordinate complex or a second cone convention.
- K-injectivity of H, H' and G(H) is the first existential proof `hH` and
  the next two conjuncts in `kInjectiveFiberTriangle_comparison`.
- The actual θ is `(kInjectiveFiberChainComparison G u u' c hc).hom₁`.
  The definition composes the inverse of `mapTriangleInvRotateIso` with
  the inverse rotation of `mappingCone.mapTriangleIso` followed by
  `mappingCone.triangleMap ... c.hom c.hom hc`. Thus the coordinates are
  canonically `(cy,cx)` after the additive biproduct comparison, not a
  freely chosen isomorphism. Its `IsIso` conjunct gives the asserted chain
  isomorphism. Equality of the second and third components with `c.hom`
  is stated explicitly.
- Both chain squares follow from this actual triangle morphism's `comm₁`
  and `comm₃` fields, together with those explicit component equalities.
  The third field includes exactly the canonical termwise shift comparison,
  since the source is `G.mapHomologicalComplex.mapTriangle` of the fibre triangle.
- The original A-localized fibre triangle and the target B-localized fibre
  triangle are asserted distinguished, as is the RG-image triangle.
  `kInjectiveDerivedFiberTriangle RG σ u` uses RG on the first two arrows
  and RG of the Q-localized connecting arrow followed by σ on the last.
- `kInjectiveInverseUnit ... K hK` is `(asIso (η.app K)).symm`, with the
  isomorphism instance supplied explicitly by `hη`. Its data is determined
  by the invertible unit. The `e.hom.hom₂` and `e.hom.hom₃` equations say
  exactly `bar-c = eta_P^{-1} ≫ Q(c)`. The `e.hom.hom₁` equation says
  `Theta = eta_H^{-1} ≫ Q(theta)`. These are the node's formulas in Lean order.
- The existential `e` is an isomorphism of precisely the source and target
  triangles just specified. Its morphism fields supply all three squares.
  The final conjunct additionally spells out its connecting square:
  `source.mor₃ ≫ e.hom.hom₁⟦1⟧' = e.hom.hom₃ ≫ target.mor₃`.
  Expanding the definitions and the component equations gives exactly
  `Theta[1] sigma_(QH) RG(Qb) = Q(b') bar-c`, including the Q-shift maps.
- Naturality uses a second diagram R,R',v,v',d and commuting chain maps
  `a : P ⟶ R`, `a' : P' ⟶ R'`. `ha`, `ha'` express endomorphism
  commutation; `hca` is `v' c = c_tilde G(v)` in the node's notation.
  `kInjectiveFiberTriangleMap` is the existing diagonal cone map shifted
  by inverse rotation, so its components give the specified h and h'.
  The three conjuncts of the naturality theorem are respectively
  `G(h) ≫ theta_tilde = theta ≫ h'`,
  `RG(Qh) ≫ Theta_tilde = Theta ≫ Qh'`, and
  `RG(Qa) ≫ bar-c_tilde = bar-c ≫ Q(a')`.
  The repeated bar-c gives the remaining triangle component, and naturality
  of the actual natural isomorphism σ gives naturality of the connecting maps.
- There is no exactness assumption on G, nor enough K-injectives in B.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`.
- `def-weil-abstract-derived-category`: `HasDerivedCategory`, `DerivedCategory`,
  `DerivedCategory.Q`, `DerivedCategory.Qh`, `quotientCompQhIso`, their shift
  instances and distinguished triangle structure,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `def-weil-pbc-additive-functor`: `CategoryTheory.Functor.Additive`,
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`.
- `lem-weil-pbc-kinjective-total-derived`:
  `CategoryTheory.exists_rightDerived_of_enough_isKInjective`,
  `Sheaf.CategoryTheory.KInjectiveTotalDerived`, imported as a proof dependency.
  Its full signature and proof plan were read. The present statement fixes RG and
  its unit, as the node requests; its universal property is retained explicitly.
- `def-weil-triangulated-category`: `Pretriangulated`, `IsTriangulated`,
  `Triangle`, `Triangle.invRotate`, `distTriang`, and triangulated functor APIs
  from `Mathlib.CategoryTheory.Triangulated.*`.
- `lem-weil-pbc-kinjective-hom-derived`:
  `CochainComplex.IsKInjective.Qh_map_bijective`,
  `Mathlib.Algebra.Homology.DerivedCategory.KInjective` (proof plan).
- `lem-weil-pbc-kinjective-shift`:
  `CochainComplex.instIsKInjectiveObjIntShiftFunctor` and `isKInjective_shift_iff`,
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective` (proof plan).

Canonical construction APIs read in full:
`CochainComplex.mappingCone.triangle`, `triangleMap`, `mapTriangleIso`,
`mapHomologicalComplexIso`, `Functor.mapTriangleInvRotateIso`, and
`Pretriangulated.invRotate`. They supply exactly the biproduct, diagonal,
rotation and shift maps needed here. No existing exact-functor descent is used
with an extra exactness assumption.

Sources opened locally: Stacks `derived.tex`, the actual text at
`lemma-triangle-K-injective` (090X), `lemma-derived-shift` (05SU),
`lemma-K-injective-defined` (070Y), and `lemma-enough-K-injectives-implies` (070K).
Also opened the current main-20261015 proof of `prop-weil-pbc-direct-image-limits`,
the paragraph applying direct image to the canonical Roos triangle. Its unit
statement is not being changed.

Edge cases checked before and after writing: P=0 and P'=0; u=0 (the fibre is
P[-1] ⊕ P); u=id (contractible fibre); G=0; G=id and c=id; zero commuting
maps of diagrams; arbitrary unbounded complexes, including non-K-injectives in
the normalization clause. Negative-degree shifts have the signed differential,
and inverse rotation cancels the negative cone projection. None of these cases
is excluded by a nonzero condition, boundedness, extra exactness, a restricted
index universe, or an assumed invertible unit at a non-K-injective complex.

Searches performed (2026-10-21):

- `msearch.py leanfinder`: “Unit normalized shift of a right derived additive
  functor and its natural mapping fibre triangle comparison on K injective
  complexes”. Eight hits, including `Functor.mapDerivedCategoryFactorsh` and
  `mappingCone.mapTrianglehIso`. Those give exact-functor descent or ordinary
  termwise cone comparison, not this universal-unit-normalized unbounded statement.
- `msearch.py loogle`: `CochainComplex.mappingCone.mapTriangleIso,
  CategoryTheory.Functor.totalRightDerivedUnit`. Zero hits for the combined query.
- `msearch.py grep`: `mappingCone.*map|CommShift|IsRightDerivedFunctor` in
  `Algebra/Homology/DerivedCategory`. Twenty-five hits; the exact-functor shift
  instances require more than additivity. The ordinary cone and shift APIs
  were reused directly.
- `msearch.py leansearch`: “K injective right derived functor normalized shift
  natural mapping fibre triangle comparison”. Eight hits; ordinary right-derived
  functors on objects/injective resolutions and the existing K-injective shift
  instance, with no full matching statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `fiberTriangle|fibreTriangle|mapTriangleIso|kinjective-fiber-triangle-comparison|
  unit.*[Nn]ormal.*[Ss]hift`: unrelated triangle/unit comparisons and ordinary
  mapping-cone isomorphisms; no declaration of this node. Exact item-id grep in
  `lean/WeilConjectures` and `dag/lean_names_upstream.json` gave no match.
- Exact proposed declaration names searched in both project roots and Mathlib:
  no prior declaration. All six helpers specialize existing constructions to
  objects/maps already introduced in this node; they introduce no independent
  missing notion requiring a new definition node.

No `STATEMENT-DISPUTED` issue or node correction. No additional dependency node,
new definition node, target edit, live source edit, or direct git command.
All compilation used the prescribed `scompile.py` wrapper, each file separately,
under its unchanged 60-second limit. Earlier drafts and the full naturality draft
compiled without warnings after correcting one parenthesis and the explicit
`CochainComplex.IsKInjective` spelling for termwise complex images.

## Second reading by Q110

Self-audit by the dispatched worker, reopening the node and the completed module;
this is not a claim that another worker reviewed it. The prompt prohibits starting
agents and assigns the independent review to the maintainer after delivery.
The clause-by-clause audit above checks every hypothesis and conclusion. During
this read, the original source triangle's distinguished status and the explicit
equalities of the chain comparison's last two components with c were added, so
neither is left only in prose. The naturality theorem includes both localized
comparison components, not just the chain comparison. All three theorem signatures
retain hA, hG and the unit's universal property; the node statement is unchanged.
