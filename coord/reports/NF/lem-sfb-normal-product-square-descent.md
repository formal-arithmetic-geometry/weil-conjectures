## Worker report

Item: lem-sfb-normal-product-square-descent. The module
`Sheaf.AlgebraicGeometry.NormalProductSquareDescent` states
`AlgebraicGeometry.Scheme.Modules.normal_product_square_descent` with one `sorry`.
It also gives four concrete helpers belonging to this same construction:
`squareParameter`, `squareCoordinate`, `squareDifference`, and `squareProjection`.
All data are built from existing products, projections, tensor pullbacks, internal
Hom and tensor products; no arbitrary map, choice of a line bundle or postponed
construction is introduced. The node's statement and dependencies are unchanged.

Source read: Guo, *Divisors on coherent schemes and homogeneous spaces*, March 31,
2026 author version, Section 5.1 and Proposition 5.2(i), printed pages 11--12,
https://ningguomath.com/wp-content/uploads/2026/03/amplenew-1.pdf . Its square
condition is precisely descent of the mixed tensor difference; Proposition 5.2(i)
allows checking that condition at the generic fibre. The present node uses the
stated smooth finite-presentation specialization. Also read the full statement
and generic-fibre reduction of Stacks divisors.tex, lemma-in-image-pullback,
Tag 0BD7 (local source at lines 6968 onward).

Hypothesis and clause correspondence:

- The scheme S is `{S : Scheme.{u}}`; integrality is `[IsIntegral S]`, which
  includes nonemptiness, irreducibility and reducedness. Local Noetherianity is
  `[IsLocallyNoetherian S]`. Normality is `hS`, asserting at every point both
  `IsDomain (S.presheaf.stalk s)` and `IsIntegrallyClosed` of that same local ring.
- The canonical generic point is `genericPoint S`. Its local ring is definitionally
  `S.functionField`; `S.fromSpecStalk (genericPoint S)` is the canonical morphism
  `Spec k(S) → S`. For an integral scheme that local ring is a field, hence is its
  own residue field. This uses exactly the arbitrary-integral-scheme clause of
  def-sc-function-field; it does not specialize the base to a curve or a field.
- `X₁ X₂ X₃ : Over S` bundle the three named structure morphisms as `Xᵢ.hom`.
  Each has `[Smooth Xᵢ.hom]` and `[IsSeparated Xᵢ.hom]`. Mathlib's separatedness
  is literally closed immersion of the diagonal. Each also has
  `[LocallyOfFinitePresentation Xᵢ.hom]` and `[QuasiCompact Xᵢ.hom]`.
  A separated morphism is quasi-separated, so these are exactly finite
  presentation under the already stated separatedness assumption. No global
  quasi-compactness of S or Xᵢ is imposed.
- `[GeometricallyIntegral Xᵢ.hom]` is the existing morphism property of integral
  base changes along every field-valued point. By its documented equivalence
  `GeometricallyIntegral.iff_geometricallyIntegral_fiber` this is precisely
  geometric integrality of each residue-field fibre in the node. Integrality
  includes nonemptiness, so no separate, weaker nonempty-fibre premise is used.
- C is `((X₁ ⨯ X₂) ⨯ X₃).left`. The helper `squareParameter X₁ X₂` is
  `(X₁ ⨯ X₁) ⨯ (X₂ ⨯ X₂)` over S, giving P with coordinates
  `(x₀,x₁,y₀,y₁)`. The total scheme is `(squareParameter X₁ X₂ ⨯ X₃).left`.
  Products in Over S are the existing scheme fibre products:
  `Over.prodLeftIsoPullback` identifies them with `Limits.pullback` and respects
  both projections. Parenthesizing and coordinate order do not change the objects.
- `squareProjection X₁ X₂ X₃` is `prod.fst` over S; its `.left` is π.
- `squareCoordinate X₁ X₂ X₃ a b` is `prod.map` of the pair of selected
  projections and the identity of X₃. `false` selects the first copy (index 0),
  `true` the second copy (index 1). Thus all four r_ab are specified as morphisms
  of schemes, not arbitrary maps satisfying unnamed conditions.
- `A : C.Modules` and `[IsInvertible A]` give the invertible module on C, using
  the recorded `Scheme.Modules.IsInvertible`, not the different site predicate.
- `squareDifference X₁ X₂ X₃ A` is the left-associated tensor product in the exact
  order r00, r11, dual(r01), dual(r10). All four pullbacks are
  `Scheme.Modules.tensorPullback`. The two duals are `SheafOfModules.homObj`
  of the corresponding pulled-back module into the structure sheaf `𝟙_ _`.
  The parameter `R` is explicitly the total scheme's actual commutative sheaf.
- In hη, `Nη` belongs to `(Limits.pullback P.hom η).Modules`, exactly Pη,
  and `IsInvertible Nη` is explicit. The left side of its isomorphism is the
  tensor pullback of D(A) by `pullback.fst Y.hom η : Yη → Y`.
  The right side pulls Nη back along `((Over.pullback η).map π).left`, exactly
  the canonical base change πη : Yη → Pη. `Nonempty (… ≅ …)` asserts existence
  of the required isomorphism in the category of O_Yη-modules.
- The conclusion `∃ N : P.left.Modules, IsInvertible N ∧ Nonempty (...)` is
  exactly an invertible N on P with D(A) isomorphic to its tensor pullback by π.
  It adds no normalization, uniqueness, chosen isomorphism, or further conclusion.

Dependency declarations read and used (including their docstrings):

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `Scheme.Hom`.
- def-sbc-smooth-morphisms: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `Smooth`.
- def-sbc-locally-finite-presentation:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, `LocallyOfFinitePresentation`.
- def-pc-geometrically-irreducible: `Mathlib.AlgebraicGeometry.Geometrically.Integral`,
  `GeometricallyIntegral`, its field-test definition and fibre equivalence.
- def-pc-fibre-product:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `Limits.pullback`,
  `pullback.fst`, `pullback.snd`; the standard Over product comparison is in
  `Mathlib.CategoryTheory.Limits.Constructions.Over.Products`.
- def-sc-invertible-module: `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` and the tensor unit/structure sheaf.
- def-pc-module-pullback: `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`
  publicly imports the recorded `Scheme.Modules.tensorPullback` from
  `WeilConjectures.AlgebraicGeometry.TensorPullback`; this exact functor is used.
- def-pur-sheaf-tensor-product:
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`,
  `SheafOfModules.cochainModulesMonoidal`, the existing localization tensor.
  The dual is the existing `SheafOfModules.homObj` from
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`.
- def-pc-integral-scheme: `Mathlib.AlgebraicGeometry.Properties`, `IsIntegral`.
- pqf-def-locnoeth: `Mathlib.AlgebraicGeometry.Noetherian`, `IsLocallyNoetherian`.
- def-weil-pbc-normal-ring:
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, `IsIntegrallyClosed`,
  together with `IsDomain`, in the recorded inline form for local domains.
- def-sc-generic-point: `Mathlib.Topology.Sober`, `genericPoint` and
  `genericPoint_spec`, the canonical generic point supplied by sobriety.
- def-sc-function-field: `WeilConjectures.AlgebraicGeometry.FunctionField` imports
  `Mathlib.AlgebraicGeometry.FunctionField`, `Scheme.functionField`, the recorded
  clause for an arbitrary integral scheme.
- def-weil-residue-field: `Mathlib.AlgebraicGeometry.ResidueField`,
  `Scheme.residueField`; the residue-field interpretation occurs through the
  existing geometric-integrality property. The generic stalk is already a field.

Proof imports: Mathlib Morphisms.Proper (lem-pc-proper-base-change), Smooth
(also lem-pc-smooth-flat), Noetherian (pqf-lem-locnoeth-lft), and upstream
Morphisms.SmoothConnectedGenericGeometryCore, whose complete recorded theorem
signature and proof docstring were read. The last proof prerequisite
lem-sfb-normal-noetherian-generic-line-pullback has no Lean record or Mathlib match
in the supplied DAG, so there is no module to import for it. Its exact statement
and its Tag 0BD7 source were read and its use is documented in the proof plan;
it is not a notion required to type the present statement.

Edge cases checked before writing:

- Empty S is excluded by the node's integral hypothesis. None of the Xᵢ can have
  an empty fibre: integral fibres are nonempty. No extra rational section or
  rational point is assumed.
- S = Spec K is permitted for every field K, including positive characteristic;
  the generic morphism then identifies with the original field base. The
  implication reduces to the supplied descent hypothesis.
- Zero-dimensional fibres, identity families Xᵢ = S, and the structure sheaf A
  are included. The zero module on the nonempty C is correctly excluded from
  being a line bundle. Repeated coordinates cause no ill-typed dual or tensor.
- Normal integral locally Noetherian S may be non-quasi-compact. All morphism
  finiteness assumptions are relative; no global Noetherian hypothesis occurs.
- The single arbitrary universe u is the scheme universe throughout. The
  geometric-integrality test fields are in that same universe, not in a
  separately smaller universe that could make tests vacuous. Internal Hom here
  stays in u because the Zariski site and module carriers are all u-sized.

Searches (fresh searches for this delivery, not inherited claims):

- msearch leanfinder: “The square difference of an invertible module on three
  smooth geometrically integral families over a normal integral locally
  Noetherian base descends if it descends over the generic point”. Eight results,
  on normalizationDesc and smooth algebra; none states this theorem.
- msearch loogle: `"IsInvertible", "pullback"`. Two vector-field pullback results,
  neither about scheme modules or generic descent.
- msearch grep, AlgebraicGeometry:
  `squareDifference|square_difference|theoremOfSquare|generic.*[Ii]nvertible`.
  Zero hits in Mathlib.
- msearch leansearch: “An invertible sheaf on a smooth family over a normal
  integral base is pulled back from the base if it is pulled back on the
  generic fibre”. Eight results, including Scheme.Modules.pullback and fibre
  definitions, no line-bundle descent theorem.
- rg in both lean/WeilConjectures and lean/Sheaf:
  `squareDifference|square_difference|theoremOfSquare` and coordinate-name searches
  found no existing construction. Generic/invertible searches found generic
  stalk and other normal-group results, which do not assert this statement.
- grep of the exact item id in lean/WeilConjectures had no hits; rg of proposed
  full names in the library and dag/lean_names_upstream.json had no conflicting
  declaration. The normal-group linearization and vertical Cartier modules
  were read to check their different hypotheses and conclusions.

No new nodes, dependency repairs, statement correction or disputed statement.

Validation: scompile.py compiled both its sandbox translation and actual module
path with no errors or warnings. The final delivery dry run is recorded below.

## Second reading by NF

A second pass over the node and the complete module was made by this dispatcher
worker; the dispatch brief forbids starting another agent, so this is not claimed
as an independent worker review. The maintainer supplies the independent review.
The second pass checked normality at all stalks, local Noetherianity, all three
smooth/separated/finite-presentation hypotheses, and all three geometric fibre
conditions. It checked C, P, π and the four selected coordinates explicitly,
including the r01/r10 dual signs. It checked that the generic isomorphism uses
restriction of D(A) itself and the canonical base-changed π, and that both Nη
and the final N are invertible. It confirmed the conclusion's isomorphism
orientation and existence quantifiers. No mathematical mismatch was found.
Compilation required an explicit commutative-ring sheaf parameter for internal
Hom and qualification of `Limits.pullback` to avoid the namespace's module
pullback; these are elaboration repairs with no statement change.

Delivery dry run: `deliver2.py NF lem-sfb-normal-product-square-descent --no-push`
reported `OK (dry run)` for commit 1c7f6ba33e9: preflight and compilation passed;
nothing pushed by the dry run.
