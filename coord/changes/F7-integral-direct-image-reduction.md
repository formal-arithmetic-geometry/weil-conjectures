# AlgebraicGeometry.ProEtale.internal_integral_direct_image_limits

## Reason

The existing theorem combines scalar pullback normalization, the finite projection
formula and preservation of canonical integral completeness. Its previous proof was
one `sorry`. Separate the actual coefficient comparisons from the categorical
assembly, keeping every existing statement and every existing public import.
The three new modules give smaller proof obligations with explicit canonical maps;
the tower obligation assumes the projection isomorphisms proved by the cone argument.
No existing definition is repaired or replaced, and no source-library file changes.

## Old

The new public declarations below did not exist. The existing declaration
`AlgebraicGeometry.ProEtale.internal_integral_direct_image_limits` had its current
signature and body `:= by sorry`. Its signature is preserved verbatim.

## New

The new modules and their public declarations are:

- `Sheaf.SixFunctors.ProEtale.IntegralReductionPullbackNormalization`:
  `integralReductionPullbackMap` is an abbreviation for the specified inverse scalar
  mate at arbitrary positive exponent; `integral_reduction_pullback_normalization`
  asserts a comparison isomorphism with the equation that uniquely fixes its mate.
- `Sheaf.SixFunctors.ProEtale.IntegralDirectImageReductionCone`:
  `integralFiniteProjection` constructs the actual geometric mate;
  `integral_direct_image_reduction_cone` asserts the two scalar triangles and their
  comparison squares, before applying the triangle five lemma.
- `Sheaf.SixFunctors.ProEtale.IntegralDirectImageReductionTower`:
  `integral_direct_image_reduction_tower` assumes invertibility of all specified
  scalar mates and finite projections, and supplies level isomorphisms with the
  consecutive transition and canonical scalar-unit equations.

The signatures are recorded verbatim in the three accompanying new DAG nodes.
All objects and maps in the two new definitions are actual constructions; neither
uses an unproved existence theorem. The existing theorem obtains temporary
isomorphism witnesses only inside its proof. No public definition chooses them.

The exact new signatures (with the module parameters made explicit above them) follow.


`Sheaf.SixFunctors.ProEtale.IntegralReductionPullbackNormalization`:

```lean
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {U X : Scheme.{u}} (j : U ⟶ X)

abbrev integralReductionPullbackMap (n : ℕ) : (CondensedRing.upperStar (DerivedNakayama.integerRing l E) j).mapDerivedCategory ⋙ AdicCompletion.derivedReduction l E U n ⟶ AdicCompletion.derivedReduction l E X n ⋙ (CondensedRing.upperStar (DerivedNakayama.quotientRing l E (n + 1)) j).mapDerivedCategory

theorem integral_reduction_pullback_normalization (n : ℕ) : ∃ b : (CondensedRing.upperStar (DerivedNakayama.integerRing l E) j).mapDerivedCategory ⋙ AdicCompletion.derivedReduction l E U n ≅ AdicCompletion.derivedReduction l E X n ⋙ (CondensedRing.upperStar (DerivedNakayama.quotientRing l E (n + 1)) j).mapDerivedCategory, ∀ M : DerivedCategory (AdicCompletion.Modules l E X), (CondensedRing.upperStar (DerivedNakayama.integerRing l E) j).mapDerivedCategory.map ((Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E X n)).unit.app M) ≫ (CondensedRing.derivedComapUpperStarIso (DerivedNakayama.reductionRing l E (n + 1)) j).inv.app ((AdicCompletion.derivedReduction l E X n).obj M) = (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E U n)).unit.app ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) j).mapDerivedCategory.obj M) ≫ (AdicCompletion.restrict l E U n).map (b.hom.app M)
```


`Sheaf.SixFunctors.ProEtale.IntegralDirectImageReductionCone`:

```lean
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {U X : Scheme.{u}} (j : U ⟶ X)

def integralFiniteProjection (n : ℕ) [IsIso (integralReductionPullbackMap l E j n)] (K : DerivedCategory (AdicCompletion.Modules l E U))

theorem integral_direct_image_reduction_cone (n : ℕ) [IsIso (integralReductionPullbackMap l E j n)] (K : DerivedCategory (AdicCompletion.Modules l E U)) : let H := (CondensedRing.moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) j).obj K let c := (AdicCompletion.restrict l E X n).map (integralFiniteProjection l E j n K) ∃ (s : H ⟶ H) (q : H ⟶ (AdicCompletion.integralLevel l E X H n)) (δ : (AdicCompletion.integralLevel l E X H n) ⟶ H⟦(1 : ℤ)⟧) (q' : H ⟶ (AdicCompletion.restrict l E X n).obj ((CondensedRing.moduleObjectDerivedPushforward (DerivedNakayama.quotientRing l E (n + 1)) j).obj ((AdicCompletion.derivedReduction l E U n).obj K))) (δ' : (AdicCompletion.restrict l E X n).obj ((CondensedRing.moduleObjectDerivedPushforward (DerivedNakayama.quotientRing l E (n + 1)) j).obj ((AdicCompletion.derivedReduction l E U n).obj K)) ⟶ H⟦(1 : ℤ)⟧), Pretriangulated.Triangle.mk s q δ ∈ distTriang _ ∧ Pretriangulated.Triangle.mk s q' δ' ∈ distTriang _ ∧ q ≫ c = q' ∧ c ≫ δ' = δ
```


`Sheaf.SixFunctors.ProEtale.IntegralDirectImageReductionTower`:

```lean
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {U X : Scheme.{u}} (j : U ⟶ X)

theorem integral_direct_image_reduction_tower (K : DerivedCategory (AdicCompletion.Modules l E U)) (hχ : ∀ n : ℕ, IsIso (integralReductionPullbackMap l E j n)) (hproj : ∀ n : ℕ, letI := hχ n; IsIso (integralFiniteProjection l E j n K)) : let F := CondensedRing.moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) j ∃ a : ∀ n : ℕ, F.obj (AdicCompletion.integralLevel l E U K n) ≅ AdicCompletion.integralLevel l E X (F.obj K) n, (∀ n : ℕ, F.map (AdicCompletion.integralStep l E U K n) ≫ (a n).hom = (a (n + 1)).hom ≫ AdicCompletion.integralStep l E X (F.obj K) n) ∧ ∀ n : ℕ, F.map ((Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E U n)).unit.app K) ≫ (a n).hom = (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E X n)).unit.app (F.obj K)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.ProEtale.IntegralDirectImageLimits | F7 | Private proof imports and proved helpers assemble the unchanged public theorem. |
| Sheaf.SixFunctors.ProEtale.IntegralReductionPullbackNormalization | F7, new | Defines the specified scalar mate and its normalization obligation. |
| Sheaf.SixFunctors.ProEtale.IntegralDirectImageReductionCone | F7, new | Uses the scalar mate in the finite projection construction and cone statement. |
| Sheaf.SixFunctors.ProEtale.IntegralDirectImageReductionTower | F7, new | Uses these two explicit maps in its finite-projection hypotheses. |

There are no prior users of these new declarations. Existing importers of the item
receive exactly the same theorem signature and public imports. No target's meaning
changes, and no adaptation of another group's module is needed.

## Status

landed 20261025T101007-L-3646565 2026-10-25 (merge of deliver/F7/Sheaf.SixFunctors.ProEtale.IntegralDirectImageLimits)
