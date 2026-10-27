module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReductionFoundation
public import Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReductionPullbacks
public import Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReductionNorm2
public import Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReductionCompat
public import Sheaf.Paper.EtaleUnboundedRestrictionComparison
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities
import Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.Paper.EtaleKFlatCriteria
import WeilConjectures.CategoryTheory.SiteMorphismComposition

import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Flat coefficient tensor exchange

Source: Stacks Project, etale-cohomology.tex, Tag 0F1J, the two coefficient
identifications in the prime-torsion reduction, generalized to an arbitrary ring map
and commutative square; sites-cohomology.tex, Tags 0D6J and 07A7, for its counit
normalization (blueprint: lem-kun-flat-coefficient-tensor-exchange-comparison).

The source and target functors are the two sides of the existing tensorBaseChangeMap.
The isomorphisms below are normalized on every ordinary complex, then by the canonical
inverse-image and direct-image coefficient comparisons. They are not arbitrary isos.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

variable {R B : Type (u + 1)} [CommRing R] [CommRing B]

/-- The source M tensor f inverse image Rg direct image, on arbitrary derived inputs.
Source: Stacks 0F1J (blueprint: lem-kun-flat-coefficient-tensor-exchange-comparison). -/
@[implicit_reducible]
def flatExchangeSource (A : Type (u + 1)) [CommRing A]
    {Z T S : Scheme.{u}} (f : Z ⟶ S) (g : T ⟶ S)
    (M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    DerivedCategoryModule A T ⥤ DerivedCategoryModule A Z :=
  primePushforward A g ⋙ primePullback A f ⋙
    (derivedTensor (ModuleCat.{u + 1} A) Z).obj ((primeSingle A Z).obj M)

/-- The target Rh direct image of h inverse image M tensor e inverse image.
Source: Stacks 0F1J (blueprint: lem-kun-flat-coefficient-tensor-exchange-comparison). -/
@[implicit_reducible]
def flatExchangeTarget (A : Type (u + 1)) [CommRing A]
    {Y Z T : Scheme.{u}} (h : Y ⟶ Z) (e : Y ⟶ T)
    (M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    DerivedCategoryModule A T ⥤ DerivedCategoryModule A Z :=
  primePullback A e ⋙
    (derivedTensor (ModuleCat.{u + 1} A) Y).obj
      ((primePullback A h).obj ((primeSingle A Z).obj M)) ⋙ primePushforward A h

/-- Functoriality of the source in M, with the second derived input unchanged.
Source: Stacks 0F1J (blueprint: lem-kun-flat-coefficient-tensor-exchange-comparison). -/
def flatExchangeSourceMap (A : Type (u + 1)) [CommRing A]
    {Z T S : Scheme.{u}} (f : Z ⟶ S) (g : T ⟶ S)
    {M M' : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)} (k : M ⟶ M') :
    flatExchangeSource A f g M ⟶ flatExchangeSource A f g M' :=
  Functor.whiskerLeft (primePushforward A g ⋙ primePullback A f)
    ((derivedTensor (ModuleCat.{u + 1} A) Z).map ((primeSingle A Z).map k))

/-- Functoriality of the target in M.
Source: Stacks 0F1J (blueprint: lem-kun-flat-coefficient-tensor-exchange-comparison). -/
def flatExchangeTargetMap (A : Type (u + 1)) [CommRing A]
    {Y Z T : Scheme.{u}} (h : Y ⟶ Z) (e : Y ⟶ T)
    {M M' : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)} (k : M ⟶ M') :
    flatExchangeTarget A h e M ⟶ flatExchangeTarget A h e M' :=
  Functor.whiskerRight
    (Functor.whiskerLeft (primePullback A e)
      ((derivedTensor (ModuleCat.{u + 1} A) Y).map
        ((primePullback A h).map ((primeSingle A Z).map k)))) (primePushforward A h)

/-- Include D+ into D before applying the exact termwise restriction of scalars.
Source: Stacks 0D6J (blueprint: lem-kun-flat-coefficient-tensor-exchange-comparison). -/
@[implicit_reducible]
def flatExchangeRestrictedInput (φ : R →+* B) (T : Scheme.{u}) :
    _root_.DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) ⥤
      DerivedCategoryModule R T :=
  _root_.DerivedCategory.Plus.ι ⋙ Sheaf.derivedRestrictScalars T.smallEtaleTopology φ

/-- The coefficient tensor arrow on Y before applying Rh direct image. Its first
factor is the pulled-back degree-zero M, and its second factor uses the canonical
inverse-image/restriction comparison.
Source: Stacks 0F1J (blueprint: lem-kun-flat-coefficient-tensor-exchange-comparison). -/
def flatExchangeInnerRestriction (φ : R →+* B)
    {Y Z T : Scheme.{u}} (h : Y ⟶ Z) (e : Y ⟶ T)
    (M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R))
    (Φ : PrimeTensorCoefficientIso φ Y
      ((primePullback R h).obj ((primeSingle R Z).obj M))
      ((primePullback B h).obj ((primeSingle B Z).obj
        ((primeCoefficientQuotient φ Z).obj M))))
    (N : DerivedCategoryModule B T) :=
  ((derivedTensor (ModuleCat.{u + 1} R) Y).obj
      ((primePullback R h).obj ((primeSingle R Z).obj M))).map
    ((scalarRestrictionPullbackIso φ e).hom.app N) ≫
      Φ.hom.app ((primePullback B e).obj N)

/-- Arbitrary-ring coefficient tensor exchange, with its ordinary representative
normalization, flatness, bounded-below values, and joint naturality.
Source: Stacks 0F1J, prime-torsion coefficient identifications, generalized to R to B;
0D6J and 07A7 for the coefficient counit identities
(blueprint: lem-kun-flat-coefficient-tensor-exchange-comparison).

Proof plan:
1. Restriction leaves underlying abelian sheaves and maps unchanged, hence is exact
and conservative. Exact-functor cohomology comparison and derived factorization
identify Hq(UC) with U(Hq C); reflection of zero objects and the cone criterion give
conservativity on D (and therefore on D+).
2. Sheafify the balanced maps m tensor n to (m tensor 1) tensor n and
(m tensor b) tensor n to m tensor bn. The balanced relations give inverse maps;
naturality follows before sheafification. These are primeCoefficientTensorMap and
its inverse, not an identification of sheafified sections with sectionwise tensors.
3. Flat module pullback applied to R to B makes M_B flat, without flatness of R to B.
Exact inverse image and flat module pullback make h inverse image M and M_B flat.
The bounded-above flat K-flat criterion makes their degree-zero complexes K-flat.
Thus the ordinary tensor maps compute the derived tensors on any second complex,
preserve quasi-isomorphisms and descend, as recorded by the existing termwise and
localization normalization predicates. Exact tensor preserves lower bounds.
4. The inverse-image coefficient comparisons respect the balancing formulas and
monoidal pullback: both routes send a local generator to (pullback m tensor 1)
tensor pullback n. The inverse sends (pullback m tensor b) tensor n to pullback m
tensor bn. Composition comparisons through the given square preserve these labels.
5. Assemble a using the inverse of the direct-image mate for g, pullback comparison
for f, and normalized tensor comparison on Z. Assemble b using pullback comparison
for e, normalized tensor comparison on Y, and inverse direct-image mate for h.
These mates are invertible on bounded-below inputs by the recorded coefficient
comparison theorem, even if restriction does not preserve injectives.
6. Transpose both exchange arrows under h inverse image adjoint to Rh direct image.
Substitute the coefficient counit identity for g. Naturality of the balanced map
and Step 4 identify the transposes, including the monoidal pullback comparison.
7. Apply the coefficient counit identity for h and injectivity of adjunction
transpose to return to the displayed exchange square. Naturality in N is that of
all the comparisons; naturality in flat M follows from the same balancing formula.
Only commutativity of the square, flatness of M, and a lower bound on N are used.
-/
theorem flatCoefficientTensorExchangeComparison (φ : R →+* B)
    {Y Z T S : Scheme.{u}} (h : Y ⟶ Z) (e : Y ⟶ T) (f : Z ⟶ S) (g : T ⟶ S)
    (w : h ≫ f = e ≫ g) :
    (∀ V : Scheme.{u},
      exactFunctor _ _ (Sheaf.restrictScalars V.smallEtaleTopology φ) ∧
      (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ).ReflectsIsomorphisms) ∧
    (∀ M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R),
      exactFunctor _ _ (tensorRight M) →
        exactFunctor _ _ (tensorRight ((primeCoefficientQuotient φ Z).obj M))) ∧
    ∃ (a : ∀ (M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R))
        (_ : exactFunctor _ _ (tensorRight M)),
      flatExchangeRestrictedInput φ T ⋙ flatExchangeSource R f g M ≅
        _root_.DerivedCategory.Plus.ι ⋙
          flatExchangeSource B f g ((primeCoefficientQuotient φ Z).obj M) ⋙
            Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)
      (b : ∀ (M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R))
        (_ : exactFunctor _ _ (tensorRight M)),
      flatExchangeRestrictedInput φ T ⋙ flatExchangeTarget R h e M ≅
        _root_.DerivedCategory.Plus.ι ⋙
          flatExchangeTarget B h e ((primeCoefficientQuotient φ Z).obj M) ⋙
            Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ),
    (∀ (M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R))
      (hM : exactFunctor _ _ (tensorRight M)),
      ∃ (ΦZ : PrimeTensorCoefficientIso φ Z ((primeSingle R Z).obj M)
          ((primeSingle B Z).obj ((primeCoefficientQuotient φ Z).obj M)))
        (ΦY : PrimeTensorCoefficientIso φ Y
          ((primePullback R h).obj ((primeSingle R Z).obj M))
          ((primePullback B h).obj ((primeSingle B Z).obj
            ((primeCoefficientQuotient φ Z).obj M)))),
      PrimeTensorCoefficientNormalized φ Z M ((primeCoefficientQuotient φ Z).obj M)
        ((primeCoefficientQuotientUnit φ Z).app M) _ _ (Iso.refl _) (Iso.refl _) ΦZ ∧
      PrimeTensorCoefficientNormalized φ Y (primePulledSheaf R h M)
        (primePulledSheaf B h ((primeCoefficientQuotient φ Z).obj M))
        (primePullbackCoefficientMap φ h M ((primeCoefficientQuotient φ Z).obj M)
          ((primeCoefficientQuotientUnit φ Z).app M)) _ _
        (primePullbackSingleIso R h M)
        (primePullbackSingleIso B h ((primeCoefficientQuotient φ Z).obj M)) ΦY ∧
      (∀ N : _root_.DerivedCategory.Plus
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)),
        ((derivedTensor (ModuleCat.{u + 1} R) Z).obj ((primeSingle R Z).obj M)).map
            ((primePullback R f).map
              ((scalarRestrictionDirectImageMap φ g).app N.obj)) ≫ (a M hM).hom.app N =
          ((derivedTensor (ModuleCat.{u + 1} R) Z).obj ((primeSingle R Z).obj M)).map
            ((scalarRestrictionPullbackIso φ f).hom.app ((primePushforward B g).obj N.obj)) ≫
              ΦZ.hom.app ((primePullback B f).obj ((primePushforward B g).obj N.obj))) ∧
      (∀ N : _root_.DerivedCategory.Plus
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)),
        (b M hM).hom.app N ≫ (scalarRestrictionDirectImageMap φ h).app
          (((derivedTensor (ModuleCat.{u + 1} B) Y).obj
            ((primePullback B h).obj ((primeSingle B Z).obj
              ((primeCoefficientQuotient φ Z).obj M)))).obj ((primePullback B e).obj N.obj)) =
          (primePushforward R h).map (flatExchangeInnerRestriction φ h e M ΦY N.obj))) ∧
    (∀ (M M' : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R))
      (hM : exactFunctor _ _ (tensorRight M)) (hM' : exactFunctor _ _ (tensorRight M'))
      (k : M ⟶ M')
      (N : _root_.DerivedCategory.Plus
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))),
      (flatExchangeSourceMap R f g k).app ((flatExchangeRestrictedInput φ T).obj N) ≫
          (a M' hM').hom.app N =
        (a M hM).hom.app N ≫ (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).map
          ((flatExchangeSourceMap B f g ((primeCoefficientQuotient φ Z).map k)).app N.obj)) ∧
    (∀ (M M' : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R))
      (hM : exactFunctor _ _ (tensorRight M)) (hM' : exactFunctor _ _ (tensorRight M'))
      (k : M ⟶ M')
      (N : _root_.DerivedCategory.Plus
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))),
      (flatExchangeTargetMap R h e k).app ((flatExchangeRestrictedInput φ T).obj N) ≫
          (b M' hM').hom.app N =
        (b M hM).hom.app N ≫ (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).map
          ((flatExchangeTargetMap B h e ((primeCoefficientQuotient φ Z).map k)).app N.obj)) ∧
    (∀ (M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R))
      (hM : exactFunctor _ _ (tensorRight M))
      (N : _root_.DerivedCategory.Plus
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))),
      tensorBaseChangeMap (ModuleCat.{u + 1} R) h e f g w ((primeSingle R Z).obj M)
          ((flatExchangeRestrictedInput φ T).obj N) ≫ (b M hM).hom.app N =
        (a M hM).hom.app N ≫ (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).map
          (tensorBaseChangeMap (ModuleCat.{u + 1} B) h e f g w
            ((primeSingle B Z).obj ((primeCoefficientQuotient φ Z).obj M)) N.obj)) ∧
    (∀ (M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R))
      (_ : exactFunctor _ _ (tensorRight M))
      (N : _root_.DerivedCategory.Plus
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))), ∃ n : ℤ,
      ((flatExchangeSource R f g M).obj ((flatExchangeRestrictedInput φ T).obj N)).IsGE n ∧
      ((flatExchangeTarget R h e M).obj ((flatExchangeRestrictedInput φ T).obj N)).IsGE n ∧
      ((flatExchangeSource B f g ((primeCoefficientQuotient φ Z).obj M)).obj N.obj).IsGE n ∧
      ((flatExchangeTarget B h e ((primeCoefficientQuotient φ Z).obj M)).obj N.obj).IsGE n) := by
  sorry

end AlgebraicGeometry.Etale
