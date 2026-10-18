/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.OpenClosed.Derived
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.Finite.Exact
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.OpenClosed.Exact
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Sheaf.Paper.SfHomTriangulated
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.KInjectiveRestrictLocalized
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Sheaf.CategoryTheory.KInjectiveTotalDerived

/-!
# The etale internal Hom localization triangle over an arbitrary ring

Source: ILO, Travaux de Gabber, Expose XVII, proof of Lemma 7.6.10, printed p. 313;
Stacks Project, Tags 09XQ and 08JC
(blueprint: lem-per-etale-internal-hom-localization).

The supported inverse image is the actual kernel functor, with its actual scalar action.
Endpoint identifications are normalized by tensor evaluation and the support counit.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (A : Type (u + 1)) [CommRing A]

/-- The kernel of the open restriction unit, with kernel-induced maps.
Source: Stacks Tag 09XQ (blueprint: lem-per-etale-internal-hom-localization). -/
def perEtaleSupportKernel {U X : Scheme.{u}} (j : U ⟶ X) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  kernel (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit

/-- The closed inverse image of the support kernel, before deriving.
Source: Stacks Tag 09XQ (blueprint: lem-per-etale-internal-hom-localization). -/
def perEtaleClosedSupport {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  perEtaleSupportKernel A j ⋙ upperStar (ModuleCat.{u + 1} A) i

/-- The support functor is additive, as needed to form its right derived functor.
Source: Stacks Tag 09XQ (blueprint: lem-per-etale-internal-hom-localization).
Proof: kernel inclusions are monic; composing the kernel maps with these inclusions
identifies the map of a sum with the sum of the maps. Inverse image is additive. -/
@[instance] theorem perEtaleClosedSupport_additive {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) : (perEtaleClosedSupport A i j).Additive := by
  sorry

/-- Termwise inverse image, as used in the statement.
Source: ILO XVII 7.6.10 (blueprint: lem-per-etale-internal-hom-localization). -/
abbrev perEtalePull {Y X : Scheme.{u}} (g : Y ⟶ X) :=
  (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory

/-- Exact closed direct image, applied termwise.
Source: ILO XVII 7.6.10 (blueprint: lem-per-etale-internal-hom-localization). -/
abbrev perEtaleClosedPush {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :=
  (lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategory

/-- Ordinary derived internal Hom, with its two variables uncurried.
Source: ILO XVII 7.6.10 (blueprint: lem-per-etale-internal-hom-localization). -/
abbrev perEtaleHom (X : Scheme.{u}) :=
  Functor.uncurry.obj (derivedHom (ModuleCat.{u + 1} A) X)

/-- Canonical tensor compatibility of termwise inverse image, transported from the
existing K-flat derived comparison through the exact-inverse-image comparison.
Source: Stacks Tag 0G7E (blueprint: lem-per-etale-internal-hom-localization). -/
def perEtalePullTensorIso {Y X : Scheme.{u}} (g : Y ⟶ X)
    (K L : DerivedCategoryModule A X) :
    (perEtalePull A g).obj (((derivedTensor (ModuleCat.{u + 1} A) X).obj K).obj L) ≅
      ((derivedTensor (ModuleCat.{u + 1} A) Y).obj ((perEtalePull A g).obj K)).obj
        ((perEtalePull A g).obj L) :=
  ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).app _).symm ≪≫
    leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g K L ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) Y).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).app K)).app _ ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj _).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).app L)

/-- Closed precomposition source, before its internal adjunction identification.
Source: ILO XVII 7.6.10 (blueprint: lem-per-etale-internal-hom-localization). -/
abbrev perEtaleClosedHomSource {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :=
  ((perEtalePull A i ⋙ perEtaleClosedPush A i).op.prod (𝟭 (DerivedCategoryModule A X))) ⋙
    perEtaleHom A X

/-- The closed endpoint of the localization triangle.
Source: ILO XVII 7.6.10 (blueprint: lem-per-etale-internal-hom-localization). -/
abbrev perEtaleClosedHom {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) :=
  ((perEtalePull A i).op.prod (perEtaleClosedSupport A i j).rightDerivedFunctor) ⋙
    perEtaleHom A Z ⋙ perEtaleClosedPush A i

/-- Open precomposition source, before its internal adjunction identification.
Source: ILO XVII 7.6.10 (blueprint: lem-per-etale-internal-hom-localization). -/
abbrev perEtaleOpenHomSource {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  ((perEtalePull A j ⋙
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory).op.prod
        (𝟭 (DerivedCategoryModule A X))) ⋙ perEtaleHom A X

/-- The open endpoint, using derived direct image.
Source: ILO XVII 7.6.10 (blueprint: lem-per-etale-internal-hom-localization). -/
abbrev perEtaleOpenHom {U X : Scheme.{u}} (j : U ⟶ X) :=
  ((perEtalePull A j).op.prod (perEtalePull A j)) ⋙ perEtaleHom A U ⋙
    (lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor

/-- The exact closed inverse-image/direct-image adjunction, applied termwise.
Source: Stacks Tag 04CA (blueprint: lem-per-etale-internal-hom-localization). -/
def perEtaleClosedStarAdjunction {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    perEtalePull A i ⊣ perEtaleClosedPush A i :=
  (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).mapDerivedCategoryAdjunction

/-- The inverse closed internal-adjunction comparison, fixed by evaluation.
First pull back the tensor, use both closed counits and evaluate on Z; transpose
along i* ⊣ i_* and then apply the derived support counit. Thus the endpoint
identification cannot be replaced by an arbitrarily rescaled isomorphism.
Source: Stacks Tag 09XQ on each etale slice; ILO XVII 7.6.10
(blueprint: lem-per-etale-internal-hom-localization). -/
def perEtaleClosedHomComparison {Z U X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    (a : lowerStar (ModuleCat.{u + 1} A) i ⊣ perEtaleClosedSupport A i j)
    (K N : DerivedCategoryModule A X) :
    (perEtaleClosedHom A i j).obj (op K, N) ⟶
      (perEtaleClosedHomSource A i).obj (op K, N) :=
  (derivedTensorHomAdjunction (ModuleCat.{u + 1} A)
      ((perEtaleClosedPush A i).obj ((perEtalePull A i).obj K))).homEquiv _ _
    (((perEtaleClosedStarAdjunction A i).homEquiv _ _
      ((perEtalePullTensorIso A i _ _).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Z).map
          ((perEtaleClosedStarAdjunction A i).counit.app
            ((perEtalePull A i).obj K))).app _ ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Z).obj _).map
          ((perEtaleClosedStarAdjunction A i).counit.app
            ((perEtaleHom A Z).obj
              (op ((perEtalePull A i).obj K),
                (perEtaleClosedSupport A i j).rightDerivedFunctor.obj N))) ≫
        (derivedTensorHomAdjunction (ModuleCat.{u + 1} A)
          ((perEtalePull A i).obj K)).counit.app
            ((perEtaleClosedSupport A i j).rightDerivedFunctor.obj N))) ≫
      a.mapDerivedCategoryRightDerivedAdjunction.counit.app N)

/-- The open internal-adjunction comparison, fixed by evaluation.
Insert the unit j*K → j*j!j*K, identify the pulled-back tensor, evaluate, and transpose
successively along tensor-Hom and j* ⊣ Rj_*. This is the slice internal adjunction.
Source: Stacks Tag 08FJ; ILO XVII 7.6.10
(blueprint: lem-per-etale-internal-hom-localization). -/
def perEtaleOpenHomComparison {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (K N : DerivedCategoryModule A X) :
    (perEtaleOpenHomSource A j).obj (op K, N) ⟶
      (perEtaleOpenHom A j).obj (op K, N) :=
  (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).homEquiv _ _
    ((derivedTensorHomAdjunction (ModuleCat.{u + 1} A)
      ((perEtalePull A j).obj K)).homEquiv _ _
        (((derivedTensor (ModuleCat.{u + 1} A) U).map
          ((derivedOpenImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) j).unit.app ((perEtalePull A j).obj K))).app _ ≫
          (perEtalePullTensorIso A j _ _).inv ≫
          (perEtalePull A j).map
            ((derivedTensorHomAdjunction (ModuleCat.{u + 1} A)
              (((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory).obj
                ((perEtalePull A j).obj K))).counit.app N)))

/-- Include exactly the pairs K in D^b and N in D^+ into the ambient product category.
Source: ILO XVII 7.6.10 (blueprint: lem-per-etale-internal-hom-localization). -/
abbrev perEtaleBoundedPlusPairs (X : Scheme.{u}) :
    (_root_.DerivedCategory.Bounded (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))ᵒᵖ ×
        _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      (DerivedCategoryModule A X)ᵒᵖ × DerivedCategoryModule A X :=
  (_root_.DerivedCategory.Bounded.ι).op.prod (_root_.DerivedCategory.Plus.ι)

/-- The natural distinguished internal Hom localization triangle with its specified arrows.
The endpoint isomorphisms are fixed by evaluation, not supplied as hypotheses. The
support adjunction is normalized by the kernel inclusion. Natural transformations are
on the product D^b(X,A)^op × D^+(X,A), so naturality includes both input variables.

Source: ILO, Travaux de Gabber, Expose XVII, proof of Lemma 7.6.10, p. 313;
Stacks Tags 09XQ, 095L, 08JC, 08FJ, 0G7E and 0A96
(blueprint: lem-per-etale-internal-hom-localization).

Proof plan, following the seven steps of the DAG node:
1. Choose a bounded representative B of K (lem-sfb-bounded-representative) and a
   bounded-below injective representative I of N (lem-weil-pbc-dplus-injective-representative).
   Exact constant-coefficient inverse image computes i*K and j*K termwise
   (prop-weil-pbc-inverse-image-modules-exact). Closed direct image is exact, and its
   normalized support adjoint takes injectives to injectives
   (lem-per-etale-closed-sheaf-internal-adjunction). Thus support(I) is bounded below
   K-injective and computes Ri!N (lem-weil-pbc-right-derived-plus-injective).
2. Apply the open/closed short exact sequence termwise to B
   (lem-weil-pbc-open-closed-short-exact). Exactness of j!, i*, j*, i_* and the
   cone-to-quotient comparison (lem-pc-cone-short-exact-quasi-iso) give the distinguished
   triangle j!j*K → K → i_*i*K →, with its actual counit and unit.
3. Apply contravariant internal Hom into N (lem-sf-hom-triangulated), with the signed
   Hom shift. This reverses the first two maps by precomposition.
4. Apply the closed sheaf internal adjunction to every B^p,I^q
   (lem-per-etale-closed-sheaf-internal-adjunction). The products in each total degree
   are finite since B is bounded; i_* preserves them. Naturality commutes with the
   differential d_I f - (-1)^n f d_B. The resulting closed endpoint isomorphism has
   inverse perEtaleClosedHomComparison, by tensor evaluation and the support counit.
5. On every etale slice the open extension/restriction adjunction identifies
   Hom(j!G,F) with j_*Hom(G,j*F)
   (lem-weil-pbc-extension-by-zero-adjunction, def-pur-sheaf-hom).
6. Choose a K-flat resolution P → B with flat terms (lem-pc-kflat-resolution).
   Pullback preserves K-flatness (lem-weil-pbc-ringed-topoi-derived-tensor-pullback),
   and open restriction preserves K-injectives (lem-pur-kinjective-restrict-localized).
   Hence Hom(j*P,j*I) is K-injective (lem-pur-hom-kflat-into-kinjective).
   Apply step 5 degreewise; j_* commutes with the total products by its sectionwise
   formula. This identifies the open endpoint with Rj_*RHom(j*K,j*N), with comparison
   perEtaleOpenHomComparison, computing derived direct image on a K-injective model
   (lem-weil-pbc-kinjective-total-derived).
7. Transport step 3 along these endpoint isomorphisms and shift the closed comparison
   on the last arrow. Naturality of adjunctions, of the cone-to-quotient map, and of
   the Hom-complex differential makes all three arrows natural. Quasi-isomorphism
   invariance of derived Hom descends them independently of representatives.
   Isomorphism invariance of distinguished triangles gives the result. None of the
   constructions assumes constructibility, finite Tor amplitude, finite A, or duality. -/
theorem etale_internalHom_localization
    {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    ∃ a : lowerStar (ModuleCat.{u + 1} A) i ⊣ perEtaleClosedSupport A i j,
      (∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A),
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit.app
            ((perEtaleSupportKernel A j).obj F) ≫ a.counit.app F =
          (kernel.ι (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit).app F) ∧
      ∃ (eC : perEtaleBoundedPlusPairs A X ⋙ perEtaleClosedHom A i j ≅
            perEtaleBoundedPlusPairs A X ⋙ perEtaleClosedHomSource A i)
        (eO : perEtaleBoundedPlusPairs A X ⋙ perEtaleOpenHomSource A j ≅
            perEtaleBoundedPlusPairs A X ⋙ perEtaleOpenHom A j),
        (∀ (K : _root_.DerivedCategory.Bounded
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
          (N : _root_.DerivedCategory.Plus
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))),
          eC.hom.app (op K, N) = perEtaleClosedHomComparison A i j a K.obj N.obj ∧
          eO.hom.app (op K, N) = perEtaleOpenHomComparison A j K.obj N.obj) ∧
        ∃ δ : perEtaleBoundedPlusPairs A X ⋙ perEtaleOpenHom A j ⟶
            (perEtaleBoundedPlusPairs A X ⋙ perEtaleClosedHom A i j) ⋙
              shiftFunctor (DerivedCategoryModule A X) (1 : ℤ),
          ∀ (K : _root_.DerivedCategory.Bounded
              (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
            (N : _root_.DerivedCategory.Plus
              (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))),
            Triangle.mk
              (eC.hom.app (op K, N) ≫
                ((derivedHom (ModuleCat.{u + 1} A) X).map
                  ((perEtaleClosedStarAdjunction A i).unit.app K.obj).op).app N.obj)
              (((derivedHom (ModuleCat.{u + 1} A) X).map
                ((derivedOpenImmersionLowerShriekUpperStarAdjunction
                  (ModuleCat.{u + 1} A) j).counit.app K.obj).op).app N.obj ≫
                    eO.hom.app (op K, N))
              (δ.app (op K, N)) ∈ distTriang _ := by
  sorry

end AlgebraicGeometry.Etale
