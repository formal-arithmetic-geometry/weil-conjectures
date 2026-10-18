/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatTelescopeClosure
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-!
# Flat-term K-flat total tensor models

Source: Stacks Project, Cohomology on Sites, Tags 07A2 and 07A4;
Modules on Sites, Tag 0G6Q (blueprint: lem-pur-kflat-total-tensor-model).

The helpers below only specialize existing category and tensor constructions.
The derived tensor in the conclusion is exactly the localized bifunctor supplied by
`site_derived_tensor_descent_independentCoefficients`, characterized by its natural
representative comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules.KFlatTotalTensorModel

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{r})

/-- Use the recorded small-site sheafification in the coefficient universe.
Source: Stacks, Section 03DA (blueprint: lem-pur-kflat-total-tensor-model). -/
instance smallSiteHasSheafify : HasSheafify J AddCommGrpCat.{r} :=
  SheafOfModules.hasSheafify_coefficientUniverse.{u, v, r}

/-- Use the recorded locally-bijective criterion in the coefficient universe.
Source: Stacks, Section 03DA (blueprint: lem-pur-kflat-total-tensor-model). -/
instance smallSiteWEqualsLocallyBijective : J.WEqualsLocallyBijective AddCommGrpCat.{r} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u, v, r}

/-- The existing category of module sheaves on the given small site.
Source: Stacks, Tag 07A2 (blueprint: lem-pur-kflat-total-tensor-model). -/
abbrev Modules := SheafOfModules.{r}
  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

/-- The canonical monoidal structure with every universe-sensitive instance fixed explicitly.
Source: Stacks, Tag 03EK (blueprint: lem-pur-kflat-total-tensor-model). -/
@[instance_reducible]
def monoidal : MonoidalCategory (Modules R) :=
  @SheafOfModules.monoidalCategory.{v, u, r} C _ J
    (inferInstance : J.HasSheafCompose
      (forget₂ CommRingCat.{r} RingCat.{r})) R
    (smallSiteWEqualsLocallyBijective (J := J))
    (inferInstance : HasWeakSheafify J AddCommGrpCat.{r})
    (SheafOfModules.isMonoidal_W_independentCoefficients.{u, v, r} R)

/-- The existing sheaf tensor, with its canonical monoidal structure explicitly supplied.
Source: Stacks, Tags 03EK and 07A2 (blueprint: lem-pur-kflat-total-tensor-model). -/
def tensor : Modules R ⥤ Modules R ⥤ Modules R :=
  @curriedTensor (Modules R) _ (monoidal R)

/-- Reuse the existing zero-map preservation for the canonical tensor alias.
Source: Stacks, Tag 03EK (blueprint: lem-pur-kflat-total-tensor-model). -/
instance tensor_preservesZeroMorphisms : (tensor R).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients.{u, v, r} R

/-- Reuse zero-map preservation in the second tensor variable.
Source: Stacks, Tag 03EK (blueprint: lem-pur-kflat-total-tensor-model). -/
instance tensor_obj_preservesZeroMorphisms (M : Modules R) :
    ((tensor R).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients.{u, v, r} R M

/-- Reuse the coproduct totalization of the canonical tensor bicomplex.
Source: Stacks, Tag 06YM (blueprint: lem-pur-kflat-total-tensor-model). -/
instance hasTotal (K L : CochainComplex (Modules R) ℤ) :
    CochainComplex.HasMapBifunctor K L (tensor R) := inferInstance

/-- The direct-sum total tensor bifunctor, with the usual cochain Koszul differential.
This is `CochainComplex.mapBifunctor` on objects, not a new totalization.
Source: Stacks, Tags 06YM and 07A2 (blueprint: lem-pur-kflat-total-tensor-model). -/
def total : CochainComplex (Modules R) ℤ × CochainComplex (Modules R) ℤ ⥤
    CochainComplex (Modules R) ℤ :=
  Functor.uncurry.obj ((tensor R).map₂CochainComplex)

/-- The total tensor of flat-term K-flat complexes is again a flat-term K-flat complex,
with its natural, summandwise inverse-associator chain isomorphism and its derived model.
All complexes are integer-indexed without any boundedness restriction. The termwise
flatness clause applies to the direct sum over all pairs of integers with the given sum.
The last bifunctor is the chosen descent of the total tensor from the cited resolving
subcategory; its natural comparison determines it up to compatible natural isomorphism.

Source: Stacks Project, Cohomology on Sites, Tags 07A2 and 07A4, and Modules on Sites,
Tag 0G6Q (blueprint: lem-pur-kflat-total-tensor-model).

Proof plan:
1. Given an acyclic H, K-flatness of P makes Tot(H tensor P) acyclic, and K-flatness
   of Q makes Tot(Tot(H tensor P) tensor Q) acyclic (def-pc-kflat-complex).
   The reassociation in step 4 transfers this acyclicity to Tot(H tensor Tot(P tensor Q)).
2. Each P^p tensor Q^q is flat: tensoring by it is the composite of the two exact
   tensor functors, identified by associativity (def-pc-flat-sheaf-modules and
   lem-pc-sheaf-modules-tensor-closed).
3. The pairs p+q=i are countable. Their coproduct is flat by lem-pc-kflat-closure.
   This is precisely the degree i term of the direct-sum total complex.
4. Distribute tensor through coproducts by the tensor/internal-Hom adjunction
   (lem-pc-sheaf-modules-tensor-closed), then use the inverse sheaf associator on
   each triple summand. The three differential components have signs 1, (-1)^a,
   and (-1)^(a+p) on both sides. Thus reassociation is a chain map with inverse
   given by the associator. Naturality follows on each summand from its naturality.
5. Apply the natural resolving-class comparison of lem-weil-pbc-site-derived-tensor-descent
   to P,Q. Their total is in the same resolving class by steps 1 and 3, so it is an
   admissible representative for subsequent derived tensor or derived pullback.
-/
theorem kFlat_total_tensor_model
    [HasDerivedCategory.{w} (Modules R)]
    (P Q : CochainComplex (Modules R) ℤ)
    (_hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (_hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q)
    (_hPflat : ∀ p : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X p))
    (_hQflat : ∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (Q.X q)) :
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)
        ((total R).obj (P, Q)) ∧
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R)
      (((total R).obj (P, Q)).X i)) ∧
    (∃ α : ∀ H : CochainComplex (Modules R) ℤ,
        (total R).obj (H, (total R).obj (P, Q)) ≅
          (total R).obj ((total R).obj (H, P), Q),
      (∀ (H : CochainComplex (Modules R) ℤ) (a p q b c i : ℤ)
          (hpq : p + q = c) (ha : a + c = i)
          (hap : a + p = b) (hb : b + q = i),
        ((tensor R).obj (H.X a)).map
            (CochainComplex.ιMapBifunctor P Q (tensor R) p q c hpq) ≫
          CochainComplex.ιMapBifunctor H ((total R).obj (P, Q)) (tensor R) a c i ha ≫
          (α H).hom.f i =
        (@MonoidalCategory.associator (Modules R) _
            (monoidal R).toMonoidalCategoryStruct
            (H.X a) (P.X p) (Q.X q)).inv ≫
          ((tensor R).map (CochainComplex.ιMapBifunctor H P (tensor R) a p b hap)).app
            (Q.X q) ≫
          CochainComplex.ιMapBifunctor ((total R).obj (H, P)) Q (tensor R) b q i hb) ∧
      ∀ (H H' : CochainComplex (Modules R) ℤ) (f : H ⟶ H'),
        (total R).map (CategoryTheory.Prod.mkHom f (𝟙 ((total R).obj (P, Q)))) ≫
            (α H').hom =
          (α H).hom ≫ (total R).map
            (CategoryTheory.Prod.mkHom ((total R).map (CategoryTheory.Prod.mkHom f (𝟙 P)))
              (𝟙 Q))) ∧
    Nonempty (DerivedCategory.Q.obj ((total R).obj (P, Q)) ≅
      (SheafOfModules.siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R).obj
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) := by
  sorry

end SheafOfModules.KFlatTotalTensorModel
