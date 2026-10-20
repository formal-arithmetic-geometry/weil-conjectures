/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Paper.RingedTopoiCanonicalTensorPullback
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-!
# Canonical tensor pullback on the small pro-etale site

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0G7E;
Modules on Sites, Tag 03EL (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
The object universe of the site is u+1 and its morphism universe is u.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

/-- The ordinary sheaf tensor, with the original small pro-etale site.
Source: Stacks 03EL (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
noncomputable abbrev proEtaleOrdinaryTensor (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  @curriedTensor (proEtaleRingModules X R) _ (SheafOfModules.monoidalCategory R)

/-- Bilinearity of the existing tensor on the small site with separate Hom universe.
Source: Stacks 03EK (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: the four identities hold for sectionwise tensor maps on pure tensors. They pass
through module sheafification, yielding the four MonoidalPreadditive laws. -/
@[instance] theorem proEtaleTensorPreadditive (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    @MonoidalPreadditive (proEtaleRingModules X R) _ _
      (SheafOfModules.monoidalCategory R) := by
  exact SheafOfModules.cochainModulesPreadditive R

/-- The flat-term K-flat representatives used in the ordinary uncompleted tensor.
Source: Stacks 07A4 (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
def proEtaleFlatRepresentatives (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    ObjectProperty (CochainComplex (proEtaleRingModules X R) ℤ) :=
  fun P ↦ P.IsAcyclicTensorKFlat ∧
    ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology X) (R := R) (P.X n)

/-- A presentation of derived tensor by signed total tensor on flat K-flat complexes.
The representative isomorphism identifies the functor with the specified localization;
there is no completion or boundedness condition.
Source: Stacks 07A4 (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
structure ProEtaleTensorModel (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) where
  tensor : DerivedCategory (proEtaleRingModules X R) ×
    DerivedCategory (proEtaleRingModules X R) ⥤ DerivedCategory (proEtaleRingModules X R)
  representative :
    ((proEtaleFlatRepresentatives X R).ι.prod (proEtaleFlatRepresentatives X R).ι) ⋙
      Functor.uncurry.obj ((proEtaleOrdinaryTensor X R).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
    (((proEtaleFlatRepresentatives X R).ι ⋙ DerivedCategory.Q).prod
      ((proEtaleFlatRepresentatives X R).ι ⋙ DerivedCategory.Q)) ⋙ tensor

/-- The section m tensor n in the sheafified tensor, using the existing sheafification.
Source: Stacks 03EL (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
noncomputable def proEtaleTensorPair (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M N : proEtaleRingModules X R) (U : X.ProEtᵒᵖ)
    (m : M.val.obj U) (n : N.val.obj U) :
    (((proEtaleOrdinaryTensor X R).obj M).obj N).val.obj U :=
  (SheafOfModules.tensorObjIsoSheafification M N).inv.val.app U
    (((PresheafOfModules.sheafificationAdjunction.{u + 1}
      (𝟙 ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)).unit.app
          (M.val ⊗ N.val)).app U (m ⊗ₜ[R.obj.obj U] n))

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

/-- The ordinary comparison is uniquely determined by tensoring the canonical unit sections.
Naturality and the unit formula characterize the map on all local generators of inverse
image and scalar extension, including sections over objects not themselves base changes.
Source: Stacks 03EL (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: on a local generator send s tensor (m tensor n) to
(s tensor m) tensor (1 tensor n). The balancing relations make it linear and restriction
compatible; sheafification extends it. The inverse multiplies the two scalars. These
formulas prove both inverse laws and naturality. The adjunction unit is the specified
insertion on every base-change object. All inverse-image sections are locally generated
by its restrictions, so the displayed equation determines the comparison uniquely. -/
theorem proEtaleOrdinaryTensorPullback_existsUnique :
    ∃! mu : ∀ M N : proEtaleRingModules Y R,
      (proEtaleRingModulePullback f R S c).obj
          (((proEtaleOrdinaryTensor Y R).obj M).obj N) ≅
        ((proEtaleOrdinaryTensor X S).obj
          ((proEtaleRingModulePullback f R S c).obj M)).obj
            ((proEtaleRingModulePullback f R S c).obj N),
      (∀ (M M' N N' : proEtaleRingModules Y R) (v : M ⟶ M') (z : N ⟶ N'),
        (proEtaleRingModulePullback f R S c).map
            (((proEtaleOrdinaryTensor Y R).map v).app N ≫
              ((proEtaleOrdinaryTensor Y R).obj M').map z) ≫ (mu M' N').hom =
          (mu M N).hom ≫
            ((proEtaleOrdinaryTensor X S).map
              ((proEtaleRingModulePullback f R S c).map v)).app
                ((proEtaleRingModulePullback f R S c).obj N) ≫
            ((proEtaleOrdinaryTensor X S).obj
              ((proEtaleRingModulePullback f R S c).obj M')).map
                ((proEtaleRingModulePullback f R S c).map z)) ∧
      ∀ (M N : proEtaleRingModules Y R) (U : Y.ProEt)
        (m : M.val.obj (Opposite.op U)) (n : N.val.obj (Opposite.op U)),
        (mu M N).hom.val.app (Opposite.op ((proEtaleBaseChange f).obj U))
            (((proEtaleRingModuleAdjunction f R S c).unit.app
              (((proEtaleOrdinaryTensor Y R).obj M).obj N)).val.app (Opposite.op U)
                (proEtaleTensorPair Y R M N (Opposite.op U) m n)) =
          proEtaleTensorPair X S ((proEtaleRingModulePullback f R S c).obj M)
            ((proEtaleRingModulePullback f R S c).obj N)
            (Opposite.op ((proEtaleBaseChange f).obj U))
            (((proEtaleRingModuleAdjunction f R S c).unit.app M).val.app (Opposite.op U) m)
            (((proEtaleRingModuleAdjunction f R S c).unit.app N).val.app (Opposite.op U) n) := sorry

/-- The canonical ordinary comparison, selected with its full unique characterization.
Source: Stacks 03EL (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
noncomputable def proEtaleOrdinaryTensorPullback :=
  Classical.choose (proEtaleOrdinaryTensorPullback_existsUnique f R S c).exists

/-- Naturality of the selected ordinary comparison, needed to form its signed total.
Source: Stacks 03EL (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: take the naturality conjunct of the chosen witness's characterization. -/
theorem proEtaleOrdinaryTensorPullback_naturality
    (M M' N N' : proEtaleRingModules Y R) (v : M ⟶ M') (z : N ⟶ N') :
    (proEtaleRingModulePullback f R S c).map
        (((proEtaleOrdinaryTensor Y R).map v).app N ≫
          ((proEtaleOrdinaryTensor Y R).obj M').map z) ≫
        (proEtaleOrdinaryTensorPullback f R S c M' N').hom =
      (proEtaleOrdinaryTensorPullback f R S c M N).hom ≫
        ((proEtaleOrdinaryTensor X S).map
          ((proEtaleRingModulePullback f R S c).map v)).app
            ((proEtaleRingModulePullback f R S c).obj N) ≫
        ((proEtaleOrdinaryTensor X S).obj
          ((proEtaleRingModulePullback f R S c).obj M')).map
            ((proEtaleRingModulePullback f R S c).map z) := by
  exact (Classical.choose_spec
    (proEtaleOrdinaryTensorPullback_existsUnique f R S c).exists).1 M M' N N' v z

/-- The inverse ordinary comparison, summed over every bidegree with the usual signs.
Source: Stacks 07A4 (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
noncomputable def proEtaleTensorPullbackTotal
    (P Q : CochainComplex (proEtaleRingModules Y R) ℤ) :
    CochainComplex.mapBifunctor
      (((proEtaleRingModulePullback f R S c).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)
      (((proEtaleRingModulePullback f R S c).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Q) (proEtaleOrdinaryTensor X S) ⟶
    ((proEtaleRingModulePullback f R S c).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        (CochainComplex.mapBifunctor P Q (proEtaleOrdinaryTensor Y R)) := by
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.monoidalCategory S
  exact tensorPullbackTotal (proEtaleRingModulePullback f R S c)
    (proEtaleOrdinaryTensorPullback f R S c)
    (fun {_ _ _ _} v z ↦ proEtaleOrdinaryTensorPullback_naturality f R S c _ _ _ _ v z) P Q

/-- The total comparison is invertible since pullback preserves its sum and summand maps.
Source: Stacks 07A4 (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: pullback is a left adjoint, so preserves the coproducts in total tensor. Each
summand comparison is invertible. Thus each component, and hence the chain map, is invertible. -/
theorem proEtaleTensorPullbackTotal_isIso
    (P Q : CochainComplex (proEtaleRingModules Y R) ℤ) :
    IsIso (proEtaleTensorPullbackTotal f R S c P Q) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  exact tensorPullbackTotal_isIso (proEtaleRingModulePullback f R S c)
    (proEtaleOrdinaryTensorPullback f R S c)
    (fun {_ _ _ _} v z ↦ proEtaleOrdinaryTensorPullback_naturality f R S c _ _ _ _ v z)
    (proEtaleRingModuleDirectImage f R S c) (proEtaleRingModuleAdjunction f R S c) P Q

/-- The specified chain comparison as an isomorphism.
Source: Stacks 07A4 (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
noncomputable def proEtaleTensorPullbackTotalIso
    (P Q : CochainComplex (proEtaleRingModules Y R) ℤ) :=
  @asIso _ _ _ _ (proEtaleTensorPullbackTotal f R S c P Q)
    (proEtaleTensorPullbackTotal_isIso f R S c P Q)

/-- Pullback preserves flat K-flat representatives and has a unique canonical tensor comparison.
Source: Stacks 07A4 and 0G7E (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: flat pullback and the K-flat pullback theorem preserve the representative class.
Resolve both inputs by flat K-flat complexes. On them, compose the inverse of the total
ordinary comparison with the two tensor representative isomorphisms and the exact
pullback factorization. The displayed square is precisely this construction. Tensor
descent extends it naturally to all derived inputs and proves uniqueness. The identity
resolution gives the same formula when the inputs are already flat K-flat. -/
theorem proEtaleCanonicalTensorPullback
    (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S) :
    (∀ P : CochainComplex (proEtaleRingModules Y R) ℤ,
      proEtaleFlatRepresentatives Y R P →
        proEtaleFlatRepresentatives X S
          (((proEtaleRingModulePullback f R S c).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)) ∧
    ∃! alpha : a.tensor ⋙ proEtaleRingDerivedPullback f R S c ≅
      ((proEtaleRingDerivedPullback f R S c).prod
        (proEtaleRingDerivedPullback f R S c)) ⋙ b.tensor,
      ∀ (P Q : CochainComplex (proEtaleRingModules Y R) ℤ)
        (hp : proEtaleFlatRepresentatives Y R P) (hq : proEtaleFlatRepresentatives Y R Q),
        ∃ (hp' : proEtaleFlatRepresentatives X S
            (((proEtaleRingModulePullback f R S c).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P))
          (hq' : proEtaleFlatRepresentatives X S
            (((proEtaleRingModulePullback f R S c).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj Q)),
          (proEtaleRingDerivedPullback f R S c).map
              (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
            alpha.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
            b.tensor.map (Prod.mkHom
              ((proEtaleRingDerivedPullbackFactors f R S c).hom.app P)
              ((proEtaleRingDerivedPullbackFactors f R S c).hom.app Q)) =
          (proEtaleRingDerivedPullbackFactors f R S c).hom.app
              (CochainComplex.mapBifunctor P Q (proEtaleOrdinaryTensor Y R)) ≫
            (DerivedCategory.Q.mapIso (proEtaleTensorPullbackTotalIso f R S c P Q)).inv ≫
            b.representative.hom.app
              (⟨_, hp'⟩, ⟨_, hq'⟩) := sorry

/-- The unique derived comparison specified on every flat K-flat pair, rather than an
arbitrary natural isomorphism.
Source: Stacks 07A4 (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
noncomputable def proEtaleCanonicalTensorComparison
    (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S) :=
  Classical.choose (proEtaleCanonicalTensorPullback f R S c a b).2.exists

end AlgebraicGeometry.Scheme
