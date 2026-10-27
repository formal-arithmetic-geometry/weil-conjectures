/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.Paper.NormAlgclCohomologyTopologyComparison
public import Sheaf.Paper.InternalScalarTensorComparison
public import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
public import Sheaf.Paper.QlbarInternalHomCoefficientComparison
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Paper.AdicConstructibilityPredicateComparison
import Sheaf.Paper.ConstructibleInternalHomContinuity
import Sheaf.CategoryTheory.DerivedSectionsScalarCoherence
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import Sheaf.Algebra.Homology.ScalarInternalHomAdjunction
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-! # Canonical finite-model coefficient-topology comparison maps

Source: blueprint main-20261015, stability direct-images proof, paragraph (3),
agent topology-comparison obligation, with the eight-step DAG proof
(blueprint: def-sfb-finite-model-topology-comparison-maps).

All scalar extensions below are the existing total left derived functors. The tensor
comparison uses the scalar-unit normalized ordinary comparison and its K-flat derived
lift. In particular no flatness assumption is made on the coefficient inclusion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteModelTopologyHom

variable (X : Scheme.{u})
  {R S T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  [MonObj T] [IsCommMonObj T]


/-- The published extension-restriction adjunction, with the scalar functor's
structural arguments fixed before coefficient specialization. Its unit is v to 1 tensor v.
Source: DAG K-flat scalar-extension convention, Stacks 07A4
(blueprint: def-sfb-finite-model-topology-comparison-maps). -/
def scalarAdjunction
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] :
    CondensedRing.internalScalarExtension a X ⊣
      (Mod.comap (coefficientMap a X)).mapDerivedCategory :=
  Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)

/-- The actual scalar-extended evaluation transpose. The adjunction uses K tensor D;
the Koszul braiding gives the equivalent D tensor K convention of the DAG.
Source: DAG phi_R and proof steps 4, 5, 7, Stacks 08J9
(blueprint: def-sfb-finite-model-topology-comparison-maps). -/
@[irreducible] def homComparison
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    (K N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (CondensedRing.internalScalarExtension a X).obj
        (((CondensedRing.derivedHom Λ X).obj (op K)).obj N) ⟶
      ((CondensedRing.derivedHom Λ' X).obj
        (op ((CondensedRing.internalScalarExtension a X).obj K))).obj
          ((CondensedRing.internalScalarExtension a X).obj N) :=
  (CondensedRing.derivedTensorHomAdjunction Λ'
    ((CondensedRing.internalScalarExtension a X).obj K)).homEquiv _ _
      (((CondensedRing.internalScalarTensorIso a X).inv.app K).app
          (((CondensedRing.derivedHom Λ X).obj (op K)).obj N) ≫
        (CondensedRing.internalScalarExtension a X).map
          ((CondensedRing.derivedTensorHomAdjunction Λ K).counit.app N))


/-- The bifunctorial action of the existing derived internal Hom.
Source: DAG naturality in K and N
(blueprint: def-sfb-finite-model-topology-comparison-maps). -/
def homArrow
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {K K' N N' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (f : K' ⟶ K) (g : N ⟶ N') :=
  ((CondensedRing.derivedHom Λ X).map f.op).app N ≫
    ((CondensedRing.derivedHom Λ X).obj (op K')).map g



/-- Derived sections of underlying abelian sheaves. This is the same ordinary unbounded
R Gamma as in the recorded coefficient-topology comparison, for any ring object.
Source: DAG global-sections convention, Stacks 0D6E
(blueprint: def-sfb-finite-model-topology-comparison-maps). -/
def sections (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] :=
  letI := (constantSheafΓAdj (Scheme.ProEt.topology X) Ab.{u + 1}).isRightAdjoint
  letI : (Sheaf.Γ (Scheme.ProEt.topology X) Ab.{u + 1}).Additive :=
    Functor.additive_of_preserves_binary_products _
  (Mod.forget R).mapDerivedCategory ⋙
    (Sheaf.Γ (Scheme.ProEt.topology X) Ab.{u + 1}).rightDerivedFunctor


/-- Forgetting a restricted action preserves underlying derived sheaves canonically.
Source: DAG scalar-forgetting identification, Stacks 0D6E
(blueprint: def-sfb-finite-model-topology-comparison-maps). -/
def restrictionSections (a : R ⟶ S) [IsMonHom a] :
    (Mod.comap a).mapDerivedCategory ⋙ sections X R ≅ sections X S :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryCompIso (Mod.comap a) (Mod.forget R)).symm _


/-- The composition comparison for coefficients pulled back from the point.
Source: DAG proof step 7, scalar reassociation (Stacks 0D6D)
(blueprint: def-sfb-finite-model-topology-comparison-maps). -/
def coefficientComposition
    {Λ Λ' Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    [MonObj Λ''] [IsCommMonObj Λ'']
    (a : Λ ⟶ Λ') [IsMonHom a] (b : Λ' ⟶ Λ'') [IsMonHom b] :
    CondensedRing.internalScalarExtension a X ⋙ CondensedRing.internalScalarExtension b X ≅
      CondensedRing.internalScalarExtension (a ≫ b) X :=
  (((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).comp
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap b X))).ofNatIsoRight
      ((Functor.mapDerivedCategoryCompIso
          (Mod.comap (coefficientMap b X)) (Mod.comap (coefficientMap a X))).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          ((Mod.comapComp (coefficientMap a X) (coefficientMap b X)).symm ≪≫
            Mod.comapCongr (coefficientMap_comp a b X).symm))).leftAdjointUniq
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap (a ≫ b) X))

/-- The scalar-unit adjunct of a specified scalar-extended arrow.
Source: DAG m_D and Psi, Stacks 07A4
(blueprint: def-sfb-finite-model-topology-comparison-maps). -/
def restrictionMate
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    (V : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (W : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ' X)))
    (f : (CondensedRing.internalScalarExtension a X).obj V ⟶ W) :
    V ⟶ (Mod.comap (coefficientMap a X)).mapDerivedCategory.obj W :=
  (scalarAdjunction X a).homEquiv V W f

/-- Derived sections of a specified scalar adjunct, with the canonical action forgetting.
Source: DAG Psi and R Gamma(m_D), Stacks 0D6E
(blueprint: def-sfb-finite-model-topology-comparison-maps). -/
def globalize
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    (V : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (W : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ' X)))
    (f : (CondensedRing.internalScalarExtension a X).obj V ⟶ W) :
    (sections X (condensedRingObj Λ X)).obj V ⟶
      (sections X (condensedRingObj Λ' X)).obj W :=
  (sections X (condensedRingObj Λ X)).map (restrictionMate X a V W f) ≫
    (restrictionSections X (coefficientMap a X)).hom.app W

/-- Composition of exact restrictions for a tower of pulled-back coefficient maps.
Source: DAG scalar-forgetting identification, Stacks 0D6D
(blueprint: def-sfb-finite-model-topology-comparison-maps). -/
def restrictionComposition
    {Λ Λ' Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    [MonObj Λ''] [IsCommMonObj Λ'']
    (a : Λ ⟶ Λ') [IsMonHom a] (b : Λ' ⟶ Λ'') [IsMonHom b] :
    (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientMap b X)).mapDerivedCategory ⋙
      (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientMap a X)).mapDerivedCategory ≅
        (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientMap (a ≫ b) X)).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso
      (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientMap b X)) (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientMap a X))).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((Mod.comapComp (coefficientMap a X) (coefficientMap b X)).symm ≪≫
        Mod.comapCongr (coefficientMap_comp a b X).symm)

/-- Restrict a specified middle-linear coefficient arrow to the initial ring.
Source: DAG A-linear m_D, Stacks 0D6D
(blueprint: def-sfb-finite-model-topology-comparison-maps). -/
def restrictTowerMap
    {Λ Λ' Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    [MonObj Λ''] [IsCommMonObj Λ'']
    (a : Λ ⟶ Λ') [IsMonHom a] (b : Λ' ⟶ Λ'') [IsMonHom b]
    (V : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ' X)))
    (W : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ'' X)))
    (f : V ⟶ (Mod.comap (coefficientMap b X)).mapDerivedCategory.obj W) :
    (Mod.comap (coefficientMap a X)).mapDerivedCategory.obj V ⟶
      (Mod.comap (coefficientMap (a ≫ b) X)).mapDerivedCategory.obj W :=
  (Mod.comap (coefficientMap a X)).mapDerivedCategory.map f ≫
    (restrictionComposition X a b).hom.app W

/-- The evaluation transpose along the second scalar map, transported by the canonical
composition isomorphisms on both Hom arguments.
Source: DAG chi defining Psi, Stacks 08J9
(blueprint: def-sfb-finite-model-topology-comparison-maps). -/
def towerHomComparison
    {Λ Λ' Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    [MonObj Λ''] [IsCommMonObj Λ'']
    (a : Λ ⟶ Λ') [IsMonHom a] (b : Λ' ⟶ Λ'') [IsMonHom b]
    (K N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :=
  homComparison X b
      ((CondensedRing.internalScalarExtension a X).obj K)
      ((CondensedRing.internalScalarExtension a X).obj N) ≫
    homArrow X Λ'' ((coefficientComposition X a b).inv.app K)
      ((coefficientComposition X a b).hom.app N)

/-- The composite scalar-extended evaluation along a coefficient tower, starting at
extension along the composite map. This is an actual arrow, not an arbitrary choice.
Source: DAG equality of scalar-extended evaluation transposes, Stacks 07A4 and 08J9
(blueprint: def-sfb-finite-model-topology-comparison-maps). -/
def evaluationRoute
    {Λ Λ' Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    [MonObj Λ''] [IsCommMonObj Λ'']
    (a : Λ ⟶ Λ') [IsMonHom a] (b : Λ' ⟶ Λ'') [IsMonHom b]
    (K N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :=
  (coefficientComposition X a b).inv.app
      (((CondensedRing.derivedHom Λ X).obj (op K)).obj N) ≫
    (CondensedRing.internalScalarExtension b X).map (homComparison X a K N) ≫
    towerHomComparison X a b K N

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The E to C inclusion already specified by the finite-subextension framework.
Source: DAG A to C_X (blueprint: def-sfb-finite-model-topology-comparison-maps). -/
abbrev finiteToUnion := Profinite.padicSubfieldRingObjToPadicAlgCl.{u} ℓ E

/-- The E to B inclusion is the composite through the finite-subextension ring.
Source: DAG A to B_X (blueprint: def-sfb-finite-model-topology-comparison-maps). -/
abbrev finiteToNorm := finiteToUnion ℓ E ≫ NormAlgclComparison.coefficientInclusion ℓ

/-- S_C is total K-flat scalar extension to finite-subextension-valued coefficients.
Source: DAG S_C (blueprint: def-sfb-finite-model-topology-comparison-maps). -/
def toUnion := CondensedRing.internalScalarExtension (finiteToUnion ℓ E) X

/-- S_B is total K-flat scalar extension to all norm-continuous coefficients.
Source: DAG S_B (blueprint: def-sfb-finite-model-topology-comparison-maps). -/
def toNorm := CondensedRing.internalScalarExtension (finiteToNorm ℓ E) X

/-- The canonical JS_C to S_B reassociation, including its scalar-unit normalization.
Source: DAG Psi and proof step 7
(blueprint: def-sfb-finite-model-topology-comparison-maps). -/
def reassociation := coefficientComposition X (finiteToUnion ℓ E)
  (NormAlgclComparison.coefficientInclusion ℓ)

variable (K N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  (condensedRingObj (Profinite.continuousMapRingObj E) X)))

/-- D is the existing relative derived internal Hom of the finite-field inputs.
Source: DAG definition of D (blueprint: def-sfb-finite-model-topology-comparison-maps). -/
def finiteHom :=
  ((CondensedRing.derivedHom (Profinite.continuousMapRingObj E) X).obj (op K)).obj N

/-- The existing relative derived Hom after extension to finite-valued coefficients.
Source: DAG target of phi_C (blueprint: def-sfb-finite-model-topology-comparison-maps). -/
def unionHom :=
  ((CondensedRing.derivedHom (Profinite.padicAlgClRingObj ℓ) X).obj
    (op ((toUnion X ℓ E).obj K))).obj ((toUnion X ℓ E).obj N)

/-- The existing relative derived Hom after extension to norm-continuous coefficients.
Source: DAG target of phi_B (blueprint: def-sfb-finite-model-topology-comparison-maps). -/
def normHom :=
  ((CondensedRing.derivedHom (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X).obj
    (op ((toNorm X ℓ E).obj K))).obj ((toNorm X ℓ E).obj N)

/-- The C-linear coefficient comparison is the scalar unit followed by reassociation.
It is represented by z tensor v mapping to c_X(z) tensor v.
Source: DAG m_D and proof step 7
(blueprint: def-sfb-finite-model-topology-comparison-maps). -/
def coefficientComparison :=
  restrictionMate X (NormAlgclComparison.coefficientInclusion ℓ)
    _ _ ((reassociation X ℓ E).hom.app K)

/-- The same coefficient comparison as an A-linear map, using the canonical
composition comparison of exact restrictions.
Source: DAG m_D and proof step 7
(blueprint: def-sfb-finite-model-topology-comparison-maps). -/
def finiteCoefficientComparison :=
  restrictTowerMap X (finiteToUnion ℓ E) (NormAlgclComparison.coefficientInclusion ℓ)
    _ _ (coefficientComparison X ℓ E K)

/-- R Gamma of the actual coefficient comparison, with the prescribed action-forgetting
identification on its target.
Source: DAG R Gamma(m_D), Stacks 0D6E
(blueprint: def-sfb-finite-model-topology-comparison-maps). -/
def globalCoefficientComparison :=
  globalize X (NormAlgclComparison.coefficientInclusion ℓ)
    _ _ ((reassociation X ℓ E).hom.app K)

/-- Applying J to evaluation and transposing gives chi; transport its two arguments
by the canonical JS_C to S_B comparisons. This is the actual induced internal Hom map.
Source: DAG Psi and proof step 7
(blueprint: def-sfb-finite-model-topology-comparison-maps). -/
def inducedHom :=
  towerHomComparison X (finiteToUnion ℓ E) (NormAlgclComparison.coefficientInclusion ℓ) K N

/-- The actual derived global Hom morphism Psi induced by J: insert its scalar unit,
apply J to evaluation, transpose, and use the canonical reassociations and scalar
forgetting comparison. No arbitrary comparison morphism is an input.
Source: DAG Psi and proof steps 7--8
(blueprint: def-sfb-finite-model-topology-comparison-maps). -/
def globalHomComparison :=
  globalize X (NormAlgclComparison.coefficientInclusion ℓ) _ _ (inducedHom X ℓ E K N)











end AlgebraicGeometry.ProEtale.FiniteModelTopologyHom
