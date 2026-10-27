/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q50
-/
module

public import Sheaf.Algebra.Homology.RingedSiteGlobalHomIdentification
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
public import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
public import Sheaf.Paper.ModuleCupHomologyRepresentability
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import Sheaf.Paper.PullbackTensorCanonicalShiftUnit
import Sheaf.Paper.DerivedAdjunctionShift
import Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Sheaf.SixFunctors.ResolvingDerivedAdjunction
import Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction

/-! # Global-sections cup and evaluation on shifted derived Hom

Source: Stacks Project, Tags 0B6C, 0B6D and 08JA
(blueprint: lem-sfb-ringed-global-hom-cup-comparison).

The point is presented by ordinary A-modules, equivalently module sheaves on the
one-object identity-only site with only the maximal covering sieve. Scalar sections
are the recorded compatible-family construction. The pullback is specified by its
adjunction, and its tensor comparison by the ordinary unit formula and K-flat models.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures

namespace CategoryTheory.RingedGlobalHomCupComparison
open RingedSiteScalarGlobalSections RingedSiteGlobalHomIdentification

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u}) (A : Type u) [CommRing A]
  (s : A →+* Scalars R)
  [HasDerivedCategory.{u} (Modules R)]

/-- The ordinary sheaf tensor, using the recorded monoidal structure.
Source: Stacks 06YL (blueprint: lem-sfb-ringed-global-hom-cup-comparison). -/
abbrev moduleTensor : Modules R ⥤ Modules R ⥤ Modules R :=
  @MonoidalCategory.curriedTensor (Modules R) _ (SheafOfModules.monoidalCategory R)

/-- Flat-term K-flat coefficient complexes, as used by canonical derived pullback.
Source: Stacks 07A4 (blueprint: lem-sfb-ringed-global-hom-cup-comparison). -/
def ScalarFlat (P : CochainComplex (ModuleCat.{u} A) ℤ) : Prop :=
  (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P ∧
    ∀ n : ℤ, ObjectProperty.flat (P.X n)

/-- A presentation of pullback from the ringed point with the specified scalar action.
The ordinary adjunction uniquely determines the sheafified extension-of-scalars
functor, up to its unique adjunction-compatible isomorphism. Its unit fixes the ordinary
tensor comparison on pure tensors. The derived adjunction and tensor comparison are
normalized by those ordinary maps, so none of these is an arbitrary map or adjunction.
Source: Stacks 07A4, 0B6C, 0B6D
(blueprint: lem-sfb-ringed-global-hom-cup-comparison). -/
structure PullbackData
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{u, u, u, u} J R))
    (T : CoefficientTensorModels.{u, u, u, u} J R S) where
  ordinary : ModuleCat.{u} A ⥤ Modules R
  [additive : ordinary.Additive]
  [colimits : PreservesColimitsOfSize.{0, 0} ordinary]
  adjunction : ordinary ⊣ sections R A s
  ordinaryTensor : (Functor.postcompose₂.obj ordinary).obj
      (curriedTensor (ModuleCat.{u} A)) ≅
    (((Functor.whiskeringLeft₂ _).obj ordinary).obj ordinary).obj (moduleTensor R)
  unit_formula : ∀ (M N : ModuleCat.{u} A) (x : M) (y : N) (U : Cᵒᵖ),
    (((ordinaryTensor.hom.app M).app N).val.app U)
        ((adjunction.unit.app (M ⊗ N) (x ⊗ₜ[A] y)).val U) =
      (SheafOfModules.tensorObjIsoSheafification (R := R)
        (ordinary.obj M) (ordinary.obj N)).inv.val.app U
          (((PresheafOfModules.sheafificationAdjunction.{u} (𝟙
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
              ((ordinary.obj M).val ⊗ (ordinary.obj N).val)).app U
                (((adjunction.unit.app M x).val U) ⊗ₜ[R.obj.obj U]
                  ((adjunction.unit.app N y).val U)))
  left : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (Modules R)
  epsilon : DerivedCategory.Qh ⋙ left ⟶
    ordinary.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  isLeftDerived : left.IsLeftDerivedFunctor epsilon
    (HomotopyCategory.quasiIso (ModuleCat.{u} A) (.up ℤ))
  flat : ∀ (P : CochainComplex (ModuleCat.{u} A) ℤ), ScalarFlat A P →
    CochainComplex.IsKFlatIndependentCoefficients
      ((ordinary.mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ n : ℤ, (((ordinary.mapHomologicalComplex (.up ℤ)).obj P).X n).IsFlat
  derivedAdjunction : left ⊣ derivedSections R A s
  adjunction_formula : ∀ (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : Complexes R) (f : (ordinary.mapHomologicalComplex (.up ℤ)).obj P ⟶ I),
    derivedAdjunction.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)
        (derivedPullbackComplexComparison ordinary left epsilon P ≫
          DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((adjunction.mapHomologicalComplex (.up ℤ)).homEquiv P I f) ≫
        (sections R A s).rightDerivedFunctorUnitQ I
  tensor : Functor.uncurry.obj (curriedTensor (DerivedCategory (ModuleCat.{u} A))) ⋙ left ≅
    (left.prod left) ⋙ S.tensor
  tensor_formula : ∀ (P Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : ScalarFlat A P) (hQ : ScalarFlat A Q),
    tensor.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        S.tensor.map
          (X := (left.obj (DerivedCategory.Q.obj P), left.obj (DerivedCategory.Q.obj Q)))
          (Y := (DerivedCategory.Q.obj ((ordinary.mapHomologicalComplex (.up ℤ)).obj P),
            DerivedCategory.Q.obj ((ordinary.mapHomologicalComplex (.up ℤ)).obj Q)))
          (Prod.mkHom (derivedPullbackComplexComparison ordinary left epsilon P)
            (derivedPullbackComplexComparison ordinary left epsilon Q)) =
      left.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
        derivedPullbackComplexComparison ordinary left epsilon (P ⊗ Q) ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorComparison ordinaryTensor.hom (.up ℤ) P Q) ≫
        (T.iso J R S _ _ (flat P hP).1 (flat Q hQ).1).hom

attribute [instance] PullbackData.additive

/-- The prescribed relative cup is the adjoint of the tensor of the two counits.
Source: Stacks 0B6C (blueprint: lem-sfb-ringed-global-hom-cup-comparison). -/
def cup
    {S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{u, u, u, u} J R)}
    {T : CoefficientTensorModels.{u, u, u, u} J R S} (p : PullbackData R A s S T)
    (K L : DerivedCategory (Modules R)) :
    (derivedSections R A s).obj K ⊗ (derivedSections R A s).obj L ⟶
      (derivedSections R A s).obj (S.tensor.obj (K, L)) :=
  p.derivedAdjunction.homEquiv _ _
    (p.tensor.hom.app ((derivedSections R A s).obj K, (derivedSections R A s).obj L) ≫
      S.tensor.map (p.derivedAdjunction.counit.app K, p.derivedAdjunction.counit.app L))

/-- Native symmetry on ordinary module derived categories, induced by Koszul symmetry.
Source: Stacks 08J9 (blueprint: lem-sfb-ringed-global-hom-cup-comparison). -/
@[instance_reducible] def scalarSymmetry : BraidedCategory (DerivedCategory (ModuleCat.{u} A)) :=
  CategoryTheory.DerivedMonoidal.braidedCategory' DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ModuleCat.{u} A) (.up ℤ))

/-- Right-tensor transposition for the existing ordinary-module derived internal Hom.
The native closed API uses left tensor; the Koszul symmetry converts it to right tensor.
Source: Stacks 08J9 (blueprint: lem-sfb-ringed-global-hom-cup-comparison). -/
def transpose (X Y Z : DerivedCategory (ModuleCat.{u} A)) :
    (X ⊗ Y ⟶ Z) ≃ (X ⟶ (ordinaryModuleDerivedInternalHom A).obj (op Y, Z)) :=
  ((Iso.homCongr ((scalarSymmetry A).braiding Y X) (Iso.refl Z)).symm).trans
    ((ihom.adjunction Y).homEquiv X Z)

/-- The shifted free rank-one module tensored with Y is Y[-n], with canonical signs.
Source: Stacks 08JA, 064B (blueprint: lem-sfb-ringed-global-hom-cup-comparison). -/
def singleAction (n : ℤ) (Y : DerivedCategory (ModuleCat.{u} A)) :
    DerivedCategory.Q.obj
      ((HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) n).obj (ModuleCat.of A A)) ⊗ Y ≅
        Y⟦-n⟧ :=
  whiskerRightIso
    ((((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso (-n) n 0
      (neg_add_cancel n)).app (ModuleCat.of A A)).symm ≪≫
        (shiftFunctor _ (-n)).mapIso (DerivedCategory.singleFunctorObjUnitIso (ModuleCat A))) Y ≪≫
    ((tensorRight Y).commShiftIso (-n)).app (𝟙_ _) ≪≫
      (shiftFunctor _ (-n)).mapIso (λ_ Y)

/-- The comparison, its evaluation formula, and its canonical all-degree identifications.
Naturality is expressed by the natural transformation type. The source equivalences
have the recorded Hom-cocycle normalization. The target equivalences are fixed on
every cocycle z of a representative K: the chain map from A[-n] sending 1 to z is
uncurried and composed with the canonical shifted left unitor. They are not chosen
merely to make the final formula hold.
Source: Stacks 0B6C, 0B6D, 08JA
(blueprint: lem-sfb-ringed-global-hom-cup-comparison). -/
structure Comparison
    {S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{u, u, u, u} J R)}
    {T : CoefficientTensorModels.{u, u, u, u} J R S} (p : PullbackData R A s S T) where
  chi : globalHom R A s ⟶
    ((derivedSections R A s).op.prod (derivedSections R A s)) ⋙ ordinaryModuleDerivedInternalHom A
  formula : ∀ (L M : DerivedCategory (Modules R)), chi.app (op L, M) =
    transpose A _ _ _
      (cup R A s p ((derivedInternalHomOfUniverses.{u, u, u, u} J R).obj (op L, M)) L ≫
        (derivedSections R A s).map (S.evaluation L M))
  sourceIdentification : HomIdentification R A s
  targetIdentification : ∀ (Y Z : DerivedCategory (ModuleCat.{u} A)) (n : ℤ),
    ((DerivedCategory.homologyFunctor (ModuleCat A) n).obj
      ((ordinaryModuleDerivedInternalHom A).obj (op Y, Z))) ≃+ (Y ⟶ Z⟦n⟧)
  target_normalization : ∀ (Y Z : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (e : DerivedCategory.Q.obj K ⟶ (ordinaryModuleDerivedInternalHom A).obj (op Y, Z))
    (f : (HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) n).obj (ModuleCat.of A A) ⟶ K)
    (z : K.cycles n),
    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n (ModuleCat.of A A)).inv ≫
      f.f n) (1 : A) = K.iCycles n z →
    targetIdentification Y Z n
      (((DerivedCategory.homologyFunctor (ModuleCat A) n).map e)
        (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n).app K).inv
          (K.homologyπ n z))) =
      (shiftEquiv' (DerivedCategory (ModuleCat A)) (-n) n (neg_add_cancel n)).toAdjunction.homEquiv
        Y Z ((singleAction A n Y).inv ≫ (transpose A _ Y Z).symm (DerivedCategory.Q.map f ≫ e))
  cohomology_formula : ∀ (L M : DerivedCategory (Modules R)) (n : ℤ) (v : L ⟶ M⟦n⟧),
    targetIdentification ((derivedSections R A s).obj L) ((derivedSections R A s).obj M) n
      (((DerivedCategory.homologyFunctor (ModuleCat A) n).map (chi.app (op L, M)))
        ((sourceIdentification.equiv L M n).symm v)) =
      (derivedSections R A s).map v ≫
        ((derivedSections R A s).commShiftIso n).hom.app M

/-- Global-sections cup followed by evaluation transposes to the canonical natural
comparison, and on every shifted Hom group it applies derived global sections.
No boundedness, flatness of the structural scalar map, quasi-coherence, perfectness
or invertibility of the comparison is required.

Source: Stacks Project, Tags 0B6C, 0B6D, 08JA and 08J9
(blueprint: lem-sfb-ringed-global-hom-cup-comparison).

Proof: (1) Choose the recorded K-flat tensor model and derive the module pullback
adjunction to the scalar-valued sections functor. The canonical tensor comparison
and unit/shift coherence are those of lem-weil-pbc-pullback-tensor-canonical-shift-unit;
lem-weil-pbc-derived-adjunction-shift gives shift compatibility of its counit.
(2) Transpose the tensor of the two counits to define cup, then transpose cup followed
by derived sections of evaluation to obtain chi. Naturality of evaluation, tensor
comparison and counit proves contravariance in L and covariance in M.
(3) lem-sfb-derived-internal-hom-sections-model identifies the section Hom complex
with global Hom cochains; lem-sc-module-cup-homology-representability identifies
its degree-n classes with maps from A[-n]. (4) Choose a flat K-flat P for L and a
K-injective I for M, using lem-pc-kflat-resolution and prop-pur-kinjective-resolutions-exist.
By lem-pur-hom-kflat-into-kinjective the sheaf Hom(P,I) is K-injective. Its sections
complex represents G(H(L,M)); no K-injectivity of that sections complex is asserted.
(5) For the cocycle phi representing v, lem-sfb-resolving-derived-adjunction-normalization
and the ordinary module adjunction take 1 mapped to phi to r mapped to r*phi.
Componentwise uncurrying from lem-sf-ringed-derived-tensor-hom-adjunction identifies
evaluation with v[-n], after the shifted left unitor. (6) The inverse adjunction
formula expands the transpose of cup/evaluation to evaluation composed with the two
counits and the canonical tensor comparison. (7) Naturality of this comparison and
the shifted unitors, then shift compatibility of the counit, identify that transpose
with G(v[-n]) after its canonical shift comparison. (8) Repeat the Hom-cocycle
calculation on the one-object A-site. It is precisely target_normalization, so
shifting back gives G(v) followed by G(M[n]) isomorphic to G(M)[n]. This works for
all integers, zero objects, the zero ring and the empty site. -/
theorem globalHomCupComparison :
    ∃ S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{u, u, u, u} J R),
      ∃ T : CoefficientTensorModels.{u, u, u, u} J R S,
        ∃ p : PullbackData R A s S T, Nonempty (Comparison R A s p) := by
  sorry

end CategoryTheory.RingedGlobalHomCupComparison
