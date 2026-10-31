/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientReductionCore
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.SystemScalarCoherence
import Mathlib.CategoryTheory.Sites.CoverLifting

/-! # Constant systems preserve flat-term K-flat complexes

Source: Zheng Construction 4.1; Stacks 03EK and 06YY.
(blueprint: lem-pur-quotient-constant-kflat).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
variable (R : Sheaf J CommRingCat.{max c v r})

/-- Constant systems preserve flat-term K-flat complexes on the vertical sequence site.
Source: Zheng Construction 4.1; Stacks 0G7E
(blueprint: lem-pur-quotient-constant-kflat).
Proof: the projection from the vertical sequence site has the constant-sequence
functor as inverse image on sheaves of sets, with right adjoint inverse limit.
Finite limits are computed componentwise, so this is a geometric morphism.
The inverse image of R is precisely quotientConstantRing, and its module inverse
image is quotientConstant, with unchanged actions and vertical restrictions.
Apply K-flat pullback (Stacks 0G7E) with the identity structural coefficient map.
Extension along that identity is naturally the identity on modules, normalized
by multiplication on tensors. Transport K-flatness and degreewise flatness
through this natural isomorphism. This proves both clauses without any varying
coefficient ring, scalar model, or tensor-comparison data. -/
theorem quotientConstant_preservesGood
    (P : CochainComplex (Mod.{c, v, max c v r} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (fP : flatTerms.{c, v, r} J R P) :
    CochainComplex.IsKFlatIndependentCoefficients (R := quotientConstantRing.{c, v, r} J R)
      (((quotientConstant.{c, v, r} J R).mapHomologicalComplex (.up ℤ)).obj P) ∧
    flatTerms.{c, v, r} (coefficientSequenceTopology J) (quotientConstantRing.{c, v, r} J R)
      (((quotientConstant.{c, v, r} J R).mapHomologicalComplex (.up ℤ)).obj P) := by
  classical
  let p := CategoryTheory.Prod.snd ℕ C
  let K := coefficientSequenceTopology J
  let S := quotientConstantRing.{c, v, r} J R
  let F := quotientConstant.{c, v, r} J R
  let : p.IsCocontinuous K J := ⟨fun h ↦ h⟩
  let : ∀ (G : (ℕ × C)ᵒᵖ ⥤ Type (max c v r)),
      p.op.HasPointwiseRightKanExtension G := fun G X ↦ by
    let : HasLimitsOfShape (StructuredArrow X p.op) (Type (max c v r)) :=
      hasLimitsOfShape_of_essentiallySmall _ _
    infer_instance
  let L := p.sheafPushforwardContinuous (Type (max c v r)) K J
  let V := p.sheafPushforwardCocontinuous (Type (max c v r)) K J
  let adj : L ⊣ V := p.sheafAdjunctionCocontinuous (Type (max c v r)) K J
  let I : SheafOfModules.AlgebraicInverseImage L R S :=
    { ringUnderlying := Iso.refl _
      ringAdd := by intro T a b t h U x; exact h (op U.unop.2) x
      ringMul := by intro T a b t h U x; exact h (op U.unop.2) x
      ringZero := by intro T a h U x; exact h (op U.unop.2) x
      ringOne := by intro T a h U x; exact h (op U.unop.2) x
      modules := F
      moduleUnderlying := NatIso.ofComponents (fun M ↦ Iso.refl _) (by intros; rfl)
      moduleAdd := by intro M T a b t h U x; exact h (op U.unop.2) x
      moduleZero := by intro M T a h U x; exact h (op U.unop.2) x
      moduleSMul := by intro M T a b t h U x; exact h (op U.unop.2) x }
  let A : SheafOfModules.SystemScalarModel.{c, v, max c v r} (𝟙 S) :=
    (SheafOfModules.nonempty_systemScalarModel.{c, v, max c v r} _).some
  let T := F ⋙ A.model.E
  have ht := SheafOfModules.isKFlat_ringedToposPullback L V adj I (𝟙 S) T
    (fun M ↦ A.model.obj_eq (F.obj M))
    (fun f ↦ A.model.map_eq (F.map f)) P hP fP
  let e : T ≅ F := Functor.isoWhiskerLeft F
    (SheafOfModules.systemScalarModelUnit rfl A) ≪≫ F.rightUnitor
  let ec := (NatIso.mapHomologicalComplex e (.up ℤ)).app P
  exact ⟨SheafOfModules.kFlat_iso_independent S ec ht.1,
    fun i ↦ SheafOfModules.flatOnSite_of_iso S
      ((HomologicalComplex.eval _ (.up ℤ) i).mapIso ec) (ht.2 i)⟩

end WeilConjectures.SemilinearSections
