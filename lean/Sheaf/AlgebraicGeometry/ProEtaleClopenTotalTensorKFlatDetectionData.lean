/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q71
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Sheaf.Paper.CoefficientRingedTensorHomModel
import Sheaf.Algebra.Homology.TotalTensorSignedCoherence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Tensor restriction and flatness on finite clopen pro-etale partitions

Source: Stacks Project, sites-modules.tex, Tag 0GMW and its bilinear universal property;
sites-cohomology.tex, Tags 06YN and 0FPQ; finite-clopen application in the node's proof.
(blueprint: lem-pur-clopen-total-tensor-kflat-detection)

All abbreviations below expose the recorded sectionwise restriction and tensor constructions.
The zero insertion in the last clause is characterized by its restrictions: the identity at
its own component and zero elsewhere. This covers every zero insertion supplied by gluing.
-/

@[expose] public noncomputable section

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures

attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory

namespace AlgebraicGeometry.Scheme.ProEt

namespace ClopenData

/-- The recorded module category, in the fixed universe containing the small site.
Source: Stacks 03D7 (blueprint: lem-pur-clopen-total-tensor-kflat-detection). -/
abbrev clopenTensorModules {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :=
  ringedSiteModules.{max u (t + 1)}
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)

/-- Commutative-ring restriction along the same composition functor as ring restriction.
Source: Stacks 04TR (blueprint: lem-pur-clopen-total-tensor-kflat-detection). -/
abbrev clopenTensorRings {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j] :=
  (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).sheafPushforwardContinuous
    CommRingCat.{max u (t + 1)} (topology Y) (topology X)

/-- The dependency's actual restriction, with its sectionwise module actions unchanged.
Source: Stacks 04TR (blueprint: lem-pur-clopen-total-tensor-kflat-detection). -/
abbrev clopenTensorRestriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    clopenTensorModules.{t, u} R ⥤
      clopenTensorModules.{t, u} ((clopenTensorRings.{t, u} j).obj R) :=
  clopenModuleRestriction j
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)}
      RingCat.{max u (t + 1)})).obj R)

/-- The recorded additivity instance, exposed for degreewise restriction.
Source: Stacks 04TR (blueprint: lem-pur-clopen-total-tensor-kflat-detection). -/
instance clopenTensorRestrictionAdditive {X Y : Scheme.{t}} (j : Y ⟶ X)
    [IsOpenImmersion j] (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    (clopenTensorRestriction.{t, u} j R).Additive :=
  clopenModuleRestriction_additive j _

/-- Degreewise restriction of unbounded cochain complexes.
Source: Stacks 06YN (blueprint: lem-pur-clopen-total-tensor-kflat-detection). -/
abbrev clopenTensorComplexRestriction {X Y : Scheme.{t}} (j : Y ⟶ X)
    [IsOpenImmersion j] (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :=
  (clopenTensorRestriction.{t, u} j R).mapHomologicalComplex (.up ℤ)

/-- The comparison in the direction displayed in the node is the inverse tensorator.
Its input structure contains the associativity, symmetry and both unit diagrams.
Source: Stacks 0GMW (blueprint: lem-pur-clopen-total-tensor-kflat-detection). -/
def clopenTensorComparison {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (h : (clopenTensorRestriction.{t, u} j R).Braided) (F H : clopenTensorModules.{t, u} R) :
    (clopenTensorRestriction.{t, u} j R).obj (F ⊗ H) ≅
      (clopenTensorRestriction.{t, u} j R).obj F ⊗ (clopenTensorRestriction.{t, u} j R).obj H :=
  letI := h
  (Functor.Monoidal.μIso (clopenTensorRestriction.{t, u} j R) F H).symm

/-- Restriction of the module tensor unit is the component ring module.
Source: Stacks 0GMW (blueprint: lem-pur-clopen-total-tensor-kflat-detection). -/
def clopenTensorUnitComparison {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (h : (clopenTensorRestriction.{t, u} j R).Braided) :
    (clopenTensorRestriction.{t, u} j R).obj (𝟙_ (clopenTensorModules.{t, u} R)) ≅
      𝟙_ (clopenTensorModules.{t, u} ((clopenTensorRings.{t, u} j).obj R)) :=
  letI := h
  (Functor.Monoidal.εIso (clopenTensorRestriction.{t, u} j R)).symm

/-- A local pure tensor, using the existing sheafification unit and tensor comparison.
Source: Stacks 0GMW (blueprint: lem-pur-clopen-total-tensor-kflat-detection). -/
def clopenTensorPure {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (F H : clopenTensorModules.{t, u} R) (U : X.ProEtᵒᵖ)
    (x : F.val.obj U) (y : H.val.obj U) : (F ⊗ H).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction.{max u (t + 1)}
    (𝟙 ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)}
      RingCat.{max u (t + 1)})).obj R).obj)).unit.app (F.val ⊗ H.val) ≫
    (SheafOfModules.tensorObjIsoSheafification (R := R) F H).inv.val).app U)
    (x ⊗ₜ[R.obj.obj U] y)

/-- The actual total-tensor summand inclusion, with its total bifunctor explicit.
Source: Stacks 0FPQ (blueprint: lem-pur-clopen-total-tensor-kflat-detection). -/
def clopenTotalTensorSummand {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (P Q : CochainComplex (clopenTensorModules.{t, u} R) ℤ)
    (p q n : ℤ) (hpq : p + q = n) :
    P.X p ⊗ Q.X q ⟶
      ((coefficientTotalTensor.{u, t + 1, t} (topology X) R).obj (P, Q)).X n :=
  letI := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  HomologicalComplex.ιMapBifunctor P Q (curriedTensor _) (.up ℤ) p q n hpq


end ClopenData

end AlgebraicGeometry.Scheme.ProEt
