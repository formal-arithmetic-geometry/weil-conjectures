/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SecSmoothPurity.NormalizedCoefficientDiagram
public import Sheaf.SecSmoothPurity.NormalizedScalarTensorTransitions
import all Sheaf.SecSmoothPurity.NormalizedKappaTransitions
import all Sheaf.SecSmoothPurity.NormalizedScalarTensorTransitions
import all Sheaf.SecSmoothPurity.CochainCoefficientArrows
import Sheaf.SecSmoothPurity.ModuleTensorGenerators

/-! # Generalized pullback tensor section formulas

Source: Stacks Project, Modules on Sites, Tag 03EL and Cohomology on Sites, Tag 07A4.
(blueprint: lem-pur-normalized-pull-tensor-generator-sections).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] SheafOfModules.monoidalCategory
universe w uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open SheafOfModules
open scoped TensorProduct ChangeOfRings
namespace CategoryTheory.CochainPullback.StrictCoefficient.PullCalculation

attribute [local irreducible] scalarComp scalarUnit extensionAdjunction
attribute [local irreducible] generator
set_option backward.defeqAttrib.useBackward true
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]


open KappaCalculation ScalarCalculation
/-- Generalized section formula for normalized pullback tensor comparisons.
Source: Stacks 03EL and 07A4
(blueprint: lem-pur-normalized-pull-tensor-generator-sections). -/
def diagramGeneratorSection (d : Diagram (J := J) (K := K))
    (c : ∀ i : Index, Comparison (d.ringed i)) (i : Index)
    (M : Modules (d.R.obj i)) (Z : Sheaf J (Type w))
    (x : Z ⟶ (underlying (d.R.obj i)).obj M) (U : Dᵒᵖ)
    (v : (d.inverse.obj Z).obj.obj U) : ((d.L i).obj M).val.obj U :=
  @id (((d.L i).obj M).val.obj U) ((generator (d.ringed i) (c i) x).hom.app U v)

/-- Generalized section formula for normalized pullback tensor comparisons.
Source: Stacks 03EL and 07A4
(blueprint: lem-pur-normalized-pull-tensor-generator-sections). -/
def PullTensorTransitionValues {d : Diagram (J := J) (K := K)}
    (e : Comparisons d) (c : ∀ i : Index, Comparison (d.ringed i)) : Prop :=
  ∀ {i j : Index} (a : i ⟶ j)
    (P Q : Complex (d.R.obj i)) (P' Q' : Complex (d.R.obj j))
    (f : (extend (d.R.map a)).obj P ⟶ P')
    (g : (extend (d.R.map a)).obj Q ⟶ Q')
    (p q n : ℤ) (hpq : p + q = n) (Z : Sheaf J (Type w))
    (x : Z ⟶ (underlying (d.R.obj i)).obj (P.X p))
    (y : Z ⟶ (underlying (d.R.obj i)).obj (Q.X q))
    (z : Z ⟶ (underlying (d.R.obj i)).obj ((total P Q).X n)),
    (∀ (V : Cᵒᵖ) (v : Z.obj.obj V),
      z.hom.app V v = totalPure P Q p q n hpq V (x.hom.app V v) (y.hom.app V v)) →
    ∀ (U : Dᵒᵖ) (v : (d.inverse.obj Z).obj.obj U) (b : (d.S.obj i).obj.obj U),
      (((extend (d.S.map a)).map (tensorComparison (d.ringed i) (c i) P Q).hom ≫
          (e.sigmaSC a ((pull (d.ringed i)).obj P) ((pull (d.ringed i)).obj Q)).hom ≫
          tensorTotalMap (e.pullArrow a P P' f) (e.pullArrow a Q Q' g)).f n).val.app U
        (extensionTmul (d.S.map a) ((d.L i).obj ((total P Q).X n)) U 1
          (b • (diagramGeneratorSection d c i ((total P Q).X n) Z z U v))) =
        totalPure ((pull (d.ringed j)).obj P') ((pull (d.ringed j)).obj Q') p q n hpq U
          (((d.S.map a).hom.app U b) •
            (diagramGeneratorSection d c j (P'.X p) Z
              (x ≫ KappaCalculation.semilinearSectionMap (d.R.map a) f p) U v))
          (diagramGeneratorSection d c j (Q'.X q) Z
            (y ≫ KappaCalculation.semilinearSectionMap (d.R.map a) g q) U v)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private theorem generator_total (d : Diagram (J := J) (K := K))
    (c : ∀ i : Index, Comparison (d.ringed i)) (i : Index)
    (P Q : Complex (d.R.obj i)) (p q n : ℤ) (hpq : p + q = n)
    (Z : Sheaf J (Type w))
    (x : Z ⟶ (underlying (d.R.obj i)).obj (P.X p))
    (y : Z ⟶ (underlying (d.R.obj i)).obj (Q.X q))
    (z : Z ⟶ (underlying (d.R.obj i)).obj ((total P Q).X n))
    (hz : ∀ (V : Cᵒᵖ) (v : Z.obj.obj V),
      z.hom.app V v = totalPure P Q p q n hpq V (x.hom.app V v) (y.hom.app V v))
    (U : Dᵒᵖ) (v : (d.inverse.obj Z).obj.obj U) :
    ((tensorComparison (d.ringed i) (c i) P Q).hom.f n).val.app U
      ((generator (d.ringed i) (c i) z).hom.app U v) =
    totalPure ((pull (d.ringed i)).obj P) ((pull (d.ringed i)).obj Q) p q n hpq U
      ((generator (d.ringed i) (c i) x).hom.app U v)
      ((generator (d.ringed i) (c i) y).hom.app U v) := by
  let t := CochainComplex.ιMapBifunctor P Q
    (curriedTensor (Modules (d.R.obj i))) p q n hpq
  have hz' : z = moduleTensorPair x y ≫ (underlying (d.R.obj i)).map t := by
    apply Sheaf.hom_ext
    ext V v
    exact hz V v
  rw [hz']
  have h := CategoryTheory.CochainPullback.generator_naturality
    (d.ringed i) (c i) t (moduleTensorPair x y)
  have ht := congrArg (fun z ↦ z ≫
    (underlying (d.S.obj i)).map ((tensorComparison (d.ringed i) (c i) P Q).hom.f n)) h
  rw [Category.assoc, ← Functor.map_comp, ScalarCalculation.tensorComparison_ι,
    Functor.map_comp, ← Category.assoc, generator_tensorPair] at ht
  exact congrArg (fun z ↦ z.hom.app U v) ht

private theorem pullArrow_generator_smul (d : Diagram (J := J) (K := K))
    (c : ∀ i : Index, Comparison (d.ringed i)) (e : Comparisons d)
    (hn : e.Normalized c) {i j : Index} (a : i ⟶ j)
    (P : Complex (d.R.obj i)) (Q : Complex (d.R.obj j))
    (f : (extend (d.R.map a)).obj P ⟶ Q) (p : ℤ)
    (Z : Sheaf J (Type w)) (x : Z ⟶ (underlying (d.R.obj i)).obj (P.X p))
    (U : Dᵒᵖ) (v : (d.inverse.obj Z).obj.obj U)
    (b : (d.S.obj j).obj.obj U) (b' : (d.S.obj i).obj.obj U) :
    ((e.pullArrow a P Q f).f p).val.app U
      (extensionTmul (d.S.map a) ((d.L i).obj (P.X p)) U b
        (b' • (@id (((d.L i).obj (P.X p)).val.obj U)
          ((generator (d.ringed i) (c i) x).hom.app U v)))) =
      (b * (d.S.map a).hom.app U b') •
        (@id (((d.L j).obj (Q.X p)).val.obj U)
          ((generator (d.ringed j) (c j)
            (x ≫ KappaCalculation.semilinearSectionMap (d.R.map a) f p)).hom.app U v)) := by
  erw [extension_smul_arg, extension_smul, map_smul, map_smul]
  erw [pullArrow_generator d c e hn a P Q f p Z x U v]
  rw [smul_smul, mul_comm]
  rfl


/-- Pullback tensor comparisons carry generalized homogeneous tensor sections to
the pair of their arbitrary semilinear transitions.
Source: Stacks 03EL and 07A4
(blueprint: lem-pur-normalized-pull-tensor-generator-sections).
Proof: express the tensor section as the pairing followed by its coproduct
inclusion. Naturality and the normalized pure formula identify its image with
the pairing of the inverse-image generators. The scalar tensor formula inserts
one in the second factor. Kappa normalization and naturality apply each arbitrary
semilinear map. Linearity moves the coefficient through its ring map. -/
theorem normalizedPullTensorGeneratorSections (d : Diagram (J := J) (K := K))
    (c : ∀ i : Index, Comparison (d.ringed i)) (e : Comparisons d)
    (hn : e.Normalized c) : PullTensorTransitionValues e c := by
  intro i j a P Q P' Q' f g p q n hpq Z x y z hz U v b
  have hz' := generator_total d c i P Q p q n hpq Z x y z hz U v
  change ((tensorTotalMap (e.pullArrow a P P' f) (e.pullArrow a Q Q' g)).f n).val.app U
    (((e.sigmaSC a ((pull (d.ringed i)).obj P)
      ((pull (d.ringed i)).obj Q)).hom.f n).val.app U
        (((extensionFunctor (d.S.map a)).map
          ((tensorComparison (d.ringed i) (c i) P Q).hom.f n)).val.app U _)) = _
  erw [extension_map, map_smul, hz', ← ScalarCalculation.totalPure_smul, Comparisons.sigmaSC,
    ScalarCalculation.scalarTotal_hom, ScalarCalculation.totalMap_pure]
  apply congrArg₂
    (totalPure ((pull (d.ringed j)).obj P') ((pull (d.ringed j)).obj Q') p q n hpq U)
  · simpa only [one_mul, diagramGeneratorSection, id_eq, pull,
      Functor.mapHomologicalComplex, Diagram.ringed] using
      pullArrow_generator_smul d c e hn a P P' f p Z x U v 1 b
  · simpa only [diagramGeneratorSection, id_eq, pull,
      Functor.mapHomologicalComplex, Diagram.ringed] using
      pullArrow_generator d c e hn a Q Q' g q Z y U v


end CategoryTheory.CochainPullback.StrictCoefficient.PullCalculation
