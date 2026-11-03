/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeEnvelope.NativeNormalizedRealEnvelope
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraTwist
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-! # Exact constant twists on native Weil modules

Source: latest blueprint, def-wf-constant-weil-twist and lem-wf-constant-twist-cohomology.
(blueprint: def-zl-native-constant-twist-functor)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeEnvelope
open CategoryTheory.Endofunctor

/-- Tensor interchange with the identity transported by a monoidal functor.
Source: latest blueprint, constant-line tensor comparison.
(blueprint: def-zl-native-constant-twist-functor)

Proof: a functor preserves the identity, and the two tensor morphisms are the
successive whiskerings given by the tensor interchange definition.
-/
theorem tensor_comparison {C : Type*} [Category* C] [MonoidalCategory C]
    (P : C ⥤ C) [P.Monoidal] (M B : C)
    (φ : P.obj M ≅ M) (ψ : P.obj B ≅ B) :
    P.map (𝟙 (M ⊗ B)) ≫
        ((Functor.Monoidal.μIso P M B).inv ≫ (φ.hom ⊗ₘ ψ.hom)) =
      (((Functor.Monoidal.μIso P M B).inv ≫ (P.obj M ◁ ψ.hom)) ≫
        (φ.hom ▷ B)) ≫ 𝟙 _ := by
  rw [P.map_id]
  simp only [Category.id_comp, Category.comp_id, tensorHom_def', Category.assoc]

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [IsSeparated X₀.hom]

/-- Tensoring with the actual constant Weil line as a functor on all native Weil modules.
The comparison is inverse pullback tensorator followed by the line's structure map.
Source: latest blueprint, constant twist definition.
(blueprint: def-zl-native-constant-twist-functor) -/
def constantTwistFunctor (b : (PadicAlgCl l)ˣ) :
    condensedWeilModules (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀).hom ⥤
      condensedWeilModules (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀).hom :=
  let P := CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
    (D.geometricFrobenius X₀).hom
  let B := CondensedRing.ConstantWeil.lineModule l D X₀ hl b
  IsoAlgebra.mapOfNatIso
    ((Functor.Monoidal.commTensorRight P B.carrier).symm ≪≫
      Functor.isoWhiskerLeft P
        ((curriedTensor (NativeCondensedModule.Modules l (D.geometricFiber X₀).left)).flip.mapIso
          B.str))

/-- The functorial construction gives the recorded tensor-product Weil datum.
Source: latest blueprint, the inverse-tensorator convention for constant twists.
(blueprint: def-zl-native-constant-twist-functor)

Proof: both objects have carrier M tensor B. Under the identity on that carrier the
functor's Weil structure first applies the inverse tensorator, then the line's Weil
map, then the Weil map of M. The interchange law for tensor morphisms identifies
this composite with the tensor of the two Weil maps used by normalizedTwist.
-/
def constantTwistFunctorObjIso (b : (PadicAlgCl l)ˣ)
    (M : condensedWeilModules (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀).hom) :
    (constantTwistFunctor D l hl X₀ b).obj M ≅ normalizedTwist D l X₀ hl M b := by
  apply IsoAlgebra.isoMk (K := (constantTwistFunctor D l hl X₀ b).obj M)
    (K' := normalizedTwist D l X₀ hl M b) (Iso.refl _)
  let P := CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
    (D.geometricFrobenius X₀).hom
  let B := CondensedRing.ConstantWeil.lineModule l D X₀ hl b
  change P.map (𝟙 (M.carrier ⊗ B.carrier)) ≫
      ((Functor.Monoidal.μIso P M.carrier B.carrier).inv ≫
        (M.str.hom ⊗ₘ B.str.hom)) =
    (((Functor.Monoidal.μIso P M.carrier B.carrier).inv ≫
      (P.obj M.carrier ◁ B.str.hom)) ≫ (M.str.hom ▷ B.carrier)) ≫ 𝟙 _
  exact tensor_comparison P M.carrier B.carrier M.str B.str

instance constantTwistFunctor_preservesFiniteLimits (b : (PadicAlgCl l)ˣ) :
    PreservesFiniteLimits (constantTwistFunctor D l hl X₀ b) := by
  have : PreservesFiniteLimits
      (tensorRight (𝟙_ (NativeCondensedModule.Modules l (D.geometricFiber X₀).left))) :=
    preservesFiniteLimits_of_natIso (rightUnitorNatIso _).symm
  have : PreservesFiniteLimits
      (tensorRight (CondensedRing.ConstantWeil.lineModule l D X₀ hl b).carrier) := this
  dsimp only [constantTwistFunctor]
  exact IsoAlgebra.preservesFiniteLimits_mapOfNatIso _

instance constantTwistFunctor_preservesFiniteColimits (b : (PadicAlgCl l)ˣ) :
    PreservesFiniteColimits (constantTwistFunctor D l hl X₀ b) := by
  have : PreservesFiniteColimits
      (tensorRight (𝟙_ (NativeCondensedModule.Modules l (D.geometricFiber X₀).left))) :=
    preservesFiniteColimits_of_natIso (rightUnitorNatIso _).symm
  have : PreservesFiniteColimits
      (tensorRight (CondensedRing.ConstantWeil.lineModule l D X₀ hl b).carrier) := this
  dsimp only [constantTwistFunctor]
  exact IsoAlgebra.preservesFiniteColimits_mapOfNatIso _

instance constantTwistFunctor_additive (b : (PadicAlgCl l)ˣ) :
    (constantTwistFunctor D l hl X₀ b).Additive := by
  have : (tensorRight
      (𝟙_ (NativeCondensedModule.Modules l (D.geometricFiber X₀).left))).Additive :=
    Functor.additive_of_iso (rightUnitorNatIso _).symm
  dsimp only [constantTwistFunctor]
  exact IsoAlgebra.additive_mapOfNatIso _

end WeilConjectures.NativeEnvelope
