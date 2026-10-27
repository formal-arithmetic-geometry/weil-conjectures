/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q127
-/
module

public import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Equivalence

/-! # Tensor extension of the structure algebra on a fibred groupoid

Source: Alper, Adequate moduli spaces, Lemma 5.2.6, printed p.508;
Stacks Project, Tags 06TV and 06WG (blueprint: def-sfb-stack-scalar-algebra).

The sheafified pushout of the structure presheaf and the constant algebra is the
usual tensor extension. Its constant-algebra leg gives the specified section unit.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace CategoryTheory

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R]
variable {F : BasedCategory.{v, w} (Over (Spec (.of k)))}
variable (φ : BasedFunctor F (discreteModuli
  (yoneda.obj (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R)))))))

/-- Pull a scalar back along the actual scheme map of a test object.
Source: Alper, Lemma 5.2.6 (blueprint: def-sfb-stack-scalar-algebra). -/
def moduliScalarMap (x : F.obj) : R →+* (moduliStructurePresheaf F).obj (op x) :=
  ULift.ringEquiv.{u, max (u + 1) v w}.symm.toRingHom.comp
    (((Scheme.ΓSpecIso (.of R)).inv ≫
      (eqToHom (congrArg (fun T : Over (Spec (.of k)) ↦ T.left)
        (φ.w_obj x)).symm ≫ (yoneda.preimage (φ.obj x).hom).left).appTop).hom)

/-- Pulling scalars back commutes with every restriction.
Source: Alper, Lemma 5.2.6; Stacks Tag 06TV
(blueprint: def-sfb-stack-scalar-algebra).
Proof: the comma morphism of φ gives the triangle of underlying scheme maps to
Spec R, after the transports supplied by φ.w. Apply contravariant functoriality
of global functions and compose with the canonical Γ(Spec R) identification and ULift. -/
theorem moduliScalarMap_naturality {x y : F.objᵒᵖ} (f : x ⟶ y) :
    CommRingCat.ofHom
        ((moduliScalarMap φ x.unop).comp ULift.ringEquiv.{u, max (u + 1) v w}.toRingHom) ≫
        (moduliStructurePresheaf F).map f =
      CommRingCat.ofHom
        ((moduliScalarMap φ y.unop).comp ULift.ringEquiv.{u, max (u + 1) v w}.toRingHom) := by
  sorry

/-- The constant R algebra acts on the structure presheaf by structural pullback.
Source: Alper, Lemma 5.2.6 (blueprint: def-sfb-stack-scalar-algebra). -/
def moduliScalarStructure :
    (Functor.const F.objᵒᵖ).obj (CommRingCat.of (ULift.{max (u + 1) v w} R)) ⟶
      moduliStructurePresheaf F where
  app x := CommRingCat.ofHom
    ((moduliScalarMap φ x.unop).comp ULift.ringEquiv.{u, max (u + 1) v w}.toRingHom)
  naturality _ _ f := by simpa using (moduliScalarMap_naturality φ f).symm

variable (C : Type u) [CommRing C] [Algebra R C]

/-- The constant algebra map, transported canonically into the site universe.
Source: Alper, Lemma 5.2.6 (blueprint: def-sfb-stack-scalar-algebra). -/
def moduliScalarConstantMap :
    (Functor.const F.objᵒᵖ).obj (CommRingCat.of (ULift.{max (u + 1) v w} R)) ⟶
      (Functor.const F.objᵒᵖ).obj (CommRingCat.of (ULift.{max (u + 1) v w} C)) :=
  (Functor.const F.objᵒᵖ).map (CommRingCat.ofHom (algebraMap R C).ulift)

/-- Pointwise tensor product, expressed as the ring pushout to retain canonical maps.
On an affine test Spec A this is A tensor_R C, with the canonical ULift transports.
Source: Alper, Lemma 5.2.6 (blueprint: def-sfb-stack-scalar-algebra). -/
def moduliScalarPresheaf : F.objᵒᵖ ⥤ CommRingCat.{max (u + 1) v w} :=
  pushout (moduliScalarStructure φ) (moduliScalarConstantMap (F := F) C)

/-- Ring sheafification in the common ambient universe of the site.
Source: Stacks Tags 00W1 and 06TV (blueprint: def-sfb-stack-scalar-algebra). -/
instance moduliScalarSheafify :
    HasWeakSheafify (moduliFppfTopology F) CommRingCat.{max (u + 1) v w} := by
  have : EssentiallySmall.{max (u + 1) v w} F.obj :=
    essentiallySmallSelf.{u + 1, v, w} _
  exact (hasSheafifyEssentiallySmallSite (moduliFppfTopology F)
    CommRingCat.{max (u + 1) v w}).isRightAdjoint

/-- The tensor extension O_F tensor_R C is the associated sheaf of the tensor presheaf.
Source: Alper, Lemma 5.2.6 (blueprint: def-sfb-stack-scalar-algebra). -/
def moduliScalarSheaf : Sheaf (moduliFppfTopology F) CommRingCat.{max (u + 1) v w} :=
  (presheafToSheaf (moduliFppfTopology F) CommRingCat).obj (moduliScalarPresheaf φ C)

/-- The tensor sheaf as an algebra over the existing structure sheaf.
Source: Alper, Lemma 5.2.6 (blueprint: def-sfb-stack-scalar-algebra). -/
def moduliScalarAlgebra (hF : IsFibredInGroupoids F) : ModuliAlgebraSheaf F hF :=
  Under.mk
    ({ hom := pushout.inl (moduliScalarStructure φ) (moduliScalarConstantMap (F := F) C) ≫
        toSheafify (moduliFppfTopology F) (moduliScalarPresheaf φ C) } :
      moduliStructureSheaf F hF ⟶ moduliScalarSheaf φ C)

/-- The canonical map from constant C sends c to the section 1 tensor c.
Source: Alper, Lemma 5.2.6 (blueprint: def-sfb-stack-scalar-algebra). -/
def moduliScalarSheafUnit :
    (Functor.const F.objᵒᵖ).obj (CommRingCat.of (ULift.{max (u + 1) v w} C)) ⟶
      (moduliScalarSheaf φ C).obj :=
  pushout.inr (moduliScalarStructure φ) (moduliScalarConstantMap (F := F) C) ≫
    toSheafify (moduliFppfTopology F) (moduliScalarPresheaf φ C)

/-- The actual adjunction unit C → Γ(F, O_F tensor_R C), as compatible families.
Source: Alper, Lemma 5.2.6 (blueprint: def-sfb-stack-scalar-algebra). -/
def moduliScalarUnit : C →+* moduliGlobalSectionsRing (moduliScalarSheaf φ C) where
  toFun c := ⟨fun x ↦ (moduliScalarSheafUnit φ C).app x (ULift.up c),
    fun f ↦ by
      have h := congrArg (fun g ↦ g (ULift.up c))
        ((moduliScalarSheafUnit φ C).naturality f)
      simpa using h.symm⟩
  map_one' := by apply Subtype.ext; funext x; exact map_one _
  map_mul' a b := by apply Subtype.ext; funext x; exact map_mul _ _ _
  map_zero' := by apply Subtype.ext; funext x; exact map_zero _
  map_add' a b := by apply Subtype.ext; funext x; exact map_add _ _ _

/-- The global section algebra has its C action through the specified unit.
Source: Alper, Lemma 5.2.6 (blueprint: def-sfb-stack-scalar-algebra). -/
instance moduliScalarSectionsAlgebra :
    Algebra C (moduliGlobalSectionsRing (moduliScalarSheaf φ C)) :=
  (moduliScalarUnit φ C).toAlgebra

end CategoryTheory
