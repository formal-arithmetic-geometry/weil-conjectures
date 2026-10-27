/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q160
-/
module

public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale

/-! # The canonical étale ring map for schemes in the original universe

Source: Stacks Project, Properties of Spaces, Tags 03G2 and 03G8; Descent, Tag 03LC
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).

The existing algebraic-space construction is retained. The scheme presentation uses
its ordinary small étale site and regular functions, with the structural map obtained
as the adjoint mate of the already defined pullback of functions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Hom

/-- Regular functions as a commutative-ring sheaf on the ordinary scheme étale site.
This only bundles the recorded presheaf and its existing sheaf-condition theorem.
Source: Stacks, Tags 03G7 and 03DU
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def etaleDifferentialStructure (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology CommRingCat.{u} :=
  ⟨X.etaleStructurePresheaf, X.isSheaf_etaleStructurePresheaf⟩

/-- The ordinary scheme étale direct image on commutative-ring sheaves admits its
canonical inverse image in the original coefficient universe. Source: Stacks 03G2,
03G8 and 03LC (blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: use the small affine étale basis of each scheme (Tag 03ED). On its small
skeleton, left Kan extension followed by commutative-ring sheafification is left
adjoint to direct image. Transport along the basis restriction equivalences. The
right adjoint is precomposition with scheme base change, so uniqueness of adjoints
identifies the result with the ring inverse image of the canonical geometric morphism.
The unit sends a regular function to its pullback on every relative étale diagram. -/
theorem etaleDifferentialRingDirect_isRightAdjoint {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (f.Etale.sheafPushforwardContinuous CommRingCat.{u}
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint := by
  let i := Scheme.AffineEtale.Spec Y
  let G := i ⋙ f.Etale
  let : G.IsContinuous (Scheme.AffineEtale.topology Y) X.smallEtaleTopology :=
    Functor.isContinuous_comp i f.Etale
      (Scheme.AffineEtale.topology Y) Y.smallEtaleTopology X.smallEtaleTopology
  let (F : Y.AffineEtaleᵒᵖ ⥤ CommRingCat.{u}) : G.op.HasPointwiseLeftKanExtension F := by
    intro U
    have : HasColimitsOfShape (CostructuredArrow G.op U) CommRingCat.{u} :=
      hasColimitsOfShape_of_essentiallySmall.{u} _ _
    infer_instance
  have : (G.sheafPushforwardContinuous CommRingCat.{u}
      (Scheme.AffineEtale.topology Y) X.smallEtaleTopology).IsRightAdjoint :=
    inferInstance
  apply (Functor.isRightAdjoint_comp_iff_left
    (f.Etale.sheafPushforwardContinuous CommRingCat.{u}
      Y.smallEtaleTopology X.smallEtaleTopology)
    (i.sheafPushforwardContinuous CommRingCat.{u}
      (Scheme.AffineEtale.topology Y) Y.smallEtaleTopology)).mp
  exact Functor.isRightAdjoint_of_iso
    (Functor.sheafPushforwardContinuousComp i f.Etale CommRingCat.{u}
      (Scheme.AffineEtale.topology Y) Y.smallEtaleTopology X.smallEtaleTopology).symm

/-- The ring inverse image, namely the left adjoint of the canonical direct image.
The adjunction determines this object up to its unique unit-compatible isomorphism;
only the existence proof is postponed, and no arbitrary map or object is chosen.
Source: Stacks, Tags 03G2, 03G8 and 03LC
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def etaleDifferentialRingInverse {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf Y.smallEtaleTopology CommRingCat.{u} ⥤
      Sheaf X.smallEtaleTopology CommRingCat.{u} :=
  @Functor.leftAdjoint _ _ _ _
    (f.Etale.sheafPushforwardContinuous CommRingCat.{u}
      Y.smallEtaleTopology X.smallEtaleTopology)
    (etaleDifferentialRingDirect_isRightAdjoint f)

/-- The inverse-image structural ring map is the mate of the existing pullback of
regular functions along base change. Thus the map is canonically normalized on
all scheme charts. This is the scheme presentation of the existing space map.
Source: Stacks, Tags 03G8 and 03LC
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def etaleDifferentialRingMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (etaleDifferentialRingInverse f).obj (etaleDifferentialStructure Y) ⟶
      etaleDifferentialStructure X :=
  ((@Adjunction.ofIsRightAdjoint _ _ _ _
    (f.Etale.sheafPushforwardContinuous CommRingCat.{u}
      Y.smallEtaleTopology X.smallEtaleTopology)
    (etaleDifferentialRingDirect_isRightAdjoint f)).homEquiv _ _).symm
      ⟨Scheme.etaleStructurePresheafToPullback f⟩

end AlgebraicGeometry.Scheme.Hom
