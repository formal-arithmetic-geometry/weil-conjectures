module

public import Sheaf.AlgebraicGeometry.SpacePicardAbelianPullback
public import Sheaf.AlgebraicGeometry.SpaceSquareZeroStalkData
public import Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback
public import Sheaf.CategoryTheory.Sites.RingedSitePicardH1Natural

/-! # Normalized units sequences for algebraic-space Picard obstructions

Source: Stacks Project, More on Morphisms of Spaces, Tag 0DNM; Tags 03AJ and 040E
(blueprint: def-sfb-space-picard-obstruction-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open CategoryTheory.RingedSitePicard
namespace AlgebraicGeometry.AlgebraicSpace
variable {S : Scheme.{u}}

/-- The ideal's additive sheaf on the existing small affine basis, without a lift.
Source: Stacks 0DNM and 039Z (blueprint: def-sfb-space-picard-obstruction-data). -/
def picardIdeal {X X' : AlgebraicSpace S} {i : X ⟶ X'}
    {T : ThickeningSiteModel i} (I : SquareZeroIdeal T) :
    Sheaf X.smallEtaleModelTopology AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf X.smallStructureRings).obj (X.smallModuleRestriction.obj I.obj)

/-- The thickened commutative structure sheaf on the reduced affine basis.
Source: Stacks 05ZS and 0DNM (blueprint: def-sfb-space-picard-obstruction-data). -/
def picardThickenedRing {X X' : AlgebraicSpace S} {i : X ⟶ X'}
    (T : ThickeningSiteModel i) : Sheaf X.smallEtaleModelTopology CommRingCat.{u} :=
  letI := T.inverse_continuous
  (X.smallEtaleInclusion.sheafPushforwardContinuous CommRingCat.{u}
    X.smallEtaleModelTopology X.etaleTopology).obj
    ((T.equivalence.inverse.sheafPushforwardContinuous CommRingCat.{u}
      X.etaleTopology X'.etaleTopology).obj X'.commStructureSheaf)

/-- A presentation of the units sequence with both maps fixed on every section.
Inclusion is j to 1+j and projection is the actual quotient on regular functions.
The data include local sheaf exactness, not surjectivity on global sections.
Source: Stacks 0DNM (blueprint: def-sfb-space-picard-obstruction-data). -/
structure PicardUnitsSequence {X X' : AlgebraicSpace S} {i : X ⟶ X'}
    (T : ThickeningSiteModel i) (I : SquareZeroIdeal T) where
  inclusion : picardIdeal I ⟶ units (picardThickenedRing T)
  projection : units (picardThickenedRing T) ⟶ units X.smallStructureSheaf
  inclusion_value (U : X.SmallEtaleModel) (m : (picardIdeal I).obj.obj (op U)) :
    (Additive.toMul (inclusion.hom.app (op U) m)).val =
      1 + I.inclusion (X.smallEtaleInclusion.obj U) m
  projection_value (U : X.SmallEtaleModel)
    (a : (units (picardThickenedRing T)).obj.obj (op U)) :
    (Additive.toMul (projection.hom.app (op U) a)).val =
      T.quotient.app (op (X.smallEtaleInclusion.obj U)) (Additive.toMul a).val
  zero : inclusion ≫ projection = 0
  exact : (ShortComplex.mk inclusion projection zero).ShortExact

/-- The boundary is Yoneda composition with the normalized units extension class.
Picard comparison identifies line classes with H1 of units; this is the canonical
connecting map, including its sign, with no choice of an arbitrary homomorphism.
Source: Stacks 0DNM and 040E (blueprint: def-sfb-space-picard-obstruction-data). -/
def PicardUnitsSequence.obstruction {X X' : AlgebraicSpace S} {i : X ⟶ X'}
    {T : ThickeningSiteModel i} {I : SquareZeroIdeal T} (E : PicardUnitsSequence T I)
    (c : Comparison.{u, u} X.smallStructureSheaf) :
    @AddMonoidHom (Pic X.smallStructureSheaf) (Sheaf.H (picardIdeal I) 2)
      c.group.toAddZero inferInstance :=
  letI := c.group
  (E.exact.extClass.postcomp (integers.{u} X.smallEtaleModelTopology) (by decide)).comp
    c.comparison.toAddMonoidHom

/-- The ideal coefficient map is fixed by pullback of regular functions on every
compatible pair of lifted charts. Such pairs exist etale locally by formal etaleness.
This is the additive inverse-image form of h0-star J to K, so no flatness is imposed.
Source: Stacks 0DNM (blueprint: def-sfb-space-picard-obstruction-data). -/
def IsPicardIdealMap {X X' Y Y' : AlgebraicSpace S}
    {i : X ⟶ X'} {j : Y ⟶ Y'} (T : ThickeningSiteModel i) (W : ThickeningSiteModel j)
    (I : SquareZeroIdeal T) (K : SquareZeroIdeal W) (h : Y ⟶ X) (h' : Y' ⟶ X')
    (P : PicardAbInverse h) (α : P.functor.obj (picardIdeal I) ⟶ picardIdeal K) : Prop :=
  ∀ (U : Y.SmallEtaleModel) (V : X.SmallEtaleModel)
    (a : (Y.smallEtaleInclusion.obj U).obj.left ⟶ (X.smallEtaleInclusion.obj V).obj.left)
    (ha : yoneda.map a ≫ (X.smallEtaleInclusion.obj V).obj.hom =
      (Y.smallEtaleInclusion.obj U).obj.hom ≫ h.hom.hom)
    (b : (W.equivalence.inverse.obj (Y.smallEtaleInclusion.obj U)).obj.left ⟶
      (T.equivalence.inverse.obj (X.smallEtaleInclusion.obj V)).obj.left),
    W.reduction.app (Y.smallEtaleInclusion.obj U) ≫ b =
      a ≫ T.reduction.app (X.smallEtaleInclusion.obj V) →
    (W.equivalence.inverse.obj (Y.smallEtaleInclusion.obj U)).obj.hom ≫ h'.hom.hom =
      yoneda.map b ≫ (T.equivalence.inverse.obj (X.smallEtaleInclusion.obj V)).obj.hom →
    ∀ m : (picardIdeal I).obj.obj (op V),
      K.inclusion (Y.smallEtaleInclusion.obj U)
        (α.hom.app (op U) (P.chartSection (picardIdeal I) U V a ha m)) =
      (forget₂ CommRingCat RingCat).map (Scheme.Γ.map b.left.op)
        (I.inclusion (X.smallEtaleInclusion.obj V) m)

/-- Scalar extension of the additive ideal map, prescribed on local tensors.
Source: Stacks 0DNM and 03D7 (blueprint: def-sfb-space-picard-obstruction-data). -/
def IsPicardModuleIdealMap {X X' Y Y' : AlgebraicSpace S}
    {i : X ⟶ X'} {j : Y ⟶ Y'} (T : ThickeningSiteModel i) (W : ThickeningSiteModel j)
    (I : SquareZeroIdeal T) (K : SquareZeroIdeal W) (h : Y ⟶ X) (h' : Y' ⟶ X')
    (β : (moduleTensorPullback h).obj I.obj ⟶ K.obj) : Prop :=
  ∀ (V : X.EtaleSite) (q : ModuleChart h V)
    (b : (W.equivalence.inverse.obj q.left).obj.left ⟶
      (T.equivalence.inverse.obj V).obj.left),
    W.reduction.app q.left ≫ b = q.hom.left ≫ T.reduction.app V →
    (W.equivalence.inverse.obj q.left).obj.hom ≫ h'.hom.hom =
      yoneda.map b ≫ (T.equivalence.inverse.obj V).obj.hom →
    ∀ (a : Y.structureSheaf.obj.obj (op q.left)) (m : I.obj.val.obj (op V))
      (r : W.rings.obj (op q.left)), W.quotient.app (op q.left) r = a →
      K.inclusion q.left (β.val.app (op q.left) (moduleTensorSection h I.obj V q a m)) =
        r * @id (W.rings.obj (op q.left))
          ((forget₂ CommRingCat RingCat).map (Scheme.Γ.map b.left.op) (I.inclusion V m))

end AlgebraicGeometry.AlgebraicSpace
