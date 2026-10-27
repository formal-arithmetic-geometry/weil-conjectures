module

public import Sheaf.AlgebraicGeometry.SpaceSquareZeroExtensionData
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
public import Sheaf.CategoryTheory.Sites.RingedSitePicardData
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-! # Normalized units presentations for algebraic-space Picard obstructions

Source: Stacks Project, More on Morphisms of Spaces, Tag 0DNM, proof; Cohomology on
Sites, Tags 040E and 03FD (blueprint: def-sfb-space-picard-units-presentation).

These are presentations of the actual quotient on the common étale site, not additional
hypotheses on a thickening. No existence of a presentation is asserted in this definition.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open CategoryTheory.RingedSitePicard

attribute [instance] SheafOfModules.isGrothendieckAbelian

namespace AlgebraicGeometry.AlgebraicSpace

/-- Module cohomology on the existing small ringed model: Ext from the structure module.
An injective module resolution computes this as the cohomology of Hom(O,I), hence as the
right derived global sections. Restriction to the affine basis preserves this functor.
Source: Stacks 03FD; Mathlib InjectiveResolution.extAddEquivCohomologyClass
(blueprint: def-sfb-space-picard-units-presentation). -/
abbrev picardModuleCohomology {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : X.SmallModules) (n : ℕ) :=
  Ext.{u} (SheafOfModules.unit X.smallStructureRings) M n

/-- A ring sheaf's underlying additive sheaf, retaining its actual sections.
Source: Stacks 0DNM (blueprint: def-sfb-space-picard-units-presentation). -/
abbrev picardRingAdditive {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
    (A : Sheaf K CommRingCat.{u}) : Sheaf K AddCommGrpCat.{u} :=
  (sheafCompose K
    (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})).obj A

/-- Restriction on units for a ring-sheaf quotient.
Source: Stacks 0DNM (blueprint: def-sfb-space-picard-units-presentation). -/
def picardUnitsMap {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
    {A B : Sheaf K CommRingCat.{u}} (p : A ⟶ B) : units A ⟶ units B :=
  (sheafCompose K CommRingCat.unitsAddCommGrp.{u}).map p

/-- The kernel sequence of restriction on units.
Source: Stacks 0DNM (blueprint: def-sfb-space-picard-units-presentation). -/
def picardUnitsSequence {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
    {A B : Sheaf K CommRingCat.{u}} (p : A ⟶ B) :
    ShortComplex (Sheaf K AddCommGrpCat.{u}) :=
  ShortComplex.mk (kernel.ι (picardUnitsMap p)) (picardUnitsMap p) (kernel.condition _)

/-- A section-normalized presentation of the quotient rings, ideal with its quotient
module action, and units sequence on the reduced space's small affine étale model.
The identification with the normalized lifted scheme charts fixes the thick ring and
quotient. The inclusion identifies the specified quasi-coherent module with its actual
kernel. The units identification is fixed by x ↦ 1+x. The integer-to-structure map is
fixed by 1 ↦ 1; it will define the canonical module-to-abelian cohomology map by Ext.
Source: Stacks 0DNM, 05ZS, 040E, 03FD
(blueprint: def-sfb-space-picard-units-presentation). -/
structure SpacePicardUnitsPresentation {S : Scheme.{u}} {Z Z' : AlgebraicSpace S}
    (j : Z ⟶ Z') where
  model : ThickeningSiteModel j
  thickRing : Sheaf Z.smallEtaleModelTopology CommRingCat.{u}
  ringIdentification : (ring thickRing).obj ≅ Z.smallEtaleInclusion.op ⋙ model.rings
  quotient : thickRing ⟶ Z.smallStructureSheaf
  quotient_normalization :
    ((sheafCompose Z.smallEtaleModelTopology (forget₂ CommRingCat RingCat)).map
      quotient).hom =
      ringIdentification.hom ≫ Functor.whiskerLeft Z.smallEtaleInclusion.op model.quotient
  ideal : Z.QCoh
  inclusion : (SheafOfModules.toSheaf Z.smallStructureRings).obj
    (Z.smallModuleRestriction.obj ideal.obj) ⟶ picardRingAdditive thickRing
  injective (U : Z.SmallEtaleModelᵒᵖ) : Function.Injective (inclusion.hom.app U)
  kernel_eq (U : Z.SmallEtaleModelᵒᵖ) (a : thickRing.obj.obj U) :
    quotient.hom.app U a = 0 ↔ ∃ m, inclusion.hom.app U m = a
  locally_surjective (U : Z.SmallEtaleModel) (a : Z.smallStructureSheaf.obj.obj (op U)) :
    ∃ R : Sieve U, R ∈ Z.smallEtaleModelTopology U ∧
      ∀ (V : Z.SmallEtaleModel) (v : V ⟶ U), R v →
        ∃ b : thickRing.obj.obj (op V),
          quotient.hom.app (op V) b = Z.smallStructureSheaf.obj.map v.op a
  square_zero (U : Z.SmallEtaleModelᵒᵖ)
    (m n : (Z.smallModuleRestriction.obj ideal.obj).val.obj U) :
    @id (thickRing.obj.obj U) (inclusion.hom.app U m) *
      @id (thickRing.obj.obj U) (inclusion.hom.app U n) = 0
  scalar (U : Z.SmallEtaleModelᵒᵖ) (a : thickRing.obj.obj U)
    (m : (Z.smallModuleRestriction.obj ideal.obj).val.obj U) :
    @id (thickRing.obj.obj U) (inclusion.hom.app U (quotient.hom.app U a • m)) =
      a * @id (thickRing.obj.obj U) (inclusion.hom.app U m)
  exact : (picardUnitsSequence quotient).ShortExact
  unitsIdentification : (SheafOfModules.toSheaf Z.smallStructureRings).obj
    (Z.smallModuleRestriction.obj ideal.obj) ≅ (picardUnitsSequence quotient).X₁
  one_add (U : Z.SmallEtaleModelᵒᵖ)
    (m : (Z.smallModuleRestriction.obj ideal.obj).val.obj U) :
    (Additive.toMul ((kernel.ι (picardUnitsMap quotient)).hom.app U
      (unitsIdentification.hom.hom.app U m))).val =
      1 + @id (thickRing.obj.obj U) (inclusion.hom.app U m)
  integerUnit : integers.{u} Z.smallEtaleModelTopology ⟶
    (SheafOfModules.toSheaf Z.smallStructureRings).obj
      (SheafOfModules.unit Z.smallStructureRings)
  integerUnit_one (U : Z.SmallEtaleModelᵒᵖ) :
    @id (Z.smallStructureSheaf.obj.obj U)
      (integerUnit.hom.app U (integerOne.{u} U)) = 1

/-- The canonical module-to-abelian cohomology homomorphism: forget an extension and
precompose with the integer-to-structure map sending 1 to 1. Inverse comparison is used
only after bijectivity has been asserted, so no arbitrary comparison is chosen.
Source: Stacks 03FD (blueprint: def-sfb-space-picard-units-presentation). -/
def SpacePicardUnitsPresentation.moduleToAbelian
    {S : Scheme.{u}} {Z Z' : AlgebraicSpace S} {j : Z ⟶ Z'}
    (P : SpacePicardUnitsPresentation j) (n : ℕ) :
    picardModuleCohomology Z (Z.smallModuleRestriction.obj P.ideal.obj) n →+
      Sheaf.H ((SheafOfModules.toSheaf Z.smallStructureRings).obj
        (Z.smallModuleRestriction.obj P.ideal.obj)) n :=
  ((Ext.mk₀ P.integerUnit).precomp _ (zero_add n)).comp
    ((SheafOfModules.toSheaf Z.smallStructureRings).mapExtAddHom _ _ n)

end AlgebraicGeometry.AlgebraicSpace
