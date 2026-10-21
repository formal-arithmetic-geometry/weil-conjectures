/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.Paper.WeilCompactSupportCohomology
public import Sheaf.Paper.CompactSupportCoefficientAction
import Sheaf.Paper.QcqsCompactSupportRealization
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Compact support with canonical Frobenius comparison

Source: blueprint main-20261015, lem-zl-shriek-composition and
lem-fix-weil-operations; SGA 4, XVII, §5--6
(blueprint: def-zl-common-stage-weil-shriek).

Open extension and proper image are adjoints of the existing common-stage pullback.
Their Frobenius comparisons are specified mates of its normalized Frobenius square.
Their composite is identified naturally with the recorded compact-support action.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Endofunctor AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

section Proper
variable {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  (p₀ : X₀ ⟶ Y₀) [IsProper p₀.left]

/-- Proper inverse image has its constructible direct-image right adjoint.
Source: SGA 4, XVII, §5; blueprint lem-fix-weil-operations
(blueprint: def-zl-common-stage-weil-shriek).
Proof: proper direct image preserves bounded constructibility at every finite level.
Apply it to the coherent completed tower, rationalize, and descend through the
common-stage coefficient comparisons. The ordinary pullback/direct-image adjunction
restricts to the complete constructible categories and then localizes. Its Hom
bijections commute with finite coefficient extension; at a common finite field they
therefore give the adjunction on every common-stage Hom group. -/
theorem zlPull_proper_isLeftAdjoint : (zlPull D l hl Ω p₀).IsLeftAdjoint := by
  sorry

/-- Proper image selected by its adjunction to the recorded inverse image.
Source: SGA 4, XVII, §5 (blueprint: def-zl-common-stage-weil-shriek). -/
def zlCommonStageProperPush :=
  letI := zlPull_proper_isLeftAdjoint D l hl Ω p₀
  (zlPull D l hl Ω p₀).rightAdjoint

/-- The adjunction determining the proper image, including its unit and counit.
Source: SGA 4, XVII, §5 (blueprint: def-zl-common-stage-weil-shriek). -/
def zlCommonStageProperAdjunction :
    zlPull D l hl Ω p₀ ⊣ zlCommonStageProperPush D l hl Ω p₀ :=
  letI := zlPull_proper_isLeftAdjoint D l hl Ω p₀
  Adjunction.ofIsLeftAdjoint (zlPull D l hl Ω p₀)

/-- The proper Frobenius exchange is the specified counit mate of inverse-image exchange.
Source: blueprint lem-fix-weil-operations, first paragraph
(blueprint: def-zl-common-stage-weil-shriek). -/
def zlProperFrobeniusMap :
    zlCommonStageProperPush D l hl Ω p₀ ⋙ sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω ⟶
      sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω ⋙ zlCommonStageProperPush D l hl Ω p₀ :=
  (mateEquiv (zlCommonStageProperAdjunction D l hl Ω p₀)
    (zlCommonStageProperAdjunction D l hl Ω p₀)
    (TwoSquare.mk _ _ _ _ (zlFrobeniusSquare D l hl Ω p₀).inv)).natTrans

/-- The proper exchange for the geometric-Frobenius automorphism square is invertible.
Source: blueprint lem-fix-weil-operations, inverse automorphism squares
(blueprint: def-zl-common-stage-weil-shriek).
Proof: inverse image along geometric Frobenius is an equivalence, with inverse the
arithmetic-Frobenius pullback. Form the mate for its inverse square. The normalized
pullback composition identities identify both pasted squares with identity squares.
Mate pasting then makes their two composites identity transformations. Thus the
specified proper exchange, rather than an arbitrary comparison, is invertible. -/
theorem zlProperFrobeniusMap_isIso : IsIso (zlProperFrobeniusMap D l hl Ω p₀) := by
  sorry

/-- Proper Frobenius exchange with its actual mate as forward map.
Source: blueprint lem-fix-weil-operations (blueprint: def-zl-common-stage-weil-shriek). -/
def zlProperFrobenius :
    zlCommonStageProperPush D l hl Ω p₀ ⋙ sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω ≅
      sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω ⋙ zlCommonStageProperPush D l hl Ω p₀ :=
  letI := zlProperFrobeniusMap_isIso D l hl Ω p₀
  asIso (zlProperFrobeniusMap D l hl Ω p₀)
end Proper

section Open
variable {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  (j₀ : X₀ ⟶ Y₀) [IsOpenImmersion j₀.left]

/-- Open inverse image has constructible extension by zero as its left adjoint.
Source: SGA 4, XVII, §5; blueprint lem-fix-weil-operations
(blueprint: def-zl-common-stage-weil-shriek).
Proof: the finite-type schemes are Noetherian, so the open immersion is quasi-compact.
Exact extension by zero preserves constructibility at every positive coefficient
level. Apply it to the completed tower and its quotient maps. The open adjunction
restricts to complete constructible inputs. Rational localization and the compatible
coefficient-extension units descend its Hom bijections to the common-stage category.
The resulting left adjoint is the usual open extension, on all objects and maps. -/
theorem zlPull_open_isRightAdjoint : (zlPull D l hl Ω j₀).IsRightAdjoint := by
  sorry

/-- Open extension selected by its adjunction to the recorded inverse image.
Source: SGA 4, XVII, §5 (blueprint: def-zl-common-stage-weil-shriek). -/
def zlCommonStageOpenShriek :=
  letI := zlPull_open_isRightAdjoint D l hl Ω j₀
  (zlPull D l hl Ω j₀).leftAdjoint

/-- The open adjunction determining extension by zero, including its unit and counit.
Source: SGA 4, XVII, §5 (blueprint: def-zl-common-stage-weil-shriek). -/
def zlCommonStageOpenAdjunction :
    zlCommonStageOpenShriek D l hl Ω j₀ ⊣ zlPull D l hl Ω j₀ :=
  letI := zlPull_open_isRightAdjoint D l hl Ω j₀
  Adjunction.ofIsRightAdjoint (zlPull D l hl Ω j₀)

/-- Inverse open Frobenius exchange is the left mate of the normalized pullback square.
Source: blueprint lem-fix-weil-operations, open extension paragraph
(blueprint: def-zl-common-stage-weil-shriek). -/
def zlOpenFrobeniusInverseMap :
    sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω ⋙ zlCommonStageOpenShriek D l hl Ω j₀ ⟶
      zlCommonStageOpenShriek D l hl Ω j₀ ⋙ sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω :=
  ((mateEquiv (zlCommonStageOpenAdjunction D l hl Ω j₀)
    (zlCommonStageOpenAdjunction D l hl Ω j₀)).symm
    (TwoSquare.mk _ _ _ _ (zlFrobeniusSquare D l hl Ω j₀).hom)).natTrans

/-- The specified open mate is invertible for the geometric-Frobenius square.
Source: blueprint lem-fix-weil-operations, inverse automorphism squares
(blueprint: def-zl-common-stage-weil-shriek).
Proof: form the left mate for the inverse Frobenius square. Frobenius and its inverse
are scheme automorphisms, so their normalized pullback squares paste to identity.
The left-mate pasting identities identify both composites with the identity. Hence
this inverse open exchange is invertible on the whole common-stage category. -/
theorem zlOpenFrobeniusInverseMap_isIso :
    IsIso (zlOpenFrobeniusInverseMap D l hl Ω j₀) := by
  sorry

/-- Open Frobenius exchange, inverse to the specified left mate.
Source: blueprint lem-fix-weil-operations (blueprint: def-zl-common-stage-weil-shriek). -/
def zlOpenFrobenius :
    zlCommonStageOpenShriek D l hl Ω j₀ ⋙ sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω ≅
      sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω ⋙ zlCommonStageOpenShriek D l hl Ω j₀ :=
  letI := zlOpenFrobeniusInverseMap_isIso D l hl Ω j₀
  (asIso (zlOpenFrobeniusInverseMap D l hl Ω j₀)).symm
end Open

section CompactSupport
variable {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left)

/-- Apply open extension first, then proper derived image, in the common-stage category.
Source: SGA 4, XVII, §5--6; blueprint lem-zl-shriek-composition
(blueprint: def-zl-common-stage-weil-shriek). -/
def zlCommonStageShriek :=
  letI : IsProper (zlCompactificationProper D f₀ c).left :=
    inferInstanceAs (IsProper c.g)
  zlCommonStageOpenShriek D l hl Ω (zlCompactificationOpen D f₀ c) ⋙
    zlCommonStageProperPush D l hl Ω (zlCompactificationProper D f₀ c)

/-- The composite proper/open Frobenius exchange, with canonical mate factors.
Source: blueprint lem-fix-weil-operations, compact-support paragraph
(blueprint: def-zl-common-stage-weil-shriek). -/
def zlShriekFrobenius :
    zlCommonStageShriek D l hl Ω f₀ c ⋙ sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω ≅
      sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω ⋙ zlCommonStageShriek D l hl Ω f₀ c :=
  letI : IsProper (zlCompactificationProper D f₀ c).left :=
    inferInstanceAs (IsProper c.g)
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (zlProperFrobenius D l hl Ω (zlCompactificationProper D f₀ c)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (zlOpenFrobenius D l hl Ω (zlCompactificationOpen D f₀ c)) _ ≪≫
    Functor.associator _ _ _

/-- Compact support on the existing fixed pairs. Its structure is Ex! followed by Rf!(theta).
Source: blueprint lem-fix-weil-operations (blueprint: def-zl-common-stage-weil-shriek). -/
def zlComplexShriek :
    sfCommonStageWeilComplex D l hl X₀ Ω ⥤ sfCommonStageWeilComplex D l hl Y₀ Ω :=
  IsoAlgebra.mapOfNatIso (zlShriekFrobenius D l hl Ω f₀ c)

/-- The underlying operation naturally agrees with every normalized compact-support action.
Source: Bhatt--Scholze 6.7.6--6.7.7; SGA 4, XVII, §5--6
(blueprint: def-zl-common-stage-weil-shriek).
Proof: proper image and open extension in the recorded coefficient construction satisfy
adjunction with the normalized inverse image. Uniqueness of adjoints identifies them
naturally with the two chosen adjoints above, on every object and morphism. Their
composite is the completed proper/open construction. Its projection-normalized tower
realization gives the integral compact-support action; localizing and applying the
specified tensor-unit coefficient comparisons gives the common-stage action S. Compare
the geometric base change of c with cg through a common proper refinement. Proper base
change and open unit mates identify their composites naturally. Compose these maps to
obtain the claimed natural isomorphism, without a restriction on representatives. -/
theorem zlCommonStageShriek_recorded [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (cg : Compactification (zlFiberMap D f₀))
    (S : SfCompactSupportCoefficientAction
      (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
      (f := zlFiberMap D f₀) l D.k (zlClosurePrimeUnit D l hl) Ω cg) :
    Nonempty (zlCommonStageShriek D l hl Ω f₀ c ≅ S.system.functor) := by
  sorry
end CompactSupport

/-- Frobenius exchange for the iterated compact-support functor, in its actual order.
Source: blueprint lem-zl-shriek-composition, iterated Weil structure
(blueprint: def-zl-common-stage-weil-shriek). -/
def zlShriekCompositeFrobenius {X₀ Y₀ Z₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (f₀ : X₀ ⟶ Y₀) (g₀ : Y₀ ⟶ Z₀)
    (cf : Compactification f₀.left) (cg : Compactification g₀.left) :
    (zlCommonStageShriek D l hl Ω f₀ cf ⋙ zlCommonStageShriek D l hl Ω g₀ cg) ⋙
        sfCommonStageWeilFrobeniusPullback D l hl Z₀ Ω ≅
      sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω ⋙
        (zlCommonStageShriek D l hl Ω f₀ cf ⋙ zlCommonStageShriek D l hl Ω g₀ cg) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (zlShriekFrobenius D l hl Ω g₀ cg) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (zlShriekFrobenius D l hl Ω f₀ cf) _ ≪≫
    Functor.associator _ _ _

end WeilConjectures
