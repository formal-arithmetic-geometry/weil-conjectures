/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.Paper.WeilCompactSupportCohomology
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.FieldShriekCompositionQcqs
public import Sheaf.Paper.ImmersionWeilLocalBehavior

/-! # Frobenius comparison on completed compact-support representatives

Source: blueprint main-20261015, sec-deligne-laumon-general,
sk-l-dl-general-composition/lem-zl-shriek-composition.proof.md;
lem-fix-weil-operations, composition-comparison clause
(blueprint: def-zl-frobenius-compact-support-comparison).

The open comparison is the inverse of the open-adjunction mate. The proper
comparison is the direct-image mate. Both use the coefficient-normalized inverse
image compositor. Thus all maps are fixed before any coefficient localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport

variable (D : FiniteFieldDatum.{u})
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  (f₀ : X₀ ⟶ Y₀) (c₀ : Compactification f₀.left)

/-- The geometric-fibre factorization is the base change of the model factorization.
Source: blueprint composition proof, geometric-fibre paragraph
(blueprint: def-zl-frobenius-compact-support-comparison).
Proof: apply the base-change functor to c₀.i ≫ c₀.g = f₀.left. Its functoriality
and the defining equalities of zlCompactificationOpen and zlCompactificationProper
give the asserted equality, including on empty schemes. -/
theorem zlGeometricCompactification_comm :
    zlFiberMap D f₀ =
      zlFiberMap D (zlCompactificationOpen D f₀ c₀) ≫
        zlFiberMap D (zlCompactificationProper D f₀ c₀) := by
  sorry

/-- The geometric proper part is proper by stability under base change.
Source: blueprint composition proof; Stacks 01W4
(blueprint: def-zl-frobenius-compact-support-comparison).
Proof: the geometric-fibre square for the model proper map is Cartesian. Apply
properness under base change to c₀.g; the resulting map is the displayed fibre map. -/
theorem zlGeometricCompactification_isProper :
    IsProper (zlFiberMap D (zlCompactificationProper D f₀ c₀)) := by
  sorry

/-- The geometric open part is open by stability under base change.
Source: blueprint composition proof; Stacks 01JU
(blueprint: def-zl-frobenius-compact-support-comparison).
Proof: the geometric-fibre square for the model open map is Cartesian. Apply
stability of open immersions under base change to c₀.i. -/
theorem zlGeometricCompactification_isOpenImmersion :
    IsOpenImmersion (zlFiberMap D (zlCompactificationOpen D f₀ c₀)) := by
  sorry

/-- Base change of the actual model compactification, retaining its middle model.
Source: blueprint composition proof, geometric-fibre paragraph
(blueprint: def-zl-frobenius-compact-support-comparison). -/
def zlGeometricCompactification : Compactification (zlFiberMap D f₀) where
  Z := (D.geometricFiber (zlCompactificationMiddle D f₀ c₀)).left
  i := zlFiberMap D (zlCompactificationOpen D f₀ c₀)
  g := zlFiberMap D (zlCompactificationProper D f₀ c₀)
  comm := zlGeometricCompactification_comm D f₀ c₀
  isProper := zlGeometricCompactification_isProper D f₀ c₀
  isOpenImmersion := zlGeometricCompactification_isOpenImmersion D f₀ c₀

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The canonical ordinary completed-coefficient inverse image of geometric Frobenius.
This is an auxiliary ambient functor, not a second constructible pullback definition.
Source: blueprint Frobenius comparison; Stacks 099N
(blueprint: def-zl-frobenius-compact-support-comparison). -/
abbrev zlAmbientFrobenius (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :=
  pull (completed l E) (D.geometricFrobenius T₀).hom

/-- Pullback around the Frobenius square, with both compositors fixed on coefficients.
Source: blueprint Weil-operation compatibility; Stacks 099N(5)
(blueprint: def-zl-frobenius-compact-support-comparison). -/
def zlAmbientFrobeniusSquare :
    pull (completed l E) (zlFiberMap D f₀) ⋙ zlAmbientFrobenius D l E X₀ ≅
      zlAmbientFrobenius D l E Y₀ ⋙ pull (completed l E) (zlFiberMap D f₀) :=
  (geometricPullComposition (completed l E) (D.geometricFrobenius X₀).hom
      (zlFiberMap D f₀) (completedPull_comp l E _ _)).symm ≪≫
    eqToIso (congrArg (fun h ↦ pull (completed l E) h) (zlFrobenius_naturality D f₀)) ≪≫
      geometricPullComposition (completed l E) (zlFiberMap D f₀)
        (D.geometricFrobenius Y₀).hom (completedPull_comp l E _ _)

/-- The open mate in its unit-normalized direction, before inversion.
Source: blueprint Weil operations; Stacks 03DI
(blueprint: def-zl-frobenius-compact-support-comparison). -/
def zlFrobeniusOpenMate :
    zlAmbientFrobenius D l E X₀ ⋙
        (openExtension (completed l E) (zlGeometricCompactification D f₀ c₀).i).mapDerivedCategory ⟶
      (openExtension (completed l E) (zlGeometricCompactification D f₀ c₀).i).mapDerivedCategory ⋙
        zlAmbientFrobenius D l E
            (zlCompactificationMiddle D f₀ c₀) :=
  ((mateEquiv
    (openDerivedAdjunction (completed l E) (zlGeometricCompactification D f₀ c₀).i)
    (openDerivedAdjunction (completed l E) (zlGeometricCompactification D f₀ c₀).i)).symm
      (TwoSquare.mk _ _ _ _
        (zlAmbientFrobeniusSquare D (zlCompactificationOpen D f₀ c₀) l E).hom)).natTrans

/-- Proper direct-image mate of the same normalized Frobenius square.
Source: blueprint Weil operations; Stacks 0D6D
(blueprint: def-zl-frobenius-compact-support-comparison). -/
def zlFrobeniusProperMate :
    push (completed l E) (zlGeometricCompactification D f₀ c₀).g ⋙
        zlAmbientFrobenius D l E Y₀ ⟶
      zlAmbientFrobenius D l E (zlCompactificationMiddle D f₀ c₀) ⋙
        push (completed l E) (zlGeometricCompactification D f₀ c₀).g :=
  (mateEquiv
    (proEtaleRingDerivedAdjunction (zlGeometricCompactification D f₀ c₀).g
      ((completed l E).ring _) ((completed l E).ring _) ((completed l E).pull _))
    (proEtaleRingDerivedAdjunction (zlGeometricCompactification D f₀ c₀).g
      ((completed l E).ring _) ((completed l E).ring _) ((completed l E).pull _))
    (TwoSquare.mk _ _ _ _
      (zlAmbientFrobeniusSquare D (zlCompactificationProper D f₀ c₀) l E).inv)).natTrans

/-- Both prescribed mates are invertible for geometric Frobenius.
Source: blueprint lem-fix-weil-operations; Stacks 099N and 03DI
(blueprint: def-zl-frobenius-compact-support-comparison).
Proof: geometric Frobenius and its middle-model map are scheme isomorphisms.
Their exact inverse-image equivalences identify each square with an identity
square. Transpose the normalized pullback square under the open adjunction and
the proper derived adjunction. Transposing the inverse square gives inverses;
the two triangle identities prove the inverse equations. This works in the
ambient completed-ring module categories, before imposing constructibility. -/
theorem zlFrobeniusMates_isIso :
    IsIso (zlFrobeniusOpenMate D f₀ c₀ l E) ∧
      IsIso (zlFrobeniusProperMate D f₀ c₀ l E) := by
  sorry

/-- The canonical compact-support Frobenius comparison on completed representatives.
It is proper exchange followed by the inverse open mate.
Source: blueprint lem-fix-weil-operations, compact-support clause
(blueprint: def-zl-frobenius-compact-support-comparison). -/
def zlCompactSupportFrobenius :
    image (completed l E) (zlGeometricCompactification D f₀ c₀) ⋙
        zlAmbientFrobenius D l E Y₀ ≅
      zlAmbientFrobenius D l E X₀ ⋙
        image (completed l E) (zlGeometricCompactification D f₀ c₀) := by
  letI := (zlFrobeniusMates_isIso D f₀ c₀ l E).1
  letI := (zlFrobeniusMates_isIso D f₀ c₀ l E).2
  exact (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _ (asIso (zlFrobeniusProperMate D f₀ c₀ l E)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (zlFrobeniusOpenMate D f₀ c₀ l E)).symm _ ≪≫
    Functor.associator _ _ _

/-- Frobenius inverse image preserves the integral constructible domain.
Source: blueprint Weil-operation clause; Bhatt--Scholze 6.5.9
(blueprint: def-zl-frobenius-compact-support-comparison).
Proof: an isomorphism of schemes induces an exact equivalence on module sheaves,
including their completed coefficient sheaves. This equivalence preserves products,
the actual Roos completion map, and its inverse. It therefore preserves derived
completeness. Each finite reduction is exact inverse image of the old reduction,
with its etale-origin constructibility witness and the same common finite interval.
These are exactly the two clauses of sfIntegralConstructible. -/
theorem zlAmbientFrobenius_constructible
    (hl : l ≠ D.p) (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber T₀).left) :
    sfIntegralConstructible l E (D.geometricFiber T₀).left
      ((zlAmbientFrobenius D l E T₀).obj K.obj) := by
  sorry

/-- The geometric-fibre functor respects composition.
Source: blueprint composition proof, geometric-fibre paragraph
(blueprint: def-zl-frobenius-compact-support-comparison).
Proof: unfold zlFiberMap, apply Over.pullback.map_comp, and take underlying maps. -/
theorem zlFiberMap_comp {Z₀ : Over (Spec (.of D.k₀))} (g₀ : Y₀ ⟶ Z₀) :
    zlFiberMap D (f₀ ≫ g₀) = zlFiberMap D f₀ ≫ zlFiberMap D g₀ := by
  sorry

/-- The composite's model compactification, with only its index equality transported.
Its open map, proper map, and middle scheme are unchanged.
Source: blueprint geometric-fibre composition convention
(blueprint: def-zl-frobenius-compact-support-comparison). -/
def zlGeometricCompositeCompactification {Z₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (g₀ : Y₀ ⟶ Z₀) (c : Compactification (f₀ ≫ g₀).left) :
    Compactification (zlFiberMap D f₀ ≫ zlFiberMap D g₀) :=
  (zlGeometricCompactification D (f₀ ≫ g₀) c).copy (zlFiberMap_comp D f₀ g₀).symm

/-- The completed-representative realization of the fixed integral compositor.
It first uses the two projection-normalized realization isomorphisms, applies the
canonical integral compositor, and returns through the composite realization.
Source: blueprint composition constraint; Stacks 0F7J
(blueprint: def-zl-frobenius-compact-support-comparison). -/
def zlCompletedShriekCompositor (hl : l ≠ D.p)
    {Z₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (g₀ : Y₀ ⟶ Z₀)
    [IsSeparated g₀.left] [LocallyOfFiniteType g₀.left] [QuasiCompact g₀.left]
    (cg₀ : Compactification g₀.left) (cfg₀ : Compactification (f₀ ≫ g₀).left)
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left) :
    (image (completed l E) (zlGeometricCompactification D g₀ cg₀)).obj
        ((image (completed l E) (zlGeometricCompactification D f₀ c₀)).obj K.obj) ≅
      (image (completed l E) (zlGeometricCompactification D (f₀ ≫ g₀) cfg₀)).obj K.obj :=
  (image (completed l E) (zlGeometricCompactification D g₀ cg₀)).mapIso
      ((sfQcqsCompactSupportRealization l E D.k (coefficientPrimeUnit l D hl)
        (zlGeometricCompactification D f₀ c₀)).app K) ≪≫
    (sfQcqsCompactSupportRealization l E D.k (coefficientPrimeUnit l D hl)
      (zlGeometricCompactification D g₀ cg₀)).app
        ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl)
          (zlGeometricCompactification D f₀ c₀) E).obj K) ≪≫
    (sfIntegralConstructible l E (D.geometricFiber Z₀).left).ι.mapIso
      ((sfFieldShriekCompositionIntegral D l hl
        (zlGeometricCompactification D f₀ c₀) (zlGeometricCompactification D g₀ cg₀)
        (zlGeometricCompositeCompactification D f₀ g₀ cfg₀) E).app K) ≪≫
    (sfQcqsCompactSupportRealization l E D.k (coefficientPrimeUnit l D hl)
      (zlGeometricCompositeCompactification D f₀ g₀ cfg₀)).symm.app K

end WeilConjectures
