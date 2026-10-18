/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q90
-/
module

public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Sheaf.Paper.NormalizedDVREffectivity
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Paper.DerivedNakayama
import Sheaf.Paper.NormalizedDVRTower

/-!
# Normalized reconstruction and its adjunction calculus

Source: current Weil blueprint, sec-smooth-purity,
prop-pur-adic-reconstruction-trace-coherence, sole proof paragraph
(blueprint: lem-pur-normalized-reconstruction-adjunction-calculus).

All categories are unbounded. The system category, reduction, total limit and their
unit/counit are the recorded evaluation calculus, with its actual projection normalization.
The property Q selects any replete full subcategory; Q = top gives the entire normalized
category. No cohomological, constructibility or Tor-amplitude restriction is imposed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u tX tY tZ v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- Reconstruction uses the actual evaluation-calculus adjunction.
Source: the sole proof paragraph of prop-pur-adic-reconstruction-trace-coherence
(blueprint: lem-pur-normalized-reconstruction-adjunction-calculus).
Proof: (1) K-flat scalar extension shows reduction is normalized, as recorded in S.
(2) Apply lem-coef-normalized-dvr-effectivity to the evaluated normalized tower.
The resulting scalar-extension comparisons are precisely S.counit_projection;
joint conservativity of derived evaluation makes the actual counit invertible.
The same effectivity theorem gives completeness of its total limit.
(3) The triangle identity makes reduction of the unit invertible. Its first evaluation
is reduction modulo the uniformizer, by S.unit_projection. Apply
sk-lem-pe-derived-nakayama between the complete source and complete target.
Naturality is already that of S.adjunction. No boundedness is used. -/
theorem purNormalizedReconstruction
    (_hl : IsUnit (l : Γ(W, ⊤))) (S : CoefficientDerivedSystemCalculus l E W) :
    (∀ (N : coefficientSequenceDerived l E W), IsNormalizedCoefficientSequence l E W N →
      IntegralOnSlice.IsComplete l E W none ((coefficientSequenceLimit l E W).obj N) ∧
        IsIso (S.adjunction.counit.app N)) ∧
    (∀ (K : DerivedCategory (scalarReductionSource l E W)),
      IntegralOnSlice.IsComplete l E W none K → IsIso (S.adjunction.unit.app K)) := by
  sorry

/-- The normalized replete subcategory selected by Q. Source: the same proof paragraph
(blueprint: lem-pur-normalized-reconstruction-adjunction-calculus). -/
def purNormalizedProperty (Q : ObjectProperty (coefficientSequenceDerived l E W)) :
    ObjectProperty (coefficientSequenceDerived l E W) :=
  fun N ↦ IsNormalizedCoefficientSequence l E W N ∧ Q N

/-- Complete objects whose reduction belongs to Q. Source: the same proof paragraph
(blueprint: lem-pur-normalized-reconstruction-adjunction-calculus). -/
def purCompleteProperty (S : CoefficientDerivedSystemCalculus l E W)
    (Q : ObjectProperty (coefficientSequenceDerived l E W)) :
    ObjectProperty (DerivedCategory (scalarReductionSource l E W)) :=
  fun K ↦ IntegralOnSlice.IsComplete l E W none K ∧ Q (S.reduction.obj K)

variable (hl : IsUnit (l : Γ(W, ⊤))) (S : CoefficientDerivedSystemCalculus l E W)
  (Q : ObjectProperty (coefficientSequenceDerived l E W)) [Q.IsClosedUnderIsomorphisms]

/-- Reduction restricted to the specified full subcategories, on objects and maps.
Source: the same proof paragraph
(blueprint: lem-pur-normalized-reconstruction-adjunction-calculus). -/
def purRestrictedReduction :
    (purCompleteProperty l E W S Q).FullSubcategory ⥤
      (purNormalizedProperty l E W Q).FullSubcategory :=
  (purNormalizedProperty l E W Q).lift
    ((purCompleteProperty l E W S Q).ι ⋙ S.reduction)
    (fun K ↦ ⟨S.reduction_normalized K.obj, K.property.2⟩)

/-- Total limit restricted using completeness and the actual counit isomorphism.
Source: the same proof paragraph
(blueprint: lem-pur-normalized-reconstruction-adjunction-calculus). -/
def purRestrictedLimit :
    (purNormalizedProperty l E W Q).FullSubcategory ⥤
      (purCompleteProperty l E W S Q).FullSubcategory :=
  (purCompleteProperty l E W S Q).lift
    ((purNormalizedProperty l E W Q).ι ⋙ coefficientSequenceLimit l E W)
    (fun N ↦ ⟨((purNormalizedReconstruction l E W hl S).1 N.obj N.property.1).1,
      Q.prop_of_iso
        (@asIso _ _ _ _ (S.adjunction.counit.app N.obj)
          ((purNormalizedReconstruction l E W hl S).1 N.obj N.property.1).2).symm
        N.property.2⟩)

/-- Restriction of the specified adjunction along the full inclusions.
Source: the same proof paragraph
(blueprint: lem-pur-normalized-reconstruction-adjunction-calculus). -/
def purRestrictedAdjunction :
    purRestrictedReduction l E W S Q ⊣ purRestrictedLimit l E W hl S Q :=
  S.adjunction.restrictFullyFaithful
    (purCompleteProperty l E W S Q).fullyFaithfulι
    (purNormalizedProperty l E W Q).fullyFaithfulι (Iso.refl _) (Iso.refl _)

/-- The restricted unit and counit are exactly the ambient ones and are invertible.
Source: the same proof paragraph
(blueprint: lem-pur-normalized-reconstruction-adjunction-calculus).
Proof: restrict the ambient unit/counit along the two full inclusions. The comparison
squares are identities, so their images are the actual unit/counit of S.adjunction.
Apply purNormalizedReconstruction and reflection of isomorphisms by a full inclusion.
Closure of Q under isomorphisms was used only to restrict the total limit. -/
theorem purRestrictedUnitCounit :
    (∀ K, IsIso ((purRestrictedAdjunction l E W hl S Q).unit.app K)) ∧
    (∀ N, IsIso ((purRestrictedAdjunction l E W hl S Q).counit.app N)) ∧
    (∀ K, ((purRestrictedAdjunction l E W hl S Q).unit.app K).hom =
      S.adjunction.unit.app K.obj) ∧
    (∀ N, ((purRestrictedAdjunction l E W hl S Q).counit.app N).hom =
      S.adjunction.counit.app N.obj) := by
  sorry

/-- The restricted adjoint equivalence, retaining the actual unit and counit.
Source: the same proof paragraph
(blueprint: lem-pur-normalized-reconstruction-adjunction-calculus). -/
def purReconstructionEquivalence :
    (purCompleteProperty l E W S Q).FullSubcategory ≌
      (purNormalizedProperty l E W Q).FullSubcategory :=
  letI := (purRestrictedUnitCounit l E W hl S Q).1
  letI := (purRestrictedUnitCounit l E W hl S Q).2.1
  (purRestrictedAdjunction l E W hl S Q).toEquivalence

namespace PurReconstruction

variable {C₁ : Type u₁} [Category.{v₁} C₁] {N₁ : Type u₂} [Category.{v₂} N₁]
  {C₂ : Type u₃} [Category.{v₃} C₂] {N₂ : Type u₄} [Category.{v₄} N₂]
  {C₃ : Type u₅} [Category.{v₅} C₃] {N₃ : Type u₆} [Category.{v₆} N₃]

/-- Realization L_Y F R_X. Source: the same proof paragraph
(blueprint: lem-pur-normalized-reconstruction-adjunction-calculus). -/
def realized (eX : C₁ ≌ N₁) (eY : C₂ ≌ N₂) (F : N₁ ⥤ N₂) : C₁ ⥤ C₂ :=
  eX.functor ⋙ F ⋙ eY.inverse

/-- The transported adjunction is the composite of the three specified adjunctions.
Source: the same proof paragraph
(blueprint: lem-pur-normalized-reconstruction-adjunction-calculus). -/
def realizedAdjunction (eX : C₁ ≌ N₁) (eY : C₂ ≌ N₂)
    {F : N₁ ⥤ N₂} {G : N₂ ⥤ N₁} (adj : F ⊣ G) :
    realized eX eY F ⊣ realized eY eX G :=
  (eX.toAdjunction.comp adj).comp eY.symm.toAdjunction

/-- The natural identification Fbar L_X = L_Y F, induced by the actual system counit.
Source: the same proof paragraph
(blueprint: lem-pur-normalized-reconstruction-adjunction-calculus). -/
def realizationComparison (eX : C₁ ≌ N₁) (eY : C₂ ≌ N₂) (F : N₁ ⥤ N₂) :
    eX.inverse ⋙ realized eX eY F ≅ F ⋙ eY.inverse :=
  isoWhiskerRight eX.counitIso (F ⋙ eY.inverse) ≪≫ Functor.leftUnitor _

/-- Realization of a transformation, by functorial whiskering.
Source: the same proof paragraph
(blueprint: lem-pur-normalized-reconstruction-adjunction-calculus). -/
def realizedTransformation (eX : C₁ ≌ N₁) (eY : C₂ ≌ N₂)
    {F F' : N₁ ⥤ N₂} (α : F ⟶ F') : realized eX eY F ⟶ realized eX eY F' :=
  Functor.whiskerLeft eX.functor (Functor.whiskerRight α eY.inverse)

/-- The natural composition comparison inserts e_Y between R_Y and L_Y.
Source: the same proof paragraph
(blueprint: lem-pur-normalized-reconstruction-adjunction-calculus). -/
def compositionComparison (eX : C₁ ≌ N₁) (eY : C₂ ≌ N₂) (eZ : C₃ ≌ N₃)
    (F : N₁ ⥤ N₂) (H : N₂ ⥤ N₃) :
    realized eX eY F ⋙ realized eY eZ H ≅ realized eX eZ (F ⋙ H) :=
  isoWhiskerLeft (eX.functor ⋙ F)
    (isoWhiskerRight eY.counitIso (H ⋙ eZ.inverse) ≪≫ Functor.leftUnitor _)

/-- The explicit transported counit, transpose and composition formulas.
These are propositions about the preceding constructions, with no extra choice of maps.
Source: the same proof paragraph
(blueprint: lem-pur-normalized-reconstruction-adjunction-calculus). -/
structure Calculus (eX : C₁ ≌ N₁) (eY : C₂ ≌ N₂) (eZ : C₃ ≌ N₃) : Prop where
  /-- The counit is u inverse after L epsilon after L F(e). -/
  counit : ∀ (F : N₁ ⥤ N₂) (G : N₂ ⥤ N₁) (adj : F ⊣ G) (K : C₂),
    (realizedAdjunction eX eY adj).counit.app K =
      eY.inverse.map (F.map (eX.counit.app (G.obj (eY.functor.obj K)))) ≫
        eY.inverse.map (adj.counit.app (eY.functor.obj K)) ≫ eY.unitInv.app K
  /-- After the e-induced identifications, the transpose is L(epsilon after F(a)). -/
  transpose : ∀ (F : N₁ ⥤ N₂) (G : N₂ ⥤ N₁) (adj : F ⊣ G)
    (P : N₁) (N : N₂) (a : P ⟶ G.obj N),
    ((realizedAdjunction eX eY adj).homEquiv _ _).symm
        (eX.inverse.map a ≫ (realizationComparison eY eX G).inv.app N) =
      (realizationComparison eX eY F).hom.app P ≫
        eY.inverse.map (F.map a ≫ adj.counit.app N)
  /-- The composition comparison has the specified component L_Z H(e_Y). -/
  composition : ∀ (F : N₁ ⥤ N₂) (H : N₂ ⥤ N₃) (K : C₁),
    (compositionComparison eX eY eZ F H).hom.app K =
      eZ.inverse.map (H.map (eY.counit.app (F.obj (eX.functor.obj K))))
  /-- The composition comparisons commute with transformations in both functors. -/
  transformation : ∀ (F F' : N₁ ⥤ N₂) (H H' : N₂ ⥤ N₃) (α : F ⟶ F') (β : H ⟶ H'),
    Functor.whiskerRight (realizedTransformation eX eY α) (realized eY eZ H) ≫
        Functor.whiskerLeft (realized eX eY F') (realizedTransformation eY eZ β) ≫
        (compositionComparison eX eY eZ F' H').hom =
      (compositionComparison eX eY eZ F H).hom ≫
        realizedTransformation eX eZ (Functor.whiskerRight α H ≫ Functor.whiskerLeft F' β)

end PurReconstruction

/-- Reconstruction and adjunction calculus, including arbitrary replete restrictions.
Source: prop-pur-adic-reconstruction-trace-coherence, sole proof paragraph
(blueprint: lem-pur-normalized-reconstruction-adjunction-calculus).
Proof: purNormalizedReconstruction and purRestrictedUnitCounit give the actual
restricted adjoint equivalences. For the counit compose L_X adjoint R_X, F adjoint G,
and R_Y adjoint L_Y, tracking the identity through their Hom bijections. This yields
u inverse after L(epsilon) after L F(e). For the transpose use naturality of e at a,
then cancel unit/counit pairs by the triangles; the result is L(epsilon after F(a)).
The comparison is a natural isomorphism, hence is natural for every system map.
For composition insert e_Y in the middle R_Y L_Y. Its naturality proves compatibility
with transformations in F and H. These calculations use only the restricted categories,
so functors and adjunctions need be defined only there, including the empty subcategory.
The earlier reconstruction proof is precisely the node's first four steps, and these
three calculations are its final three steps. -/
theorem purNormalizedReconstructionAdjunctionCalculus
    (X : Scheme.{tX}) (Y : Scheme.{tY}) (Z : Scheme.{tZ})
    (hX : IsUnit (l : Γ(X, ⊤))) (hY : IsUnit (l : Γ(Y, ⊤)))
    (hZ : IsUnit (l : Γ(Z, ⊤)))
    (SX : CoefficientDerivedSystemCalculus l E X)
    (SY : CoefficientDerivedSystemCalculus l E Y)
    (SZ : CoefficientDerivedSystemCalculus l E Z)
    (QX : ObjectProperty (coefficientSequenceDerived l E X))
    (QY : ObjectProperty (coefficientSequenceDerived l E Y))
    (QZ : ObjectProperty (coefficientSequenceDerived l E Z))
    [QX.IsClosedUnderIsomorphisms] [QY.IsClosedUnderIsomorphisms]
    [QZ.IsClosedUnderIsomorphisms] :
    PurReconstruction.Calculus
      (purReconstructionEquivalence l E X hX SX QX)
      (purReconstructionEquivalence l E Y hY SY QY)
      (purReconstructionEquivalence l E Z hZ SZ QZ) := by
  sorry

end WeilConjectures
