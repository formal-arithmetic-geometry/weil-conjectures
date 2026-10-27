/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.TraceFormula.AmpleSchemeTestLinePreparationDefs
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Sheaf.AlgebraicGeometry.AlgebraicSpaceInvertibleDescent
import Sheaf.SixFunctors.TraceFormula.SchemeEtaleInvertibleComparison
import Sheaf.SixFunctors.TraceFormula.EtaleLineSectionsNormalizedComparisons
import Sheaf.AlgebraicGeometry.TensorPullbackOpenRestriction

/-!
# Normalized pullback of the restriction line-descent datum

Source: Stacks, Spaces Descent, Tags 04W8 and 060X; Descent, Tags 03DX and 03LC
(blueprint: lem-trf-ample-test-normalized-line-descent).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.AlgebraicSpace

attribute [local irreducible] tensorPullback tensorPullbackObj

/-- Only the normalized line-descent part of scheme-test preparation. It contains no
relative ampleness, base scheme, or quasi-compactness/separatedness conclusion.
Source: Stacks, Spaces Descent, Tags 04W8 and 060X; Descent, Tags 03DX and 03LC
(blueprint: lem-trf-ample-test-normalized-line-descent). -/
structure AmpleTestNormalizedLineData {S : Scheme.{u}} {I : Type v}
    (F X : AlgebraicSpace S) (k : X ⟶ F) (M : F.Modules)
    (Fᵢ : I → F.EtaleSite) (Xᵢ : I → X.EtaleSite)
    (xF : ∀ i : I, (Xᵢ i).obj.left ⟶ (Fᵢ i).obj.left) where
  /-- The original Zariski restrictions are ordinary invertible modules. -/
  original_invertible : ∀ i : I, ((F.schemeRestriction (Fᵢ i)).obj M).IsInvertible
  /-- Original ordinary/etale restriction identifications. -/
  original : ∀ i : I, OrdinaryEtaleIdentification F (Fᵢ i) M
    ((F.schemeRestriction (Fᵢ i)).obj M)
  /-- They are the canonical restriction identifications, normalized on all opens. -/
  original_normalized : ∀ i : I, AmpleTestRestrictionNormalized F (Fᵢ i) M (original i)
  /-- Represented original double overlaps. -/
  R : I → I → Over S
  /-- First overlap projection. -/
  r₁ : ∀ i j : I, R i j ⟶ (Fᵢ i).obj.left
  /-- Second overlap projection. -/
  r₂ : ∀ i j : I, R i j ⟶ (Fᵢ j).obj.left
  /-- The original overlap square. -/
  overlapCartesian : ∀ i j : I, IsPullback (yoneda.map (r₁ i j))
    (yoneda.map (r₂ i j)) (Fᵢ i).obj.hom (Fᵢ j).obj.hom
  /-- Original restriction transitions. -/
  α : ∀ i j : I,
    (tensorPullback (r₂ i j).left).obj ((F.schemeRestriction (Fᵢ j)).obj M) ≅
      (tensorPullback (r₁ i j).left).obj ((F.schemeRestriction (Fᵢ i)).obj M)
  /-- The transitions are induced by restriction of the same `M`. -/
  original_transitions : AmpleTestInducesTransitions F Fᵢ R r₁ r₂
    (fun i ↦ (F.schemeRestriction (Fᵢ i)).obj M) α M original
  /-- Represented new double overlaps. -/
  D : I → I → Over S
  /-- First new overlap projection. -/
  d₁ : ∀ i j : I, D i j ⟶ (Xᵢ i).obj.left
  /-- Second new overlap projection. -/
  d₂ : ∀ i j : I, D i j ⟶ (Xᵢ j).obj.left
  /-- The new overlap square. -/
  newOverlapCartesian : ∀ i j : I, IsPullback (yoneda.map (d₁ i j))
    (yoneda.map (d₂ i j)) (Xᵢ i).obj.hom (Xᵢ j).obj.hom
  /-- The map of overlaps induced by the projections to the old charts. -/
  overlapMap : ∀ i j : I, D i j ⟶ R i j
  /-- Its first defining equation. -/
  overlapMap_fst : ∀ i j : I, overlapMap i j ≫ r₁ i j = d₁ i j ≫ xF i
  /-- Its second defining equation. -/
  overlapMap_snd : ∀ i j : I, overlapMap i j ≫ r₂ i j = d₂ i j ≫ xF j
  /-- Transitions of the literal tensor pullbacks `N_i`. -/
  β : ∀ i j : I,
    (tensorPullback (d₂ i j).left).obj
        ((tensorPullback (xF j).left).obj ((F.schemeRestriction (Fᵢ j)).obj M)) ≅
      (tensorPullback (d₁ i j).left).obj
        ((tensorPullback (xF i).left).obj ((F.schemeRestriction (Fᵢ i)).obj M))
  /-- They are precisely pullbacks of the original restriction transitions. -/
  transition_eq : ∀ i j : I, β i j = ampleTestPulledTransition
    ((F.schemeRestriction (Fᵢ i)).obj M) ((F.schemeRestriction (Fᵢ j)).obj M)
    (r₁ i j) (r₂ i j) (α i j) (xF i) (xF j) (d₁ i j) (d₂ i j) (overlapMap i j)
    (overlapMap_fst i j) (overlapMap_snd i j)
  /-- The diagonal identity, including nontrivial self-overlaps. -/
  diagonal : ∀ (i : I) (d : (Xᵢ i).obj.left ⟶ D i i)
    (h₁ : d ≫ d₁ i i = 𝟙 _) (h₂ : d ≫ d₂ i i = 𝟙 _),
    atlasTransitionOver
      ((tensorPullback (xF i).left).obj ((F.schemeRestriction (Fᵢ i)).obj M))
      ((tensorPullback (xF i).left).obj ((F.schemeRestriction (Fᵢ i)).obj M))
      (d₁ i i) (d₂ i i) (β i i) d (𝟙 _) (𝟙 _) h₁ h₂ = Iso.refl _
  /-- The triple-overlap cocycle on every scheme test. -/
  cocycle : ∀ (i j k : I) (U : Over S)
    (a : U ⟶ (Xᵢ i).obj.left) (b : U ⟶ (Xᵢ j).obj.left) (c : U ⟶ (Xᵢ k).obj.left)
    (q₁₂ : U ⟶ D i j) (q₂₃ : U ⟶ D j k) (q₁₃ : U ⟶ D i k)
    (h₁₂₁ : q₁₂ ≫ d₁ i j = a) (h₁₂₂ : q₁₂ ≫ d₂ i j = b)
    (h₂₃₁ : q₂₃ ≫ d₁ j k = b) (h₂₃₂ : q₂₃ ≫ d₂ j k = c)
    (h₁₃₁ : q₁₃ ≫ d₁ i k = a) (h₁₃₂ : q₁₃ ≫ d₂ i k = c),
    atlasTransitionOver
        ((tensorPullback (xF i).left).obj ((F.schemeRestriction (Fᵢ i)).obj M))
        ((tensorPullback (xF k).left).obj ((F.schemeRestriction (Fᵢ k)).obj M))
        (d₁ i k) (d₂ i k) (β i k) q₁₃ a c h₁₃₁ h₁₃₂ =
      atlasTransitionOver
        ((tensorPullback (xF j).left).obj ((F.schemeRestriction (Fᵢ j)).obj M))
        ((tensorPullback (xF k).left).obj ((F.schemeRestriction (Fᵢ k)).obj M))
        (d₁ j k) (d₂ j k) (β j k) q₂₃ b c h₂₃₁ h₂₃₂ ≪≫
      atlasTransitionOver
        ((tensorPullback (xF i).left).obj ((F.schemeRestriction (Fᵢ i)).obj M))
        ((tensorPullback (xF j).left).obj ((F.schemeRestriction (Fᵢ j)).obj M))
        (d₁ i j) (d₂ i j) (β i j) q₁₂ a b h₁₂₁ h₁₂₂
  /-- The descended small-etale module. -/
  N : X.Modules
  /-- It is a line module. -/
  isLine : X.IsLineModule N
  /-- The local identifications with the ordinary tensor pullbacks. -/
  identification : ∀ i : I, OrdinaryEtaleIdentification X (Xᵢ i) N
    ((tensorPullback (xF i).left).obj ((F.schemeRestriction (Fᵢ i)).obj M))
  /-- These identifications induce exactly the pulled-back transitions. -/
  induces : AmpleTestInducesTransitions X Xᵢ D d₁ d₂
    (fun i ↦ (tensorPullback (xF i).left).obj ((F.schemeRestriction (Fᵢ i)).obj M))
    β N identification
  /-- Uniqueness up to the unique isomorphism preserving all local identifications. -/
  unique : AmpleTestUniqueRealization X Xᵢ D d₁ d₂
    (fun i ↦ (tensorPullback (xF i).left).obj ((F.schemeRestriction (Fᵢ i)).obj M))
    β N identification
  /-- Compatibility with restriction when the projection to F is etale. -/
  etaleComparison : AmpleTestEtaleComparison F X k M N Fᵢ Xᵢ xF
    original identification

/-- Pull the restriction descent datum of a line module across any cartesian family
of scheme charts and descend it with its exact normalized section identifications.
Source: Stacks, Spaces Descent, Tags 04W8 and 060X; Descent, Tags 03DX, 05VG and 03LC
(blueprint: lem-trf-ample-test-normalized-line-descent).

Proof: restriction of a line module to a scheme chart gives an ordinary invertible
module by the Zariski/etale equivalence. Its comparison on every localized etale test
is the tensor-unit normalized one; on an open inclusion the unit followed by this
comparison is the identity. Represent the original and new double overlaps using the
representable diagonals. The identity of the two restrictions of M on an original
overlap gives alpha; full faithfulness of scheme comparison fixes it uniquely.
Representability and the equation for xF give the maps of new overlaps to old ones.
Define beta by pulling alpha back and inserting the specified tensor composition maps.
The unit-normalized composition maps are associative: both bracketings on a pure tensor
c tensor (d tensor m) multiply the same scalars. Thus the diagonal and triple cocycle
identities of alpha imply those of beta. Effective invertible descent gives N and its
local identifications inducing beta. For two realizations, the local maps e' composed
with inverse e agree on overlaps; full faithfulness glues a unique global map. Glue the
local inverses as well; injectivity proves the two composites are identities, giving the
unique isomorphism preserving every identification. For etale k, restriction of M to X
has the same local tensor-pullback identifications, with the composite-section formula
of Tag 03LC. Applying that same uniqueness argument gives precisely etaleComparison.
No ampleness or flatness of k is used; its etaleness is needed only in the last clause.
For an index universe larger than the site, select a small covering subfamily (scheme
points of a fixed atlas give a small set of choices), descend there, then recover all
remaining chart identifications by full faithfulness. The empty target is covered by
the same sheaf gluing statement. -/
theorem exists_ampleTestNormalizedLineData
    {S : Scheme.{u}} {I : Type v} (F X : AlgebraicSpace S) (k : X ⟶ F)
    (M : F.Modules) (hM : F.IsLineModule M)
    (Fᵢ : I → F.EtaleSite) (Xᵢ : I → X.EtaleSite)
    (xF : ∀ i : I, (Xᵢ i).obj.left ⟶ (Fᵢ i).obj.left)
    (hcomm : ∀ i : I, (Xᵢ i).obj.hom ≫ k.hom.hom =
      yoneda.map (xF i) ≫ (Fᵢ i).obj.hom)
    (hcover : IsJointlySurjective (fun i : I ↦ (Xᵢ i).obj.hom)) :
    Nonempty (AmpleTestNormalizedLineData F X k M Fᵢ Xᵢ xF) := by sorry

end AlgebraicGeometry.AlgebraicSpace
