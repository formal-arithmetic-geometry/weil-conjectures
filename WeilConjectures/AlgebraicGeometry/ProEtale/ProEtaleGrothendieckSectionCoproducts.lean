/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleQcqsSiteLimits
import WeilConjectures.AlgebraicGeometry.ProEtaleQcqsSubsite
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Comma.Over.Basic
import WeilConjectures.CategoryTheory.Finite.FiniteHypercoverColimits
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.CategoryTheory.Sites.Hypercover.IsSheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import WeilConjectures.CategoryTheory.Sites.Categorical.CategoricalFiniteCechCriterion
import WeilConjectures.CategoryTheory.Sites.Categorical.CategoricalInjectiveCechExactness
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # Coproducts of Grothendieck-valued pro-etale sheaf sections on qcqs objects -/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

private def qcqsTopology (X : Scheme.{u}) : GrothendieckTopology (Qcqs X) :=
  (qcqsInclusion X).restrictedTopology (topology X)

/-- Sections on a qcqs pro-etale object commute with coproducts with coefficients in
any Grothendieck abelian category. Source: Stacks Project, Tag 0738 and the qcqs
subsite in the proof of Tag 09A1.

Proof: The qcqs full subsite is cover dense, since affine open covers factor through
it. Every covering sieve on this subsite contains a finite affine refinement; pairwise
pullbacks stay qcqs. Consequently finite one-hypercovers generate its topology.
Restriction along the dense inclusion is an equivalence of sheaf categories. The
coproduct functor in a Grothendieck abelian category is exact and therefore preserves
finite limits. The finite-hypercover pointwise-colimit theorem shows that the sheaf
inclusion on the subsite preserves coproducts. Compose restriction, this inclusion,
and evaluation at the given qcqs object. This composite is precisely the original
section functor. All three factors preserve coproducts, including the empty one. -/
private theorem qcqs_evaluation_preservesCoproducts
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    (X : Scheme.{u}) (V : X.ProEt)
    [CompactSpace V.left] [QuasiSeparatedSpace V.left] (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I)
      (sheafToPresheaf (topology X) A ⋙ (CategoryTheory.evaluation X.ProEtᵒᵖ A).obj (op V)) := by
  let : HasColimitsOfSize.{u + 1, u + 1} A := IsGrothendieckAbelian.hasColimits A
  let : HasLimitsOfSize.{u + 1, u + 1} A := IsGrothendieckAbelian.hasLimits A
  let : HasLimitsOfSize.{u, u + 1} A :=
    hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} A
  let J := qcqsTopology X
  let G := qcqsInclusion X
  let : G.IsDenseSubsite J (topology X) := by
    dsimp [G, J, qcqsTopology]
    infer_instance
  let R := G.sheafPushforwardContinuous A J (topology X)
  let : ∀ W, HasLimitsOfShape (StructuredArrow W G.op) A := fun _ ↦ inferInstance
  let : R.IsEquivalence := by
    change (G.sheafPushforwardContinuous A J (topology X)).IsEquivalence
    infer_instance
  let : PreservesColimitsOfShape (Discrete I) (sheafToPresheaf J A) :=
    sheafToPresheaf_preservesColimits_of_finiteHypercovers J
  let W : Qcqs X := ⟨V, inferInstance, inferInstance⟩
  change PreservesColimitsOfShape (Discrete I)
    ((R ⋙ sheafToPresheaf J A) ⋙ (CategoryTheory.evaluation (Qcqs X)ᵒᵖ A).obj (op W))
  infer_instance

variable {X : Scheme.{u}}

private lemma compactSpace_and_quasiSeparatedSpace_of_iso {A B : X.ProEt} (e : A ≅ B)
    (h : CompactSpace A.left ∧ QuasiSeparatedSpace A.left) :
    CompactSpace B.left ∧ QuasiSeparatedSpace B.left := by
  let φ := TopCat.homeoOfIso
    (Scheme.forgetToTop.mapIso ((ProEt.forget X ⋙ Over.forget X).mapIso e))
  exact ⟨@Homeomorph.compactSpace _ _ _ _ h.1 φ, (quasiSeparatedSpace_congr φ).1 h.2⟩

/-- A fibre product of weakly étale `X`-schemes with quasi-compact quasi-separated
underlying schemes over one with quasi-separated underlying scheme has quasi-compact
quasi-separated underlying scheme. -/
private lemma compactSpace_and_quasiSeparatedSpace_pullback {V A B : X.ProEt}
    (f : A ⟶ V) (g : B ⟶ V)
    [QuasiSeparatedSpace V.left] [CompactSpace A.left] [QuasiSeparatedSpace A.left]
    [CompactSpace B.left] [QuasiSeparatedSpace B.left] :
    CompactSpace (pullback f g).left ∧ QuasiSeparatedSpace (pullback f g).left := by
  let iso := PreservesPullback.iso (ProEt.forget X ⋙ Over.forget X) f g
  have : QuasiCompact f.left := quasiCompact_of_compactSpace _
  have : CompactSpace ↥(Limits.pullback (C := Scheme.{u}) f.left g.left) := inferInstance
  have : QuasiSeparatedSpace ↥(Limits.pullback (C := Scheme.{u}) f.left g.left) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd f.left g.left)
  let φ := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso iso).symm
  exact ⟨@Homeomorph.compactSpace _ _ _ _ ‹_› φ, (quasiSeparatedSpace_congr φ).1 ‹_›⟩

/-- A finite product in `Over V` of weakly étale `X`-schemes with quasi-compact quasi-separated
underlying schemes has quasi-compact quasi-separated underlying scheme, if `V` has. -/
private lemma compactSpace_and_quasiSeparatedSpace_piObj {V : X.ProEt} [CompactSpace V.left]
    [QuasiSeparatedSpace V.left] {J : Type*} [Finite J] (U : J → Over V)
    (hU : ∀ j, CompactSpace (U j).left.left ∧ QuasiSeparatedSpace (U j).left.left) :
    CompactSpace (∏ᶜ U).left.left ∧ QuasiSeparatedSpace (∏ᶜ U).left.left := by
  let P : ObjectProperty (Over V) := fun A ↦
    CompactSpace A.left.left ∧ QuasiSeparatedSpace A.left.left
  have hiso {A B : Over V} (e : A ≅ B) (h : P A) : P B :=
    compactSpace_and_quasiSeparatedSpace_of_iso ((Over.forget V).mapIso e) h
  have : P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty) := ⟨by
    rintro A ⟨h⟩
    have hA : IsTerminal A := (isLimitEquivIsTerminalOfIsEmpty _ _) h.isLimit
    exact hiso (Over.mkIdTerminal.uniqueUpToIso hA) ⟨‹_›, ‹_›⟩⟩
  have : P.IsClosedUnderBinaryProducts := ⟨by
    rintro A ⟨h⟩
    let e : A ≅ h.diag.obj ⟨.left⟩ ⨯ h.diag.obj ⟨.right⟩ :=
      h.isLimit.conePointUniqueUpToIso (limit.isLimit _) ≪≫ HasLimit.isoOfNatIso (diagramIsoPair _)
    refine hiso e.symm ?_
    obtain ⟨_, _⟩ := h.prop_diag_obj ⟨.left⟩
    obtain ⟨_, _⟩ := h.prop_diag_obj ⟨.right⟩
    exact compactSpace_and_quasiSeparatedSpace_of_iso (Over.prodLeftIsoPullback _ _).symm
      (compactSpace_and_quasiSeparatedSpace_pullback _ _)⟩
  have : P.IsClosedUnderFiniteProducts := .mk'
  exact P.prop_product hU

end AlgebraicGeometry.Scheme.ProEt
