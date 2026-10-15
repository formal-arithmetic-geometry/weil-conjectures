/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF maintainer L
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf

/-!
# Challenge: upstream proper base change dependencies

The human's 2026-10-12 decision adopts the corrected upstream statements (PR 1413,
46dc75fcf and reviewer fix 84babb37e). At slopmaster2 ffb7b9060 the selected targets are
six sorry carriers: geometric-stalk comparison, two curve field-extension declarations,
filtered cohomology, section continuity, and henselian idempotent lifting.
Their signatures are copied from that tip; torsion module sheaves use the upstream name
`Scheme.IsTorsionModuleSheaf`. The reduction and the prime-coefficient acyclicity bridge
are now proved upstream. No private copy of either base-change property is needed.

The main result is `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper` for bounded below
complexes of abelian sheaves with torsion cohomology (Stacks 0DDE). Its torsion-ring form is
`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring`; the former module
statement is `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_torsionHomology`.
See `coord/target-migration.md` for the closure audit and target choice.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open AlgebraicGeometry Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Target 1: verbatim upstream signature at `ffb7b9060`.
(blueprint: `lemma-weil-pbc-p1-exchange-geometric-stalk`) -/
theorem AlgebraicGeometry.Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_projectiveLine
    {S T X' : Scheme.{u}} {g : T ⟶ S} {f' : X' ⟶ T} {g' : X' ⟶ ProjectiveLine S}
    (sq : IsPullback g' f' (ProjectiveLine S ↘ S) g)
    {k k' : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T) (ι : Spec (.of k') ⟶ Spec (.of k))
    (hι : ι ≫ σ = τ ≫ g)
    (hσ : ∃ (s : S) (φ : S.residueField s ⟶ .of k),
      φ.hom.IsIntegral ∧ Spec.map φ ≫ S.fromSpecResidueField s = σ)
    (hτ : ∃ (t : T) (φ : T.residueField t ⟶ .of k'),
      φ.hom.IsIntegral ∧ Spec.map φ ≫ T.fromSpecResidueField t = τ)
    (F : Sheaf (ProjectiveLine S).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionModuleSheaf F] (q : ℕ) :
    ∃ (e₁ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeSourceFunctor Λ g (ProjectiveLine S ↘ S) q).obj F) ≃+
        Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((ProjectiveSpace.map _ σ)^*[ModuleCat.{u + 1} Λ].obj F)) q)
      (e₂ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeTargetFunctor Λ g' f' q).obj F) ≃+
        Sheaf.H ((ProjectiveSpace.map _ ι)^*[AddCommGrpCat.{u + 1}].obj
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((ProjectiveSpace.map _ σ)^*[ModuleCat.{u + 1} Λ].obj F))) q),
      ∀ x, e₂ ((((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).map
          (Etale.baseChangeHomologyMap Λ sq q F)).hom x) =
        Etale.cohomologyMap (ProjectiveSpace.map _ ι)
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((ProjectiveSpace.map _ σ)^*[ModuleCat.{u + 1} Λ].obj F)) q (e₁ x) :=
  sorry

/-- Target 2: verbatim upstream signature at `ffb7b9060`.
(blueprint: `prop-weil-pbc-algebraically-closed-extension`) -/
theorem AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isAlgClosed {k k' : Type u}
    [Field k] [IsAlgClosed k]
    [Field k'] [IsAlgClosed k'] {C C' : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    [IsProper f] {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f ι) (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionModuleSheaf F] (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) :=
  sorry

/-- Target 3: verbatim upstream signature at `ffb7b9060`.
(blueprint: `lemma-weil-pbc-curve-separably-closed-passage`) -/
theorem AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isSepClosed_of_isAlgClosed
    (H : ∀ {k k' : Type u} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
      {C C' : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] [IsProper f]
      {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
      (_ : IsPullback ι' f' f ι) (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      [Scheme.IsTorsionModuleSheaf F] (q : ℕ),
      Function.Bijective (Etale.cohomologyMap ι'
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q))
    {k k' : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k'] {C C' : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve f] [IsProper f] {ι : Spec (.of k') ⟶ Spec (.of k)}
    {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C} (h : IsPullback ι' f' f ι)
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsTorsionModuleSheaf F] (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) :=
  sorry

/-- Comparator-only verbatim upstream definition needed by a target signature. -/
noncomputable abbrev AlgebraicGeometry.Etale.shiftedHomFunctor {Z : Scheme.{u}}
    (A : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ AddCommGrpCat.{u + 1} :=
  DerivedCategory.Plus.singleFunctor _ 0 ⋙ shiftFunctor _ q ⋙
    preadditiveCoyoneda.obj (op ((DerivedCategory.Plus.singleFunctor _ 0).obj A))

/-- Comparator-only verbatim upstream definition needed by a target signature. -/
noncomputable abbrev AlgebraicGeometry.Etale.finalObject (Z : Scheme.{u}) : Z.Etale :=
  MorphismProperty.Over.mk ⊤ (𝟙 Z) (inferInstance : Etale (𝟙 Z))

/-- Comparator-only verbatim upstream definition needed by a target signature. -/
noncomputable def AlgebraicGeometry.Etale.unitComparison {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) (h₁₂ : T ⟶ R)
    (hh₁₂ : h₁₂ = h₁ ≫ h₂) (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (h₂)_*[AddCommGrpCat.{u + 1}].obj ((h₂)^*[AddCommGrpCat.{u + 1}].obj G) ⟶
      (h₁₂)_*[AddCommGrpCat.{u + 1}].obj ((h₁₂)^*[AddCommGrpCat.{u + 1}].obj G) :=
  (h₂)_*[AddCommGrpCat.{u + 1}].map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h₁).unit.app
        ((h₂)^*[AddCommGrpCat.{u + 1}].obj G)) ≫
    (lowerStarComp AddCommGrpCat.{u + 1} h₁ h₂ h₁₂ hh₁₂).hom.app _ ≫
      (h₁₂)_*[AddCommGrpCat.{u + 1}].map
        ((upperStarComp AddCommGrpCat.{u + 1} h₁ h₂ h₁₂ hh₁₂).inv.app G)

/-- Target 4: verbatim upstream signature at `2104a988e` (upstream changed `J : Type u` to `J : Type (u + 1)` after `ffb7b9060`; we follow upstream, the human 2026-10-15).
(blueprint: `lem-weil-pbc-cohomology-filtered-colimit`) -/
theorem AlgebraicGeometry.Etale.preservesColimitsOfShape_shiftedHomFunctor_freeSheaf_finalObject (Z : Scheme.{u})
    [CompactSpace Z] [QuasiSeparatedSpace Z] (q : ℤ) (J : Type (u + 1)) [SmallCategory J]
    [IsFiltered J] :
    PreservesColimitsOfShape J
      (Etale.shiftedHomFunctor Λ ((Etale.freeSheaf Λ Z).obj (Etale.finalObject Z)) q) :=
  sorry

/-- Target 5: verbatim upstream signature at `ffb7b9060`.
(blueprint: `lem-weil-pbc-etale-section-continuity`) -/
theorem AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit
    {R : Scheme.{u}} {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (π : D ⟶ (Functor.const J).obj R)
    (c : Cone D) (P : c.pt ⟶ R) (hP : ∀ j, P = c.π.app j ≫ π.app j)
    [∀ j, CompactSpace (D.obj j)]
    [∀ j, QuasiSeparatedSpace (D.obj j)] [∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)]
    [QuasiSeparatedSpace R] (hc : IsLimit c)
    (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) (W : R.Etale)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] :
    (∀ t : ((P)_*[AddCommGrpCat.{u + 1}].obj
        ((P)^*[AddCommGrpCat.{u + 1}].obj G)).obj.obj (op W),
      ∃ (j : J) (s : ((π.app j)_*[AddCommGrpCat.{u + 1}].obj
        ((π.app j)^*[AddCommGrpCat.{u + 1}].obj G)).obj.obj (op W)),
        (unitComparison (c.π.app j) (π.app j) P (hP j) G).hom.app (op W) s = t) ∧
    ∀ (j : J) (s : ((π.app j)_*[AddCommGrpCat.{u + 1}].obj
        ((π.app j)^*[AddCommGrpCat.{u + 1}].obj G)).obj.obj (op W)),
      (unitComparison (c.π.app j) (π.app j) P (hP j) G).hom.app (op W) s = 0 →
        ∃ (j' : J) (f : j' ⟶ j), (unitComparison (D.map f) (π.app j) (π.app j')
          (by simp) G).hom.app (op W) s = 0 :=
  sorry

/-- Target 6: verbatim upstream signature at `ffb7b9060`.
(blueprint: `thm-weil-pbc-henselian-idempotent-lifting`) -/
theorem AlgebraicGeometry.Scheme.bijective_appTop_idempotent_of_henselianRing
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    {Y Y₀ : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f] (i : Y₀ ⟶ Y)
    (f₀ : Y₀ ⟶ Spec (.of (A ⧸ I)))
    (h : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) :
    Function.Bijective (fun e : {e : Γ(Y, ⊤) // IsIdempotentElem e} ↦
      (⟨i.appTop.hom e.1, e.2.map i.appTop.hom⟩ : {e : Γ(Y₀, ⊤) // IsIdempotentElem e})) :=
  sorry
