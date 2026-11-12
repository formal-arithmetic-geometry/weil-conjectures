/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModel
public import WeilConjectures.SixFunctors.Etale.Derived.DoubleDual
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IhomCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.UpperShriekCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.UpperShriekCompatibilityProper

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Obj
attribute [local instance] DerivedCategory.braidedCategory'
attribute [local irreducible] DerivedCategory.monoidalClosed

/-- Forgetting membership in a full monoidal closed subcategory preserves biduality. -/
lemma CategoryTheory.ObjectProperty.toIhomIhom_hom
    {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
    {P : ObjectProperty C} [P.IsMonoidal] [P.IsMonoidalClosed]
    (W L : P.FullSubcategory) :
    (toIhomIhom W L).hom = toIhomIhom W.obj L.obj := rfl

/-- A composite of restrictions of braided functors is braided. -/
lemma CategoryTheory.ObjectProperty.braided_lift_comp
    {C D E : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]
    [Category* D] [MonoidalCategory D] [BraidedCategory D]
    [Category* E] [MonoidalCategory E] [BraidedCategory E]
    (P : ObjectProperty C) [P.IsMonoidal] (Q : ObjectProperty D) [Q.IsMonoidal]
    (R : ObjectProperty E) [R.IsMonoidal]
    (F : C ⥤ D) [F.Braided] (G : D ⥤ E) [G.Braided]
    (hF : ∀ K : P.FullSubcategory, Q (F.obj K.obj))
    (hG : ∀ K : Q.FullSubcategory, R (G.obj K.obj)) (K M : P.FullSubcategory) :
    let T := Q.lift (P.ι ⋙ F) hF ⋙ R.lift (Q.ι ⋙ G) hG
    Functor.LaxMonoidal.μ T K M ≫ T.map (β_ K M).hom =
      (β_ (T.obj K) (T.obj M)).hom ≫ Functor.LaxMonoidal.μ T M K := by
  apply ObjectProperty.hom_ext
  exact Functor.LaxBraided.braided (F := F ⋙ G) K.obj M.obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] in
private lemma integral_qbar_biduality_map_hom
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {K M : BoundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left)} (f : K ⟶ M) :
    ((boundedConstructibleExtendScalars X.left ℓ E ⋙
      constructibleToPadicAlgCl X.left ℓ E).map f).hom =
      ((Mod.extendScalars (padicIntegersToPadicSubfield X.left ℓ E)).leftDerivedFunctor ⋙
        derivedExtendScalarsToPadicAlgCl X.left ℓ E).map f.hom := rfl

/-- The actual scalar-extension double-dual comparison, including its evaluation equation.

Source: Bhatt--Scholze, Lemmas 6.7.13 and 6.7.18, Proposition 6.8.14 and Remark
6.8.15; latest blueprint `det-prop-sf-biduality-general.proof.md`.
Proof in words: compose integral rationalization with extension from E to the
finite-subextension-valued condensed Qbar coefficient.  Exceptional coefficient
change identifies the scalar extension of the integral dualizing object with the
chosen bounded exceptional pullback of the Qbar unit, by uniqueness of right
adjoints and its counit.  The two internal-Hom coefficient comparisons give the
displayed isomorphism of double duals.  Uncurry each comparison: it is scalar
extension of evaluation, with the scalar tensorator.  Naturality and symmetry
therefore give the stated equation for the canonical evaluation transpose.  These
comparisons can be checked after algebraic closure and descended conservatively;
no claim of invertibility of either biduality arrow is part of this statement.
(blueprint: lem-pd-constructible-sheaf-biduality-scalar-comparison) -/
theorem integral_qbar_biduality_comparison
    [IsIso S.hom] (a : X ⟶ S)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (L : BoundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left)) :
    let F := (Mod.extendScalars (padicIntegersToPadicSubfield X.left ℓ E)).leftDerivedFunctor ⋙
      derivedExtendScalarsToPadicAlgCl X.left ℓ E
    let W := ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 a).obj (𝟙_ _)).obj
    let W' := ((boundedConstructibleUpperShriek ℓ a).obj (𝟙_ _)).obj
    ∃ c : F.obj ((ihom ((ihom L.obj).obj W)).obj W) ≅
        (ihom ((ihom (F.obj L.obj)).obj W')).obj W',
      toIhomIhom W' (F.obj L.obj) = F.map (toIhomIhom W L.obj) ≫ c.hom := by
  let := leftDerivedExtendScalarsPadicIntegersBraided ℓ E X.left
  let := leftDerivedExtendScalarsPadicAlgClBraided ℓ E X.left
  let := ObjectProperty.fullBraidedSubcategory
    (boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left))
  let := boundedConstructibleBraiding (ℓ := ℓ) X
  let T := boundedConstructibleExtendScalars X.left ℓ E ⋙
    constructibleToPadicAlgCl X.left ℓ E
  let W := (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 a).obj (𝟙_ _)
  let W' := (boundedConstructibleUpperShriek ℓ a).obj (𝟙_ _)
  -- Identify the dualizing objects using the exceptional-pullback comparisons.
  let w : T.obj W ≅ W' := by
    have := isIso_boundedConstructibleUpperShriekToPadicAlgCl ℓ E a
    exact (constructibleToPadicAlgCl X.left ℓ E).mapIso
        ((boundedConstructibleUpperShriekExtendScalarsIso ℓ E a).app (𝟙_ _) ≪≫
          (ContinuousMapRingObj.boundedConstructibleUpperShriek ℓ E a).mapIso
            (Functor.Monoidal.εIso (boundedConstructibleExtendScalars S.left ℓ E)).symm) ≪≫
      (asIso (boundedConstructibleUpperShriekToPadicAlgCl ℓ E a)).app (𝟙_ _) ≪≫
      (boundedConstructibleUpperShriek ℓ a).mapIso
        (Functor.Monoidal.εIso (constructibleToPadicAlgCl S.left ℓ E)).symm
  let : T.Braided := by
    constructor
    intro K M
    exact ObjectProperty.braided_lift_comp (boundedConstructible _) (boundedConstructible _)
      (boundedConstructible _)
      (Mod.extendScalars (padicIntegersToPadicSubfield X.left ℓ E)).leftDerivedFunctor
      (derivedExtendScalarsToPadicAlgCl X.left ℓ E)
      (boundedConstructible_derivedExtendScalars_obj X.left ℓ E)
      (boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj X.left ℓ E) K M
  -- Both dual comparisons are invertible on bounded constructible objects.
  have hβ (K : BoundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left)) :
      IsIso (dualComparison T w.hom K) := by
    have := isIso_ihomComparison_boundedConstructibleIntegersToPadicAlgCl ℓ E K
    unfold dualComparison
    infer_instance
  have := hβ L
  have := hβ ((ihom L).obj W)
  have := isIso_pre_app (dualComparison T w.hom L) W'
  let c := asIso (dualComparison T w.hom ((ihom L).obj W)) ≪≫
    (asIso ((pre (dualComparison T w.hom L)).app W')).symm
  -- The lax braided bidual square gives the compatibility before forgetting.
  refine ⟨(boundedConstructible _).ι.mapIso c, ?_⟩
  have h : toIhomIhom W' (T.obj L) = T.map (toIhomIhom W L) ≫ c.hom := by
    dsimp only [c, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
    rw [map_toIhomIhom_comp_dualComparison_assoc, IsIso.hom_inv_id, Category.comp_id]
  have h' := congrArg (fun f ↦ f.hom) h
  rw [ObjectProperty.toIhomIhom_hom, ObjectProperty.comp_hom,
    integral_qbar_biduality_map_hom, ObjectProperty.toIhomIhom_hom] at h'
  exact h'

end AlgebraicGeometry.ProEtale.CondensedRing
