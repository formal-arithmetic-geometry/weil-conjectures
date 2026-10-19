/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.AlgebraicGeometry.ProEtaleOpenUnitEvaluation
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.AlgebraicGeometry.FiniteCoefficientOpenKInjective
import Sheaf.AlgebraicGeometry.FiniteCoefficientOpenRestriction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-!
# Open direct image and its unit on K-injective pro-etale complexes

Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-localization, proof of
lem-exc-proetale-support-triangle; Stacks Project, Tags 03CE, 04IX, 08FI, 070I,
070K, 070Y, 08BJ and 09T5 (blueprint: lem-exc-proetale-open-derived-image).

The coefficients are the published sheafified continuous-function ring sheaves, including
noncommutative finite rings. The direct image is Mathlib's pushforward along their actual
coefficient map. Its unit is normalized by the published small-model Kan adjunction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The open direct image, with the action through the canonical coefficient map.
On V its underlying group is G(V times_T U); no commutativity is needed.
This only specializes Mathlib's pushforward to the recorded ring map.
Source: Stacks Project, Tags 03CE and 04IX
(blueprint: lem-exc-proetale-open-derived-image). -/
noncomputable abbrev finiteCoefficientOpenDirectImage {U T : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] (A : Type (u + 1))
    [Ring A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    FiniteCoefficientModules U A ⥤ FiniteCoefficientModules T A :=
  SheafOfModules.pushforward.{u + 1} (F := Scheme.proEtaleBaseChange j)
    (J := Scheme.ProEt.topology T) (K := Scheme.ProEt.topology U)
    (finiteCoefficientDirectImageMap j A)

/-- The specified Kan-adjunction unit on sections, before the coefficient action is
transported along c inverse. That transport changes no underlying section or map.
The model transports retain the underlying objects, so the result already has the
section type of the actual direct image of the published transported pullback.
Source: Stacks Project, Tags 00YV and 03D2
(blueprint: lem-exc-proetale-open-derived-image). -/
noncomputable def finiteCoefficientOpenUnitSection {U T : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] (A : Type (u + 1))
    [Ring A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (N : FiniteCoefficientModules T A) (V : T.ProEt) (m : N.val.obj (op V)) :
    ((finiteCoefficientOpenDirectImage j A).obj
      ((finiteCoefficientModulePullback j A).obj N)).val.obj (op V) :=
  (((SheafOfModules.pullbackPushforwardAdjunction.{u + 1}
    (finiteCoefficientModelRingUnit j A)).unit.app
      ((Scheme.proEtaleModuleToModel (finiteCoefficientRingSheaf T A)).obj N)).val.app
        (AsSmall.up.op.obj (op V))) m

private theorem isLeftKanExtension_of_full_whiskering
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (L : C ⥤ D) (G : D ⥤ E)
    [((Functor.whiskeringLeft C D E).obj L).Full]
    [((Functor.whiskeringLeft C D E).obj L).Faithful]
    {F : C ⥤ E} (e : F ≅ L ⋙ G) : G.IsLeftKanExtension e.hom := by
  let W := (Functor.whiskeringLeft C D E).obj L
  refine ⟨⟨IsInitial.ofUniqueHom
    (fun Y ↦ StructuredArrow.homMk (W.preimage (e.inv ≫ Y.hom)) ?_) ?_⟩⟩
  · change e.hom ≫ W.map (W.preimage (e.inv ≫ Y.hom)) = Y.hom
    rw [W.map_preimage]
    simp
  · intro Y m
    apply StructuredArrow.hom_ext
    apply W.map_injective
    change W.map m.right = W.map (W.preimage (e.inv ≫ Y.hom))
    rw [W.map_preimage]
    have h := m.w
    change e.hom ≫ W.map m.right = Y.hom at h
    rw [← h]
    simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exists_openDerivedAdjunction.{u₁, u₂, v₁, v₂, w₁, w₂}
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G) :
    ∃ (R : DerivedCategory D ⥤ DerivedCategory C)
    (beta : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ R),
    R.IsRightDerivedFunctor beta (HomologicalComplex.quasiIso D (.up ℤ)) ∧
    ∃ d : F.mapDerivedCategory ⊣ R,
      (∀ (J : CochainComplex D ℤ) [J.IsKInjective], IsIso (beta.app J)) ∧
      ∀ I : CochainComplex C ℤ,
        d.unit.app (DerivedCategory.Q.obj I) ≫ R.map (F.mapDerivedCategoryFactors.hom.app I) =
          DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app I) ≫
            beta.app ((F.mapHomologicalComplex (.up ℤ)).obj I) := by
  let q := HomotopyCategory.quotient D (.up ℤ)
  let H := G.mapHomotopyCategory (.up ℤ) ⋙ (DerivedCategory.Qh (C := C))
  let e : q ⋙ H ≅ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (G.mapHomotopyCategoryFactors (.up ℤ)) DerivedCategory.Qh ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso C)
  let beta := e.inv ≫ Functor.whiskerLeft q G.rightDerivedFunctorUnit ≫
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (DerivedCategory.quotientCompQhIso D).hom G.rightDerivedFunctor
  have : H.IsLeftKanExtension e.inv :=
    isLeftKanExtension_of_full_whiskering q H e.symm
  have : G.rightDerivedFunctor.IsLeftKanExtension G.rightDerivedFunctorUnit :=
    Functor.IsRightDerivedFunctor.isLeftKanExtension _ _
      (HomotopyCategory.quasiIso D (.up ℤ))
  refine ⟨G.rightDerivedFunctor, beta, ?_, adj.mapDerivedCategoryRightDerivedAdjunction,
    ?_, ?_⟩
  · constructor
    exact (Functor.isLeftKanExtension_iff_postcompose e.inv
      DerivedCategory.Q (DerivedCategory.quotientCompQhIso D)
      G.rightDerivedFunctorUnit beta (by rfl)).mp inferInstance
  · intro J hJ
    dsimp only [beta, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.associator_inv_app, Functor.whiskerRight_app]
    infer_instance
  · intro I
    have h := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso C (.up ℤ)) F.mapDerivedCategoryFactorsh.hom
      G.rightDerivedFunctorUnit ((HomotopyCategory.quotient C (.up ℤ)).obj I)
    rw [F.mapDerivedCategoryFactorsh_hom_app,
      Adjunction.mapHomotopyCategory_unit_app_quotient] at h
    have hf (K : CochainComplex C ℤ) :
        DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).inv.app K) =
          𝟙 (DerivedCategory.Qh.obj ((HomotopyCategory.quotient D (.up ℤ)).obj
            ((F.mapHomologicalComplex (.up ℤ)).obj K))) := by
      change DerivedCategory.Qh.map (𝟙 _) = 𝟙 _
      exact DerivedCategory.Qh.map_id _
    have hg (K : CochainComplex D ℤ) :
        DerivedCategory.Qh.map ((G.mapHomotopyCategoryFactors (.up ℤ)).inv.app K) =
          𝟙 (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj
            ((G.mapHomologicalComplex (.up ℤ)).obj K))) := by
      change DerivedCategory.Qh.map (𝟙 _) = 𝟙 _
      exact DerivedCategory.Qh.map_id _
    rw [hf] at h
    erw [Category.comp_id] at h
    let eta := (adj.mapHomotopyCategory (.up ℤ)).derivedη
      (HomotopyCategory.quasiIso C (.up ℤ)) F.mapDerivedCategoryFactorsh.hom
      G.rightDerivedFunctorUnit
    change eta.app (DerivedCategory.Q.obj I) ≫ _ = _
    rw [← cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app I)]
    rw [← cancel_mono (G.rightDerivedFunctor.map
      ((DerivedCategory.quotientCompQhIso D).inv.app
        ((F.mapHomologicalComplex (.up ℤ)).obj I)))]
    have hn := eta.naturality ((DerivedCategory.quotientCompQhIso C).hom.app I)
    change (DerivedCategory.quotientCompQhIso C).hom.app I ≫
      eta.app (DerivedCategory.Q.obj I) = _ at hn
    rw [← Category.assoc, hn]
    simp only [Functor.comp_map, Category.assoc]
    dsimp only [beta, e, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_inv_app, Iso.trans_inv,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      Iso.symm_inv, Functor.associator_hom_app]
    rw [hg]
    simp only [Category.comp_id, Category.id_comp, Category.assoc,
      ← Functor.map_comp, Iso.hom_inv_id_app, Category.comp_id]
    rw [← DerivedCategory.quotientCompQhIso_hom_naturality_assoc]
    conv_rhs =>
      erw [Iso.hom_inv_id_app_assoc, Category.id_comp,
        CategoryTheory.Functor.map_id, Category.comp_id]
    exact h


/-- Restriction identifies the actual open module inverse image, its action and its
specified adjunction unit; it preserves K-injectives and computes the derived open unit.
The natural ring comparison is fixed on constant sections. The first unit equation fixes
`adj` to the small-model inverse-image adjunction, preventing a rescaled adjunction.
The second unit equation identifies it with restriction. The derived comparison `alpha`
is the termwise factorization through Q, and `beta` is the total right-derived comparison.
Its invertibility on the restricted K-injective is precisely the claimed representation.
The final equation says that, after these two comparisons, the derived unit is Q of the
ordinary complex unit, whose degreewise sections are the restrictions just specified.

Source: Weil blueprint, proof of lem-exc-proetale-support-triangle; Stacks Project,
Tags 03CE, 04IX, 08FI, 070I, 070K, 070Y, 08BJ and 09T5
(blueprint: lem-exc-proetale-open-derived-image).

Proof:
1. Identify the open site with the slice by lem-weil-proetale-weakly-etale-localization.
   The initial inverse-image indexing pair at W/U identifies inverse image with evaluation
   on W/T (lem-sfb-proetale-object-inverse-image-restriction, its ring-independent clause).
2. Restrict the continuous-function coefficient presheaf. It is the identical presheaf
   on U; lem-cbc-sieve-slice-sheafification carries its sheafification unit to the slice.
   Thus the ring comparison fixes constants and is the canonical coefficient comparison
   of prop-weil-pbc-proetale-constant-ring-map. Transported actions are those in
   prop-weil-pbc-proetale-constant-exact, without permuting any noncommuting factors.
3. The Hom transpose sends phi:N|U -> G to phi at V times_T U after restriction from V.
   Conversely evaluate a map N -> j_*G on W/U and identify W times_T U with W.
   Naturality proves these are inverse and linear. The original Kan adjunction unit is
   the coprojection indexed by (V,id); under the initial-pair comparison it is exactly
   restriction along the first projection. This gives both displayed unit normalizations.
4. Apply lem-pur-kinjective-restrict-localized to A_T. Transport over the site and ring
   identifications to obtain K-injectivity of the actual pullback. Exactness from
   prop-weil-pbc-proetale-constant-exact gives its termwise descent through Q.
5. The ring-sheaf Grothendieck theorem lem-weil-pbc-ring-sheaves-grothendieck and
   lem-sfb-grothendieck-k-injective give resolutions for every complex. Termwise j_* is
   additive and preserves the shift and cone matrices. Apply
   lem-weil-pbc-kinjective-total-derived to its homotopy functor followed by Q_T.
   Precomposing with the homotopy quotient gives the displayed right-derived comparison
   on complexes and its universal property. It is invertible on the restricted I.
6. Exact left adjoint j^* makes j_* preserve K-injectives by
   lem-weil-pbc-right-adjoint-preserves-kinjective. The sheaf Hom adjunction descends to
   chain maps and homotopies, since its component formulas commute with differentials
   and addition. Apply lem-weil-pbc-kinjective-hom-derived on both sides, then beta, to
   obtain the derived adjunction from the specified ordinary adjunction.
7. For J = j^*I, the identity transposes to the ordinary unit. Consequently its derived
   transpose is Q_T(eta_I) followed by beta_J. The factor alpha identifies Q_U(j^*I)
   with j^*(Q_TI). This is the final equation and gives exactly the asserted unit. -/
theorem finiteCoefficientOpenDerivedImage {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] (A : Type (u + 1))
    [Ring A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    ∃ d : (finiteCoefficientRingSheaf U A).obj ≅
        (Scheme.proEtaleOpenComposition j).op ⋙ (finiteCoefficientRingSheaf T A).obj,
      (∀ (W : U.ProEt) (a : A),
        (d.hom.app (op W)) ((finiteCoefficientScalarMap U A).app (op W) a) =
          (finiteCoefficientScalarMap T A).app
            (op ((Scheme.proEtaleOpenComposition j).obj W)) a) ∧
      ∃ rho : ∀ (N : FiniteCoefficientModules T A) (W : U.ProEt),
          ((finiteCoefficientModulePullback j A).obj N).val.obj (op W) ≃+
            N.val.obj (op ((Scheme.proEtaleOpenComposition j).obj W)),
        (∀ (N : FiniteCoefficientModules T A) (W : U.ProEt)
          (r : (finiteCoefficientRingSheaf U A).obj.obj (op W))
          (m : ((finiteCoefficientModulePullback j A).obj N).val.obj (op W)),
          rho N W (r • m) = (d.hom.app (op W) r) • rho N W m) ∧
        (∀ (N : FiniteCoefficientModules T A) (W W' : U.ProEt) (b : W' ⟶ W)
          (m : ((finiteCoefficientModulePullback j A).obj N).val.obj (op W)),
          rho N W' (((finiteCoefficientModulePullback j A).obj N).val.map b.op m) =
            N.val.map ((Scheme.proEtaleOpenComposition j).map b).op (rho N W m)) ∧
        (∀ (N N' : FiniteCoefficientModules T A) (h : N ⟶ N') (W : U.ProEt)
          (m : ((finiteCoefficientModulePullback j A).obj N).val.obj (op W)),
          rho N' W (((finiteCoefficientModulePullback j A).map h).val.app (op W) m) =
            h.val.app (op ((Scheme.proEtaleOpenComposition j).obj W)) (rho N W m)) ∧
        ∃ (_ : (finiteCoefficientOpenDirectImage j A).Additive)
          (adj : finiteCoefficientModulePullback j A ⊣ finiteCoefficientOpenDirectImage j A),
          (∀ (N : FiniteCoefficientModules T A) (V : T.ProEt) (m : N.val.obj (op V)),
            (adj.unit.app N).val.app (op V) m = finiteCoefficientOpenUnitSection j A N V m) ∧
          (∀ (N : FiniteCoefficientModules T A) (V : T.ProEt) (m : N.val.obj (op V)),
            rho N ((Scheme.proEtaleBaseChange j).obj V)
                ((adj.unit.app N).val.app (op V) m) =
              N.val.map (Scheme.proEtaleOpenSectionProjection j V).op m) ∧
          ∃ (L : FiniteCoefficientDerivedCategory T A ⥤ FiniteCoefficientDerivedCategory U A)
            (alpha : DerivedCategory.Q ⋙ L ≅
              (finiteCoefficientModulePullback j A).mapHomologicalComplex (.up ℤ) ⋙
                DerivedCategory.Q)
            (R : FiniteCoefficientDerivedCategory U A ⥤ FiniteCoefficientDerivedCategory T A)
            (beta : (finiteCoefficientOpenDirectImage j A).mapHomologicalComplex (.up ℤ) ⋙
                DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R),
            R.IsRightDerivedFunctor beta
                (HomologicalComplex.quasiIso (FiniteCoefficientModules U A) (.up ℤ)) ∧
            ∃ derivedAdj : L ⊣ R,
              ∀ (I : CochainComplex (FiniteCoefficientModules T A) ℤ) [I.IsKInjective],
                CochainComplex.IsKInjective
                    (((finiteCoefficientModulePullback j A).mapHomologicalComplex (.up ℤ)).obj
                      I) ∧
                IsIso (beta.app
                  (((finiteCoefficientModulePullback j A).mapHomologicalComplex (.up ℤ)).obj
                    I)) ∧
                derivedAdj.unit.app (DerivedCategory.Q.obj I) ≫ R.map (alpha.hom.app I) =
                  DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app I) ≫
                    beta.app
                      (((finiteCoefficientModulePullback j A).mapHomologicalComplex (.up ℤ)).obj
                        I) := by
  obtain ⟨d, hd, rho, hlinear, hsite, hmodule, hadd, adj, hunit, hrestriction⟩ :=
    finiteCoefficientOpenRestriction j A
  let : (finiteCoefficientOpenDirectImage j A).Additive := hadd
  let : PreservesFiniteLimits (finiteCoefficientModulePullback j A) :=
    (finiteCoefficientModulePullback_exact j A).1
  let : PreservesFiniteColimits (finiteCoefficientModulePullback j A) :=
    (finiteCoefficientModulePullback_exact j A).2.1
  let : IsGrothendieckAbelian.{u + 1} (FiniteCoefficientModules U A) :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
      (Scheme.ProEt.topology U) (finiteCoefficientRingSheaf U A)
  obtain ⟨R, beta, hR, derivedAdj, hbeta, hderived⟩ :=
    exists_openDerivedAdjunction (finiteCoefficientModulePullback j A)
      (finiteCoefficientOpenDirectImage j A) adj
  refine ⟨d, hd, rho, hlinear, hsite, hmodule, hadd, adj, hunit, hrestriction,
    (finiteCoefficientModulePullback j A).mapDerivedCategory,
    (finiteCoefficientModulePullback j A).mapDerivedCategoryFactors,
    R, beta, hR, derivedAdj, ?_⟩
  intro I hI
  have hKI := finiteCoefficientOpenPullback_isKInjective j A I
  let := hKI
  exact ⟨hKI, hbeta _, hderived I⟩

end AlgebraicGeometry.ProEtale
