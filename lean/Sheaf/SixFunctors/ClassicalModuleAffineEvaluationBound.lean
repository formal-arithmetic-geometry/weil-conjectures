/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q72
-/
module

public import Sheaf.SixFunctors.ClassicalDefinition
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Sheaf.CategoryTheory.ConstantRingModuleSheaves
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
import Sheaf.AlgebraicGeometry.EtaleModuleAffineBound
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules

/-!
# Uniform affine evaluation bound for classical pro-etale module sheaves

Source: current Weil conjectures blueprint, Fixed-degree truncation paragraph of
`sk-prop-pe-unbounded-classical-unit.proof.md`; Stacks Project, Tags 099W and 03F3
(blueprint: lem-sfb-classical-module-affine-evaluation-bound).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Evaluation at a pro-etale object as an ordinary module over the coefficient ring.
The scalar map is the sheafification unit on the constant ring presheaf, composed with
inverse universe lift. Thus its value on `a` is precisely the constant section `a`.
Source: the definition of E_W in the affine evaluation bound, and Stacks Tag 03F3
(blueprint: lem-sfb-classical-module-affine-evaluation-bound). -/
noncomputable abbrev proEtaleConstantModuleEvaluation
    (X : Scheme.{u}) (A : Type u) [CommRing A] (W : X.ProEt) :
    ringedSiteModules.{u + 1}
      ((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1, u} A))) ⥤ ModuleCat.{u + 1} A :=
  SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ (op W) ⋙
    ModuleCat.restrictScalars
      (((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} A)))).app
          (op W)).hom.comp ULift.ringEquiv.symm.toRingHom)

private theorem etale_fixed_isZero_of_ringed
    (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ)
    (h : ∀ J : InjectiveResolution ((Scheme.etaleConstantModuleFunctor X Λ).obj F),
      IsZero ((((SheafOfModules.evaluation (Scheme.etaleConstantModuleRing X Λ)
        (op (Scheme.Etale.mk (𝟙 X)))).mapHomologicalComplex (.up ℕ)).obj
          J.cocomplex).homology n)) :
    IsZero (((Etale.sectionsFunctor (ModuleCat.{u + 1} Λ) X).rightDerived n).obj F) := by
  let E := Scheme.etaleConstantModuleFunctor X Λ
  have : E.IsEquivalence := Scheme.etaleConstantModuleFunctor_isEquivalence X Λ
  have : E.Additive := Functor.additive_of_preserves_binary_products E
  let I := injectiveResolution F
  let J : InjectiveResolution (E.obj F) :=
    { cocomplex := (E.mapHomologicalComplex _).obj I.cocomplex
      ι := E.mapResolution I.ι
      injective := fun n ↦ by
        change Injective (E.obj (I.cocomplex.X n))
        infer_instance }
  let V := Etale.sectionsFunctor (ModuleCat.{u + 1} Λ) X
  let K := (V.mapHomologicalComplex _).obj I.cocomplex
  let R := SheafOfModules.evaluation (Scheme.etaleConstantModuleRing X Λ)
    (op (Scheme.Etale.mk (𝟙 X)))
  let L := (R.mapHomologicalComplex _).obj J.cocomplex
  let U := forget₂ (ModuleCat.{u + 1}
    ((Scheme.etaleConstantModuleRing X Λ).obj.obj (op (Scheme.Etale.mk (𝟙 X)))))
      AddCommGrpCat.{u + 1}
  let U' := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  have hz : IsZero (((U.mapHomologicalComplex _).obj L).homology n) :=
    (U.map_isZero (h J)).of_iso ((L.sc n).mapHomologyIso U)
  have hz' : IsZero (((U'.mapHomologicalComplex _).obj K).homology n) := hz
  have hz'' : IsZero (U'.obj (K.homology n)) :=
    hz'.of_iso ((K.sc n).mapHomologyIso U').symm
  have : Subsingleton (K.homology n) := AddCommGrpCat.subsingleton_of_isZero hz''
  exact (ModuleCat.isZero_iff_subsingleton.mpr this).of_iso (I.isoRightDerivedObj V n)

private theorem evaluation_isZero_of_fixed
    (X : Scheme.{u}) (A : Type u) [CommRing A] (W : X.ProEt)
    (H : ringedSiteModules.{u + 1}
      ((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1, u} A))))
    (I : InjectiveResolution H) (n : ℕ)
    (h : IsZero (((sectionsFunctor (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) W).rightDerived n).obj
      ((constantRingModuleRestriction (Scheme.ProEt.topology X) (ULift.{u + 1, u} A)).obj H))) :
    IsZero ((((proEtaleConstantModuleEvaluation X A W).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex).homology n) := by
  let Λ := ULift.{u + 1, u} A
  let E := constantRingModuleRestriction (Scheme.ProEt.topology X) Λ
  obtain ⟨⟨e, he, ha, _, _⟩, _, _⟩ := constant_ring_module_sheaves
    (Scheme.ProEt.topology X) Λ
  have : E.IsEquivalence := by
    dsimp only [E]
    rw [← he]
    infer_instance
  have : E.Additive := by
    dsimp only [E]
    rw [← he]
    exact ha
  let J : InjectiveResolution (E.obj H) :=
    { cocomplex := (E.mapHomologicalComplex _).obj I.cocomplex
      ι := E.mapResolution I.ι
      injective := fun n ↦ by
        change Injective (E.obj (I.cocomplex.X n))
        infer_instance }
  let V := sectionsFunctor (ModuleCat.{u + 1} Λ) W
  have hz : IsZero (((V.mapHomologicalComplex _).obj J.cocomplex).homology n) :=
    h.of_iso (J.isoRightDerivedObj V n).symm
  let R : ModuleCat.{u + 1} Λ ⥤ ModuleCat.{u + 1} A :=
    ModuleCat.restrictScalars (ULift.ringEquiv.symm.toRingHom : A →+* Λ)
  have : PreservesFiniteLimits R := ⟨fun _ _ _ ↦
    ⟨ModuleCat.preservesLimit_restrictScalars _ _⟩⟩
  have : PreservesFiniteColimits R := ⟨fun _ _ _ ↦
    ⟨ModuleCat.preservesColimit_restrictScalars _ _⟩⟩
  have hz' := R.map_isZero hz
  let K := (V.mapHomologicalComplex _).obj J.cocomplex
  have hz'' : IsZero (((R.mapHomologicalComplex _).obj K).homology n) :=
    hz'.of_iso ((K.sc n).mapHomologyIso R)
  exact hz''

/-- Every classical module sheaf has vanishing evaluation cohomology above `2 dim X + 1`,
uniformly over affine etale objects. Dimension of the empty scheme is assigned zero.
The conclusion is stated for every injective module resolution and takes cohomology
only after applying the A-linear evaluation functor. Since q is greater than the
nonnegative bound, q.toNat represents exactly that integer degree.

Source: current blueprint, Fixed-degree truncation paragraph of
`sk-prop-pe-unbounded-classical-unit.proof.md`; Stacks Tags 099W and 03F3
(blueprint: lem-sfb-classical-module-affine-evaluation-bound).

Proof:
1. Restrict the constant-ring action to obtain a fixed-ULift-A module sheaf F.
Its underlying set sheaf is unchanged, hence classical. Descend F by
det-pe-classical-sheaves-modules and extend the descended module action through the
etale constant-ring equivalence, obtaining G with comparison pullback isomorphic to F.
2. Apply lem-sfb-etale-module-affine-bound to G with the lifted annihilation equation.
Transport a fixed-module injective resolution through the etale constant-ring
equivalence. Forgetting scalars commutes with homology and reflects zero modules,
so etale_fixed_isZero_of_ringed gives vanishing of fixed-module derived sections.
3. The upstream degree-zero-input specialization of sk-prop-sf-comparison transfers
this vanishing to W_proet. The comparison pullback coherence isomorphism identifies
its coefficients with the inverse image of F. Only bounded-below comparison is used.
4. The upstream localization lemma, using exact injective-preserving restriction,
gives vanishing of ambient derived evaluation at W. Transport the given resolution
I through the constant-ring restriction equivalence, then restrict scalars along
inverse ULift. Both operations preserve the relevant homology; the final evaluated
complex is definitionally the one in the conclusion. This is
evaluation_isZero_of_fixed. The same bound works for every W and every classical H. -/
theorem classical_module_affine_evaluation_bound
    (k : Type u) [Field k] (_hk : Finite k ∨ IsAlgClosed k)
    (ℓ : ℕ) (_hℓ : ℓ.Prime) (_hℓk : IsUnit (ℓ : k))
    (A : Type u) [CommRing A] [Finite A]
    (a : ℕ) (_ha : 1 ≤ a) (_hA : (ℓ : A) ^ a = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (W : X.Etale) [IsAffine W.left]
    (H : ringedSiteModules.{u + 1}
      ((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1, u} A))))
    (_hH : IsClassicalModuleSheaf H) (I : InjectiveResolution H)
    (q : ℤ)
    (_hq : (2 * ((topologicalKrullDim X).unbotD 0).toNat + 1 : ℕ) < q) :
    IsZero ((((proEtaleConstantModuleEvaluation X A (Scheme.ProEt.mk W.hom)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex).homology q.toNat) := by
  let Λ := ULift.{u + 1, u} A
  let F := (constantRingModuleRestriction (Scheme.ProEt.topology X) Λ).obj H
  have hF : IsClassical ((sheafCompose (Scheme.ProEt.topology X)
      (forget (ModuleCat.{u + 1} Λ))).obj F) := _hH
  obtain ⟨adj, _, _, _, _, hc⟩ := proEtaleClassicalSheavesModules X Λ
  obtain ⟨G₀, ⟨e₀⟩⟩ := (hc F).mp hF
  let G := (Scheme.etaleConstantModuleFunctor X Λ).obj G₀
  have e : (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj
      ((Scheme.etaleConstantModuleRestrictionFunctor X Λ).obj G) ≅ F :=
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapIso
      ((Scheme.etaleConstantModuleUnitIso X Λ).app G₀).symm ≪≫ e₀
  have hA : (ℓ : Λ) ^ a = 0 := by
    apply ULift.ext
    exact _hA
  have het : IsZero (((Etale.sectionsFunctor (ModuleCat.{u + 1} Λ) W.left).rightDerived
      q.toNat).obj ((Etale.upperStar (ModuleCat.{u + 1} Λ) W.hom).obj
        ((Scheme.etaleConstantModuleRestrictionFunctor X Λ).obj G))) := by
    apply etale_fixed_isZero_of_ringed
    intro J
    exact etaleModule_affine_cohomology_isZero _hk ℓ _hℓ _hℓk Λ a _ha hA
      X W G q _hq J
  have hpro := isZero_rightDerived_globalSectionsFunctor_comparisonUpperStar_obj
    (ModuleCat.{u + 1} Λ) W.left _ q.toNat het
  have hglobal : IsZero (((globalSectionsFunctor (ModuleCat.{u + 1} Λ)
      W.left).rightDerived q.toNat).obj
        ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) W.hom).obj F)) := by
    apply hpro.of_iso
    exact ((globalSectionsFunctor (ModuleCat.{u + 1} Λ) W.left).rightDerived
      q.toNat).mapIso
        ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) W.hom).mapIso e.symm ≪≫
          (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) W.hom).app _)
  have hsections := isZero_rightDerived_sectionsFunctor_of_upperStar
    (ModuleCat.{u + 1} Λ) (Scheme.ProEt.mk W.hom) F q.toNat hglobal
  exact evaluation_isZero_of_fixed X A (Scheme.ProEt.mk W.hom) H I q.toNat hsections

end AlgebraicGeometry.ProEtale
