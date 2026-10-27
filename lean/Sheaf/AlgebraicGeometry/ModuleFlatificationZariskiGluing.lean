/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.AlgebraicGeometry.ModuleStrictTransform
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.FiniteTypeIdealModule
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.Blowup.FlatBaseChange
public import WeilConjectures.Blowup.Gluing
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.Compactification.FiniteTypeExtension

/-!
# Finite Zariski gluing of module flatifications

Source: Stacks Project, More on Flatness, Tags 0814 and 080Y, final paragraph;
Divisors, Tags 080M, 080N, 080A and 080I
(blueprint: lem-trf-module-flatification-zariski-gluing).

## Main definitions

* `zariskiGluingOtherCentres`: the product with one factor omitted.
* `zariskiGluingFirstBlowupMap`: restriction of an extended centre's blowup.
* `zariskiGluingModuleMap`: the map from the local twice-base-changed family.
* `zariskiGluingModuleSourceIso`: comparison of the ordinary pullback sources.
* `ModuleFlatificationZariskiComparison`: the local quotient normalization and flatness.

## Main statements

* `module_flatification_zariski_gluing`: existence of extensions, their product
  factorization, quotient-compatible local comparisons, and global flatness.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The product of all centres other than `a`, with empty product the unit ideal.
Source: Stacks, Divisors, Tags 080N and 080A
(blueprint: lem-trf-module-flatification-zariski-gluing). -/
noncomputable def zariskiGluingOtherCentres {S : Scheme.{u}} {A : Type v} [Fintype A]
    (L : A → S.IdealSheafData) (a : A) : S.IdealSheafData := by
  classical
  exact ∏ b ∈ Finset.univ.erase a, L b

/-- The canonical restriction comparison, using equality of the restricted ideal
and the given centre, followed by the existing flat blowup base-change map.
Source: Stacks, Divisors, Tag 0805
(blueprint: lem-trf-module-flatification-zariski-gluing). -/
noncomputable def zariskiGluingFirstBlowupMap {S : Scheme.{u}} (W : S.Opens)
    (L : S.IdealSheafData) (J : W.toScheme.IdealSheafData) (h : L.comap W.ι = J) :
    J.blowup ⟶ Limits.pullback L.blowupMap W.ι :=
  eqToHom (congrArg (fun I ↦ I.blowup) h.symm) ≫ L.blowupFlatBaseChange W.ι

/-- The map of families induced by a local two-step blowup identification over `W`.
It is fixed by its projections to `X` and the global blown-up base.
Source: Stacks, Divisors, Tags 0805 and 080I
(blueprint: lem-trf-module-flatification-zariski-gluing). -/
noncomputable def zariskiGluingModuleMap {X S : Scheme.{u}} (f : X ⟶ S)
    (P : S.IdealSheafData) (W : S.Opens) (J : W.toScheme.IdealSheafData)
    (K : J.blowup.IdealSheafData)
    (e : K.blowup ≅ Limits.pullback P.blowupMap W.ι)
    (he : e.hom ≫ pullback.snd P.blowupMap W.ι = K.blowupMap ≫ J.blowupMap) :
    Limits.pullback (pullback.snd (f ∣_ W) J.blowupMap) K.blowupMap ⟶
      Limits.pullback f P.blowupMap :=
  pullback.lift
    (pullback.fst (pullback.snd (f ∣_ W) J.blowupMap) K.blowupMap ≫
      pullback.fst (f ∣_ W) J.blowupMap ≫ (f ⁻¹ᵁ W).ι)
    (pullback.snd (pullback.snd (f ∣_ W) J.blowupMap) K.blowupMap ≫
      e.hom ≫ pullback.fst P.blowupMap W.ι)
    (by
      have h₁ := pullback.condition (f := f ∣_ W) (g := J.blowupMap)
      have h₂ := pullback.condition
        (f := pullback.snd (f ∣_ W) J.blowupMap) (g := K.blowupMap)
      have h₃ := pullback.condition (f := P.blowupMap) (g := W.ι)
      have h₄ := morphismRestrict_ι f W
      simp only [Category.assoc]
      rw [← h₄, reassoc_of% h₁, reassoc_of% h₂, h₃, reassoc_of% he])

/-- The normalized comparison of the ordinary pullback sources for the two quotients.
It uses only tensor pullback composition, and the first projection of the preceding map.
Source: Stacks, Divisors, Tag 080I; Sheaves, Tag 0097
(blueprint: lem-trf-module-flatification-zariski-gluing). -/
noncomputable def zariskiGluingModuleSourceIso {X S : Scheme.{u}} (f : X ⟶ S)
    (P : S.IdealSheafData) (W : S.Opens) (J : W.toScheme.IdealSheafData)
    (K : J.blowup.IdealSheafData)
    (e : K.blowup ≅ Limits.pullback P.blowupMap W.ι)
    (he : e.hom ≫ pullback.snd P.blowupMap W.ι = K.blowupMap ≫ J.blowupMap)
    (F : X.Modules) :
    (tensorPullback (zariskiGluingModuleMap f P W J K e he)).obj
        ((tensorPullback (pullback.fst f P.blowupMap)).obj F) ≅
      (tensorPullback (pullback.fst (pullback.snd (f ∣_ W) J.blowupMap) K.blowupMap)).obj
        ((tensorPullback (pullback.fst (f ∣_ W) J.blowupMap)).obj
          ((tensorPullback (f ⁻¹ᵁ W).ι).obj F)) :=
  (tensorPullbackSectionComp (zariskiGluingModuleMap f P W J K e he)
    (pullback.fst f P.blowupMap)).symm.app F ≪≫
  eqToIso (congrArg (fun k ↦ (tensorPullback k).obj F) (pullback.lift_fst _ _ _)) ≪≫
  (tensorPullbackSectionComp
    (pullback.fst (pullback.snd (f ∣_ W) J.blowupMap) K.blowupMap)
    (pullback.fst (f ∣_ W) J.blowupMap ≫ (f ⁻¹ᵁ W).ι)).app F ≪≫
  (tensorPullback (pullback.fst (pullback.snd (f ∣_ W) J.blowupMap) K.blowupMap)).mapIso
    ((tensorPullbackSectionComp (pullback.fst (f ∣_ W) J.blowupMap)
      (f ⁻¹ᵁ W).ι).app F)



/-- The local quotient-compatible comparison for specified first and second centres.
The two cokernels below are exactly the existing `moduleStrictTransform` definition
unfolded. This exposes the successive quotient without assuming quasi-coherence of
an intermediate transform merely to elaborate its type. The quotient identity uniquely
normalizes the comparison; it is not an arbitrary isomorphism of module sheaves.
Source: Stacks, Divisors, Tags 080D and 080I; More on Flatness, Tag 080Y
(blueprint: lem-trf-module-flatification-zariski-gluing). -/
def ModuleFlatificationZariskiComparison {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) [F.IsQuasicoherent] (P : S.IdealSheafData)
    [P.toModules.IsFiniteType] (W : S.Opens) (J : W.toScheme.IdealSheafData)
    (K : J.blowup.IdealSheafData)
    (e : K.blowup ≅ Limits.pullback P.blowupMap W.ι)
    (he : e.hom ≫ pullback.snd P.blowupMap W.ι = K.blowupMap ≫ J.blowupMap) : Prop :=
  (∃! θ : (tensorPullback (zariskiGluingModuleMap f P W J K e he)).obj
      (moduleStrictTransform f P F) ≅
      cokernel (kernel.ι
        (moduleStrictTransformRestriction (pullback.snd (f ∣_ W) J.blowupMap) K
          (cokernel (kernel.ι
        (moduleStrictTransformRestriction (f ∣_ W) J ((tensorPullback (f ⁻¹ᵁ W).ι).obj F)))))),
    (tensorPullback (zariskiGluingModuleMap f P W J K e he)).map
        (cokernel.π (kernel.ι (moduleStrictTransformRestriction f P F))) ≫ θ.hom =
      (zariskiGluingModuleSourceIso f P W J K e he F).hom ≫
        (tensorPullback
          (pullback.fst (pullback.snd (f ∣_ W) J.blowupMap) K.blowupMap)).map
          (cokernel.π (kernel.ι
        (moduleStrictTransformRestriction (f ∣_ W) J ((tensorPullback (f ⁻¹ᵁ W).ι).obj F)))) ≫
        cokernel.π (kernel.ι
        (moduleStrictTransformRestriction (pullback.snd (f ∣_ W) J.blowupMap) K
          (cokernel (kernel.ι
        (moduleStrictTransformRestriction (f ∣_ W) J ((tensorPullback (f ⁻¹ᵁ W).ι).obj F))))))) ∧
  ((tensorPullback (zariskiGluingModuleMap f P W J K e he)).obj
    (moduleStrictTransform f P F)).IsFlatOver
      (pullback.snd (pullback.snd (f ∣_ W) J.blowupMap) K.blowupMap)

/-- Extend all local centres, then every product of such extensions gives an admissible
flatification, with its specified global and local two-step factorizations.
Source: Stacks, More on Flatness, Tags 0814 and 080Y, final paragraph;
Divisors, Tags 080M, 080N, 080A, 080I and 080F
(blueprint: lem-trf-module-flatification-zariski-gluing).

Proof: (1) Glue J_a with the unit ideal on U, using
lemma-nagata-glue-finite-type-ideals, then extend from U union V_a using
lemma-nagata-finite-type-ideal-extension-exists. Both restrictions are retained.
(2) Products of the finite affine generating lists generate the product ideal;
its restriction to U is the unit ideal, including the empty product.
(3) thm-nagata-blowup-product-ideal and def-nagata-blowup-product-comparison
identify the product blowup with the blowup of the extended product of the other
factors on Bl(L_a). That second centre is finite type and unit above U. Its
preserved open is quasi-compact by lem-weil-pbc-open-preimage-fibre-product and
lem-weil-pbc-qcqs-morphism-permanence.
(4) Apply lem-trf-factorized-centres-product-transform with T_a = V_a,
Y_a = f inverse V_a, I_a = L_a, and J'_a the unit ideal. The open inclusions are
flat, and V_a to S is quasi-compact by the qcqs permanence lemma. The restriction
of I_a is J_a by the extension equality.
(5) That lemma identifies the local product blowup with the displayed two-step
blowup, and identifies the global transform's restriction with the successive
module transform, commuting with the ordinary-pullback quotients. The first
transform is flat by hypothesis; the last clause of that lemma gives local flatness.
(6) The inverse images of V_a cover the new base. At every point the local
calculation gives flatness of the same module stalk over the same base local ring;
def-pc-scheme-module-flat-over gives global flatness. The empty cover forces S,
X and its base changes empty, so pointwise flatness is vacuous. -/
theorem module_flatification_zariski_gluing
    {X S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (U : S.Opens) (hU : IsCompact (U : Set S)) (f : X ⟶ S)
    (F : X.Modules) [F.IsQuasicoherent] {A : Type v} [Fintype A]
    (V : A → S.Opens) (hV : ∀ a : A, IsCompact (V a : Set S))
    (hcover : iSup V = ⊤) (J : ∀ a : A, (V a).toScheme.IdealSheafData)
    (hJ : ∀ a : A, (J a).ofFiniteType)
    (hJU : ∀ a : A, (J a).comap (((V a).ι ⁻¹ᵁ U).ι) = ⊤)
    (hflat : ∀ a : A,
      (cokernel (kernel.ι (moduleStrictTransformRestriction (f ∣_ V a) (J a)
        ((tensorPullback (f ⁻¹ᵁ V a).ι).obj F)))).IsFlatOver
          (pullback.snd (f ∣_ V a) (J a).blowupMap)) :
    (∃ L : A → S.IdealSheafData,
      ∀ a : A, (L a).ofFiniteType ∧ (L a).comap U.ι = ⊤ ∧
        (L a).comap (V a).ι = J a) ∧
    ∀ (L : A → S.IdealSheafData) (hL : ∀ a : A, (L a).ofFiniteType)
      (hLU : ∀ a : A, (L a).comap U.ι = ⊤)
      (hLV : ∀ a : A, (L a).comap (V a).ι = J a),
      ∃ B : IsAdmissible S U, B.I = ∏ a : A, L a ∧
        (@moduleStrictTransform X S f B.I
          (B.I.isFiniteType_toModules_sheaf B.finiteType) F inferInstance).IsFlatOver
            (pullback.snd f B.I.blowupMap) ∧
        ∀ a : A,
          ∃ e : B.I.blowup ≅
            ((zariskiGluingOtherCentres L a).comap (L a).blowupMap).blowup,
          e.hom ≫ ((zariskiGluingOtherCentres L a).comap (L a).blowupMap).blowupMap ≫
            (L a).blowupMap = B.I.blowupMap ∧
          ∃ C : IsAdmissible (L a).blowup ((L a).blowupMap ⁻¹ᵁ U),
          C.I = (zariskiGluingOtherCentres L a).comap (L a).blowupMap ∧
          IsCompact (((L a).blowupMap ⁻¹ᵁ U) : Set (L a).blowup) ∧
          ∃ eV : (((zariskiGluingOtherCentres L a).comap (V a).ι).comap
            (J a).blowupMap).blowup ≅ Limits.pullback B.I.blowupMap (V a).ι,
          ∃ heV : eV.hom ≫ pullback.snd B.I.blowupMap (V a).ι =
            (((zariskiGluingOtherCentres L a).comap (V a).ι).comap
              (J a).blowupMap).blowupMap ≫ (J a).blowupMap,
          eV.hom ≫ pullback.fst B.I.blowupMap (V a).ι ≫ e.hom ≫
              ((zariskiGluingOtherCentres L a).comap (L a).blowupMap).blowupMap =
            (((zariskiGluingOtherCentres L a).comap (V a).ι).comap
              (J a).blowupMap).blowupMap ≫
              zariskiGluingFirstBlowupMap (V a) (L a) (J a) (hLV a) ≫
                pullback.fst (L a).blowupMap (V a).ι ∧
          @ModuleFlatificationZariskiComparison X S f F inferInstance B.I
            (B.I.isFiniteType_toModules_sheaf B.finiteType) (V a) (J a)
            (((zariskiGluingOtherCentres L a).comap (V a).ι).comap (J a).blowupMap)
            eV heV := by
  sorry

end AlgebraicGeometry.Scheme.Modules
