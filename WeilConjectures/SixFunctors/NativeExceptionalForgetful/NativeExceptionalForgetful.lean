/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeExceptionalForgetfulData
import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeExceptionalLeftModels
import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeExceptionalPointUnit
import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeExceptionalStructuralTransport
import WeilConjectures.CategoryTheory.Adjunction.SixFunctors.ForgetfulRepresentingPairRightMate

/-! # Forgetting native exceptional inverse image

Source: current blueprint, cor-coef-verdier-weil-equivariance, exceptional adjunction
and equivariant units and counits (blueprint: lem-sf-weil-native-exceptional-forgetful).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures WeilConjectures.AdicQbarRealization
namespace WeilConjectures.NativeExceptionalForgetful
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]

/-- Forgetting the native derived Weil structure commutes with compact support
and with its exceptional right adjoint, identifies their actual units and counits,
and sends the native point constant to the scalar-normalized ordinary coefficient
unit. Its structural exceptional image is the ordinary dualizing complex.
Source: current blueprint, cor-coef-verdier-weil-equivariance, exceptional adjunction
and equivariant units and counits; native refinement in the DAG
(blueprint: lem-sf-weil-native-exceptional-forgetful).

Proof:
1. Apply lem-sf-native-weil-open-proper-forgetting to the chosen native
compactification. It identifies the coefficient hearts and supplies the
Frobenius-compatible derived comparison c0. By
lem-sf-native-weil-scalar-frobenius-counit the scalar-normalized realization
comparison alpha identifies ordinary common-stage compact support with the
ordered proper/open construction. Compose alpha inverse with c0 to obtain the
left comparison. That lemma also gives the ordinary adjunction and the
invertible Frobenius mate with invariant counit.
2. Apply lem-sf-cyclic-derived-lifted-counit-represents. The Grothendieck,
exact-action and invariant-counit hypotheses are supplied by the preceding
step. Compatibility of the Hom sequence with the native proper/open functor
is lem-sf-cyclic-derived-hom-exact-sequence. Its representing triples include
the degree -1 extension term, and all their objects remain bounded constructible.
3. Apply lem-sf-forgetful-representing-pair-right-mate to these triples and
the assumed native adjunction. Its natural mate is the right comparison;
its two identities identify the given units and counits. Thus the intermediate
representing triples do not affect the comparisons.
4. At Spec k0 the native constant is the regular coefficient module with its
canonical Frobenius, in degree zero. Forgetting therefore gives R_s[0]; the
unit normalization of lem-sf-adic-qbar-constructible-realization identifies
this with rho_s(Omega). Evaluate the same right comparison on the constant
and apply the ordinary exceptional functor to this unit identification.
This gives specialization and its displayed equality. Transport the target by
pointGeometricIso; the coefficient-unit normalization and uniqueness of the
ordinary exceptional adjoint identify its value with the structural exceptional
image at literal Spec k, giving actualSpecialization. Empty schemes give
zero objects and functors; identity maps give the identity mate equations.
Changing the algebraic closure uses closureMap, and its exact direct-image
transport changes neither these equations nor any derived extension morphism. -/
theorem native_exceptional_forgetful (R : Family l D) : Nonempty (Package D l R) := by
  classical
  obtain ⟨model, hleft⟩ := native_exceptional_left_models D l R
  have comparisons (X Y : Space D) (f₀ : X.base ⟶ Y.base)
      [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
      (S : CoefficientSystem D l f₀) (c : Compactification (geometricMap D f₀))
      (G : W D l Y ⥤ W D l X) (adj : nativeShriek D l f₀ ⊣ G) :
      Nonempty (Comparison D l R (model X) (model Y) f₀ S c G adj) := by
    obtain ⟨a, hlift⟩ := hleft X Y f₀ S c
    choose H e d hd hbij using hlift
    have hm := Adjunction.forgetful_representingPair_rightMate adj
      (S.ring.operation c .closed).adjunction a H e d hd hbij
    have := hm.1
    refine ⟨{ left := a
              right := asIso (Adjunction.forgetfulRightMate adj
                (S.ring.operation c .closed).adjunction a)
              unit := hm.2.2.2.2.1
              counit := ?_ }⟩
    intro L
    change (S.ring.operation c .closed).F.map
        ((Adjunction.forgetfulRightMate adj
          (S.ring.operation c .closed).adjunction a).app L) ≫
        (S.ring.operation c .closed).adjunction.counit.app ((model Y).functor.obj L) = _
    simpa only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] using
      congrArg (fun t ↦ a.inv.app (G.obj L) ≫ t) (hm.2.2.2.1 L)
  let comparison : ∀ (X Y : Space D) (f₀ : X.base ⟶ Y.base)
      [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
      (S : CoefficientSystem D l f₀) (c : Compactification (geometricMap D f₀))
      (G : W D l Y ⥤ W D l X) (adj : nativeShriek D l f₀ ⊣ G),
      Comparison D l R (model X) (model Y) f₀ S c G adj := by
    intro X Y f₀ _ _ _ S c G adj
    exact Classical.choice (comparisons X Y f₀ S c G adj)
  obtain ⟨n⟩ := native_exceptional_point_unit D l R
  let ff : (rho D l R (point D)).FullyFaithful := Classical.choice
    ((Functor.FullyFaithful.nonempty_iff_map_bijective _).mpr
      (R.data (geometric D (point D))).fully_faithful)
  let e := (model (point D)).realization.app (constant D l (point D)) ≪≫
    n ≪≫ unitRealization D l R (point D)
  let commonUnit := ff.preimageIso e
  let specialization : ∀ (X : Space D) (a₀ : X.base ⟶ (point D).base)
      [IsSeparated a₀.left] [LocallyOfFiniteType a₀.left] [QuasiCompact a₀.left]
      (S : CoefficientSystem D l a₀) (c : Compactification (geometricMap D a₀))
      (G : W D l (point D) ⥤ W D l X) (_adj : nativeShriek D l a₀ ⊣ G),
      (U D l R X).obj (G.obj (constant D l (point D))) ≅
        (rho D l R X).obj
          ((S.ring.operation c .closed).G.obj (omega D l R (point D))) := by
    intro X a₀ _ _ _ S c G adj
    exact ((model X).realization.app (G.obj (constant D l (point D)))).symm ≪≫
      (rho D l R X).mapIso
        ((comparison X (point D) a₀ S c G adj).right.app (constant D l (point D)) ≪≫
          (S.ring.operation c .closed).G.mapIso commonUnit)
  refine ⟨{ model := model
            comparison := comparison
            nativeUnit := n
            commonUnit := commonUnit
            unit_normalization := ?_
            specialization := specialization
            specialization_eq := ?_
            actualSpecialization := ?_ }⟩
  · exact (ff.map_preimage e.hom).symm
  · intros
    rfl
  · intro X a₀ _ _ _ S' c' G adj
    letI : LocallyOfFiniteType ((geometric D X).base.left ↘ Spec (.of D.k)) :=
      (geometric D X).finiteType
    letI : QuasiCompact ((geometric D X).base.left ↘ Spec (.of D.k)) :=
      (geometric D X).quasiCompact
    letI : LocallyOfFiniteType ((geometric D (point D)).base.left ↘ Spec (.of D.k)) :=
      (geometric D (point D)).finiteType
    letI : QuasiCompact ((geometric D (point D)).base.left ↘ Spec (.of D.k)) :=
      (geometric D (point D)).quasiCompact
    letI : HasCompactification (geometricMap D a₀) := hasCompactification_of_over
      (k₀ := D.k) (X := (geometric D X).base.left)
      (Y := (geometric D (point D)).base.left) (geometricMap D a₀)
    let S := Classical.choice (ConstructibleExceptionalCoefficients.exists_system.{u, 0}
      l (PadicAlgCl l) D (Fact.out : l ≠ D.p)
      (X := (geometric D X).base.left) (Y := (geometric D (point D)).base.left)
      (geometricMap D a₀))
    let c := HasCompactification.compactification (geometricMap D a₀)
    exact specialization X a₀ S c G adj ≪≫
      Classical.choice (native_exceptional_structural_transport D l R X a₀ S c S' c')

end WeilConjectures.NativeExceptionalForgetful
