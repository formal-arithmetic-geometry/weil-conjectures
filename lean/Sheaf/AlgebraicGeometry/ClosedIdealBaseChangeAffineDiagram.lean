module

public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections

/-!
# Canonical affine diagram for a base-changed closed ideal

Source: Stacks Project, Schemes, Tags 01JU, 01JR, 01JQ, 01I9;
Cohomology of Schemes, Tag 02KG.
(blueprint: lem-sfb-closed-ideal-base-change-affine-diagram).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry
open Scheme.Modules

/-- The base change of the closed immersion, with the chosen fibre products.
Source: Stacks, Tag 01JU (blueprint: lem-sfb-closed-ideal-base-change-affine-diagram). -/
noncomputable def closedIdealBaseChangeMap {X Z T T' : Scheme.{u}}
    (f : X ⟶ T) (i : Z ⟶ X) (g : T' ⟶ T) :
    pullback (i ≫ f) g ⟶ pullback f g :=
  pullback.map (i ≫ f) g f g i (𝟙 T') (𝟙 T) (by simp) (by simp)

/-- The pulled-back ideal inclusion followed by the adjoint structure-sheaf map.
Source: Stacks, Tags 01JU, 01I9
(blueprint: lem-sfb-closed-ideal-base-change-affine-diagram). -/
noncomputable def closedIdealBaseChangeArrow {X Z Y : Scheme.{u}}
    (i : Z ⟶ X) (h : Y ⟶ X) :
    (tensorPullback h).obj i.ker.toModules ⟶ SheafOfModules.unit Y.ringCatSheaf :=
  (tensorPullback h).map i.ker.toModulesι ≫ tensorPullbackObjUnitToUnit h

/-- The affine-chart part of the diagram, with canonical coordinates on all three terms.
`J` is the actual affine ideal. The comparisons are fixed by the ideal inclusion,
projection ring maps and the section-normalized pullback unit, rather than arbitrary
isomorphisms. The balanced isomorphism is Mathlib's
`TensorProduct.AlgebraTensorModule.cancelBaseChange`.
Source: Stacks, Tags 01JR, 01JQ, 01I9 and 02KG
(blueprint: lem-sfb-closed-ideal-base-change-affine-diagram). -/
noncomputable def closedIdealBaseChangeAffineChart
    {X Z T T' : Scheme.{u}} (f : X ⟶ T) (i : Z ⟶ X) (g : T' ⟶ T)
    (V : T.affineOpens) (U : X.affineOpens) (V' : T'.affineOpens)
    (hf : U.1 ≤ f ⁻¹ᵁ V.1) (hg : V'.1 ≤ g ⁻¹ᵁ V.1) : Prop :=
  let h := pullback.fst f g
  let k := pullback.snd f g
  let i' := closedIdealBaseChangeMap f i g
  let Q := h ⁻¹ᵁ U.1 ⊓ k ⁻¹ᵁ V'.1
  let R := Γ(T, V.1)
  let A := Γ(X, U.1)
  let R' := Γ(T', V'.1)
  let J := i.ker.ideal U
  let B := A ⧸ J
  letI : Algebra R A := (f.appLE V.1 U.1 hf).hom.toAlgebra
  letI : Algebra R R' := (g.appLE V.1 V'.1 hg).hom.toAlgebra
  letI : Module R J := Module.compHom J (algebraMap R A)
  IsAffineOpen Q ∧ IsAffineOpen (i' ⁻¹ᵁ Q) ∧ IsAffineOpen (i ⁻¹ᵁ U.1) ∧
    IsPullback (h.resLE U.1 Q inf_le_left) (k.resLE V'.1 Q inf_le_right)
      (f.resLE V.1 U.1 hf) (g.resLE V.1 V'.1 hg) ∧
    ∃ (eI : J ≃+ Γ(i.ker.toModules, U.1))
      (eB : B ≃+* Γ(Z, i ⁻¹ᵁ U.1))
      (eA : Γ(pullback f g, Q) ≃+* (A ⊗[R] R'))
      (eB' : Γ(pullback (i ≫ f) g, i' ⁻¹ᵁ Q) ≃+* (B ⊗[R] R'))
      (c : (J ⊗[A] (A ⊗[R] R')) ≃+
        Γ((tensorPullback h).obj i.ker.toModules, Q)),
      (∀ j : J, i.ker.toModulesι.app U.1 (eI j) = (j : A)) ∧
      (∀ x : A, eB (Ideal.Quotient.mk J x) = i.app U.1 x) ∧
      (∀ (x : A) (r : R'), eA.symm (x ⊗ₜ[R] r) =
        h.appLE U.1 Q inf_le_left x * k.appLE V'.1 Q inf_le_right r) ∧
      (∀ (j : J) (d : A ⊗[R] R'), c (j ⊗ₜ[A] d) =
        eA.symm d • ((tensorPullback h).obj i.ker.toModules).presheaf.map
          (homOfLE (inf_le_left : Q ≤ h ⁻¹ᵁ U.1)).op
          (((tensorPullbackSectionAdjunction h).unit.app i.ker.toModules).app U.1 (eI j))) ∧
      (∀ (d : A ⊗[R] R') (t : J ⊗[A] (A ⊗[R] R')),
        c ((TensorProduct.comm A J (A ⊗[R] R')).symm
          (d • TensorProduct.comm A J (A ⊗[R] R') t)) = eA.symm d • c t) ∧
      (∀ (j : J) (x : A) (r : R'),
        TensorProduct.AlgebraTensorModule.cancelBaseChange R A A J R' (j ⊗ₜ[A] (x ⊗ₜ[R] r)) =
          (x • j) ⊗ₜ[R] r) ∧
      (∀ (j : J) (r : R'),
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A J R').symm (j ⊗ₜ[R] r) =
          j ⊗ₜ[A] ((1 : A) ⊗ₜ[R] r)) ∧
      (∀ (j : J) (d : A ⊗[R] R'),
        eA ((closedIdealBaseChangeArrow i h).app Q (c (j ⊗ₜ[A] d))) =
          ((j : A) ⊗ₜ[R] (1 : R')) * d) ∧
      (∀ (x : A) (r : R'),
        eB' (i'.app Q (eA.symm (x ⊗ₜ[R] r))) = Ideal.Quotient.mk J x ⊗ₜ[R] r) ∧
      (∀ (j : J) (r : R'), eA ((closedIdealBaseChangeArrow i h).app Q
        (c ((TensorProduct.AlgebraTensorModule.cancelBaseChange R A A J R').symm (j ⊗ₜ[R] r)))) =
          (j : A) ⊗ₜ[R] r)

/-- The closed ideal sequence after arbitrary base change, including its complete affine
coordinate diagram. No flatness or finiteness is assumed.
Source: Stacks, Tags 01JU, 01JR, 01JQ, 01I9, 02KG
(blueprint: lem-sfb-closed-ideal-base-change-affine-diagram).
Proof: (1) The fibre-product universal property identifies Z times_T T' with
Z times_X (X times_T T'), preserving projections. Tag 01JU gives closedness and
identifies the kernel ideal with the image of the pulled-back inclusion.
(2) Ideals of closed immersions are quasi-coherent; pullback preserves
quasi-coherence. Structure sheaves are quasi-coherent; affine pushforward preserves it.
(3) Apply affine pushforward base change to i. Composing with the structure-sheaf
pullback comparison gives the canonical isomorphism. Both quotient maps are linear
and send 1 to 1, so the quotient square commutes.
(4) Tags 01JR and 01JQ identify Q with U times_V V' and its closed inverse image
with Spec((A/J) tensor_R R'), compatibly with projections and quotient maps.
(5) Every point has such affine neighbourhoods of its three projections, so these Q cover.
(6) Tag 01I9 identifies pullback sections with J tensor_A A', by j tensor d mapping
to d times eta(j) restricted to Q.
(7) The balanced tensor isomorphism sends j tensor (x tensor r) to xj tensor r;
its inverse sends j tensor r to j tensor (1 tensor r). Balancing checks both composites.
(8) Naturality of the unit and the structure-sheaf unit equation give the first
arrow formula; projection-compatible affine coordinates give the quotient formula.
Substitute the inverse balanced map to obtain the stated J tensor_R R' sequence. -/
theorem closedIdealBaseChange_affineDiagram
    {X Z T T' : Scheme.{u}} (f : X ⟶ T) (i : Z ⟶ X) [IsClosedImmersion i]
    (g : T' ⟶ T) :
    IsPullback (pullback.fst (i ≫ f) g) (closedIdealBaseChangeMap f i g)
      i (pullback.fst f g) ∧
    IsClosedImmersion (closedIdealBaseChangeMap f i g) ∧
    Subobject.mk (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (closedIdealBaseChangeMap f i g).toRingCatSheafHom)) =
      imageSubobject (closedIdealBaseChangeArrow i (pullback.fst f g)) ∧
    ((tensorPullback (pullback.fst f g)).obj i.ker.toModules).IsQuasicoherent ∧
    (SheafOfModules.unit (pullback f g).ringCatSheaf).IsQuasicoherent ∧
    ((pushforward (closedIdealBaseChangeMap f i g)).obj
      (SheafOfModules.unit (pullback (i ≫ f) g).ringCatSheaf)).IsQuasicoherent ∧
    ∃ w : pullback.fst (i ≫ f) g ≫ i =
        closedIdealBaseChangeMap f i g ≫ pullback.fst f g,
      IsIso (moduleBaseChangeMap i (closedIdealBaseChangeMap f i g)
          (pullback.fst f g) (pullback.fst (i ≫ f) g) w
          (SheafOfModules.unit Z.ringCatSheaf) ≫
        (pushforward (closedIdealBaseChangeMap f i g)).map
          (tensorPullbackObjUnitToUnit (pullback.fst (i ≫ f) g))) ∧
      (tensorPullback (pullback.fst f g)).map
          (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom) ≫
        (moduleBaseChangeMap i (closedIdealBaseChangeMap f i g)
          (pullback.fst f g) (pullback.fst (i ≫ f) g) w
          (SheafOfModules.unit Z.ringCatSheaf) ≫
        (pushforward (closedIdealBaseChangeMap f i g)).map
          (tensorPullbackObjUnitToUnit (pullback.fst (i ≫ f) g))) =
        tensorPullbackObjUnitToUnit (pullback.fst f g) ≫
          SheafOfModules.unitToPushforwardObjUnit
            (closedIdealBaseChangeMap f i g).toRingCatSheafHom ∧
      (∀ (V : T.affineOpens) (U : X.affineOpens) (V' : T'.affineOpens)
          (hf : U.1 ≤ f ⁻¹ᵁ V.1) (hg : V'.1 ≤ g ⁻¹ᵁ V.1),
        closedIdealBaseChangeAffineChart f i g V U V' hf hg) ∧
      (∀ q : (pullback f g : Scheme.{u}), ∃ (V : T.affineOpens) (U : X.affineOpens)
          (V' : T'.affineOpens), U.1 ≤ f ⁻¹ᵁ V.1 ∧ V'.1 ≤ g ⁻¹ᵁ V.1 ∧
          q ∈ (pullback.fst f g ⁻¹ᵁ U.1 ⊓ pullback.snd f g ⁻¹ᵁ V'.1)) := by
  sorry

end AlgebraicGeometry
