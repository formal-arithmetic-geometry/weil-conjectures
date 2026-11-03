/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalAlgebraFlatBaseChange
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalRegularPureCodimension
public import WeilConjectures.AlgebraicGeometry.Purity.PurityNormalProjection
public import WeilConjectures.AlgebraicGeometry.RelativeTangentBundle.RelativeTangentBundle
public import WeilConjectures.AlgebraicGeometry.DiagonalConormalDifferentials
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.AffineStructureAlgebraFullyFaithful
public import WeilConjectures.AlgebraicGeometry.ChartNormalDifferential.ChartNormalDifferential
public import WeilConjectures.AlgebraicGeometry.ClosedImmersionConormalFlatBaseChange

/-!
# Centred diagonal neighbourhood and its differential under an étale source map

Source: current blueprint, `sk-prop-sp-orientation-charts.proof.md`, Steps 1--2:
remove the off-diagonal components, form the Cartesian centre squares, apply the
canonical flat conormal graded comparison, and identify its normal map with the
differential (Stacks Tags 02GE, 0473 and 0635).
(blueprint: lem-sp-chart-centre-transport)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ChartNormalDifferential

attribute [local irreducible] Scheme.Modules.tensorPullback
  ConormalGradedAlgebra.presentation PurityNormalBundle.normalCone
  RelativeTangentBundle.scheme PurityNormalBundle.projection
  RelativeTangentBundle.projection PurityNormalBundle.zeroSection
  RelativeTangentBundle.zeroSection Scheme.Hom.relativeDifferentials

namespace AlgebraicGeometry

private theorem specMap_exists_general {Z Z' N N' : Scheme.{u}}
    (f : Z ⟶ Z') (B : Z.CommAlgebraSheaf) (B' : Z'.CommAlgebraSheaf)
    (π : N ⟶ Z) (π' : N' ⟶ Z') [IsAffineHom π']
    (α : B ≅ structureAlgebra π) (α' : B' ≅ structureAlgebra π')
    (ρ : B'.right ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj B.right)
    (hρ : B'.hom ≫ ρ = (⟨f.c⟩ : Z'.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj Z.sheaf) ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).map B.hom) :
    ∃ ν : N ⟶ N', IsSpecMap f B B' π π' α α' ν
      (fun V a ↦ ρ.hom.app (op V) a) := by
  let F := TopCat.Sheaf.pushforward CommRingCat.{u} f.base
  let θ : B' ⟶ structureAlgebra (π ≫ f) :=
    Under.homMk (ρ ≫ F.map α.hom.right) (by
      rw [← Category.assoc, hρ, Category.assoc]
      change (⟨f.c⟩ : Z'.sheaf ⟶ F.obj Z.sheaf) ≫
        F.map B.hom ≫ F.map α.hom.right = _
      rw [← F.map_comp, Under.w α.hom]
      rfl)
  let κ := α'.inv ≫ θ
  obtain ⟨ν, hw, ha⟩ := exists_over_map_of_algebra (π ≫ f) π' κ
  have hκ : κ = structureAlgebraMap π' (π ≫ f) ν hw := by
    apply Under.UnderMorphism.ext
    apply CategoryTheory.Sheaf.hom_ext
    apply TopCat.Sheaf.hom_ext _ _ (B := fun U : Z'.affineOpens ↦ U.1)
      (by
        change TopologicalSpace.Opens.IsBasis (Set.range (fun U : Z'.affineOpens ↦ U.1))
        convert Z'.isBasis_affineOpens using 1
        ext U
        simp)
    intro U
    exact (ha U).symm
  refine ⟨ν, hw, ?_⟩
  intro V a
  have he : α'.hom ≫ κ = θ := by simp [κ]
  rw [hκ] at he
  exact congrArg (fun q ↦ q.right.hom.app (op V) a) he.symm

-- The identity adjunction turns a tensor-pullback map into its map on sections.

private theorem identityModuleMap {S : Scheme.{u}} (M N : S.Modules)
    (c : (tensorPullback (𝟙 S)).obj M ≅ N) :
    ∃ e : M ≅ N, ∀ V a, e.hom.app V a = pullbackSection (𝟙 S) N M c.hom V a := by
  let adj := Classical.choose (exists_tensorPullbackAdjunction (𝟙 S))
  let e := adj.unit.app M ≫ (pushforward (𝟙 S)).map c.hom ≫
    (pushforwardId S).hom.app N
  have : (tensorPullback (𝟙 S)).IsEquivalence :=
    Functor.isEquivalence_of_iso (Classical.choice (nonempty_tensorPullbackId S)).symm
  have : IsIso e := by dsimp only [e]; infer_instance
  exact ⟨asIso e, fun _ _ ↦ rfl⟩

private theorem differenceRepresentativeOn {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] (V : X.Opens) (T : (pullback f f).Opens)
    (h₁ : T ≤ (pullback.fst f f) ⁻¹ᵁ V)
    (h₂ : T ≤ (pullback.snd f f) ⁻¹ᵁ V) (a : Γ(X, V)) :
    ∃ s : (ConormalGradedAlgebra.power (pullback.diagonal f) 1).val.obj (op T),
      (ConormalGradedAlgebra.powerInclusion (pullback.diagonal f) 1).app T s =
        (pullback.snd f f).appLE V T h₂ a - (pullback.fst f f).appLE V T h₁ a := by
  let δ := pullback.diagonal f
  let φ := SheafOfModules.unitToPushforwardObjUnit δ.toRingCatSheafHom
  let b := (pullback.snd f f).appLE V T h₂ a - (pullback.fst f f).appLE V T h₁ a
  have hb : (SheafOfModules.evaluation (pullback f f).ringCatSheaf (op T)).map φ b = 0 := by
    change δ.app T b = 0
    dsimp only [b]
    rw [map_sub]
    have hsnd : (pullback.snd f f).appLE V T h₂ ≫ δ.app T =
        (pullback.fst f f).appLE V T h₁ ≫ δ.app T := by
      rw [δ.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
      simp [δ]
    exact sub_eq_zero.mpr (ConcreteCategory.congr_hom hsnd a)
  have hb' : b ∈ Set.range
      ((SheafOfModules.evaluation (pullback f f).ringCatSheaf (op T)).map (kernel.ι φ)) := by
    rw [Scheme.Modules.range_map_kernelι]
    exact hb
  obtain ⟨b', hb'⟩ := hb'
  obtain ⟨k, hk⟩ := idealKernelIso δ
  refine ⟨k.inv.app T b', ?_⟩
  have hki : k.inv ≫ δ.ker.toModulesι = kernel.ι φ := by
    rw [← hk]
    exact k.inv_hom_id_assoc _
  exact (congrArg (fun q ↦ q.app T b') hki).trans hb'

private theorem differenceRestriction {U Y : Scheme.{u}} (h : U ⟶ Y) [IsSeparated h]
    (O : (pullback h h).Opens) (δ : U ⟶ O.toScheme) [IsClosedImmersion δ]
    (hδ : δ ≫ O.ι = pullback.diagonal h)
    (dR : (tensorPullback (𝟙 U)).obj
      (ConormalGradedAlgebra.piece (pullback.diagonal h) 1) ⟶
        ConormalGradedAlgebra.piece δ 1)
    (hdR : dR = Classical.choose ((Classical.choose_spec
      (closedImmersion_conormal_functorial δ (pullback.diagonal h) O.ι (𝟙 U)
        (by simpa using hδ)).2).2))
    (e : ConormalGradedAlgebra.piece (pullback.diagonal h) 1 ≅
      ConormalGradedAlgebra.piece δ 1)
    (he : ∀ V a, e.hom.app V a = pullbackSection (𝟙 U) _ _ dR V a)
    (ω : h.relativeDifferentials ≅ ConormalGradedAlgebra.piece (pullback.diagonal h) 1)
    (hω : IsDifferenceIdentification h (pullback.diagonal h)
      (pullback.fst h h) (pullback.snd h h) ω) :
    IsDifferenceIdentification h δ (O.ι ≫ pullback.fst h h)
      (O.ι ≫ pullback.snd h h) (ω ≪≫ e) := by
  intro V T h₁ h₂ hV a s hs
  let W := O.ι ''ᵁ T
  have hW₁ : W ≤ (pullback.fst h h) ⁻¹ᵁ V := by
    rintro _ ⟨x, hx, rfl⟩
    exact h₁ hx
  have hW₂ : W ≤ (pullback.snd h h) ⁻¹ᵁ V := by
    rintro _ ⟨x, hx, rfl⟩
    exact h₂ hx
  have hVW : V ≤ (pullback.diagonal h) ⁻¹ᵁ W := by
    rw [← hδ, Scheme.Hom.comp_preimage]
    exact hV.trans (δ.preimage_mono (O.ι.preimage_image_eq T).ge)
  obtain ⟨sW, hsW⟩ := differenceRepresentativeOn h V W hW₁ hW₂ a
  have hδW : V ≤ δ ⁻¹ᵁ (O.ι ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, hδ]
    exact hVW
  obtain ⟨b, hb, hclass⟩ := conormalRepresentativeLocal δ (pullback.diagonal h) O.ι
    (𝟙 U) (by simpa using hδ) dR hdR W sW V hδW hVW
  change e.hom.app V (ω.hom.app V _) = _
  rw [he]
  have hw := hω V W hW₁ hW₂ hVW a sW hsW
  change ω.hom.app V _ = _ at hw
  rw [hw]
  erw [pullbackSection_naturality]
  erw [hclass]
  symm
  apply representative_eq_of_inclusion δ (O.ι.preimage_image_eq T).symm s b
  · rw [hb, hsW]
    have hmap := Scheme.Hom.appLE_comp_appLE O.ι (pullback.snd h h) V W T
      hW₂ (O.ι.preimage_image_eq T).ge
    have hmap' := Scheme.Hom.appLE_comp_appLE O.ι (pullback.fst h h) V W T
      hW₁ (O.ι.preimage_image_eq T).ge
    change (O.ι.appLE W T (O.ι.preimage_image_eq T).ge) _ = _
    rw [map_sub]
    exact (congrArg₂ (· - ·) (ConcreteCategory.congr_hom hmap a)
      (ConcreteCategory.congr_hom hmap' a)).trans hs.symm

private theorem differentialFromNormalDirect {U A Y M : Scheme.{u}}
    (p : A ⟶ Y) (e : U ⟶ A) [Smooth p] [Smooth (e ≫ p)]
    [IsSeparated p] [IsSeparated (e ≫ p)]
    (δ : U ⟶ M) [IsClosedImmersion δ]
    (c : (tensorPullback e).obj
      (ConormalGradedAlgebra.presentation (pullback.diagonal p)).algebra.toModule ⟶
      (ConormalGradedAlgebra.presentation δ).algebra.toModule)
    (ν : PurityNormalBundle.normalCone δ ⟶
      PurityNormalBundle.normalCone (pullback.diagonal p))
    (hν : IsSpecMap e (ConormalGradedAlgebra.presentation δ).algebra
      (ConormalGradedAlgebra.presentation (pullback.diagonal p)).algebra
      (PurityNormalBundle.projection δ)
      (PurityNormalBundle.projection (pullback.diagonal p))
      (normalAlgebraIso δ) (normalAlgebraIso (pullback.diagonal p)) ν
      (pullbackSection e _ _ c))
    (ωU : (e ≫ p).relativeDifferentials ≅
      ConormalGradedAlgebra.piece δ 1)
    (ωA : p.relativeDifferentials ≅ ConormalGradedAlgebra.piece (pullback.diagonal p) 1)
    (tU : PurityNormalBundle.normalCone δ ≅
      RelativeTangentBundle.scheme (e ≫ p))
    (htU : IsNormalTangentIdentification (e ≫ p) δ ωU tU)
    (tA : PurityNormalBundle.normalCone (pullback.diagonal p) ≅ RelativeTangentBundle.scheme p)
    (htA : IsNormalTangentIdentification p (pullback.diagonal p) ωA tA)
    (hgen : ∀ (V : A.Opens) (a : Γ(A, V)),
      pullbackSection e _ _ c V
        (((ConormalGradedAlgebra.presentation (pullback.diagonal p)).inclusion 1).app V
          (ωA.hom.app V (p.relativeDifferentialsDerivation.d a))) =
      ((ConormalGradedAlgebra.presentation δ).inclusion 1).app
        (e ⁻¹ᵁ V) (ωU.hom.app (e ⁻¹ᵁ V)
          ((e ≫ p).relativeDifferentialsDerivation.d (e.app V a)))) :
    IsDifferential p e (tU.inv ≫ ν ≫ tA.hom) := by
  have he : (tU.inv ≫ ν ≫ tA.hom) ≫ RelativeTangentBundle.projection p =
      RelativeTangentBundle.projection (e ≫ p) ≫ e := by
    calc
      _ = tU.inv ≫ PurityNormalBundle.projection δ ≫ e := by
        simp only [Category.assoc]
        rw [htA.1, hν.1]
      _ = RelativeTangentBundle.projection (e ≫ p) ≫ e := by
        rw [← htU.1]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
  refine ⟨he, ?_⟩
  intro V a
  let W := e ⁻¹ᵁ V
  obtain ⟨βU, hβU, htUspec⟩ := htU.2.2
  obtain ⟨βA, hβA, htAspec⟩ := htA.2.2
  have hA := htAspec.2 V
    ((SymmetricAlgebraSheaf.inclusion p.relativeDifferentials).app V
      (p.relativeDifferentialsDerivation.d a))
  have hAgen := congrArg
    ((normalAlgebraIso (pullback.diagonal p)).hom.right.hom.app (op V))
    (hβA V (p.relativeDifferentialsDerivation.d a))
  have hA := hAgen.symm.trans hA
  have hU := htUspec.2 W
    ((SymmetricAlgebraSheaf.inclusion (e ≫ p).relativeDifferentials).app W
      ((e ≫ p).relativeDifferentialsDerivation.d (e.app V a)))
  have hUgen := congrArg
    ((normalAlgebraIso δ).hom.right.hom.app (op W))
    (hβU W ((e ≫ p).relativeDifferentialsDerivation.d (e.app V a)))
  have hU := hUgen.symm.trans hU
  have hc := hν.2 V
    (((ConormalGradedAlgebra.presentation (pullback.diagonal p)).inclusion 1).app V
      (ωA.hom.app V (p.relativeDifferentialsDerivation.d a)))
  have hclass := hc.symm.trans
    (congrArg ((normalAlgebraIso δ).hom.right.hom.app (op W)) (hgen V a))
  have hid (S : Scheme.{u}) (T : S.Opens) :
      (𝟙 S : S ⟶ S).appLE T T le_rfl = 𝟙 Γ(S, T) := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_base, Scheme.Hom.id_app]
    exact S.presheaf.map_id _
  obtain ⟨_, hx⟩ := conjugate_app e
    (PurityNormalBundle.projection δ)
    (PurityNormalBundle.projection δ)
    (PurityNormalBundle.projection (pullback.diagonal p))
    (RelativeTangentBundle.projection (e ≫ p)) (RelativeTangentBundle.projection p)
    (Iso.refl _) tU tA ν (by simp) htU.1 htA.1 hν.1 V _ _ _ _ hA.symm hU.symm
      (by
        simp only [Iso.refl_hom, hid]
        convert hclass using 1
        rfl)
  simp only [Iso.refl_inv, Category.id_comp] at hx
  convert hx using 1
  rfl

/-- The canonical centred-neighbourhood transport, including its graded and tangent maps.
Source: current blueprint, `sk-prop-sp-orientation-charts.proof.md`, Steps 1--2;
Stacks Tags 02GE, 0473, 0635 and 08S2
(blueprint: lem-sp-chart-centre-transport).

Proof: Since the structural morphisms are separated, so are g, h and uV.
The etale diagonal of uV is open and closed in F = V ×_X V, while
F is closed in V ×_Y V by base change of the separated diagonal of g.
Thus the complement of F minus its diagonal is the specified open O and contains
the whole diagonal. Computing the fibre products gives the two centre squares
and the base-change square for (W0,s). The restrictions of b and a are separated
etale morphisms, since they are base changes and composites of uV.
Flat conormal base change now gives the unique graded map, an isomorphism in every
degree, with local formula [c] tensor r maps to [q-sharp(c) r]. Its degree zero is
the scalar map and its degree one is the canonical conormal map. Relative Spec
gives its Cartesian normal map and preserves the augmentation zero sections.
For a smooth diagonal, the symmetric-algebra identification of the normal cone
with the tangent bundle sends da to the second-factor-minus-first-factor class.
Pulling that class back along (uV,uV) sends it to the same difference for uV-sharp(a).
The universal property of differentials and the symmetric algebra therefore
identifies this specific normal map with duV; etaleness makes its tangent square
Cartesian. At d=0 the diagonal component is clopen and the graded algebra has
only degree zero. The same constructions and equations apply to the empty source. -/
theorem chart_centre_transport (k : Type u) [Field k]
    {X Y V : Scheme.{u}}
    (aX : X ⟶ Spec (CommRingCat.of k))
    (aY : Y ⟶ Spec (CommRingCat.of k))
    (aV : V ⟶ Spec (CommRingCat.of k))
    [IsSeparated aX] [IsSeparated aY] [IsSeparated aV]
    [LocallyOfFiniteType aX] [LocallyOfFiniteType aY] [LocallyOfFiniteType aV]
    [QuasiCompact aX] [QuasiCompact aY] [QuasiCompact aV]
    (g : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d g]
    (hgk : g ≫ aY = aX)
    (uV : V ⟶ X) [Etale uV]
    (huVk : uV ≫ aX = aV)
    (h : V ⟶ Y) (hh : h = uV ≫ g) :
    ∃ (a : pullback h g ⟶ pullback.diagonalObj g)
      (ha : a = pullback.map h g g g uV (𝟙 X) (𝟙 Y) (by simp [hh]) (by simp))
      (b : pullback.diagonalObj h ⟶ pullback h g)
      (hb : b = pullback.map h h h g (𝟙 V) uV (𝟙 Y) (by simp) (by simp [hh]))
      (s : V ⟶ pullback h g)
      (hs : s = pullback.lift (𝟙 V) uV (by simp [hh])),
      IsPullback a (pullback.fst h g) (pullback.fst g g) uV ∧
      IsPullback s uV a (pullback.diagonal g) ∧
      ∃ (O : (pullback.diagonalObj h).Opens) (iO : V ⟶ O.toScheme)
          (hIO : IsClosedImmersion iO)
          (hdiag : iO ≫ O.ι = pullback.diagonal h),
        O.1 =
          (Set.range (pullback.map uV uV h h (𝟙 V) (𝟙 V) g
            (by simp [hh]) (by simp [hh])) \ Set.range (pullback.diagonal h))ᶜ ∧
        Set.range (pullback.diagonal h) ⊆ O.1 ∧
        IsClosedImmersion
          (pullback.map uV uV h h (𝟙 V) (𝟙 V) g (by simp [hh]) (by simp [hh])) ∧
        IsOpenImmersion (pullback.diagonal uV) ∧
        IsClosedImmersion (pullback.diagonal uV) ∧
        IsPullback iO (𝟙 V) (O.ι ≫ b) s ∧
        IsPullback iO uV (O.ι ≫ b ≫ a) (pullback.diagonal g) ∧
        Etale (O.ι ≫ b) ∧ IsSeparated (O.ι ≫ b) ∧
        Etale (O.ι ≫ b ≫ a) ∧ IsSeparated (O.ι ≫ b ≫ a) ∧
        ∃ (hg : IsSeparated g),
          letI : IsSeparated g := hg
          letI : IsClosedImmersion (pullback.diagonal g) := inferInstance
          letI : IsClosedImmersion iO := hIO
          letI : Smooth g := SmoothOfRelativeDimension.smooth d g
          letI : Smooth (uV ≫ g) := inferInstance
          let Ag := ConormalGradedAlgebra.presentation (pullback.diagonal g)
          let Ah := ConormalGradedAlgebra.presentation iO
          ∃ (hcomp : iO ≫ O.ι ≫ b ≫ a = uV ≫ pullback.diagonal g)
            (c : (Scheme.Modules.tensorPullback uV).obj Ag.algebra.toModule ≅
              Ah.algebra.toModule),
            ConormalGradedAlgebra.IsBaseChangeMap iO (pullback.diagonal g)
              (O.ι ≫ b ≫ a) uV hcomp Ah Ag c.hom ∧
            ∃ (ωV : (uV ≫ g).relativeDifferentials ≅ ConormalGradedAlgebra.piece iO 1)
              (ωX : g.relativeDifferentials ≅
                ConormalGradedAlgebra.piece (pullback.diagonal g) 1)
              (tV : PurityNormalBundle.normalCone iO ≅
                RelativeTangentBundle.scheme (uV ≫ g))
              (tX : PurityNormalBundle.normalCone (pullback.diagonal g) ≅
                RelativeTangentBundle.scheme g)
              (ν : PurityNormalBundle.normalCone iO ⟶
                PurityNormalBundle.normalCone (pullback.diagonal g))
              (du : RelativeTangentBundle.scheme (uV ≫ g) ⟶
                RelativeTangentBundle.scheme g),
              IsDifferenceIdentification (uV ≫ g) iO
                (O.ι ≫ pullback.fst h h) (O.ι ≫ pullback.snd h h) ωV ∧
              IsDifferenceIdentification g (pullback.diagonal g)
                (pullback.fst g g) (pullback.snd g g) ωX ∧
              IsNormalTangentIdentification (uV ≫ g) iO ωV tV ∧
              IsNormalTangentIdentification g (pullback.diagonal g) ωX tX ∧
              IsSpecMap uV Ah.algebra Ag.algebra
                (PurityNormalBundle.projection iO)
                (PurityNormalBundle.projection (pullback.diagonal g))
                (normalAlgebraIso iO) (normalAlgebraIso (pullback.diagonal g)) ν
                (pullbackSection uV Ah.algebra.toModule Ag.algebra.toModule c.hom) ∧
              IsPullback ν (PurityNormalBundle.projection iO)
                (PurityNormalBundle.projection (pullback.diagonal g)) uV ∧
              PurityNormalBundle.zeroSection iO ≫ ν =
                uV ≫ PurityNormalBundle.zeroSection (pullback.diagonal g) ∧
              IsDifferential g uV du ∧
              IsPullback du (RelativeTangentBundle.projection (uV ≫ g))
                (RelativeTangentBundle.projection g) uV ∧
              RelativeTangentBundle.zeroSection (uV ≫ g) ≫ du =
                uV ≫ RelativeTangentBundle.zeroSection g ∧
              ν ≫ tX.hom = tV.hom ≫ du := by
  sorry

end AlgebraicGeometry
