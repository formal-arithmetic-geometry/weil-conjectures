/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryRingedTensorChainComparison
public import WeilConjectures.WeilSheaf.Native.NativeRingedForgetTensorChainComparison
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedUnderivedBinarySquare

/-! # The binary square for normalized native tensor complexes -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

attribute [local instance] Mod.monoidalCategoryCochainComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  {T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
    ProEtaleWeilSheaf k₀ l X}
  [T.Additive] [∀ P, (T.obj P).Additive]
  [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
  (D : NativeWeilTensorRingedAssociatorChainData k₀ l X T)

/-- Apply the bridge square termwise. All components are the specified underived
square components, so no comparison data are selected by this construction.
Source: Stacks 06YN (blueprint: new-sf-native-weil-tensor-ringed-binary-chain-square). -/
def nativeRingedChainBridgeSquare :
    D.b.native.functor.mapHomologicalComplex (.up ℤ) ⋙
        D.b.forget.mapHomologicalComplex (.up ℤ) ≅
      nativeChainForgetU (T := T) ⋙ D.b.ordinary.functor.mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex D.b.square (.up ℤ)

-- Both normalized site tensors occur in this square.
-- The degreewise comparison crosses three concrete total constructions.
/-- The normalized comparisons commute for a single pair of native complexes.
Source: Stacks 06YS, 06YU and 0FPT
(blueprint: new-sf-native-weil-tensor-ringed-binary-chain-square).

Proof: first compare underived inverses by their tensor--Hom mates. The native
uncurrying equation, the equation `he` for ordinary forgetting, and the Hom square
of the bridge give the same mate after applying the ordinary adjunction. Cancel
the sheaf tensor braidings using symmetry of the restriction tensorator. This
proves the underived binary square. Next use coproduct extensionality after the
native equivalence. The equations `hchain`, the native summand equation, the
ordinary normalized summand equation and the restriction summand equation reduce
the two sides to this underived square. Naturality of the termwise bridge square
moves each summand inclusion through it. Both exchanges contribute the same
scalar (-1)^(pq), and additivity moves that scalar through the comparisons.
This calculation uses only two factors and no associator. -/
theorem native_weil_tensor_ringed_binary_chain_square
    (d : NativeOrdinaryRingedTensorUnderivedData D.b)
    (o : NativeOrdinaryRingedTensorChainComparison D.b D.κ d)
    (r : NativeRingedForgetTensorChainComparison D.b)
    (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
    let E := D.b.native.functor.mapHomologicalComplex (.up ℤ)
    let F := D.b.forget.mapHomologicalComplex (.up ℤ)
    let G := D.b.ordinary.functor.mapHomologicalComplex (.up ℤ)
    let U := nativeChainForgetU (T := T)
    let τ := nativeRingedChainBridgeSquare D
    F.map (D.A.chain Q P).hom ≫ r.tensor.hom.app (E.obj P, E.obj Q) ≫
        (τ.hom.app P ⊗ₘ τ.hom.app Q) =
      τ.hom.app (nativeTensorComplex T P Q) ≫
        G.map (nativeChainForgetC D P Q).hom ≫ o.tensor.hom.app (U.obj P, U.obj Q) := by
  classical
  let := SheafOfModules.isMonoidal_W_independentCoefficients D.b.R
  let := SheafOfModules.monoidalCategory D.b.R
  let := SheafOfModules.isMonoidal_W_independentCoefficients D.b.Q
  let := SheafOfModules.monoidalCategory D.b.Q
  let V := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
  let E := D.b.native.functor.mapHomologicalComplex (.up ℤ)
  let F := D.b.forget.mapHomologicalComplex (.up ℤ)
  let G := D.b.ordinary.functor.mapHomologicalComplex (.up ℤ)
  let U := nativeChainForgetU (T := T)
  let τ := nativeRingedChainBridgeSquare D
  have (I : Type) : PreservesColimitsOfShape (Discrete I) D.b.forget :=
    preservesColimitsOfShape_of_equiv
      (Discrete.equivalence (Equiv.ulift.{u + 1, 0} : ULift.{u + 1} I ≃ I)) D.b.forget
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map
    (D.b.native.functor ⋙ D.b.forget)
  intro p q hpq
  have hpq : p + q = n := hpq
  have hqp : q + p = n := by omega
  have hs := D.A.summand Q P p q n hpq hqp
  have hr := r.summand (E.obj P) (E.obj Q) q p n hqp
  have ho := o.summand (U.obj Q) (U.obj P) p q n hpq hqp
  have hc := D.hchain Q P p q n hpq
  have hb := native_weil_tensor_ringed_underived_binary_square D d (Q.X p) (P.X q)
  have ht := D.b.square.hom.naturality
    (HomologicalComplex.ιMapBifunctor Q P T (.up ℤ) p q n hpq)
  dsimp only [Functor.comp_map] at ht
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  change D.b.forget.map (D.b.native.functor.map _) ≫
      D.b.forget.map ((D.A.chain Q P).hom.f n) ≫
        (r.tensor.hom.app (E.obj P, E.obj Q)).f n ≫
          (τ.hom.app P ⊗ₘ τ.hom.app Q).f n =
    D.b.forget.map (D.b.native.functor.map _) ≫
      (τ.hom.app (nativeTensorComplex T P Q)).f n ≫
        D.b.ordinary.functor.map ((nativeChainForgetC D P Q).hom.f n) ≫
          (o.tensor.hom.app (U.obj P, U.obj Q)).f n
  rw [← D.b.forget.map_comp_assoc, hs]
  simp only [nativeRingedTensorSign]
  erw [D.b.forget.map_zsmul, D.b.forget.map_comp]
  simp only [Preadditive.zsmul_comp, Category.assoc]
  erw [reassoc_of% hr]
  dsimp only [nativeChainForgetC, Iso.trans_hom, HomologicalComplex.comp_f]
  simp only [D.b.ordinary.functor.map_comp, Category.assoc]
  erw [reassoc_of% ht]
  rw [← D.b.ordinary.functor.map_comp_assoc, hc]
  simp only [D.b.ordinary.functor.map_comp, Category.assoc]
  erw [ho]
  simp only [Units.smul_def, Preadditive.comp_zsmul]
  have hi : RingedForgetTensorTransposition.tensorSummand D.b.K D.b.Q
      (F.obj (E.obj P)) (F.obj (E.obj Q)) q p n hqp ≫
        (τ.hom.app P ⊗ₘ τ.hom.app Q).f n =
      (D.b.square.hom.app (P.X q) ⊗ₘ D.b.square.hom.app (Q.X p)) ≫
        RingedForgetTensorTransposition.tensorSummand D.b.K D.b.Q
          (G.obj (U.obj P)) (G.obj (U.obj Q)) q p n hqp := by
    change HomologicalComplex.ιTensorObj _ _ q p n hqp ≫ _ = _
    rw [MonoidalCategory.tensorHom_def, HomologicalComplex.comp_f]
    erw [CochainComplex.Monoidal.ι_whiskerRight_assoc,
      CochainComplex.ιTensorObj_whiskerLeft_f]
    rw [← MonoidalCategory.tensorHom_def_assoc]
    rfl
  erw [hi]
  change ((p * q).negOnePow : ℤ) •
      (D.b.forget.map (D.A.underived (Q.X p) (P.X q)).hom ≫
        D.b.underived.tensor.hom.app (D.b.native.functor.obj (P.X q),
          D.b.native.functor.obj (Q.X p)) ≫
        (D.b.square.hom.app (P.X q) ⊗ₘ D.b.square.hom.app (Q.X p)) ≫
        RingedForgetTensorTransposition.tensorSummand D.b.K D.b.Q
          (G.obj (U.obj P)) (G.obj (U.obj Q)) q p n hqp) =
    ((p * q).negOnePow : ℤ) •
      (D.b.square.hom.app ((T.obj (Q.X p)).obj (P.X q)) ≫
        D.b.ordinary.functor.map (D.e.hom.app (Q.X p, P.X q)) ≫
        (d.underived (Q.X p).carrier (P.X q).carrier).hom ≫
        RingedForgetTensorTransposition.tensorSummand D.b.K D.b.Q
          (G.obj (U.obj P)) (G.obj (U.obj Q)) q p n hqp)
  apply congrArg (fun f ↦ ((p * q).negOnePow : ℤ) • f)
  exact (reassoc_of% hb) _

end AlgebraicGeometry.ProEtaleWeilSheaf
