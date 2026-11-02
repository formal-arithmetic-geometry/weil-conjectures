/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedGenericWeil.NativeWeilComponentCycle
public import WeilConjectures.CategoryTheory.Endofunctor.ComponentCycle.CyclicPairEquivalence
import WeilConjectures.AlgebraicGeometry.CondensedGenericWeil.NativeClopenModuleEquivalence
import WeilConjectures.WeilSheaf.StrictWeilComplex

/-! # Native component tuples and the cyclic Frobenius square

Source: Weil II (1.1.12), native component reconstruction.
(blueprint: lem-dl-a1-native-weil-cyclic-tuple).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale.CondensedGenericWeil

attribute [local irreducible] CondensedRing.upperStar

variable (D : WeilConjectures.FiniteFieldDatum.{u})
  (U₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
  [ConnectedSpace U₀.left]
variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (t : Spec (.of Ω) ⟶ (D.geometricFiber U₀).left)
  (G : ProfiniteGrp.{u})
  [∀ Q, MulAction G ((FiniteEtale.fiber (t ≫ projection D U₀)).obj Q)]
  [PreGaloisCategory.IsFundamentalGroup (FiniteEtale.fiber (t ≫ projection D U₀)) G]
variable (ell : ℕ) [Fact ell.Prime]

open CategoryTheory.Endofunctor.ComponentCycle

private theorem pi_isEquivalence_of_lift
    {C E : Type v} [Category.{w} C] [Category.{w} E] {m : ℕ}
    (L : Fin m → C ⥤ E)
    [(Functor.pi' (fun i : ULift.{u} (Fin m) ↦ L i.down)).IsEquivalence] :
    (Functor.pi' L).IsEquivalence := by
  classical
  let U := Functor.pi' (fun i : ULift.{u} (Fin m) ↦ L i.down)
  let H := Functor.pi' L
  let ff : H.FullyFaithful := {
    preimage := fun f ↦ U.preimage (fun i ↦ f i.down)
    map_preimage := fun f ↦ funext (fun i ↦ congrFun (U.map_preimage _) (ULift.up i))
    preimage_map := fun f ↦ U.preimage_map f }
  let : H.Full := ff.full
  let : H.Faithful := ff.faithful
  let : H.EssSurj := ⟨fun N ↦ by
    let M := U.objPreimage (fun i ↦ N i.down)
    let e := U.objObjPreimageIso (fun i ↦ N i.down)
    exact ⟨M, ⟨Pi.isoMk (fun i ↦ Pi.isoApp e (ULift.up i))⟩⟩⟩
  exact {}

/-- The actual family of native component restrictions, viewed as a discrete diagram.
Source: the clopen Frobenius orbit in Weil II (1.1.12).
(blueprint: lem-dl-a1-native-weil-cyclic-tuple). -/
def nativeComponentTuple (A : Geometry D U₀ t G) (B : ComponentCycle D U₀ t G A) :
    RealCondensedFibre.Modules (Profinite.padicAlgClRingObj ell) (D.geometricFiber U₀).left ⥤
      (Discrete (Fin (B.n + 1)) ⥤
        RealCondensedFibre.Modules (Profinite.padicAlgClRingObj ell) A.component.X) :=
  Functor.pi' (fun i : Fin (B.n + 1) ↦
      CondensedRing.upperStar (Profinite.padicAlgClRingObj ell)
        (A.inclusion ≫ (D.geometricFrobenius U₀ ^ (i : ℕ)).hom)) ⋙
    (piEquivalenceFunctorDiscrete _ _).functor

/-- Component tuples give an equivalence before putting in the Frobenius arrows.
Source: native module gluing on the finite disjoint clopen cover.
(blueprint: lem-dl-a1-native-weil-cyclic-tuple).

Proof: the native clopen restriction equivalence uses a universe-sized ULift
index. Reindexing its Hom inverses and object preimages by ULift.up gives the
same equivalence with Fin as index. The standard equivalence between families
and discrete diagrams finishes the comparison. -/
theorem native_component_tuple_isEquivalence (A : Geometry D U₀ t G)
    (B : ComponentCycle D U₀ t G A) :
    (nativeComponentTuple D U₀ t G ell A B).IsEquivalence := by
  classical
  let Φ := D.geometricFrobenius U₀
  let Λ := Profinite.padicAlgClRingObj ell
  let j (i : ULift.{u} (Fin (B.n + 1))) := A.inclusion ≫ (Φ ^ (i.down : ℕ)).hom
  let (i : ULift.{u} (Fin (B.n + 1))) : IsOpenImmersion (j i) := (B.clopen i.down).1
  let U := nativeClopenRestriction Λ j
  let : U.IsEquivalence :=
    native_clopen_restriction_isEquivalence Λ j
      (component_cycle_coproduct D U₀ t G A B).some
  let H := Functor.pi' (fun i : Fin (B.n + 1) ↦
    CondensedRing.upperStar Λ (A.inclusion ≫ (Φ ^ (i : ℕ)).hom))
  let : (Functor.pi' (fun i : ULift.{u} (Fin (B.n + 1)) ↦
      CondensedRing.upperStar Λ (A.inclusion ≫ (Φ ^ (i.down : ℕ)).hom))).IsEquivalence := by
    change U.IsEquivalence
    infer_instance
  let : H.IsEquivalence := pi_isEquivalence_of_lift _
  change (H ⋙ (piEquivalenceFunctorDiscrete _ _).functor).IsEquivalence
  infer_instance

private theorem positivePower_hom {X : Scheme.{u}} (g : Aut X) (n : ℕ) :
    WeilConjectures.localPositivePower g.hom n = (g ^ (n + 1)).hom := by
  induction n with
  | zero => simp [WeilConjectures.localPositivePower]
  | succ n ih =>
    simpa [WeilConjectures.localPositivePower, pow_succ', Aut.Aut_mul_def,
      Iso.trans_hom] using congrArg (fun f ↦ f ≫ g.hom) ih

/-- The nonclosing component inclusions commute with one Frobenius step.
Source: powers of the geometric Frobenius in the clopen component orbit.
(blueprint: lem-dl-a1-native-weil-cyclic-tuple). -/
theorem component_tuple_step (A : Geometry D U₀ t G) (B : ComponentCycle D U₀ t G A)
    (i : Fin B.n) :
    A.inclusion ≫ (D.geometricFrobenius U₀ ^ (i.succ : ℕ)).hom =
      (A.inclusion ≫ (D.geometricFrobenius U₀ ^ (i.castSucc : ℕ)).hom) ≫
        (D.geometricFrobenius U₀).hom := by
  simp only [Fin.val_succ, Fin.val_castSucc, pow_succ', Aut.Aut_mul_def,
    Iso.trans_hom, Category.assoc]

/-- The last component edge closes through the specified actual return automorphism.
Source: the first-return square in Weil II (1.1.12).
(blueprint: lem-dl-a1-native-weil-cyclic-tuple). -/
theorem component_tuple_close (A : Geometry D U₀ t G) (B : ComponentCycle D U₀ t G A) :
    B.returnIso.hom ≫ (A.inclusion ≫ (D.geometricFrobenius U₀ ^ (0 : ℕ)).hom) =
      (A.inclusion ≫ (D.geometricFrobenius U₀ ^ (Fin.last B.n : ℕ)).hom) ≫
        (D.geometricFrobenius U₀).hom := by
  have hone : (1 : Aut (D.geometricFiber U₀).left).hom = 𝟙 _ := rfl
  simp only [pow_zero, hone, Category.comp_id, Fin.val_last]
  rw [B.square, positivePower_hom, pow_succ']
  simp only [Aut.Aut_mul_def, Iso.trans_hom, Category.assoc]

/-- The canonical Frobenius comparison on every component of the native tuple.
Source: the pullback compositors for the adjacent and closing component squares.
(blueprint: lem-dl-a1-native-weil-cyclic-tuple). -/
def nativeTupleFrobeniusSquare (A : Geometry D U₀ t G)
    (B : ComponentCycle D U₀ t G A) :
    nativeComponentTuple D U₀ t G ell A B ⋙
        cyclicShift (CondensedRing.upperStar (Profinite.padicAlgClRingObj ell)
          B.returnIso.hom) B.n ≅
      CondensedRing.upperStar (Profinite.padicAlgClRingObj ell)
          (D.geometricFrobenius U₀).hom ⋙ nativeComponentTuple D U₀ t G ell A B := by
  let Λ := Profinite.padicAlgClRingObj ell
  let Φ := D.geometricFrobenius U₀
  let j (i : Fin (B.n + 1)) := A.inclusion ≫ (Φ ^ (i : ℕ)).hom
  let edge (i : Fin B.n) :=
    CondensedRing.upperStarCongr Λ (component_tuple_step D U₀ t G A B i) ≪≫
      CondensedRing.upperStarComp Λ (j i.castSucc) Φ.hom
  let close := (CondensedRing.upperStarComp Λ B.returnIso.hom (j 0)).symm ≪≫
    CondensedRing.upperStarCongr Λ (component_tuple_close D U₀ t G A B) ≪≫
      CondensedRing.upperStarComp Λ (j (Fin.last B.n)) Φ.hom
  exact cyclicDiagramSquare (CondensedRing.upperStar Λ Φ.hom)
    (CondensedRing.upperStar Λ B.returnIso.hom) B.n
    (fun i ↦ CondensedRing.upperStar Λ (j i)) edge close

end AlgebraicGeometry.ProEtale.CondensedGenericWeil
