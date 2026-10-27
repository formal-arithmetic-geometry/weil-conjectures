/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q158
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.Sites.RingedSitePoint
public import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Sheaf.Paper.RingedTopoiTensorSections
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.HomologicalComplex
import all Sheaf.SecSmoothPurity.CochainCompositeAlgebraic
import Sheaf.CategoryTheory.RingedSitePointScalarExtension

/-! # Stalks of tensor pullback on ringed topoi

Source: Stacks Project, Modules on Sites, Tag 05V5, lemma-pullback-stalk;
Tag 03EL, lemma-tensor-product-pullback; Sites, Tag 05V2.
(blueprint: lem-sfb-ringed-topos-pullback-stalk).

The composite point uses literal functor composition, so the comparison of set
inverse images, and hence every transported algebraic operation, is definitional.
The tensor is written with the module first and the stalk ring last.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open SheafOfModules SheafOfModules.RingedTensor
open scoped TensorProduct ChangeOfRings

namespace CategoryTheory

/-- Forget the module enhancement of a ringed-topos morphism.
Source: Stacks 05V2 (blueprint: lem-sfb-ringed-topos-pullback-stalk). -/
def RingedToposMorphism.geometric
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) :
    GeometricMorphism (Sheaf J (Type u)) (Sheaf K (Type u)) where
  inverse := f.inverse
  direct := f.direct
  adj := f.adj
  leftExact := f.leftExact

/-- The ordinary tensor with the stalk ring as its last factor; this is Mathlib's tensor.
Source: Stacks 05V5 (blueprint: lem-sfb-ringed-topos-pullback-stalk). -/
abbrev pullbackStalkTensor {A B : CommRingCat.{u}} (b : A →+* B) (M : ModuleCat.{u} A) :=
  @TensorProduct A _ M B _ _ inferInstance b.toAlgebra.toModule

/-- A pure tensor in the module-first convention.
Source: Stacks 05V5 (blueprint: lem-sfb-ringed-topos-pullback-stalk). -/
def pullbackStalkTmul {A B : CommRingCat.{u}} (b : A →+* B) (M : ModuleCat.{u} A)
    (m : M) (r : B) : pullbackStalkTensor b M :=
  @TensorProduct.tmul A _ M B _ _ inferInstance b.toAlgebra.toModule m r

/-- The action of the last factor, transported through the tensor symmetry.
Source: Stacks 05V5 (blueprint: lem-sfb-ringed-topos-pullback-stalk). -/
def pullbackStalkScale {A B : CommRingCat.{u}} (b : A →+* B) (M : ModuleCat.{u} A)
    (r : B) (x : pullbackStalkTensor b M) : pullbackStalkTensor b M :=
  letI : Algebra A B := b.toAlgebra
  TensorProduct.comm A B M (r • TensorProduct.comm A M B x)

/-- The ordinary tensor map on the first factor.
Source: Stacks 05V5 (blueprint: lem-sfb-ringed-topos-pullback-stalk). -/
def pullbackStalkTensorMap {A B : CommRingCat.{u}} (b : A →+* B)
    {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    pullbackStalkTensor b M →+ pullbackStalkTensor b N :=
  letI : Algebra A B := b.toAlgebra
  (TensorProduct.map f.hom (LinearMap.id : B →ₗ[A] B)).toAddMonoidHom

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private def compositePoint
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (g : GeometricMorphism (Sheaf J (Type u)) (Sheaf K (Type u)))
    (p : GeometricMorphism (Type u) (Sheaf J (Type u)))
    (I : AlgebraicInverseImage g.inverse S A) (a : RingedSitePoint A p) :
    RingedSitePoint S (p.comp g) := by
  let P := I.modules ⋙ a.modules
  let e : P ⋙ forget (ModuleCat.{u} a.ring) ≅
      (SheafOfModules.RingedTensor.underlying S) ⋙ (g.inverse ⋙ p.inverse) :=
    NatIso.ofComponents
      (fun M ↦ a.moduleUnderlying.app (I.modules.obj M) ≪≫
        p.inverse.mapIso (I.moduleUnderlying.app M)) (by
          intro M N h
          change (a.modules ⋙ forget (ModuleCat a.ring)).map (I.modules.map h) ≫
              a.moduleUnderlying.hom.app (I.modules.obj N) ≫
                p.inverse.map (I.moduleUnderlying.hom.app N) =
            a.moduleUnderlying.hom.app (I.modules.obj M) ≫
              p.inverse.map (I.moduleUnderlying.hom.app M) ≫
                p.inverse.map (g.inverse.map
                  ((SheafOfModules.RingedTensor.underlying S).map h))
          rw [← Category.assoc, a.moduleUnderlying.hom.naturality]
          change a.moduleUnderlying.hom.app (I.modules.obj M) ≫
              p.inverse.map ((SheafOfModules.RingedTensor.underlying A).map
                (I.modules.map h)) ≫ p.inverse.map (I.moduleUnderlying.hom.app N) = _
          rw [← p.inverse.map_comp]
          simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using
            congrArg (fun k ↦ a.moduleUnderlying.hom.app (I.modules.obj M) ≫
              p.inverse.map k) (I.moduleUnderlying.hom.naturality h))
  have hadd (M : ringedSiteModules.{u} (ringSheaf S)) (T : Sheaf K (Type u))
      (x y z : T ⟶ (SheafOfModules.RingedTensor.underlying S).obj M)
      (h : ∀ (U : Dᵒᵖ) (v : T.obj.obj U),
        (@id (M.val.obj U) (z.hom.app U v)) =
          (@id (M.val.obj U) (x.hom.app U v)) +
            (@id (M.val.obj U) (y.hom.app U v)))
      (v : (g.inverse ⋙ p.inverse).obj T) :
      (e.inv.app M) ((g.inverse ⋙ p.inverse).map z v) =
        (e.inv.app M) ((g.inverse ⋙ p.inverse).map x v) +
          (e.inv.app M) ((g.inverse ⋙ p.inverse).map y v) := by
    with_unfolding_all simpa only [e, P, id_eq, Functor.comp_obj,
      NatIso.ofComponents_inv_app, Iso.trans_inv, Functor.mapIso_inv,
      Iso.app_inv, Functor.comp_map, Functor.map_comp, types_comp_apply] using
      (a.moduleAdd (I.modules.obj M) (g.inverse.obj T)
        (g.inverse.map x ≫ I.moduleUnderlying.inv.app M)
        (g.inverse.map y ≫ I.moduleUnderlying.inv.app M)
        (g.inverse.map z ≫ I.moduleUnderlying.inv.app M)
        (I.moduleAdd M T x y z h) v)
  have hr (T : Sheaf K (Type u))
      (z : T ⟶ (sheafCompose K (forget CommRingCat.{u})).obj S)
      (v : (p.comp g).inverse.obj T) :
      (p.inverse.mapIso I.ringUnderlying ≪≫ a.ringUnderlying).hom
          ((p.comp g).inverse.map z v) =
        a.ringUnderlying.hom
          (p.inverse.map (g.inverse.map z ≫ I.ringUnderlying.hom) v) := by
    rw [p.inverse.map_comp]
    with_unfolding_all rfl
  have hm (M : ringedSiteModules.{u} (ringSheaf S)) (T : Sheaf K (Type u))
      (z : T ⟶ (SheafOfModules.RingedTensor.underlying S).obj M)
      (v : (p.comp g).inverse.obj T) :
      (e.inv.app M) ((p.comp g).inverse.map z v) =
        (a.moduleUnderlying.inv.app (I.modules.obj M))
          (p.inverse.map (g.inverse.map z ≫ I.moduleUnderlying.inv.app M) v) := by
    rw [p.inverse.map_comp]
    with_unfolding_all rfl
  refine {
    ring := a.ring
    ringUnderlying := p.inverse.mapIso I.ringUnderlying ≪≫ a.ringUnderlying
    ringAdd := ?_
    ringMul := ?_
    ringZero := ?_
    ringOne := ?_
    modules := P
    moduleUnderlying := e
    moduleAdd := hadd
    moduleZero := ?_
    moduleSMul := ?_
    modules_additive := ?_ }
  · intro T x y z h v
    exact (hr T z v).trans ((a.ringAdd (g.inverse.obj T)
      (g.inverse.map x ≫ I.ringUnderlying.hom)
      (g.inverse.map y ≫ I.ringUnderlying.hom)
      (g.inverse.map z ≫ I.ringUnderlying.hom) (I.ringAdd T x y z h) v).trans
        (congrArg₂ (· + ·) (hr T x v).symm (hr T y v).symm))
  · intro T x y z h v
    exact (hr T z v).trans ((a.ringMul (g.inverse.obj T)
      (g.inverse.map x ≫ I.ringUnderlying.hom)
      (g.inverse.map y ≫ I.ringUnderlying.hom)
      (g.inverse.map z ≫ I.ringUnderlying.hom) (I.ringMul T x y z h) v).trans
        (congrArg₂ (· * ·) (hr T x v).symm (hr T y v).symm))
  · intro T x h v
    exact (hr T x v).trans (a.ringZero (g.inverse.obj T)
      (g.inverse.map x ≫ I.ringUnderlying.hom) (I.ringZero T x h) v)
  · intro T x h v
    exact (hr T x v).trans (a.ringOne (g.inverse.obj T)
      (g.inverse.map x ≫ I.ringUnderlying.hom) (I.ringOne T x h) v)
  · intro M T x h v
    exact (hm M T x v).trans (a.moduleZero (I.modules.obj M) (g.inverse.obj T)
      (g.inverse.map x ≫ I.moduleUnderlying.inv.app M) (I.moduleZero M T x h) v)
  · intro M T r x z h v
    exact (hm M T z v).trans ((a.moduleSMul (I.modules.obj M) (g.inverse.obj T)
      (g.inverse.map r ≫ I.ringUnderlying.hom)
      (g.inverse.map x ≫ I.moduleUnderlying.inv.app M)
      (g.inverse.map z ≫ I.moduleUnderlying.inv.app M)
      (I.moduleSMul M T r x z h) v).trans
        (congrArg₂ (· • ·) (hr T r v).symm (hm M T x v).symm))
  · constructor
    intro M N h k
    ext v
    have hn (b : M ⟶ N) :
        (e.inv.app N) ((g.inverse ⋙ p.inverse).map
          ((SheafOfModules.RingedTensor.underlying S).map b) ((e.hom.app M) v)) =
          P.map b v := by
      have hh := ConcreteCategory.congr_hom (e.inv.naturality b) ((e.hom.app M) v)
      have hv : (e.inv.app M) ((e.hom.app M) v) = v :=
        ConcreteCategory.congr_hom (e.hom_inv_id_app M) v
      change (e.inv.app N) ((g.inverse ⋙ p.inverse).map
          ((SheafOfModules.RingedTensor.underlying S).map b) ((e.hom.app M) v)) =
        P.map b ((e.inv.app M) ((e.hom.app M) v)) at hh
      rw [hv] at hh
      exact hh
    have hh := hadd N ((SheafOfModules.RingedTensor.underlying S).obj M)
      ((SheafOfModules.RingedTensor.underlying S).map h)
      ((SheafOfModules.RingedTensor.underlying S).map k)
      ((SheafOfModules.RingedTensor.underlying S).map (h + k))
      (fun _ _ ↦ rfl) ((e.hom.app M) v)
    change P.map (h + k) v = P.map h v + P.map k v
    simpa only [hn] using hh

private theorem stalkPresentation
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism (ringSheaf R) (ringSheaf S)) :
    ∃ (A : Sheaf J CommRingCat.{u}) (I : AlgebraicInverseImage f.inverse S A)
      (c : A ⟶ R), (sheafCompose J (forget CommRingCat.{u})).map c =
        I.ringUnderlying.inv ≫ f.ringMap := by
  let : PreservesFiniteLimits f.inverse := f.leftExact
  let : f.inverse.Braided := Functor.Braided.ofChosenFiniteProducts f.inverse
  let A := SheafOfModules.CochainCompositeConstruction.ringImage f.inverse S
  let I := SheafOfModules.CochainCompositeConstruction.algebraicImage f.inverse S
  obtain ⟨c, hc⟩ := SheafOfModules.CochainCompositeConstruction.structuralMap
    f.inverse S R A I f.ringMap f.ring_add f.ring_mul f.ring_one
  exact ⟨A, I, c, hc⟩

set_option maxHeartbeats 800000 in
-- The dependent point presentations and explicit tensor instances need more elaboration steps.
/-- Tensor pullback has its natural, normalized, linear stalk comparison.

Source: Stacks Project, Modules on Sites, Tags 05V5 and 03EL; Sites, Tag 05V2
(blueprint: lem-sfb-ringed-topos-pullback-stalk).

Proof:
1. Composition of geometric morphisms has inverse image f.inverse followed by
p.inverse. This gives the set comparison, and applying it to every operation,
including nullary ones, gives the abelian-group and commutative-ring comparisons.
2. Construct A = f.inverse S with its transported ring operations and the algebraic
module lift I by lem-weil-pbc-geometric-module-construction. The structural map c
is f.ringMap under I.ringUnderlying; construct the normalized point presentation
at q = f composed with p by finite-product transport.
3. Apply lem-pur-independent-inverse-image-tensor-comparison to p.inverse and
A-modules R and I(M). Its generalized-section formula identifies every transported
pure pairing. No global-section generation hypothesis is used.
4. Transport the scalar-action operation through that comparison to prove R_p
linearity. The stalk of c is precisely the displayed b, by its underlying-set
normalization. Identify the inverse-image germs by composition and swap the
factors: (r tensor m)_p goes to m_q tensor r_p. The balanced relations make this
swap invertible. These constructions commute with every module morphism.
5. Apply that naturality to each differential of any cochain complex. The component
additive isomorphisms and their inverses commute with the differentials, giving
an isomorphism of complexes, without flatness or boundedness assumptions. -/
theorem RingedToposMorphism.pullback_stalk
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism (ringSheaf R) (ringSheaf S))
    (p : GeometricMorphism (Type u) (Sheaf J (Type u)))
    (s : RingedSitePoint R p) :
    ∃ (A : Sheaf J CommRingCat.{u}) (I : AlgebraicInverseImage f.inverse S A)
      (c : A ⟶ R),
      (sheafCompose J (forget CommRingCat.{u})).map c =
        I.ringUnderlying.inv ≫ f.ringMap ∧
      ∃ (t : RingedSitePoint S (p.comp f.geometric)) (b : t.ring →+* s.ring),
        (∀ x : p.inverse.obj (f.inverse.obj
            ((sheafCompose K (forget CommRingCat.{u})).obj S)),
          b (t.ringUnderlying.hom x) = s.ringUnderlying.hom (p.inverse.map f.ringMap x)) ∧
        ∃ e : ∀ M : ringedSiteModules.{u} (ringSheaf S),
          s.modules.obj (changeOfRings.{u, u, u} c (I.modules.obj M)) ≃+
            pullbackStalkTensor b (t.modules.obj M),
          (∀ (M : ringedSiteModules.{u} (ringSheaf S)) (r : s.ring)
            (x : s.modules.obj (changeOfRings.{u, u, u} c (I.modules.obj M))),
            e M (r • x) = pullbackStalkScale b (t.modules.obj M) r (e M x)) ∧
          (∀ (M N : ringedSiteModules.{u} (ringSheaf S)) (a : M ⟶ N)
            (x : s.modules.obj (changeOfRings.{u, u, u} c (I.modules.obj M))),
            e N (s.modules.map
              (changeOfRingsHom.{u, u, u} c (I.modules.obj M) (I.modules.map a)) x) =
              pullbackStalkTensorMap b (t.modules.map a) (e M x)) ∧
          (∀ (M : ringedSiteModules.{u} (ringSheaf S)) (T : Sheaf J (Type u))
            (r : T ⟶ (sheafCompose J (forget CommRingCat.{u})).obj R)
            (m : T ⟶ (SheafOfModules.RingedTensor.underlying A).obj (I.modules.obj M))
            (z : T ⟶ (SheafOfModules.RingedTensor.underlying R).obj
              (changeOfRings.{u, u, u} c (I.modules.obj M))),
            (∀ (W : Cᵒᵖ) (x : T.obj.obj W),
              z.hom.app W x = ((PresheafOfModules.sheafificationAdjunction.{u, u, u, u}
                (𝟙 (ringSheaf R).obj)).unit.app
                  (changeOfRingsPresheaf.{u, u, u} c (I.modules.obj M))).app W
                    ((@id (R.obj.obj W) (r.hom.app W x))
                      ⊗ₜ[A.obj.obj W, (c.hom.app W).hom]
                        (@id ((I.modules.obj M).val.obj W) (m.hom.app W x)))) →
            ∀ x : p.inverse.obj T,
              e M ((s.moduleUnderlying.inv.app
                (changeOfRings.{u, u, u} c (I.modules.obj M))) (p.inverse.map z x)) =
                pullbackStalkTmul b (t.modules.obj M)
                  ((t.moduleUnderlying.inv.app M)
                    (p.inverse.map (m ≫ I.moduleUnderlying.hom.app M) x))
                  (s.ringUnderlying.hom (p.inverse.map r x))) ∧
          ∀ (L : CochainComplex (ringedSiteModules.{u} (ringSheaf S)) ℤ)
            (i j : ℤ) (x : s.modules.obj (changeOfRings.{u, u, u} c (I.modules.obj (L.X i)))),
            e (L.X j) (s.modules.map
              (changeOfRingsHom.{u, u, u} c (I.modules.obj (L.X i)) (I.modules.map (L.d i j))) x) =
                pullbackStalkTensorMap b (t.modules.map (L.d i j)) (e (L.X i) x) := by
  obtain ⟨A, I, c, hc⟩ := stalkPresentation R S f
  obtain ⟨a⟩ := RingedSitePoint.nonempty A p
  obtain ⟨b, hb, e, hs, hn, hp⟩ := RingedSitePoint.scalarExtension A R c p a s
  let t := compositePoint A S f.geometric p I a
  refine ⟨A, I, c, hc, t, b, ?_, (fun M ↦ e (I.modules.obj M)), ?_, ?_, ?_, ?_⟩
  · intro x
    change b (a.ringUnderlying.hom (p.inverse.map I.ringUnderlying.hom x)) = _
    rw [hb]
    have hmap : I.ringUnderlying.hom ≫
        (sheafCompose J (forget CommRingCat.{u})).map c = f.ringMap := by
      rw [hc, ← Category.assoc, I.ringUnderlying.hom_inv_id, Category.id_comp]
    have hmp : p.inverse.map I.ringUnderlying.hom ≫
        p.inverse.map ((sheafCompose J (forget CommRingCat.{u})).map c) =
          p.inverse.map f.ringMap := by
      rw [← p.inverse.map_comp, hmap]
    have hx := ConcreteCategory.congr_hom hmp x
    exact congrArg s.ringUnderlying.hom hx
  · intro M r x
    exact hs (I.modules.obj M) r x
  · intro M N h x
    exact hn (I.modules.obj M) (I.modules.obj N) (I.modules.map h) x
  · intro M T r m z hz x
    have h := hp (I.modules.obj M) T r m z hz x
    have hmx : p.inverse.map (I.moduleUnderlying.inv.app M)
        (p.inverse.map (m ≫ I.moduleUnderlying.hom.app M) x) = p.inverse.map m x := by
      rw [p.inverse.map_comp]
      exact (p.inverse.mapIso (I.moduleUnderlying.app M)).hom_inv_id_apply
        (p.inverse.map m x)
    change e (I.modules.obj M) _ =
      @TensorProduct.tmul a.ring _ (a.modules.obj (I.modules.obj M)) s.ring _ _
        inferInstance b.toAlgebra.toModule
        ((a.moduleUnderlying.inv.app (I.modules.obj M))
          (p.inverse.map (I.moduleUnderlying.inv.app M)
            (p.inverse.map (m ≫ I.moduleUnderlying.hom.app M) x)))
        (s.ringUnderlying.hom (p.inverse.map r x))
    rw [hmx]
    exact h
  · intro L i j x
    exact hn (I.modules.obj (L.X i)) (I.modules.obj (L.X j)) (I.modules.map (L.d i j)) x

end CategoryTheory
