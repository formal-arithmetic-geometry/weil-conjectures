/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraCyclicChain
public import WeilConjectures.SixFunctors.ProEtale.Adic.UpperStarFactor
public import WeilConjectures.WeilSheaf.ConstantFieldEquivalence
public import WeilConjectures.WeilSheaf.GeometricFiberPullback

/-!
# Pulled-back Weil sheaves over a smaller base field

Let `k₀ ⊆ k'` be finite fields with `[k' : k₀] = m + 1` and `V` a `k'`-scheme, regarded also as a
`k₀`-scheme, with projections `p₀ : V̄₀ ⟶ V` and `p' : V̄' ⟶ V` of its geometric fibres over `k₀`
and over `k'`. The equivalence `ProEtaleWeilSheaf.constantFieldFunctor` between pro-étale Weil
sheaves relative to `k₀` and relative to `k'` takes the pullback `p₀^* H` of an `ℓ`-adic sheaf `H`
on `V`, with its canonical Weil structure, to `p'^* H` with its canonical Weil structure
(`AlgebraicGeometry.ProEtaleWeilSheaf.constantFieldFunctorObjGeometricFiberPullbackIso`): the
pieces `jᵢ^* p₀^* H` are all identified with `(jᵢ ≫ p₀)^* H = p'^* H`, compatibly with the Weil
structures by the associativity of the factorisation isomorphisms of pullbacks.
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

noncomputable section

namespace AlgebraicGeometry

open ProEtale

namespace ProEtaleWeilSheaf

variable {k₀ k' : Type u} [Field k₀] [Field k'] [Finite k₀] [Finite k'] [Algebra k₀ k']
  (l : ℕ) [Fact l.Prime] {V : Scheme.{u}} [V.Over (Spec (CommRingCat.of k₀))]
  [V.Over (Spec (CommRingCat.of k'))]
  (hc : (V ↘ Spec (CommRingCat.of k')) ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k')) =
    V ↘ Spec (CommRingCat.of k₀))
  {m : ℕ} (hm : Module.finrank k₀ k' = m + 1)

/-- The pieces `jᵢ : V̄' ⟶ V̄₀` lie over `V`. -/
lemma pieceMap_comp_geometricFiberProj (i : Fin (m + 1)) :
    pieceMap hc i ≫ (V ↘ Spec (CommRingCat.of k₀)).geometricFiberProj =
      (V ↘ Spec (CommRingCat.of k')).geometricFiberProj := by
  rw [pieceMap, Category.assoc, Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj]
  exact Scheme.Hom.geometricFiberComponentMap_comp_geometricFiberProj _ _ hc

/-- The identification `a^* p^* H ≅ q^* H` along a piece `a` with `a ≫ p = q` is compatible with
the Weil structure `φ^* p^* H ≅ p^* H` and the identification `φ^* ⋙ a^* ≅ b^*` for
`a ≫ φ = b`. -/
lemma compat_generic {Z W S : Scheme.{u}} (φ : W ≅ W) (p : W ⟶ S) (hφ : φ.hom ≫ p = p)
    (a b : Z ⟶ W) (q : Z ⟶ S) (hab : a ≫ φ.hom = b) (ha : a ≫ p = q) (hb : b ≫ p = q)
    (H : AdicSheaf l S) :
    (a)^*ᵃ[l].map ((adicUpperStarIsoLowerStarInv l φ).inv.app ((p)^*ᵃ[l].obj H) ≫
        (adicUpperStarFactorApp l hφ H).inv) ≫ (adicUpperStarFactorApp l ha H).inv =
    (a)^*ᵃ[l].map ((adicUpperStarIsoLowerStarInv l φ).inv.app ((p)^*ᵃ[l].obj H)) ≫
      (adicUpperStarComp l a φ.hom).inv.app ((p)^*ᵃ[l].obj H) ≫
      (adicUpperStarCongr l hab).hom.app ((p)^*ᵃ[l].obj H) ≫
        (adicUpperStarFactorApp l hb H).inv := by
  simp only [adicUpperStarFactorApp_inv]
  rw [← adicUpperStarFactor_inv_app_assoc, Functor.map_comp, Category.assoc,
    map_adicUpperStarFactor_inv_app_comp_inv_app hφ ha hab hb]

/-- The last-piece version of `compat_generic`, for `a ≫ φ = ψ ≫ j`. -/
lemma compat_generic_last {Z W S : Scheme.{u}} (φ : W ≅ W) (ψ : Z ≅ Z) (p : W ⟶ S) (q : Z ⟶ S)
    (hφ : φ.hom ≫ p = p) (hψ : ψ.hom ≫ q = q) (a j : Z ⟶ W) (h : a ≫ φ.hom = ψ.hom ≫ j)
    (ha : a ≫ p = q) (hj : j ≫ p = q) (H : AdicSheaf l S) :
    (a)^*ᵃ[l].map ((adicUpperStarIsoLowerStarInv l φ).inv.app ((p)^*ᵃ[l].obj H) ≫
        (adicUpperStarFactorApp l hφ H).inv) ≫ (adicUpperStarFactorApp l ha H).inv =
    (a)^*ᵃ[l].map ((adicUpperStarIsoLowerStarInv l φ).inv.app ((p)^*ᵃ[l].obj H)) ≫
      (adicUpperStarComp l a φ.hom).inv.app ((p)^*ᵃ[l].obj H) ≫
      (adicUpperStarCongr l h).hom.app ((p)^*ᵃ[l].obj H) ≫
      (adicUpperStarComp l ψ.hom j).hom.app ((p)^*ᵃ[l].obj H) ≫
      (adicUpperStarIsoLowerStarInv l ψ).hom.app ((j)^*ᵃ[l].obj ((p)^*ᵃ[l].obj H)) ≫
      (ψ.inv)_*ᵃ[l].map (adicUpperStarFactorApp l hj H).inv ≫
      (adicUpperStarIsoLowerStarInv l ψ).inv.app ((q)^*ᵃ[l].obj H) ≫
        (adicUpperStarFactorApp l hψ H).inv := by
  have e' : (ψ.hom ≫ j) ≫ p = q := by rw [Category.assoc, hj, hψ]
  simp only [adicUpperStarFactorApp_inv]
  rw [← adicUpperStarFactor_inv_app_assoc, ← adicUpperStarFactor_rfl, Functor.map_comp]
  simp only [Category.assoc]
  rw [← (adicUpperStarIsoLowerStarInv l ψ).hom.naturality_assoc, Iso.hom_inv_id_app_assoc,
    map_adicUpperStarFactor_inv_app_comp_inv_app hj hψ rfl e', Iso.hom_inv_id_app_assoc,
    map_adicUpperStarFactor_inv_app_comp_inv_app hφ ha h e']

variable {l} in
/-- A cyclic decomposition of `ℓ`-adic sheaves on `W` by pullbacks along `jᵢ : Z ⟶ W`, permuted
by the automorphism `φ` of `W` up to the automorphism `ψ` of `Z`: the general shape of
`AlgebraicGeometry.ProEtaleWeilSheaf.cyclicDecomposition`. -/
def adicCyclicDecomposition {Z W : Scheme.{u}} (φ : W ≅ W) (ψ : Z ≅ Z) {m : ℕ}
    (j : Fin (m + 1) → (Z ⟶ W)) (hj : ∀ k : Fin m, j k.castSucc ≫ φ.hom = j k.succ)
    (hlast : j (Fin.last m) ≫ φ.hom = ψ.hom ≫ j 0)
    (ff : (Functor.pi' fun i ↦ (j i)^*ᵃ[l]).FullyFaithful)
    (es : (Functor.pi' fun i ↦ (j i)^*ᵃ[l]).EssSurj) :
    IsoAlgebra.CyclicDecomposition ((φ.inv)_*ᵃ[l]) ((ψ.inv)_*ᵃ[l]) m where
  J i := (j i)^*ᵃ[l]
  α k := Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l φ).symm _ ≪≫
    (adicUpperStarComp l _ _).symm ≪≫ adicUpperStarCongr l (hj k)
  β := Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l φ).symm _ ≪≫
    (adicUpperStarComp l _ _).symm ≪≫ adicUpperStarCongr l hlast ≪≫
    adicUpperStarComp l _ _ ≪≫ Functor.isoWhiskerLeft _ (adicUpperStarIsoLowerStarInv l ψ)
  fullyFaithful := ff
  essSurj := es

variable {l} in
/-- The canonical Weil structure `φ^* p^* H ≅ (φ ≫ p)^* H = p^* H` for `φ ≫ p = p`, in the
pushforward convention `φ^* = (φ⁻¹)_*`. -/
noncomputable def pullbackStrIsoApp {W S : Scheme.{u}} (φ : W ≅ W) (p : W ⟶ S)
    (hφ : φ.hom ≫ p = p) (H : AdicSheaf l S) :
    (φ.inv)_*ᵃ[l].obj ((p)^*ᵃ[l].obj H) ≅ (p)^*ᵃ[l].obj H :=
  ((adicUpperStarIsoLowerStarInv l φ).app ((p)^*ᵃ[l].obj H)).symm ≪≫
    (adicUpperStarFactorApp l hφ H).symm

/-- The structure morphism of `IsoAlgebra.mk a Φ` is `Φ`. -/
lemma _root_.CategoryTheory.Endofunctor.IsoAlgebra.mk_str_hom {C : Type*} [Category C]
    {F : C ⥤ C} (a : C) (Φ : F.obj a ≅ a) : (IsoAlgebra.mk a Φ).str.hom = Φ.hom :=
  rfl

lemma pullbackStrIsoApp_hom {W S : Scheme.{u}} (φ : W ≅ W) (p : W ⟶ S) (hφ : φ.hom ≫ p = p)
    (H : AdicSheaf l S) :
    (pullbackStrIsoApp φ p hφ H).hom =
      (adicUpperStarIsoLowerStarInv l φ).inv.app ((p)^*ᵃ[l].obj H) ≫
        (adicUpperStarFactorApp l hφ H).inv :=
  rfl

lemma β_hom_app {Z W : Scheme.{u}} (φ : W ≅ W) (ψ : Z ≅ Z) (a j : Z ⟶ W)
    (h : a ≫ φ.hom = ψ.hom ≫ j) (X : AdicSheaf l W) :
    (Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l φ).symm (a)^*ᵃ[l] ≪≫
        (adicUpperStarComp l a φ.hom).symm ≪≫ adicUpperStarCongr l h ≪≫
        adicUpperStarComp l ψ.hom j ≪≫
        Functor.isoWhiskerLeft (j)^*ᵃ[l] (adicUpperStarIsoLowerStarInv l ψ)).hom.app X =
    (a)^*ᵃ[l].map ((adicUpperStarIsoLowerStarInv l φ).inv.app X) ≫
      (adicUpperStarComp l a φ.hom).inv.app X ≫ (adicUpperStarCongr l h).hom.app X ≫
      (adicUpperStarComp l ψ.hom j).hom.app X ≫
      (adicUpperStarIsoLowerStarInv l ψ).hom.app ((j)^*ᵃ[l].obj X) :=
  rfl

/-- `compat_generic_last` in the form of the compatibility with `β` of
`CategoryTheory.Endofunctor.IsoAlgebra.CyclicDecomposition.functorObjIsoMk`. -/
lemma compat_generic_last' {Z W S : Scheme.{u}} (φ : W ≅ W) (ψ : Z ≅ Z) (p : W ⟶ S)
    (q : Z ⟶ S) (hφ : φ.hom ≫ p = p) (hψ : ψ.hom ≫ q = q) (a j : Z ⟶ W)
    (h : a ≫ φ.hom = ψ.hom ≫ j) (ha : a ≫ p = q) (hj : j ≫ p = q) (H : AdicSheaf l S) :
    (a)^*ᵃ[l].map (pullbackStrIsoApp φ p hφ H).hom ≫ (adicUpperStarFactorApp l ha H).symm.hom =
    (Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l φ).symm (a)^*ᵃ[l] ≪≫
        (adicUpperStarComp l a φ.hom).symm ≪≫ adicUpperStarCongr l h ≪≫
        adicUpperStarComp l ψ.hom j ≪≫
        Functor.isoWhiskerLeft (j)^*ᵃ[l] (adicUpperStarIsoLowerStarInv l ψ)).hom.app
          ((p)^*ᵃ[l].obj H) ≫
      (ψ.inv)_*ᵃ[l].map (adicUpperStarFactorApp l hj H).symm.hom ≫
      (pullbackStrIsoApp ψ q hψ H).hom := by
  rw [pullbackStrIsoApp_hom, pullbackStrIsoApp_hom, β_hom_app, Iso.symm_hom, Iso.symm_hom]
  simp only [Category.assoc]
  exact compat_generic_last l φ ψ p q hφ hψ a j h ha hj H

/-- `compat_generic` for an object `X = p^* H` and a Weil structure `s` given up to these
identifications. -/
lemma compat_generic_of_eq {Z W S : Scheme.{u}} (φ : W ≅ W) (p : W ⟶ S) (hφ : φ.hom ≫ p = p)
    (a b : Z ⟶ W) (q : Z ⟶ S) (hab : a ≫ φ.hom = b) (ha : a ≫ p = q) (hb : b ≫ p = q)
    (H : AdicSheaf l S) (X : AdicSheaf l W) (hX : X = (p)^*ᵃ[l].obj H)
    (s : (φ.inv)_*ᵃ[l].obj X ⟶ X) (hs : HEq s (pullbackStrIsoApp φ p hφ H).hom) :
    (a)^*ᵃ[l].map s ≫
        (eqToIso (congrArg (a)^*ᵃ[l].obj hX) ≪≫ (adicUpperStarFactorApp l ha H).symm).hom =
      (Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l φ).symm (a)^*ᵃ[l] ≪≫
        (adicUpperStarComp l a φ.hom).symm ≪≫ adicUpperStarCongr l hab).hom.app X ≫
      (eqToIso (congrArg (b)^*ᵃ[l].obj hX) ≪≫ (adicUpperStarFactorApp l hb H).symm).hom := by
  subst hX
  obtain rfl := eq_of_heq hs
  simp only [eqToIso_refl, Iso.refl_trans, Iso.symm_hom, pullbackStrIsoApp_hom, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.app_inv,
    Category.assoc]
  exact compat_generic l φ p hφ a b q hab ha hb H

/-- `compat_generic_last'` for an object `X = p^* H` and a Weil structure `s` given up to these
identifications. -/
lemma compat_generic_last_of_eq {Z W S : Scheme.{u}} (φ : W ≅ W) (ψ : Z ≅ Z) (p : W ⟶ S)
    (q : Z ⟶ S) (hφ : φ.hom ≫ p = p) (hψ : ψ.hom ≫ q = q) (a j : Z ⟶ W)
    (h : a ≫ φ.hom = ψ.hom ≫ j) (ha : a ≫ p = q) (hj : j ≫ p = q) (H : AdicSheaf l S)
    (X : AdicSheaf l W) (hX : X = (p)^*ᵃ[l].obj H)
    (s : (φ.inv)_*ᵃ[l].obj X ⟶ X) (hs : HEq s (pullbackStrIsoApp φ p hφ H).hom) :
    (a)^*ᵃ[l].map s ≫
        (eqToIso (congrArg (a)^*ᵃ[l].obj hX) ≪≫ (adicUpperStarFactorApp l ha H).symm).hom =
    (Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l φ).symm (a)^*ᵃ[l] ≪≫
        (adicUpperStarComp l a φ.hom).symm ≪≫ adicUpperStarCongr l h ≪≫
        adicUpperStarComp l ψ.hom j ≪≫
        Functor.isoWhiskerLeft (j)^*ᵃ[l] (adicUpperStarIsoLowerStarInv l ψ)).hom.app X ≫
      (ψ.inv)_*ᵃ[l].map
        (eqToIso (congrArg (j)^*ᵃ[l].obj hX) ≪≫ (adicUpperStarFactorApp l hj H).symm).hom ≫
      (pullbackStrIsoApp ψ q hψ H).hom := by
  subst hX
  obtain rfl := eq_of_heq hs
  simp only [eqToIso_refl, Iso.refl_trans]
  exact compat_generic_last' l φ ψ p q hφ hψ a j h ha hj H

/-- The compatibility with `β` of
`CategoryTheory.Endofunctor.IsoAlgebra.CyclicDecomposition.functorObjIsoMk`, with all the data
of the decomposition given up to equality. -/
lemma compat_β {Z W S : Scheme.{u}} (φ : W ≅ W) (ψ : Z ≅ Z) (p : W ⟶ S)
    (q : Z ⟶ S) (hφ : φ.hom ≫ p = p) (hψ : ψ.hom ≫ q = q) (a j : Z ⟶ W)
    (h : a ≫ φ.hom = ψ.hom ≫ j) (ha : a ≫ p = q) (hj : j ≫ p = q) (H : AdicSheaf l S)
    (Jl J0 : AdicSheaf l W ⥤ AdicSheaf l Z) (hJl : Jl = (a)^*ᵃ[l]) (hJ0 : J0 = (j)^*ᵃ[l])
    (Φ : (φ.inv)_*ᵃ[l] ⋙ Jl ≅ J0 ⋙ (ψ.inv)_*ᵃ[l])
    (hΦ : HEq Φ (Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l φ).symm (a)^*ᵃ[l] ≪≫
        (adicUpperStarComp l a φ.hom).symm ≪≫ adicUpperStarCongr l h ≪≫
        adicUpperStarComp l ψ.hom j ≪≫
        Functor.isoWhiskerLeft (j)^*ᵃ[l] (adicUpperStarIsoLowerStarInv l ψ)))
    (X : AdicSheaf l W) (hX : X = (p)^*ᵃ[l].obj H)
    (s : (φ.inv)_*ᵃ[l].obj X ⟶ X) (hs : HEq s (pullbackStrIsoApp φ p hφ H).hom)
    (cl : Jl.obj X ≅ (q)^*ᵃ[l].obj H)
    (hcl : HEq cl (eqToIso (congrArg (a)^*ᵃ[l].obj hX) ≪≫ (adicUpperStarFactorApp l ha H).symm))
    (c0 : J0.obj X ≅ (q)^*ᵃ[l].obj H)
    (hc0 : HEq c0 (eqToIso (congrArg (j)^*ᵃ[l].obj hX) ≪≫ (adicUpperStarFactorApp l hj H).symm)) :
    Jl.map s ≫ cl.hom = Φ.hom.app X ≫ (ψ.inv)_*ᵃ[l].map c0.hom ≫
      (pullbackStrIsoApp ψ q hψ H).hom := by
  subst hJl hJ0
  obtain rfl := eq_of_heq hΦ
  obtain rfl := eq_of_heq hcl
  obtain rfl := eq_of_heq hc0
  exact compat_generic_last_of_eq l φ ψ p q hφ hψ a j h ha hj H X hX s hs

variable {l} in
lemma adicCyclicDecomposition_β {Z W : Scheme.{u}} (φ : W ≅ W) (ψ : Z ≅ Z) {m : ℕ}
    (j : Fin (m + 1) → (Z ⟶ W)) (hj : ∀ k : Fin m, j k.castSucc ≫ φ.hom = j k.succ)
    (hlast : j (Fin.last m) ≫ φ.hom = ψ.hom ≫ j 0)
    (ff : (Functor.pi' fun i ↦ (j i)^*ᵃ[l]).FullyFaithful)
    (es : (Functor.pi' fun i ↦ (j i)^*ᵃ[l]).EssSurj) :
    (adicCyclicDecomposition φ ψ j hj hlast ff es).β =
      Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l φ).symm (j (Fin.last m))^*ᵃ[l] ≪≫
        (adicUpperStarComp l (j (Fin.last m)) φ.hom).symm ≪≫ adicUpperStarCongr l hlast ≪≫
        adicUpperStarComp l ψ.hom (j 0) ≪≫
        Functor.isoWhiskerLeft (j 0)^*ᵃ[l] (adicUpperStarIsoLowerStarInv l ψ) :=
  rfl

variable {l} in
/-- **The first piece of a pulled-back sheaf** for `adicCyclicDecomposition`: if all the pieces
`jᵢ` lie over `q`, then the first piece of a Weil sheaf `A` isomorphic to `p^* H` with its
canonical Weil structure is `q^* H` with its canonical Weil structure. -/
def adicCyclicDecompositionFunctorObjIso {Z W S : Scheme.{u}} (φ : W ≅ W) (ψ : Z ≅ Z) {m : ℕ}
    (j : Fin (m + 1) → (Z ⟶ W)) (hj : ∀ k : Fin m, j k.castSucc ≫ φ.hom = j k.succ)
    (hlast : j (Fin.last m) ≫ φ.hom = ψ.hom ≫ j 0)
    (ff : (Functor.pi' fun i ↦ (j i)^*ᵃ[l]).FullyFaithful)
    (es : (Functor.pi' fun i ↦ (j i)^*ᵃ[l]).EssSurj) (p : W ⟶ S) (q : Z ⟶ S)
    (hφ : φ.hom ≫ p = p) (hψ : ψ.hom ≫ q = q) (hjq : ∀ i, j i ≫ p = q) (H : AdicSheaf l S)
    (A : IsoAlgebra ((φ.inv)_*ᵃ[l])) (hA : A.carrier = (p)^*ᵃ[l].obj H)
    (hs : HEq A.str.hom (pullbackStrIsoApp φ p hφ H).hom) :
    (adicCyclicDecomposition φ ψ j hj hlast ff es).functor.obj A ≅
      IsoAlgebra.mk ((q)^*ᵃ[l].obj H) (pullbackStrIsoApp ψ q hψ H) :=
  (adicCyclicDecomposition φ ψ j hj hlast ff es).functorObjIsoMk A
    (fun i ↦ eqToIso (congrArg (j i)^*ᵃ[l].obj hA) ≪≫ (adicUpperStarFactorApp l (hjq i) H).symm)
    (fun k ↦ compat_generic_of_eq l φ p hφ _ _ q (hj k) (hjq _) (hjq _) H _ hA _ hs)
    (pullbackStrIsoApp ψ q hψ H)
    (compat_β l φ ψ p q hφ hψ _ _ hlast (hjq _) (hjq 0) H _ _ rfl rfl _
      (heq_of_eq (adicCyclicDecomposition_β φ ψ j hj hlast ff es)) _ hA _ hs _ HEq.rfl _ HEq.rfl)

variable (k₀ V) in
/-- The Weil structure of `p₀^* H` is `pullbackStrIsoApp`. -/
lemma geometricFiberPullbackFrobeniusIso_app_hom (H : AdicSheaf l V) :
    ((geometricFiberPullbackFrobeniusIso k₀ l V).app H).hom =
      (pullbackStrIsoApp (V ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius _
        (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _) H).hom := by
  rw [pullbackStrIsoApp_hom, adicUpperStarFactorApp_inv, adicUpperStarFactor_inv_app]
  simp only [geometricFiberPullbackFrobeniusIso, Iso.app_hom, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom]

/-- **The constant field equivalence takes `p₀^* H` to `p'^* H`**, with their canonical Weil
structures. -/
def constantFieldFunctorObjGeometricFiberPullbackIso (H : AdicSheaf l V) :
    (constantFieldFunctor l hc hm).obj ((geometricFiberPullback k₀ l V).obj H) ≅
      (geometricFiberPullback k' l V).obj H :=
  adicCyclicDecompositionFunctorObjIso _ _ (pieceMap hc) (pieceMap_comp_frobenius hc)
    (pieceMap_last_comp_frobenius hc hm) (cyclicDecomposition l hc hm).fullyFaithful
    (cyclicDecomposition l hc hm).essSurj _ _
    (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _)
    (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _)
    (pieceMap_comp_geometricFiberProj hc) H _ (geometricFiberPullback_obj_carrier k₀ l V H)
    (by rw [geometricFiberPullback_obj_str]
        exact heq_of_eq (geometricFiberPullbackFrobeniusIso_app_hom k₀ l V H)) ≪≫
    IsoAlgebra.isoMk (Iso.refl _) (by
      have e := congrArg Iso.hom (geometricFiberPullback_obj_str k' l V H)
      rw [geometricFiberPullbackFrobeniusIso_app_hom] at e
      simp only [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
      exact e.symm)

end ProEtaleWeilSheaf

end AlgebraicGeometry
