/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraCyclicChain
public import WeilConjectures.SixFunctors.ProEtale.Adic.PullbackStrCompat
public import WeilConjectures.WeilSheaf.CondensedModelWeilCoherence

/-!
# Cyclic decompositions of `ℓ`-adic sheaves by pullbacks

A cyclic decomposition of `ℓ`-adic sheaves on `W` by the pullbacks along pieces `jᵢ : Z ⟶ W`,
permuted by an automorphism `φ` of `W` up to an automorphism `ψ` of `Z`
(`AlgebraicGeometry.ProEtale.adicCyclicDecomposition`), and the computation of the first piece
of a pulled-back sheaf `p^* H` with its canonical Weil structure: if all pieces lie over `q`, it is
`q^* H` with its canonical Weil structure
(`AlgebraicGeometry.ProEtale.adicCyclicDecompositionFunctorObjIso`).
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

noncomputable section

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type*} [Category C] {D : Type*} [Category D] {G : D ⥤ D}

/-- The underlying object of `functorOfNatIso P s` at `c` is `P c`. -/
lemma functorOfNatIso_obj_carrier (P : C ⥤ D) (s : P ⋙ G ≅ P) (c : C) :
    ((functorOfNatIso P s).obj c).carrier = P.obj c :=
  rfl

/-- The structure morphism of `functorOfNatIso P s` at `c` is `s_c`. -/
lemma functorOfNatIso_obj_str_hom_heq (P : C ⥤ D) (s : P ⋙ G ≅ P) (c : C) :
    HEq ((functorOfNatIso P s).obj c).str.hom (s.hom.app c) :=
  HEq.rfl

end CategoryTheory.Endofunctor.IsoAlgebra

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]


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


/-- The identification `β` of the last piece of `adicCyclicDecomposition`. -/
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
    (hs : HEq A.str.hom ((pullbackStrIso φ p hφ).hom.app H)) :
    (adicCyclicDecomposition φ ψ j hj hlast ff es).functor.obj A ≅
      IsoAlgebra.mk ((q)^*ᵃ[l].obj H) ((pullbackStrIso ψ q hψ).app H) :=
  (adicCyclicDecomposition φ ψ j hj hlast ff es).functorObjIsoMk A
    (fun i ↦ eqToIso (congrArg (j i)^*ᵃ[l].obj hA) ≪≫ (adicUpperStarFactorApp l (hjq i) H).symm)
    (fun k ↦ pullbackStr_compat_of_eq l φ p hφ _ _ q (hj k) (hjq _) (hjq _) H _ hA _ hs)
    ((pullbackStrIso ψ q hψ).app H)
    (pullbackStr_compat_β l φ ψ p q hφ hψ _ _ hlast (hjq _) (hjq 0) H _ _ rfl rfl _
      (heq_of_eq (adicCyclicDecomposition_β φ ψ j hj hlast ff es)) _ hA _ hs _ HEq.rfl _ HEq.rfl)

/-- **The first piece of a pulled-back sheaf** `p^* H` with its canonical Weil structure, for
`adicCyclicDecomposition`: if all the pieces lie over `q`, it is `q^* H` with its canonical Weil
structure. -/
def adicCyclicDecompositionFunctorObjPullbackIso {Z W S : Scheme.{u}} (φ : W ≅ W) (ψ : Z ≅ Z)
    {m : ℕ} (j : Fin (m + 1) → (Z ⟶ W)) (hj : ∀ k : Fin m, j k.castSucc ≫ φ.hom = j k.succ)
    (hlast : j (Fin.last m) ≫ φ.hom = ψ.hom ≫ j 0)
    (ff : (Functor.pi' fun i ↦ (j i)^*ᵃ[l]).FullyFaithful)
    (es : (Functor.pi' fun i ↦ (j i)^*ᵃ[l]).EssSurj) (p : W ⟶ S) (q : Z ⟶ S)
    (hφ : φ.hom ≫ p = p) (hψ : ψ.hom ≫ q = q) (hjq : ∀ i, j i ≫ p = q) (H : AdicSheaf l S) :
    (adicCyclicDecomposition φ ψ j hj hlast ff es).functor.obj
        ((IsoAlgebra.functorOfNatIso (p)^*ᵃ[l] (pullbackStrIso φ p hφ)).obj H) ≅
      IsoAlgebra.mk ((q)^*ᵃ[l].obj H) ((pullbackStrIso ψ q hψ).app H) :=
  adicCyclicDecompositionFunctorObjIso φ ψ j hj hlast ff es p q hφ hψ hjq H _
    (IsoAlgebra.functorOfNatIso_obj_carrier _ _ H)
    (IsoAlgebra.functorOfNatIso_obj_str_hom_heq _ _ H)

end AlgebraicGeometry.ProEtale
