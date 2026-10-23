/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.BaseChange.Coherence
public import WeilConjectures.TraceFormula.BaseChange.Iterate
public import WeilConjectures.TraceFormula.BaseChange.WeilObject

/-!

# Local traces of the base change of a Weil object

Let `k` be a finite field, `Ω ⊇ k` a separably closed field, `X` a separated scheme of finite type
over `Spec k`, `e` an automorphism of `X` over `Spec k` and `σ` an automorphism of `Spec Ω` inverse
to the `#k ^ N`-power Frobenius of `Spec Ω`. For a geometric point `x̄ : Spec Ω ⟶ X` over `Spec k`
with `x̄ ≫ e = σ ≫ x̄`, the rational point `x̄' = (x̄, 𝟙)` of `X̄ = X ×_k Ω` is fixed by the model
Frobenius `Φ = (e ≫ F_X^N) ×_k Ω` (`geometricBaseChangePoint_comp_modelFrobenius_eq_iff`). This
file compares, for a Weil object `L` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for `e`:

* the Frobenius of the stalk at `x̄` of the Weil sheaf `Hʲ(L)`, for the twisted Frobenius `σ`
  (`WeilSheaf.stalkFunctor`), and
* the `j`-th homology of the local Frobenius at `x̄'` of the base change `Lπ^* L`, a Weil object
  for the model Frobenius `Φ` (`weilStalk`, `weilGeometricBaseChange`).

They are conjugate, so they have the same trace
(`ProEtale.CondensedRing.categoricalTrace_stalkFunctor_eq_categoricalTrace_homology_weilStalk`).
The formal part is `homology_modelFrobenius_comp_eq_aux`; this file identifies the two Frobenii
with its abstract composites.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.ObjectProperty.FullSubcategory

variable {C : Type*} [Category C] {P : ObjectProperty C}

/-- The underlying morphism of `eqToHom` in a full subcategory is `eqToHom`. -/
lemma eqToHom_hom' {X Y : P.FullSubcategory} (h : X = Y) :
    (eqToHom h).hom = eqToHom (congrArg ObjectProperty.FullSubcategory.obj h) := by
  subst h
  rfl

end CategoryTheory.ObjectProperty.FullSubcategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {Ω : Type u} [Field Ω] [Algebra k Ω] [Fact (ringChar Ω).Prime]
  [Fact (ringChar Ω ≠ ℓ)]
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (N : ℕ) (g : X ⟶ X)

/-! ### The model Frobenius -/

section Model

omit [Finite k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] [Fact ℓ.Prime] in
/-- On the ambient derived categories, the composition isomorphism of the derived pullbacks on
bounded constructible complexes, with its source written through `f.left ≫ g.left`. -/
lemma boundedConstructibleUpperStarComp_hom_app_hom_eq {S : Type u} [Field S]
    [Fact (ringChar S).Prime] [Fact (ringChar S ≠ ℓ)] [Fact ℓ.Prime]
    {A B C : Over (Spec (.of S))} [LocallyOfFiniteType A.hom] [QuasiCompact A.hom]
    [IsSeparated A.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    (f : A ⟶ B) (g : B ⟶ C) (K : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g).hom.app K).hom =
      eqToHom (show ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (f ≫ g)).obj K).obj =
        L((f.left ≫ g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj K.obj from rfl) ≫
        (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) f.left g.left).hom.app K.obj := by
  rw [eqToHom_refl, Category.id_comp]
  exact boundedConstructibleUpperStarComp_hom_app_hom _ ℓ f g K

variable {X N g} in
omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Fact (ringChar Ω).Prime]
  [Fact (ringChar Ω ≠ ℓ)] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [Finite k] [Fact ℓ.Prime] in
/-- A rational point fixed by the model Frobenius, on the underlying schemes. -/
lemma left_comp_modelFrobenius_left [Finite k]
    {x' : RationalPoint ((geometricBaseChange k Ω).obj X)}
    (hx' : x' ≫ modelFrobenius Ω X N g = x') :
    x'.left ≫ (modelFrobenius Ω X N g).left = x'.left :=
  (Over.comp_left _ _ _ x' (modelFrobenius Ω X N g)).symm.trans (congrArg Over.Hom.left hx')


variable {X N g} in
/-- The local Frobenius at a rational point `x̄'` fixed by the model Frobenius `Φ` of the base
change of `(a, ψ)`, as an explicit composite on `Dᵇc(Spec Ω)⟦ℚ̲̄_ℓ⟧`:
`Lx̄'^* Lπ^* a = L(x̄' ≫ Φ)^* Lπ^* a ≅ Lx̄'^* LΦ^* Lπ^* a --b--> Lx̄'^* Lπ^* Lg^* a --ψ--> Lx̄'^* Lπ^* a`. -/
noncomputable def modelStalkFrobenius (x' : RationalPoint ((geometricBaseChange k Ω).obj X))
    (hx' : x' ≫ modelFrobenius Ω X N g = x') (a : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj a ⟶ a) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x').obj
        ((geometricBaseChangeUpperStar Ω ℓ X).obj a) ⟶
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x').obj
        ((geometricBaseChangeUpperStar Ω ℓ X).obj a) :=
  eqToHom (congrArg (fun f ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ)
      ℓ f).obj ((geometricBaseChangeUpperStar Ω ℓ X).obj a)) hx'.symm) ≫
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ x'
      (modelFrobenius Ω X N g)).hom.app ((geometricBaseChangeUpperStar Ω ℓ X).obj a) ≫
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x').map
      ((weilGeometricBaseChangeComparison Ω ℓ X N g).hom.app a ≫
        (geometricBaseChangeUpperStar Ω ℓ X).map ψ)

variable {X N g} in
/-- On the ambient derived category, the explicit local Frobenius of the base change is the
composite `modelFrobeniusAux` of the derived pullbacks. -/
lemma modelStalkFrobenius_hom [IsSepClosed Ω]
    (x' : RationalPoint ((geometricBaseChange k Ω).obj X))
    (hx' : x' ≫ modelFrobenius Ω X N g = x') (a : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj a ⟶ a) :
    (modelStalkFrobenius ℓ x' hx' a ψ).hom =
      modelFrobeniusAux (D := fun S ↦ DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S)
          Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ) S)))
        (fun a ↦ L((a)^*⟦Profinite.padicAlgClRingObj ℓ⟧))
        (fun a b ↦ leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) a b) x'.left
        (modelFrobenius Ω X N g).left (geometricBaseChangeProj X) g.left
        (frobeniusIterate (overFrobenius X) N).left (left_comp_modelFrobenius_left hx')
        (modelFrobenius_left_comp_proj' X N g) (leftDerivedUpperStarFrobeniusIso ℓ X N)
        a.obj ψ.hom := by
  rw [modelStalkFrobenius]
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  simp only [ObjectProperty.FullSubcategory.eqToHom_hom']
  simp only [boundedConstructibleUpperStarComp_hom_app_hom_eq]
  simp only [boundedConstructibleUpperStar_map_hom]
  simp only [ObjectProperty.FullSubcategory.comp_hom, weilGeometricBaseChangeComparison_hom_app_hom,
    geometricBaseChangeUpperStar_map_hom, leftDerivedUpperStarModelFrobeniusComparison_hom_app]
  simp only [modelFrobeniusAux, leftDerivedUpperStarModelFrobeniusIso_hom_app, Functor.map_comp,
    Category.assoc]
  simp only [eqToHom_trans_assoc]
  rfl

variable {X N g} in
/-- The local Frobenius at `x̄'` of the base change of a Weil object `(L, φ)` is the explicit
composite `modelStalkFrobenius` for `(L, φ)`. -/
lemma weilStalk_weilGeometricBaseChange_frobenius_hom [IsSepClosed Ω]
    (x' : RationalPoint ((geometricBaseChange k Ω).obj X))
    (hx' : x' ≫ modelFrobenius Ω X N g = x') (L : WeilBoundedConstructible ℓ g) :
    ((weilStalk ℓ (modelFrobenius Ω X N g) x' hx').obj
        ((weilGeometricBaseChange Ω ℓ X N g).obj L)).frobenius.hom =
      modelStalkFrobenius ℓ x' hx' L.carrier L.str.hom := by
  rw [WeilBoundedConstructible.weilStalk_obj_frobenius_hom_eq]
  simp only [weilGeometricBaseChange_obj_str, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rfl

end Model

/-! ### The Galois Frobenius -/

section Galois

variable {X} [IsSepClosed Ω] (e : X ≅ X) (σ : Spec (.of Ω) ≅ Spec (.of Ω))
  (x : Spec (.of Ω) ⟶ X.left) (hx : x ≫ e.hom.left = σ.hom ≫ x)

omit [Finite k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Algebra k Ω]
  [Fact (ringChar Ω).Prime] [Fact (ringChar Ω ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The Frobenius comparison of the stalk, unfolded. -/
lemma weilStalkComparison_eq : weilStalkComparison ℓ e σ.hom x hx =
    Functor.isoWhiskerLeft _ (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ.hom).symm ≪≫
      (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ.hom x).symm ≪≫
      upperStarEqToIso (Profinite.padicAlgClRingObj ℓ) hx.symm ≪≫
      upperStarComp (Profinite.padicAlgClRingObj ℓ) x e.hom.left :=
  rfl

omit [Finite k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Algebra k Ω]
  [Fact (ringChar Ω).Prime] [Fact (ringChar Ω ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The Frobenius of the stalk of a Weil sheaf at a geometric point fixed up to `σ`, as an
explicit composite:
`x̄^* F --τ⁻¹--> σ^* x̄^* F ≅ (σ ≫ x̄)^* F = (x̄ ≫ e)^* F ≅ x̄^* e^* F --x̄^* φ_F--> x̄^* F`. -/
lemma stalkFunctor_obj_str_hom (W : WeilSheaf ℓ e) :
    ((WeilSheaf.stalkFunctor ℓ e σ.hom x hx).obj W).str.hom =
      (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ.hom).inv.app
          ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj W.carrier) ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ.hom x).inv.app W.carrier ≫
        eqToHom (congrArg (fun t : Spec (.of Ω) ⟶ X.left ↦
          (t)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj W.carrier) hx.symm) ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) x e.hom.left).hom.app W.carrier ≫
        (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map W.str.hom := by
  have h1 : ((WeilSheaf.stalkFunctor ℓ e σ.hom x hx).obj W).str.hom =
      (weilStalkComparison ℓ e σ.hom x hx).hom.app W.carrier ≫
        (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map W.str.hom := by
    rw [WeilSheaf.stalkFunctor_obj_str]
    rfl
  have h2 := isoWhiskerLeft_symm_trans_hom_app_aux ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
    (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ.hom)
    (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ.hom x)
    (upperStarEqToIso (Profinite.padicAlgClRingObj ℓ) hx.symm)
    (upperStarComp (Profinite.padicAlgClRingObj ℓ) x e.hom.left) W.carrier
  have h3 := (congrArg (fun i ↦ i.hom.app W.carrier) (weilStalkComparison_eq ℓ e σ x hx)).trans h2
  refine h1.trans ((congrArg (· ≫ (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map W.str.hom) h3).trans
    ((congrArg (fun z ↦ ((upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ.hom).inv.app
        ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj W.carrier) ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ.hom x).inv.app W.carrier ≫ z ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) x e.hom.left).hom.app W.carrier) ≫
        (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map W.str.hom)
      (upperStarEqToIso_hom_app _ hx.symm W.carrier)).trans ?_))
  simp only [Category.assoc]

end Galois

end AlgebraicGeometry.ProEtale.CondensedRing
