/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V8
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

import Sheaf.AlgebraicGeometry.FrobeniusVectorBundleLocalFrames
import Mathlib.LinearAlgebra.Pi

/-! # Local Frobenius equations on finite locally free modules -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

open Modules

attribute [local instance 3000] CategoryStruct.toQuiver
attribute [local irreducible] Modules.tensorPullback Modules.tensorPullbackObj
attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf

private theorem coordinateMatrix (R : Type u) [CommRing R] (p n : ℕ)
    (f : (Fin n → R) →+ (Fin n → R))
    (hf : ∀ (a : R) (v : Fin n → R), f (a • v) = a ^ p • f v)
    (x : Fin n → R) (i : Fin n) :
    f x i = ∑ j, f (Pi.single j 1) i * x j ^ p := by
  classical
  have hx : x = ∑ j, x j • Pi.single j (1 : R) := by
    ext i
    simp [Pi.single_apply]
  calc
    f x i = f (∑ j, x j • Pi.single j 1) i := congrArg (fun z ↦ f z i) hx
    _ = _ := by simp only [map_sum, Finset.sum_apply, hf, Pi.smul_apply, smul_eq_mul,
      mul_comm]


private theorem naturalMatrixCoordinates
    (X : Scheme.{u}) (p n : ℕ)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (F : G ⟶ G)
    (e : ∀ V : X.Etale, G.obj.obj (op V) ≃+ (Fin n → Γ(V.left, ⊤)))
    (hnat : ∀ (V W : X.Etale) (g : W ⟶ V) (s : G.obj.obj (op V)),
      ∀ i, e W (G.obj.map g.op s) i = g.left.appTop (e V s i))
    (hf : ∀ (V : X.Etale) (a : Γ(V.left, ⊤)) (v : Fin n → Γ(V.left, ⊤)),
      e V (F.hom.app (op V) ((e V).symm (a • v))) =
        a ^ p • e V (F.hom.app (op V) ((e V).symm v))) :
    ∃ c : Fin n → Fin n → Γ(X, ⊤),
      ∀ (V : X.Etale) (s : G.obj.obj (op V)) (i : Fin n),
        e V (F.hom.app (op V) s) i =
          ∑ j, (@id Γ(V.left, ⊤) (V.hom.appTop (c i j))) * (e V s j) ^ p := by
  classical
  let VA : X.Etale := Etale.mk (𝟙 X)
  let b (V : X.Etale) (j : Fin n) := (e V).symm (Pi.single j 1)
  let c (i j : Fin n) : Γ(X, ⊤) := e VA (F.hom.app (op VA) (b VA j)) i
  refine ⟨c, fun V s i ↦ ?_⟩
  let k : V ⟶ VA := MorphismProperty.Over.homMk V.hom (by
    change V.hom ≫ 𝟙 X = V.hom
    simp) trivial
  have hb (j : Fin n) : G.obj.map k.op (b VA j) = b V j := by
    apply (e V).injective
    ext i
    rw [hnat]
    simp [b, Pi.single_apply]
  have hcoeff (j i : Fin n) : e V (F.hom.app (op V) (b V j)) i =
      V.hom.appTop (c i j) := by
    rw [← hb j]
    have hh := ConcreteCategory.congr_hom (F.hom.naturality k.op) (b VA j)
    simp only [ConcreteCategory.comp_apply] at hh
    rw [hh, hnat]
    rfl
  let f : (Fin n → Γ(V.left, ⊤)) →+ (Fin n → Γ(V.left, ⊤)) :=
    (e V).toAddMonoidHom.comp ((F.hom.app (op V)).hom.comp (e V).symm.toAddMonoidHom)
  have hh := coordinateMatrix Γ(V.left, ⊤) p n f (hf V) (e V s) i
  change e V (F.hom.app (op V) ((e V).symm (e V s))) i =
    ∑ j, e V (F.hom.app (op V) (b V j)) i * (e V s j) ^ p at hh
  rw [AddEquiv.symm_apply_apply] at hh
  convert (by simpa only [hcoeff] using hh) using 1; rfl


private theorem charSections (p : ℕ) (T : Scheme.{u})
    (f : T ⟶ Spec (.of (ULift.{u} (ZMod p)))) : (p : Γ(T, ⊤)) = 0 := by
  let R := CommRingCat.of (ULift.{u} (ZMod p))
  let φ : R ⟶ Γ(T, ⊤) := (Scheme.ΓSpecIso R).inv ≫ f.appTop
  have hz : (p : R) = 0 := by
    apply ULift.ext
    exact ZMod.natCast_self p
  rw [← map_natCast φ.hom, hz, map_zero]

private theorem coordinateSemilinear {R : Type u} [CommRing R]
    {B : Type (u + 1)} [AddCommGroup B] (p n : ℕ)
    (e : B ≃+ (Fin n → R)) (ρ : B → B) (act : R → B → B)
    (hlin : ∀ a s, e (act a s) = a • e s)
    (hρ : ∀ a s, ρ (act a s) = act (a ^ p) (ρ s))
    (a : R) (v : Fin n → R) :
    e (ρ (e.symm (a • v))) = a ^ p • e (ρ (e.symm v)) := by
  have hs : e.symm (a • v) = act a (e.symm v) := by
    apply e.injective
    rw [e.apply_symm_apply, hlin, e.apply_symm_apply]
  rw [hs, hρ, hlin]

private theorem sectionsSemilinear (S : Scheme.{u})
    (P : ∀ U : S.Etale, U.left.Modules) (p : ℕ)
    (ρ : ∀ U : S.Etaleᵒᵖ, ULift.{u + 1} Γ(P U.unop, ⊤) →
      ULift.{u + 1} Γ(P U.unop, ⊤))
    (hρ : ∀ (U : S.Etaleᵒᵖ) (a : ULift.{u + 1} Γ(U.unop.left, ⊤))
        (s : ULift.{u + 1} Γ(P U.unop, ⊤)),
      ρ U (ULift.up (a.down • s.down)) =
        ULift.up (a.down ^ p • (@id Γ(P U.unop, ⊤) (ρ U s).down)))
    (V : S.Etale) (b : Γ(V.left, ⊤)) (s : ULift.{u + 1} Γ(P V, ⊤)) :
    ρ (op V) (ULift.up (b • s.down)) =
      ULift.up (b ^ p • (@id Γ(P V, ⊤) (ρ (op V) s).down)) := by
  exact hρ (op V) (ULift.up b) s

private theorem naturalMatrixCoordinates_exists
    (X : Scheme.{u}) (p n : ℕ)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (F : G ⟶ G)
    (e : ∀ V : X.Etale, G.obj.obj (op V) ≃+ (Fin n → Γ(V.left, ⊤)))
    (hp : (p : Γ(X, ⊤)) = 0)
    (hnat : ∀ (V W : X.Etale) (g : W ⟶ V) (s : G.obj.obj (op V)),
      ∀ i, e W (G.obj.map g.op s) i = g.left.appTop (e V s i))
    (hf : ∀ (V : X.Etale) (a : Γ(V.left, ⊤)) (v : Fin n → Γ(V.left, ⊤)),
      e V (F.hom.app (op V) ((e V).symm (a • v))) =
        a ^ p • e V (F.hom.app (op V) ((e V).symm v))) :
    ∃ (c : Fin n → Fin n → Γ(X, ⊤))
      (e : ∀ V : X.Etale, G.obj.obj (op V) ≃+ (Fin n → Γ(V.left, ⊤))),
      (p : Γ(X, ⊤)) = 0 ∧
      (∀ (V W : X.Etale) (g : W ⟶ V) (s : G.obj.obj (op V)),
        ∀ i, e W (G.obj.map g.op s) i = g.left.appTop (e V s i)) ∧
      (∀ (V : X.Etale) (s : G.obj.obj (op V)),
        ∀ i, e V (F.hom.app (op V) s) i =
          ∑ j, (@id Γ(V.left, ⊤) (V.hom.appTop (c i j))) * (e V s j) ^ p) := by
  obtain ⟨c, heq⟩ := naturalMatrixCoordinates X p n G F e hnat hf
  exact ⟨c, e, hp, hnat, heq⟩

private theorem coordinates_of_frame
    (p : ℕ) (S T : Scheme.{u}) (E : S.Modules) [E.IsQuasicoherent]
    (F : (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf E) ⟶
      (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf E))
    (hF : ∀ (U : S.Etaleᵒᵖ) (a : ULift.{u + 1} Γ(U.unop.left, ⊤))
        (s : ULift.{u + 1} Γ((Modules.tensorPullback U.unop.hom).obj E, ⊤)),
      F.hom.app U (ULift.up (a.down • s.down)) =
        ULift.up (a.down ^ p • (@id Γ((Modules.tensorPullback U.unop.hom).obj E, ⊤)
          (F.hom.app U s).down)))
    (f : T ⟶ S) [Etale f] (n : ℕ) :
    let M : T.Etale ⥤ S.Etale :=
      MorphismProperty.Over.map (Y := S) ⊤ (inferInstance : Etale f)
    let L := Etale.localizationRestriction (U := S) AddCommGrpCat.{u + 1} f inferInstance
    let G := (sheafCompose S.smallEtaleTopology
      AddCommGrpCat.uliftFunctor.{u + 1, u}).obj (Modules.etaleTensorSectionsSheaf E)
    let act (V : T.Etale) (b : Γ(V.left, ⊤))
        (s : (Modules.etaleTensorSectionsSheaf E).obj.obj (op (M.obj V))) :=
      (@id Γ((M.obj V).left, ⊤) b) •
        (@id Γ((Modules.tensorPullback (M.obj V).hom).obj E, ⊤) s)
    (∃ e : ∀ V : T.Etale, (L.obj G).obj.obj (op V) ≃+ (Fin n → Γ(V.left, ⊤)),
      (∀ (V W : T.Etale) (g : W ⟶ V) (s : (L.obj G).obj.obj (op V)) (i : Fin n),
        e W ((L.obj G).obj.map g.op s) i = g.left.appTop (e V s i)) ∧
      (∀ (V : T.Etale) (a : Γ(V.left, ⊤)) (s : (L.obj G).obj.obj (op V)),
        e V (ULift.up (act V a s.down)) = a • e V s)) →
    (p : Γ(T, ⊤)) = 0 →
    ∃ (c : Fin n → Fin n → Γ(T, ⊤))
      (e : ∀ V : T.Etale, (L.obj G).obj.obj (op V) ≃+ (Fin n → Γ(V.left, ⊤))),
      (p : Γ(T, ⊤)) = 0 ∧
      (∀ (V W : T.Etale) (g : W ⟶ V) (s : (L.obj G).obj.obj (op V)) (i : Fin n),
        e W ((L.obj G).obj.map g.op s) i = g.left.appTop (e V s i)) ∧
      (∀ (V : T.Etale) (s : (L.obj G).obj.obj (op V)) (i : Fin n),
        e V ((L.map F).hom.app (op V) s) i =
          ∑ j, (@id Γ(V.left, ⊤) (V.hom.appTop (c i j))) * (e V s j) ^ p) := by
  intro M L G act hframe hp
  obtain ⟨e, hnat, hlin⟩ := hframe
  have hf (V : T.Etale) (a : Γ(V.left, ⊤)) (v : Fin n → Γ(V.left, ⊤)) :
      e V ((L.map F).hom.app (op V) ((e V).symm (a • v))) =
        a ^ p • e V ((L.map F).hom.app (op V) ((e V).symm v)) := by
    let act' (b : Γ(V.left, ⊤)) (s : (L.obj G).obj.obj (op V)) :=
      ULift.up (act V b s.down)
    refine coordinateSemilinear p n (e V) (fun z ↦ (L.map F).hom.app (op V) z)
      act' (hlin V) ?_ a v
    intro b z
    exact sectionsSemilinear S (fun U ↦ (Modules.tensorPullback U.hom).obj E) p
      (fun U z ↦ F.hom.app U z) hF (M.obj V) (@id Γ((M.obj V).left, ⊤) b) z
  exact naturalMatrixCoordinates_exists T p n (L.obj G) (L.map F) e hp hnat hf

/-- Finite affine coordinates for a Frobenius-semilinear vector-bundle endomorphism.

Source: Stacks Project, Tag 0GKU, lemma-frobenius-linear-on-vb, the choice of an affine
trivialization and its matrix in the first paragraph of the proof.
(blueprint: lem-weil-pbc-frobenius-vector-bundle-local-coordinates)

Proof: Pull the finite locally free module back to U and choose, around the given
point, an affine open A on which it is free with a finite basis. Reindex this basis
by Fin n. Pulling the basis back along every étale V -> A identifies sections with
n-tuples of functions; tensor pullback composition and its normalized units show
that these identifications commute with restriction from A. Define c_ij to be the
i-th coordinate of F applied to the j-th basis vector over A. Naturality of F and
its p-semilinearity then give the displayed coordinate formula over every V by
writing a section as the finite sum of its coordinate multiples of the basis.
The structure map to Spec(F_p) implies p=0 in Γ(A,O_A). The argument permits rank
zero, where the coordinate type is empty. -/
theorem frobenius_vectorBundle_local_coordinates
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
    [S.Over (Spec (.of (ULift.{u} (ZMod p))))] [CompactSpace S] [IsLocallyNoetherian S]
    (E : S.Modules) [E.IsFiniteLocallyFree]
    (F : (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf E) ⟶
      (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf E))
    (hF : ∀ (U : S.Etaleᵒᵖ) (a : ULift.{u + 1} Γ(U.unop.left, ⊤))
        (e : ULift.{u + 1} Γ((Modules.tensorPullback U.unop.hom).obj E, ⊤)),
      F.hom.app U (ULift.up (a.down • e.down)) =
        ULift.up (a.down ^ p • (@id Γ((Modules.tensorPullback U.unop.hom).obj E, ⊤)
          (F.hom.app U e).down))) :
    ∀ (U : S.Etale) (x : U.left),
      ∃ (A : U.left.Opens) (_ : IsAffineOpen A), x ∈ A ∧
      ∃ (n : ℕ) (c : Fin n → Fin n → Γ(A.toScheme, ⊤)),
      let L := Etale.localizationRestriction (U := S) AddCommGrpCat.{u + 1}
        (A.ι ≫ U.hom) inferInstance
      let G := (sheafCompose S.smallEtaleTopology
        AddCommGrpCat.uliftFunctor.{u + 1, u}).obj (Modules.etaleTensorSectionsSheaf E)
      ∃ e : ∀ V : A.toScheme.Etale,
          (L.obj G).obj.obj (op V) ≃+ (Fin n → Γ(V.left, ⊤)),
        (p : Γ(A.toScheme, ⊤)) = 0 ∧
        (∀ (V W : A.toScheme.Etale) (g : W ⟶ V) (s : (L.obj G).obj.obj (op V)),
          ∀ i, e W ((L.obj G).obj.map g.op s) i = g.left.appTop (e V s i)) ∧
        (∀ (V : A.toScheme.Etale) (s : (L.obj G).obj.obj (op V)),
          ∀ i, e V ((L.map F).hom.app (op V) s) i =
            ∑ j, (@id Γ(V.left, ⊤) (V.hom.appTop (c i j))) * (e V s j) ^ p) := by
  classical
  intro U x
  obtain ⟨A, hA, hxA, n, hframe⟩ := frobenius_vectorBundle_local_frames p S E U x
  refine ⟨A, hA, hxA, n, ?_⟩
  exact coordinates_of_frame p S A.toScheme E F hF (A.ι ≫ U.hom) n hframe
    (charSections p A.toScheme ((A.ι ≫ U.hom) ≫ (S ↘ Spec (.of (ULift.{u} (ZMod p))))))

end AlgebraicGeometry.Scheme
