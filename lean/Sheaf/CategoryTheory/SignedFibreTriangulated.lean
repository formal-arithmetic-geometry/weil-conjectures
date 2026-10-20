/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.Algebra.Category.Grp.Abelian
import Sheaf.CategoryTheory.SignedFibreCone
import Sheaf.CategoryTheory.ConeFunctorDescent

/-!
# The signed fibre functor preserves cone triangles

Source: Stacks Project, Derived Categories, Tags 014E, 014F and 014S, with the explicit
signed two-term calculation of the DAG (blueprint: lem-amb-signed-fibre-triangulated).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits CochainComplex

namespace CategoryTheory

/-- Source: Stacks Project, Derived Categories, Tags 014E, 014F and 014S; explicit
signed two-term refinement (blueprint: lem-amb-signed-fibre-triangulated).

The existential functor is specified by its degreewise coordinate isomorphisms `e`:
its differential is `(d_A a, r a - d_B b)` and its maps are diagonal. The homotopy
components are `(A(H) a, -B(H) b)`. The shift comparison is `(a, -b)`. The two
projection equations for `Phi` say exactly `(x,y,z,w) ↦ (x,z,y,-w)`, using the
canonical cone projections, including the biproduct decompositions preserved by
additive functors. Cone triangles use the boundary `-p` of `mappingCone.triangle`.

Proof plan (DAG steps 1--8): additivity makes the component differentials square
to zero, and naturality of `r` cancels the mixed terms. The same naturality proves
the diagonal maps commute with differentials; identities, composition and addition
are componentwise. For a homotopy, the mixed terms in `D h + h D` cancel and its
remaining components are `A(f-g)` and `B(f-g)`; hence the functor descends to the
homotopy category. The sign change on the second summand intertwines the two shift
differentials and is its own inverse. Decompose both cones using the images of their
inclusions and projections under `A` and `B`; these are biproduct decompositions by
additivity. The four differential components before interchange are
`(d_A x + A(f)y, -d_A y, r x - d_B z - B(f)w, r y + d_B w)`.
Interchanging the middle two coordinates and negating the fourth gives the target
cone differential. The inverse interchanges them back and negates the fourth.
Diagonal maps of commuting squares commute with this interchange. The inclusion
is unchanged, while the two boundary composites are both `(-y,w)`. Thus each cone
triangle maps isomorphically to the cone triangle of its image. By
`lem-trf-additive-homotopy-category-triangulated`, all distinguished triangles are
isomorphic to cone triangles, proving exactness with the specified shift comparison.
Finally additive functors preserve zero objects; if `I` vanishes below `N`, both
summands vanish there. Shifts and cones preserve bounded-below complexes, so the
same construction restricts to their homotopy categories. -/
theorem exists_signedFibre_triangulated
    {C : Type u} [Category.{v} C] [Abelian C]
    (A B : C ⥤ AddCommGrpCat.{w}) [A.Additive] [B.Additive] (r : A ⟶ B) :
    ∃ (F : CochainComplex C ℤ ⥤ CochainComplex AddCommGrpCat.{w} ℤ)
      (_addF : F.Additive) (_shiftF : F.CommShift ℤ)
      (e : ∀ (I : CochainComplex C ℤ) (n : ℤ),
        (F.obj I).X n ≅ AddCommGrpCat.of (A.obj (I.X n) × B.obj (I.X (n - 1))))
      (Phi : ∀ {I J : CochainComplex C ℤ} (f : I ⟶ J),
        F.obj (mappingCone f) ≅ mappingCone (F.map f))
      (G : HomotopyCategory C (.up ℤ) ⥤ HomotopyCategory AddCommGrpCat.{w} (.up ℤ))
      (_addG : G.Additive) (_shiftG : G.CommShift ℤ)
      (alpha : F ⋙ HomotopyCategory.quotient AddCommGrpCat.{w} (.up ℤ) ≅
        HomotopyCategory.quotient C (.up ℤ) ⋙ G),
      (∀ (I : CochainComplex C ℤ) (n : ℤ) (t : (F.obj I).X n),
        (e I (n + 1)).hom ((F.obj I).d n (n + 1) t) =
          (A.map (I.d n (n + 1)) ((e I n).hom t).1,
            B.map (I.XIsoOfEq (Int.add_sub_cancel n 1).symm).hom
              (r.app (I.X n) ((e I n).hom t).1) -
            B.map (I.d (n - 1) ((n + 1) - 1)) ((e I n).hom t).2)) ∧
      (∀ {I J : CochainComplex C ℤ} (f : I ⟶ J) (n : ℤ) (t : (F.obj I).X n),
        (e J n).hom ((F.map f).f n t) =
          (A.map (f.f n) ((e I n).hom t).1,
            B.map (f.f (n - 1)) ((e I n).hom t).2)) ∧
      (∀ {I J : CochainComplex C ℤ} {f g : I ⟶ J} (H : Homotopy f g),
        ∃ h : Homotopy (F.map f) (F.map g),
          ∀ (n : ℤ) (t : (F.obj I).X n),
            (e J (n - 1)).hom (h.hom n (n - 1) t) =
              (A.map (H.hom n (n - 1)) ((e I n).hom t).1,
                -B.map (H.hom (n - 1) ((n - 1) - 1)) ((e I n).hom t).2)) ∧
      (∀ (I : CochainComplex C ℤ) (n : ℤ) (t : (F.obj (I⟦(1 : ℤ)⟧)).X n),
        (e I (n + 1)).hom
            (((F.obj I).shiftFunctorObjXIso 1 n (n + 1) rfl).hom
              (((F.commShiftIso (1 : ℤ)).hom.app I).f n t)) =
          (A.map (I.shiftFunctorObjXIso 1 n (n + 1) rfl).hom
              ((e (I⟦(1 : ℤ)⟧) n).hom t).1,
            -B.map (I.shiftFunctorObjXIso 1 (n - 1) ((n + 1) - 1)
                ((Int.add_sub_cancel n 1).trans (Int.sub_add_cancel n 1).symm)).hom
              ((e (I⟦(1 : ℤ)⟧) n).hom t).2)) ∧
      (∀ {I J : CochainComplex C ℤ} (f : I ⟶ J) (n : ℤ)
          (t : (F.obj (mappingCone f)).X n),
        (e J n).hom
            ((mappingCone.snd (F.map f)).v n n (add_zero n) ((Phi f).hom.f n t)) =
          (A.map ((mappingCone.snd f).v n n (add_zero n))
              ((e (mappingCone f) n).hom t).1,
            B.map ((mappingCone.snd f).v (n - 1) (n - 1) (add_zero (n - 1)))
              ((e (mappingCone f) n).hom t).2) ∧
        (e I (n + 1)).hom
            ((mappingCone.fst (F.map f)).1.v n (n + 1) rfl ((Phi f).hom.f n t)) =
          (A.map ((mappingCone.fst f).1.v n (n + 1) rfl)
              ((e (mappingCone f) n).hom t).1,
            -B.map ((mappingCone.fst f).1.v (n - 1) ((n + 1) - 1)
                ((Int.sub_add_cancel n 1).trans (Int.add_sub_cancel n 1).symm))
              ((e (mappingCone f) n).hom t).2)) ∧
      (∀ {I J I' J' : CochainComplex C ℤ} (f : I ⟶ J) (f' : I' ⟶ J')
          (a : I ⟶ I') (b : J ⟶ J') (h : f ≫ b = a ≫ f'),
        F.map (mappingCone.map f f' a b h) ≫ (Phi f').hom =
          (Phi f).hom ≫ mappingCone.map (F.map f) (F.map f') (F.map a) (F.map b)
            ((F.map_comp f b).symm.trans ((congrArg F.map h).trans (F.map_comp a f')))) ∧
      (∀ {I J : CochainComplex C ℤ} (f : I ⟶ J),
        F.map (mappingCone.inr f) ≫ (Phi f).hom = mappingCone.inr (F.map f) ∧
        F.map (mappingCone.triangle f).mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app I =
          (Phi f).hom ≫ (mappingCone.triangle (F.map f)).mor₃) ∧
      alpha.hom.CommShift ℤ ∧ G.IsTriangulated ∧
      (∀ (I : CochainComplex C ℤ) (N : ℤ),
        I.IsStrictlyGE N → (F.obj I).IsStrictlyGE N) ∧
      (∀ K : HomotopyCategory C (.up ℤ),
        HomotopyCategory.plus C K → HomotopyCategory.plus AddCommGrpCat.{w} (G.obj K)) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.defeqAttrib.useBackward true in
    let F := SignedFibre.functor A B r
    let : F.CommShift ℤ := SignedFibre.commShift A B r
    let e : ∀ (I : CochainComplex C ℤ) (n : ℤ),
        (F.obj I).X n ≅ AddCommGrpCat.of (A.obj (I.X n) × B.obj (I.X (n - 1))) :=
      fun _ _ ↦ Iso.refl _
    let Phi : ∀ {I J : CochainComplex C ℤ} (f : I ⟶ J),
        F.obj (mappingCone f) ≅ mappingCone (F.map f) :=
      fun f ↦ SignedFibre.coneIso A B r f
    have hb : ∀ (I : CochainComplex C ℤ) (N : ℤ),
        I.IsStrictlyGE N → (F.obj I).IsStrictlyGE N := by
      intro I N h
      exact @SignedFibre.obj_isStrictlyGE C _ _ A B _ _ r I N h
    have hc : ∀ {I J : CochainComplex C ℤ} (f : I ⟶ J),
        Nonempty (F.mapTriangle.obj (mappingCone.triangle f) ≅
          mappingCone.triangle (F.map f)) := by
      intro I J f
      refine ⟨Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Phi f) ?_ ?_ ?_⟩
      · simp [Functor.mapTriangle]
      · simpa [Functor.mapTriangle] using SignedFibre.coneIso_inr A B r f
      · simp only [Functor.mapTriangle, Pretriangulated.Triangle.mk_mor₃, Iso.refl_hom,
          Functor.map_id, Category.comp_id]
        change SignedFibre.map A B r (mappingCone.triangle f).mor₃ ≫
            (SignedFibre.shiftIso A B r I 1).hom = _
        exact SignedFibre.coneIso_boundary A B r f
    obtain ⟨G, addG, shiftG, alpha, hα, hG, hplus⟩ := exists_coneFunctor_descent F
      (fun H ↦ ⟨SignedFibre.homotopy A B r H⟩) hc hb
    refine ⟨F, inferInstance, inferInstance, e, Phi, G, addG, shiftG, alpha,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, hα, hG, hb, hplus⟩
    · intro I n t
      dsimp only [e, Iso.refl_hom]
      exact SignedFibre.obj_d_apply A B r I n (n + 1) rfl t
    · intro I J f n t
      rfl
    · intro I J f g H
      exact ⟨SignedFibre.homotopy A B r H, fun _ _ ↦ rfl⟩
    · intro I n t
      change (SignedFibre.shiftXIso A B I 1 n).hom t = _
      rw [SignedFibre.shiftXIso_hom_apply]
      dsimp [e, shiftFunctorObjXIso]
      simp only [A.map_id, Units.neg_smul, one_smul]
      rfl
    · intro I J f n t
      exact ⟨SignedFibre.coneXIso_snd_apply A B r f n t,
        SignedFibre.coneXIso_fst_apply A B r f n t⟩
    · intro I J I' J' f f' a b h
      exact SignedFibre.coneIso_naturality A B r f f' a b h
    · intro I J f
      exact ⟨SignedFibre.coneIso_inr A B r f, SignedFibre.coneIso_boundary A B r f⟩
end CategoryTheory
