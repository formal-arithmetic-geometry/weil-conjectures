/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Homology.ExtResolution
public import WeilConjectures.CategoryTheory.Sites.SemiSimplicialHypercover.FreeResolution

/-!
# Cohomology computed by hypercovers

Let `U` be a semi-simplicial hypercover of a site `(C, J)` and `F` a sheaf of `R`-modules. A
cocycle `z ∈ F(U_q)` of the cochain complex `C^•(U, F)` corresponds to a morphism
`R[U_q] ⟶ F` vanishing on the image of `R[U_{q + 1}]`, i.e. to a cocycle on the free resolution
`R[U_•] ⟶ R` of the constant sheaf; hence it has a class in the sheaf cohomology
`Ext^q(R, F)` (`CategoryTheory.SemiSimplicialObject.IsHypercover.cohomologyClass`).

These classes vanish on coboundaries, are natural in `F`, compatible with refinements
`V ⟶ U` of hypercovers and with connecting homomorphisms. The main result is the computation of
sheaf cohomology by hypercovers (blueprint `thm-weil-pbc-hypercover-cohomology`, [Stacks,
Tag 01H0]) in an elementwise form, for any class `𝒰` of hypercovers which is nonempty and in
which local lifting requirements can be met after refinement
(`CategoryTheory.SemiSimplicialObject.exists_cohomologyClass_eq` and
`CategoryTheory.SemiSimplicialObject.exists_isCoboundary_of_cohomologyClass_eq_zero`):

* every cohomology class is the class of a cocycle on some hypercover in `𝒰`;
* a cocycle whose class vanishes becomes a coboundary after refinement within `𝒰`.

Equivalently, `Ext^q(R, F)` is the colimit over refinements of the cohomology groups
`H^q(C^•(U, F))`. The proof is by dimension shifting along a short exact sequence
`0 ⟶ F ⟶ I ⟶ Q ⟶ 0` with `I` injective, whose cochain complexes on hypercovers are exact in
positive degrees
(`CategoryTheory.SemiSimplicialObject.IsHypercover.exactAt_cochainComplex_of_injective`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite Abelian

namespace CategoryTheory.SemiSimplicialObject

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Type (max u v)} [Ring R] [HasSheafify J (ModuleCat.{max u v} R)]

/-- Morphisms `R[V] ⟶ F` from a free sheaf are sections of `F` over `V`. -/
noncomputable def freeSheafHomEquiv (V : C) (F : Sheaf J (ModuleCat.{max u v} R)) :
    ((freeSheaf J R).obj V ⟶ F) ≃ F.obj.obj (op V) :=
  sorry

/-- The cocycles of the cochain complex `C^•(U, F)` in degree `q`. -/
def IsCocycle (U : SemiSimplicialObject C) (F : Sheaf J (ModuleCat.{max u v} R)) (q : ℕ)
    (z : F.obj.obj (op (U.obj q))) : Prop :=
  (U.cochainDifferential F.obj q).hom z = 0

/-- The coboundaries of the cochain complex `C^•(U, F)` in degree `q`: `z = 0` if `q = 0`. -/
def IsCoboundary (U : SemiSimplicialObject C) (F : Sheaf J (ModuleCat.{max u v} R)) :
    ∀ (q : ℕ), F.obj.obj (op (U.obj q)) → Prop
  | 0, z => z = 0
  | q + 1, z => ∃ y, (U.cochainDifferential F.obj q).hom y = z

variable [HasExt.{w} (Sheaf J (ModuleCat.{max u v} R))]

namespace IsHypercover

variable {U : SemiSimplicialObject C}

/-- The class in `Ext^q(R, F)` of a cocycle `z ∈ F(U_q)` on a hypercover `U`. -/
noncomputable def cohomologyClass (hU : U.IsHypercover J) (F : Sheaf J (ModuleCat.{max u v} R))
    (q : ℕ) (z : F.obj.obj (op (U.obj q))) (hz : U.IsCocycle F q z) :
    Ext (constSheaf J R) F q :=
  sorry

variable (hU : U.IsHypercover J)
include hU

lemma cohomologyClass_add (F : Sheaf J (ModuleCat.{max u v} R)) (q : ℕ)
    (z z' : F.obj.obj (op (U.obj q))) (hz : U.IsCocycle F q z) (hz' : U.IsCocycle F q z') :
    hU.cohomologyClass F q (z + z') (by sorry) =
      hU.cohomologyClass F q z hz + hU.cohomologyClass F q z' hz' :=
  sorry

/-- Coboundaries have vanishing class. -/
lemma cohomologyClass_eq_zero_of_isCoboundary (F : Sheaf J (ModuleCat.{max u v} R)) (q : ℕ)
    (z : F.obj.obj (op (U.obj q))) (hz : U.IsCocycle F q z) (hz' : U.IsCoboundary F q z) :
    hU.cohomologyClass F q z hz = 0 :=
  sorry

/-- Naturality in the sheaf. -/
lemma cohomologyClass_map {F G : Sheaf J (ModuleCat.{max u v} R)} (φ : F ⟶ G) (q : ℕ)
    (z : F.obj.obj (op (U.obj q))) (hz : U.IsCocycle F q z) :
    hU.cohomologyClass G q ((φ.hom.app _).hom z) (by sorry) =
      (hU.cohomologyClass F q z hz).comp (Ext.mk₀ φ) (add_zero q) :=
  sorry

/-- Compatibility with refinements: the class of the restriction of a cocycle along a morphism of
hypercovers `f : V ⟶ U` is the class of the cocycle. -/
lemma cohomologyClass_restrict {V : SemiSimplicialObject C} (hV : V.IsHypercover J) (f : V ⟶ U)
    (F : Sheaf J (ModuleCat.{max u v} R)) (q : ℕ) (z : F.obj.obj (op (U.obj q)))
    (hz : U.IsCocycle F q z) :
    hV.cohomologyClass F q ((F.obj.map (f.app q).op).hom z) (by sorry) =
      hU.cohomologyClass F q z hz :=
  sorry

/-- Compatibility with connecting homomorphisms: for a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`
of sheaves, a cocycle `w ∈ X₃(U_q)` which lifts to `w' ∈ X₂(U_q)`, and `v ∈ X₁(U_{q + 1})` mapping
to `d w'`, the class of `v` is the image of the class of `w` under the connecting map. -/
lemma cohomologyClass_extClass {S : ShortComplex (Sheaf J (ModuleCat.{max u v} R))}
    (hS : S.ShortExact) (q : ℕ) (w' : S.X₂.obj.obj (op (U.obj q)))
    (hw : U.IsCocycle S.X₃ q ((S.g.hom.app _).hom w')) (v : S.X₁.obj.obj (op (U.obj (q + 1))))
    (hv : (S.f.hom.app _).hom v = (U.cochainDifferential S.X₂.obj q).hom w')
    (hv' : U.IsCocycle S.X₁ (q + 1) v) :
    hU.cohomologyClass S.X₁ (q + 1) v hv' =
      (hU.cohomologyClass S.X₃ q _ hw).comp hS.extClass rfl :=
  sorry

/-- In degree `0` the classes of cocycles exhaust `Ext⁰(R, F)`, each exactly once. -/
lemma bijective_cohomologyClass_zero (F : Sheaf J (ModuleCat.{max u v} R)) :
    Function.Bijective (fun z : {z : F.obj.obj (op (U.obj 0)) // U.IsCocycle F 0 z} ↦
      hU.cohomologyClass F 0 z.1 z.2) :=
  sorry

end IsHypercover

variable [EnoughInjectives (Sheaf J (ModuleCat.{max u v} R))]

/-- **Every cohomology class is computed on a hypercover** (blueprint
`thm-weil-pbc-hypercover-cohomology`). Let `𝒰` be a nonempty class of hypercovers in which local
lifts of sections through epimorphisms of sheaves can be obtained after refinement. Then every
class in `Ext^q(R, F)` is the class of a cocycle on some hypercover of `𝒰`. -/
theorem exists_cohomologyClass_eq (𝒰 : SemiSimplicialObject C → Prop)
    (h𝒰 : ∀ U, 𝒰 U → U.IsHypercover J) (hne : ∃ U, 𝒰 U)
    (hlift : ∀ U, 𝒰 U → ∀ (p : ℕ) {G Q : Sheaf J (ModuleCat.{max u v} R)} (φ : G ⟶ Q) [Epi φ]
      (w : Q.obj.obj (op (U.obj p))), ∃ (V : SemiSimplicialObject C) (_ : 𝒰 V) (f : V ⟶ U)
        (w' : G.obj.obj (op (V.obj p))), (φ.hom.app _).hom w' = (Q.obj.map (f.app p).op).hom w)
    (F : Sheaf J (ModuleCat.{max u v} R)) (q : ℕ) (x : Ext (constSheaf J R) F q) :
    ∃ (U : SemiSimplicialObject C) (hU : 𝒰 U) (z : F.obj.obj (op (U.obj q)))
      (hz : U.IsCocycle F q z), (h𝒰 U hU).cohomologyClass F q z hz = x :=
  sorry

/-- **A cocycle with vanishing class is a coboundary after refinement** (blueprint
`thm-weil-pbc-hypercover-cohomology`). Under the assumptions of
`CategoryTheory.SemiSimplicialObject.exists_cohomologyClass_eq`, if the class of a cocycle `z`
on a hypercover `U ∈ 𝒰` vanishes, then its restriction to some refinement `V ⟶ U` in `𝒰` is a
coboundary. -/
theorem exists_isCoboundary_of_cohomologyClass_eq_zero (𝒰 : SemiSimplicialObject C → Prop)
    (h𝒰 : ∀ U, 𝒰 U → U.IsHypercover J)
    (hlift : ∀ U, 𝒰 U → ∀ (p : ℕ) {G Q : Sheaf J (ModuleCat.{max u v} R)} (φ : G ⟶ Q) [Epi φ]
      (w : Q.obj.obj (op (U.obj p))), ∃ (V : SemiSimplicialObject C) (_ : 𝒰 V) (f : V ⟶ U)
        (w' : G.obj.obj (op (V.obj p))), (φ.hom.app _).hom w' = (Q.obj.map (f.app p).op).hom w)
    (F : Sheaf J (ModuleCat.{max u v} R)) (q : ℕ) (U : SemiSimplicialObject C) (hU : 𝒰 U)
    (z : F.obj.obj (op (U.obj q))) (hz : U.IsCocycle F q z)
    (h : (h𝒰 U hU).cohomologyClass F q z hz = 0) :
    ∃ (V : SemiSimplicialObject C) (_ : 𝒰 V) (f : V ⟶ U),
      V.IsCoboundary F q ((F.obj.map (f.app q).op).hom z) :=
  sorry

end CategoryTheory.SemiSimplicialObject
