/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator

/-! # Descent frames for associated vector bundles

Source: Milne, Algebraic Groups (2017), Section 18c, pp.389--390, and
Stacks Project, Tag 023T, descent of quasi-coherent modules.
(blueprint: def-sfb-associated-vector-bundle-frame)

A frame identifies the pullback of the specified sheaf with the trivial bundle.
Its relation on all algebra-valued points specifies the right descent action
(g,w)h = (gh,h inverse w). No descended object is chosen from mere existence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.AssociatedVectorBundle

/-- The finite free sheaf, including rank zero.
Source: Milne, Section 18c (blueprint: def-sfb-associated-vector-bundle-frame). -/
abbrev free (X : Scheme.{u}) (n : ℕ) : X.Modules :=
  SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))

/-- Restriction of an atlas frame along a scheme-valued point, with the canonical
composition and free-pullback comparisons.
Source: Stacks 023T (blueprint: def-sfb-associated-vector-bundle-frame). -/
def frameAt {F : Type u} [Field F] {G Q S : Over (Spec (.of F))}
    (q : G ⟶ Q) (E : Q.left.Modules) (n : ℕ)
    (θ : (Scheme.Modules.pullback q.left).obj E ≅ free G.left n) (g : S ⟶ G) :
    (Scheme.Modules.pullback (g ≫ q).left).obj E ≅ free S.left n :=
  (Scheme.Modules.pullbackComp g.left q.left).symm.app E ≪≫
    (Scheme.Modules.pullback g.left).mapIso θ ≪≫
      Scheme.Modules.pullbackFreeIso g.left (ULift.{u} (Fin n))

/-- The vector with coordinates v in the frame over an algebra-valued point.
Source: Milne, Section 18c (blueprint: def-sfb-associated-vector-bundle-frame). -/
def framedVector {F : Type u} [Field F] {G Q : Over (Spec (.of F))}
    (q : G ⟶ Q) (E : Q.left.Modules) (n : ℕ)
    (θ : (Scheme.Modules.pullback q.left).obj E ≅ free G.left n)
    {A : Type u} [CommRing A] [Algebra F A] (g : points G A) (v : ULift.{u} (Fin n) → A) :
    Γ((Scheme.Modules.pullback (g ≫ q).left).obj E, ⊤) :=
  (frameAt q E n θ g).inv.app ⊤
    ((Scheme.Modules.freeSectionsEquiv (ULift.{u} (Fin n))).symm
      (fun i => (Scheme.ΓSpecIso (.of A)).inv (v i)))

/-- The frame is exactly the descent datum of the rational H-module r.
The relation θ_gh(w) = θ_g(hw) is equivalent to (g,w)h = (gh,h inverse w).
HEq expresses equality under transport along (gh)q = gq; after that equality
is substituted it is ordinary equality of sections. Quantification includes
nonreduced algebras. For a represented fpqc right torsor, effective descent
identifies E, with this frame, with the associated bundle's sheaf of sections.
Source: Milne, Section 18c, and Stacks 023T
(blueprint: def-sfb-associated-vector-bundle-frame). -/
def IsDescentFrame {F : Type u} [Field F]
    (G H : Grp (Over (Spec (.of F)))) (i : H ⟶ G)
    {Q : Over (Spec (.of F))} (q : G.X ⟶ Q) (n : ℕ)
    (r : GeneralLinearGroup.RationalHom H.X (ULift.{u} (Fin n))) [IsMonHom r]
    (E : Q.left.Modules)
    (θ : (Scheme.Modules.pullback q.left).obj E ≅ free G.X.left n) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra F A]
    (g : points G.X A) (h : points H.X A),
    (g * (h ≫ i.hom.hom)) ≫ q = g ≫ q ∧
      ∀ v : ULift.{u} (Fin n) → A,
        HEq (framedVector q E n θ (g * (h ≫ i.hom.hom)) v)
          (framedVector q E n θ g
            ((r.points A h : Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin n)) A).mulVec v))

end AlgebraicGeometry.AssociatedVectorBundle
