module

public import Sheaf.AlgebraicGeometry.GroupScheme.Borel
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Geometric Borel and parabolic fibres over a ring

Source: Conrad, Reductive group schemes, Definition 5.2.1 and Corollary 5.2.7,
pp.151,155 (blueprint: def-sfb-geometric-parabolic-subgroup).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.GeometricParabolic

/-- Canonical scalar extension of a group scheme by the given ring map.
Source: Conrad, Section 5.2 (blueprint: def-sfb-geometric-parabolic-subgroup). -/
def fibre {A F : Type u} [CommRing A] [CommRing F] (f : A →+* F) :
    Grp (Over (Spec (.of A))) ⥤ Grp (Over (Spec (.of F))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp

/-- Borel fibres are tested at every geometric point of Spec A.
Source: Conrad, Definition 5.2.1 (blueprint: def-sfb-geometric-parabolic-subgroup). -/
def HasBorelFibres {A : Type u} [CommRing A]
    {P G : Grp (Over (Spec (.of A)))} (i : P ⟶ G) : Prop :=
  ∀ (F : Type u) [Field F] [IsAlgClosed F] (f : A →+* F),
    IsBorelGroupScheme ((fibre f).map i).hom.hom

/-- A smooth connected geometric subgroup is parabolic if it contains a Borel.
Containment is factorization of group-scheme embeddings. Smoothness and closedness
of the original relative subgroup are supplied separately by the caller.
Source: Conrad, Definition 5.2.1 (blueprint: def-sfb-geometric-parabolic-subgroup). -/
def HasParabolicFibres {A : Type u} [CommRing A]
    {P G : Grp (Over (Spec (.of A)))} (i : P ⟶ G) : Prop :=
  ∀ (F : Type u) [Field F] [IsAlgClosed F] (f : A →+* F),
    Smooth ((fibre f).obj P).X.hom ∧ ConnectedSpace ((fibre f).obj P).X.left ∧
      ∃ (B : Grp (Over (Spec (.of F)))) (b : B ⟶ (fibre f).obj G),
        IsBorelGroupScheme b.hom.hom ∧ ∃ j : B ⟶ (fibre f).obj P,
          j ≫ (fibre f).map i = b

end AlgebraicGeometry.GeometricParabolic
