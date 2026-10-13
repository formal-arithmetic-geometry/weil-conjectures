module

public import Sheaf.Algebra.Homology.HomTensorDegreewise

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (R : Sheaf J CommRingCat.{u})
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

set_option hygiene false in
local notation "Mod" => SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

/-- Degree-zero localized currying, with the zero additions removed from the indices.
Source: Stacks Project, sites-cohomology.tex, Tag 0A90, degreewise evaluation;
`HomTensorCurryCondition` in HomTensorDegreewise.
(blueprint: lem-pc-hom-tensor-curry-zero).

Proof: specialize HomTensorCurryCondition to degree zero and the displayed
p,r,U,s,W,x,y. Its outer projection lands in degree p+0=p, its output
projection lands in degree p+r+0=p+r, and its inner projection has
r+(p+0)=p+r+0. Transport along the two integer add-zero equalities;
proof irrelevance identifies all witnesses of these index equalities.
This changes no morphism, tensor, section, or localized evaluation. -/
theorem homTensorCurryCondition_zero (P L I : CochainComplex Mod ℤ) :
    letI := SheafOfModules.monoidalCategory R
    ∀ (a : (homComplex (R := R) P (homComplex (R := R) L I)).X 0 ⟶
        (homComplex (R := R)
          (CochainComplex.mapBifunctor P L (curriedTensor Mod)) I).X 0),
      HomTensorCurryCondition R P L I 0 a →
      ∀ (p r : ℤ) (U : Cᵒᵖ)
        (s : (homComplex (R := R) P (homComplex (R := R) L I)).X 0 |>.val.obj U)
        (W : (Over U.unop)ᵒᵖ) (x : (P.X p).val.obj (op W.unop.left))
        (y : (L.X r).val.obj (op W.unop.left)),
      let φ := ((homTensorProjection R
        (CochainComplex.mapBifunctor P L (curriedTensor Mod)) I
        0 (p + r) (p + r) (add_zero _)).val.app U).hom ((a.val.app U).hom s)
      let ψ := ((homTensorProjection R P (homComplex (R := R) L I)
        0 p p (add_zero _)).val.app U).hom s
      let χ := ((homTensorProjection R L I p r (p + r)
        (by omega)).val.app (op W.unop.left)).hom ((ψ.app W).hom x)
      (φ.app W).hom
        (((CochainComplex.ιMapBifunctor P L (curriedTensor Mod)
          p r (p + r) rfl).val.app (op W.unop.left)).hom
          (((homTensorSectionMap R (P.X p) (L.X r)).app (op W.unop.left)).hom
            (x ⊗ₜ[R.obj.obj (op W.unop.left)] y))) =
        (χ.app (op (Over.mk (𝟙 W.unop.left)))).hom y := by
  let := SheafOfModules.monoidalCategory R
  intro a ha p r U s W x y
  have aux (p' t : ℤ) (hp : p + 0 = p') (ht : p + r + 0 = t) :
      let φ := ((homTensorProjection R
        (CochainComplex.mapBifunctor P L (curriedTensor Mod)) I
        0 (p + r) t ht).val.app U).hom ((a.val.app U).hom s)
      let ψ := ((homTensorProjection R P (homComplex (R := R) L I)
        0 p p' hp).val.app U).hom s
      let χ := ((homTensorProjection R L I p' r t
        (by omega)).val.app (op W.unop.left)).hom ((ψ.app W).hom x)
      (φ.app W).hom
        (((CochainComplex.ιMapBifunctor P L (curriedTensor Mod)
          p r (p + r) rfl).val.app (op W.unop.left)).hom
          (((homTensorSectionMap R (P.X p) (L.X r)).app (op W.unop.left)).hom
            (x ⊗ₜ[R.obj.obj (op W.unop.left)] y))) =
        (χ.app (op (Over.mk (𝟙 W.unop.left)))).hom y := by
    subst p' t
    exact ha p r U s W x y
  exact aux p (p + r) (add_zero _) (add_zero _)

end CategoryTheory
