module

public import Sheaf.Algebra.Homology.HomTensorDegreewise

/-!
# Localized pure-tensor differential calculation

Source: Stacks Project, Tag 0A90 and the calculation in Tag 0A5Y.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

set_option synthInstance.maxSize 256 in
/-- The iterated Hom differential agrees with the three tensor differential terms
on one localized pure tensor.
Source: Stacks Project, Tag 0A90 and the calculation in More on Algebra Tag 0A5Y.
(blueprint: lem-sc-hom-tensor-differential-summand-pure)

Proof: Apply the degree-(n+1) curry equation to the image of s under the outer
Hom differential. Expand that differential using its product projection identity.
Its postcomposition evaluates the inner differential on the outer evaluation of s;
its precomposition contributes minus (-1)^n times the evaluation at d_K(x).
Expand the inner differential: its postcomposition is d_M applied to f(x)(y),
and its precomposition is minus (-1)^(p+n) times f(x)(d_L(y)).
Apply the degree-n curry equation separately to the three terms on the right.
The first tensor summand differential sends x tensor y to d_K(x) tensor y.
The second sends it to (-1)^p times x tensor d_L(y), by the definition of d2.
Naturality of the canonical presheaf-to-sheaf tensor map identifies these values
before and after sheafification. The sign identity (p+n).negOnePow =
p.negOnePow * n.negOnePow then identifies the second inner differential term
with the signed d2 term. The two subtractions occur in opposite order, which
commute in the target module. The argument works for all integer degrees and
zero sections, tensor factors or differentials. This is only a scalar equality
on pure tensors and does not assert extensionality on sheaf tensors. -/
theorem homTensorDifferential_summand_pure
    (K L M : CochainComplex Mod ℤ) (n t p q : ℤ) (h : p + q = t) :
    letI := SheafOfModules.monoidalCategory R
    let T := CochainComplex.mapBifunctor K L (curriedTensor Mod)
    let ι := CochainComplex.ιMapBifunctor K L (curriedTensor Mod) p q t h
    let f :=
      (homComplex (R := R) K (homComplex (R := R) L M)).d n (n + 1) ≫
        homTensorDegreewiseMap R K L M (n + 1) ≫
          homTensorProjection R T M (n + 1) t (t + (n + 1)) rfl ≫
            SheafOfModules.homObjMap (R := R) ι (𝟙 (M.X (t + (n + 1))))
    let g :=
      (homTensorDegreewiseMap R K L M n ≫
        homTensorProjection R T M n t (t + n) rfl ≫
          SheafOfModules.homObjMap (R := R) ι (M.d (t + n) (t + (n + 1)))) -
      n.negOnePow • (homTensorDegreewiseMap R K L M n ≫
        homTensorProjection R T M n (t + 1) (t + (n + 1)) (by omega) ≫
          SheafOfModules.homObjMap (R := R)
            (HomologicalComplex.mapBifunctor.d₁ K L (curriedTensor Mod)
              (ComplexShape.up ℤ) p q (t + 1)) (𝟙 (M.X (t + (n + 1))))) -
      n.negOnePow • (homTensorDegreewiseMap R K L M n ≫
        homTensorProjection R T M n (t + 1) (t + (n + 1)) (by omega) ≫
          SheafOfModules.homObjMap (R := R)
            (HomologicalComplex.mapBifunctor.d₂ K L (curriedTensor Mod)
              (ComplexShape.up ℤ) p q (t + 1)) (𝟙 (M.X (t + (n + 1)))))
    ∀ (U : Cᵒᵖ)
      (s : (homComplex (R := R) K (homComplex (R := R) L M)).X n |>.val.obj U)
      (W : (Over U.unop)ᵒᵖ) (x : (K.X p).val.obj (op W.unop.left))
      (y : (L.X q).val.obj (op W.unop.left)),
      (((f.val.app U).hom s).app W).hom
        (((homTensorSectionMap R (K.X p) (L.X q)).app (op W.unop.left)).hom
          (x ⊗ₜ[R.obj.obj (op W.unop.left)] y)) =
      (((g.val.app U).hom s).app W).hom
        (((homTensorSectionMap R (K.X p) (L.X q)).app (op W.unop.left)).hom
          (x ⊗ₜ[R.obj.obj (op W.unop.left)] y)) := by sorry

end CategoryTheory
