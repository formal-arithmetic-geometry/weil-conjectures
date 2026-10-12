module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace CategoryTheory.Over.DescentDatum

/-- The gluing construction produces the ambient scheme, charts, and glued map.
(blueprint: lem-pd-glued-effective-model-charts-aux) -/
theorem exists_glued_model_data
    {X Y : Scheme.{u}} {p : X ⟶ Y}
    (hp : Presieve.singleton p ∈ Scheme.fpqcPrecoverage Y)
    {V : Over X} (D : Over.DescentDatum p V)
    {I : Type u} (U : I → V.left.Opens)
    (hcover : ∀ x : V.left, ∃ i, x ∈ U i)
    (E : ∀ i, Over.DescentDatum p (Over.mk ((U i).ι ≫ V.hom)))
    (hcompat : ∀ (i : I) {T : Scheme.{u}} (f₁ f₂ : T ⟶ X)
      (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ Over.mk ((U i).ι ≫ V.hom)),
      ((E i).transport f₁ f₂ h a).left ≫ (U i).ι =
        (D.transport f₁ f₂ h (Over.homMk (a.left ≫ (U i).ι)
          (by simpa only [Over.mk_hom, Category.assoc] using Over.w a))).left)
    (W : I → Over Y) (q : ∀ i, (U i).toScheme ⟶ (W i).left)
    (hcart : ∀ i, IsPullback (q i) ((U i).ι ≫ V.hom) (W i).hom p)
    (hinv : ∀ (i : I) {T : Scheme.{u}} (f₁ f₂ : T ⟶ X)
      (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ Over.mk ((U i).ι ≫ V.hom)),
      ((E i).transport f₁ f₂ h a).left ≫ q i = a.left ≫ q i) :
    ∃ (W₀ : Over Y) (q₀ : V.left ⟶ W₀.left) (j : ∀ i, (W i).left ⟶ W₀.left),
      (∀ i, IsOpenImmersion (j i)) ∧
      (∀ w : W₀.left, ∃ i, ∃ z : (W i).left, j i z = w) ∧
      (∀ i, j i ≫ W₀.hom = (W i).hom) ∧
      (∀ i, q i ≫ j i = (U i).ι ≫ q₀) := by sorry

end CategoryTheory.Over.DescentDatum
