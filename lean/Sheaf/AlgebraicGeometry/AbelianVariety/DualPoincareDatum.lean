module

public import Sheaf.AlgebraicGeometry.LineAlgebraicEquivalence
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # The normalized dual abelian variety datum

Source: Milne, Abelian Varieties, I §8, pp.36–40, and §9 opening paragraph.
(blueprint: def-sfb-abelian-dual-poincare-datum)

The representing property includes every parameter scheme and every rigidification.
No dual variety, line module or classifying map is selected by an existence proof.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj

open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

open Scheme.Modules

/-- The identity axis in a family on `A × T`.
Source: Milne AV I §8, p.36 (blueprint: def-sfb-abelian-dual-poincare-datum). -/
def abelianIdentityAxis {k : Type u} [Field k]
    (A T : Over (Spec (.of k))) [GrpObj A] : T ⟶ A ⊗ T :=
  lift (toUnit T ≫ η[A]) (𝟙 T)

/-- Fibrewise algebraic triviality, tested on all algebraically closed field-valued points.
The fibre of `A` is regarded over that field, rather than over `k`. In particular this
condition neither assumes that the parameter is reduced nor tests only its rational points.
Source: Milne AV I §8, pp.36–40 (blueprint: def-sfb-abelian-dual-poincare-datum). -/
def IsFibrewiseAlgebraicallyTrivial {k : Type u} [Field k]
    (A T : Over (Spec (.of k))) (M : (A ⊗ T).left.Modules) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of k))
    (t : Over.mk s ⟶ T),
    AreAlgebraicallyEquivalent (Over.mk (pullback.snd A.hom s))
      ((Scheme.Modules.pullback (A ◁ t).left).obj M)
      (𝟙_ (pullback A.hom s).Modules)

/-- Pulling the specified rigidification back along a parameter map. The comparison is
built from the canonical composition, equality and unit comparisons for module pullback.
Source: Milne AV I §8, pp.36–40 (blueprint: def-sfb-abelian-dual-poincare-datum). -/
def abelianRigidificationPullback {k : Type u} [Field k]
    (A D T : Over (Spec (.of k))) [GrpObj A]
    (P : (A ⊗ D).left.Modules)
    (r : (Scheme.Modules.pullback (abelianIdentityAxis A D).left).obj P ≅
      𝟙_ D.left.Modules) (f : T ⟶ D) :
    (Scheme.Modules.pullback (abelianIdentityAxis A T).left).obj
      ((Scheme.Modules.pullback (A ◁ f).left).obj P) ≅ 𝟙_ T.left.Modules :=
  (Scheme.Modules.pullbackComp (abelianIdentityAxis A T).left (A ◁ f).left).app P ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left
      ((lift_whiskerLeft (toUnit T ≫ η[A]) (𝟙 T) f).trans
        ((congrArg₂ lift
          ((Category.assoc f (toUnit D) η[A]).trans
            (congrArg (fun h ↦ h ≫ η[A]) (comp_toUnit f))).symm
          ((Category.id_comp f).trans (Category.comp_id f).symm)).trans
            (comp_lift f (toUnit D ≫ η[A]) (𝟙 D)).symm)))).app P ≪≫
    ((Scheme.Modules.pullbackComp f.left (abelianIdentityAxis A D).left).app P).symm ≪≫
    (Scheme.Modules.pullback f.left).mapIso r ≪≫ Scheme.Modules.pullbackObjUnitIso f.left

/-- A normalized Poincare module representing rigidified fibrewise algebraically trivial
line families. The last equation says explicitly that the classifying isomorphism respects
the supplied rigidification. The second identity axis represents the trivial line class.
Source: Milne AV I §8, pp.36–40 (blueprint: def-sfb-abelian-dual-poincare-datum). -/
structure AbelianDualPoincareDatum {k : Type u} [Field k]
    (A : Over (Spec (.of k))) [GrpObj A] where
  dual : Over (Spec (.of k))
  group : GrpObj dual
  abelian : IsAbelianVariety dual
  poincare : (A ⊗ dual).left.Modules
  invertible : poincare.IsInvertible
  rigidification : (Scheme.Modules.pullback (abelianIdentityAxis A dual).left).obj poincare ≅
    𝟙_ dual.left.Modules
  geometricFibres : IsFibrewiseAlgebraicallyTrivial A dual poincare
  otherAxis : Nonempty
    ((Scheme.Modules.pullback (lift (𝟙 A) (toUnit A ≫ η[dual])).left).obj poincare ≅
      𝟙_ A.left.Modules)
  tensorGroupLaw : ∀ (T : Over (Spec (.of k))) (f g : T ⟶ dual),
    Nonempty
      ((Scheme.Modules.pullback (A ◁ (f * g)).left).obj poincare ≅
        (Scheme.Modules.pullback (A ◁ f).left).obj poincare ⊗
          (Scheme.Modules.pullback (A ◁ g).left).obj poincare)
  universal : ∀ (T : Over (Spec (.of k))) (M : (A ⊗ T).left.Modules),
    M.IsInvertible → IsFibrewiseAlgebraicallyTrivial A T M →
    ∀ r : (Scheme.Modules.pullback (abelianIdentityAxis A T).left).obj M ≅ 𝟙_ T.left.Modules,
      ∃! f : T ⟶ dual,
        ∃ i : (Scheme.Modules.pullback (A ◁ f).left).obj poincare ≅ M,
          (Scheme.Modules.pullback (abelianIdentityAxis A T).left).map i.hom ≫ r.hom =
            (abelianRigidificationPullback A dual T poincare rigidification f).hom

attribute [instance] AbelianDualPoincareDatum.group AbelianDualPoincareDatum.abelian

/-- The explicitly normalized translated-difference family. The last tensor factor is
`c⁎(0⁎L)`; it avoids choosing a basis of the identity line and cancels on both axes.
Source: Milne AV I §8, pp.39–40 (blueprint: def-sfb-abelian-dual-poincare-datum). -/
def abelianNormalizedDifference {k : Type u} [Field k]
    (A : Over (Spec (.of k))) [GrpObj A] (L : A.left.Modules) : (A ⊗ A).left.Modules :=
  ((Scheme.Modules.pullback (μ[A]).left).obj L ⊗
    (Scheme.Modules.pullback (fst A A).left).obj (Scheme.Modules.dual L)) ⊗
    (Scheme.Modules.pullback (snd A A).left).obj (Scheme.Modules.dual L) ⊗
    (Scheme.Modules.pullback (toUnit (A ⊗ A)).left).obj
      ((Scheme.Modules.pullback (η[A]).left).obj L)

/-- A map classifies the normalized difference family. Representability forces uniqueness;
no arbitrary map replaces the family or its universal property.
Source: Milne AV I §8, pp.39–40 (blueprint: def-sfb-abelian-dual-poincare-datum). -/
def ClassifiesAbelianDifference {k : Type u} [Field k]
    {A : Over (Spec (.of k))} [GrpObj A] (D : AbelianDualPoincareDatum A)
    (L : A.left.Modules) (f : A ⟶ D.dual) : Prop :=
  Nonempty ((Scheme.Modules.pullback (A ◁ f).left).obj D.poincare ≅
    abelianNormalizedDifference A L)

end AlgebraicGeometry
