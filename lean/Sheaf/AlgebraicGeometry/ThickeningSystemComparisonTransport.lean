module
public import Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful
public import Sheaf.AlgebraicGeometry.CoherentFormalModule

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Comparison isomorphisms induce the same compatible-family subtype.
Source: Stacks Project, Lemma 087T and Remark 088F.
(blueprint: lem-weil-pbc-thickening-system-comparison-transport).
-/
theorem compatible_family_comparison_equiv
    {X : Scheme.{u}} {T : ℕ → Scheme.{u}} {i : ∀ n, T n ⟶ T (n + 1)}
    (j : ∀ n, T n ⟶ X) (hj : ∀ n, IsClosedImmersion (j n))
    (c d : ∀ n, Scheme.Modules.tensorPullback (j (n + 1)) ⋙
      Scheme.Modules.tensorPullback (i n) ≅ Scheme.Modules.tensorPullback (j n))
    (F G : CoherentModules X) :
    ∃ e : ({v : ∀ n, (Scheme.Modules.tensorPullback (j n)).obj G.obj ⟶
        (Scheme.Modules.tensorPullback (j n)).obj F.obj |
        ∀ n, (d n).hom.app G.obj ≫ v n =
          (Scheme.Modules.tensorPullback (i n)).map (v (n + 1)) ≫ (d n).hom.app F.obj}) ≃
      {v : ∀ n, (Scheme.Modules.tensorPullback (j n)).obj G.obj ⟶
        (Scheme.Modules.tensorPullback (j n)).obj F.obj |
        ∀ n, (c n).hom.app G.obj ≫ v n =
          (Scheme.Modules.tensorPullback (i n)).map (v (n + 1)) ≫ (c n).hom.app F.obj},
      ∀ v, (e v).val = v.val := by
  sorry

end AlgebraicGeometry
