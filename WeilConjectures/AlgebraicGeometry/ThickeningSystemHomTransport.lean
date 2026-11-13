/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentThickeningSystem
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful
import WeilConjectures.AlgebraicGeometry.ThickeningSystemHomTransportCore
import WeilConjectures.AlgebraicGeometry.ThickeningSystemComparisonTransport
import WeilConjectures.AlgebraicGeometry.TensorPullback

/-! # Transport of compatible morphism families

## References

* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Evaluation comparisons transport system arrows to restriction families, independently
of the natural pullback comparison chosen. This concerns a restriction functor only;
it makes no assertion about formal completions or an equivalence of categories. -/
theorem thickeningSystem_hom_transport
    {X : Scheme.{u}} {T : ℕ → Scheme.{u}} {i : ∀ n, T n ⟶ T (n + 1)}
    (j : ∀ n, T n ⟶ X) (hj : ∀ n, IsClosedImmersion (j n))
    (c d : ∀ n, Scheme.Modules.tensorPullback (j (n + 1)) ⋙
      Scheme.Modules.tensorPullback (i n) ≅ Scheme.Modules.tensorPullback (j n))
    (R : CoherentModules X ⥤ CoherentThickeningSystem T i)
    (r : ∀ n, R ⋙ CoherentThickeningSystem.evaluation T i n ≅
      ObjectProperty.ι (RingedSpace.IsCoherent X.toRingedSpace) ⋙
        Scheme.Modules.tensorPullback (j n))
    (hr : ∀ (F : CoherentModules X) (n : ℕ),
      ((R.obj F).comparison n).hom ≫ (r n).hom.app F =
        (Scheme.Modules.tensorPullback (i n)).map ((r (n + 1)).hom.app F) ≫
          (d n).hom.app F.obj)
    (F G : CoherentModules X) :
    ∃ e : (R.obj G ⟶ R.obj F) ≃
      {v : ∀ n, (Scheme.Modules.tensorPullback (j n)).obj G.obj ⟶
        (Scheme.Modules.tensorPullback (j n)).obj F.obj |
        ∀ n, (c n).hom.app G.obj ≫ v n =
          (Scheme.Modules.tensorPullback (i n)).map (v (n + 1)) ≫ (c n).hom.app F.obj},
      ∀ w : G ⟶ F, e (R.map w) =
        ⟨fun n ↦ (Scheme.Modules.tensorPullback (j n)).map w.hom,
          fun n ↦ ((c n).hom.naturality w.hom).symm⟩ := by
  obtain ⟨ed, hed⟩ := thickeningSystem_hom_transport_d j d R r hr F G
  obtain ⟨ec, hec⟩ := compatible_family_comparison_equiv j hj c d F G
  refine ⟨ed.trans ec, ?_⟩
  intro w
  apply Subtype.ext
  change (ec (ed (R.map w))).val = _
  rw [hec, hed]

end AlgebraicGeometry
