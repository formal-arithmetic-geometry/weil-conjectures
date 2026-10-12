module
public import Sheaf.AlgebraicGeometry.CoherentThickeningSystem
public import Sheaf.AlgebraicGeometry.CoherentFormalModule

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Componentwise conjugation identifies system arrows with families compatible with `d`.
Source: Stacks Project, Remark 088F and Lemma 087T.
(blueprint: lem-weil-pbc-thickening-system-hom-transport-core).
-/
theorem thickeningSystem_hom_transport_d
    {X : Scheme.{u}} {T : ℕ → Scheme.{u}} {i : ∀ n, T n ⟶ T (n + 1)}
    (j : ∀ n, T n ⟶ X) (d : ∀ n, Scheme.Modules.tensorPullback (j (n + 1)) ⋙
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
        ∀ n, (d n).hom.app G.obj ≫ v n =
          (Scheme.Modules.tensorPullback (i n)).map (v (n + 1)) ≫ (d n).hom.app F.obj},
      ∀ w : G ⟶ F, e (R.map w) =
        ⟨fun n ↦ (Scheme.Modules.tensorPullback (j n)).map w.hom,
          fun n ↦ ((d n).hom.naturality w.hom).symm⟩ := by
  sorry

end AlgebraicGeometry
