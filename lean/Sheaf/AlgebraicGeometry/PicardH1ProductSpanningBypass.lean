module

public import Sheaf.AlgebraicGeometry.PicardExternalCupScalarComparison
public import Sheaf.AlgebraicGeometry.ProperBasic
public import Sheaf.Algebra.Homology.TensorKunnethNat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Morphisms.Proper

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct DirectSum
namespace AlgebraicGeometry.Scheme
open Modules
noncomputable section
attribute [local irreducible] Modules.scalarCohomology structureSheafAb
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

private axiom h1_kunneth_actual
    (k : Type u) [Field k] (X Y : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    ∃ e : (⨁ i : {pq : ℕ × ℕ // pq.1 + pq.2 = 1},
        Modules.scalarCohomology f F i.val.1 ⊗[k] Modules.scalarCohomology g G i.val.2) ≃ₗ[k]
      Modules.scalarCohomology (pullback.fst f g ≫ f)
        (Modules.externalCupCoefficients f g F G) 1,
      ∀ (i : {pq : ℕ × ℕ // pq.1 + pq.2 = 1})
        (a : Modules.scalarCohomology f F i.val.1)
        (b : Modules.scalarCohomology g G i.val.2),
        e (DirectSum.lof k _ _ i (a ⊗ₜ[k] b)) =
          cast (congrArg (fun d ↦ ↥(Modules.scalarCohomology
            (pullback.fst f g ≫ f) (Modules.externalCupCoefficients f g F G) d)) i.property)
            (Modules.externalCup f g F G i.val.1 i.val.2 a b)

theorem picard_h1_product_spanning_bypass (k : Type u) [Field k] (X Y : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [IsProper (X ↘ Spec (CommRingCat.of k))] [IsProper (Y ↘ Spec (CommRingCat.of k))]
    (hX : Function.Bijective (globalSectionsRingHom k (X := X)))
    (hY : Function.Bijective (globalSectionsRingHom k (X := Y))) :
    ∀ c : Sheaf.H (structureSheafAb
      (pullback (X ↘ Spec (CommRingCat.of k)) (Y ↘ Spec (CommRingCat.of k)))) 1,
      ∃ a : Sheaf.H (structureSheafAb X) 1,
        ∃ b : Sheaf.H (structureSheafAb Y) 1,
          structureSheafCohomologyPullback
              (pullback.fst (X ↘ Spec (CommRingCat.of k)) (Y ↘ Spec (CommRingCat.of k))) 1 a +
            structureSheafCohomologyPullback
              (pullback.snd (X ↘ Spec (CommRingCat.of k)) (Y ↘ Spec (CommRingCat.of k))) 1 b = c := by
  classical
  let f := X ↘ Spec (CommRingCat.of k)
  let g := Y ↘ Spec (CommRingCat.of k)
  let F := SheafOfModules.unit X.ringCatSheaf
  let G := SheafOfModules.unit Y.ringCatSheaf
  have : CompactSpace X := (AlgebraicGeometry.proper_basic f).2.2.2.2.2 inferInstance |>.2
  have : CompactSpace Y := (AlgebraicGeometry.proper_basic g).2.2.2.2.2 inferInstance |>.2
  have : F.IsQuasicoherent := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have : G.IsQuasicoherent := SheafOfModules.isQuasicoherent_unit (R := Y.ringCatSheaf)
  obtain ⟨e, he⟩ := h1_kunneth_actual k X Y f g F G
  have hX' : Function.Bijective (Modules.scalarMap f ⊤) := by
    simpa [Modules.scalarMap, globalSectionsRingHom, f] using hX
  have hY' : Function.Bijective (Modules.scalarMap g ⊤) := by
    simpa [Modules.scalarMap, globalSectionsRingHom, g] using hY
  obtain ⟨eX, eY, eP, dX, dY, h10, h01⟩ :=
    picard_external_cup_scalar_comparison k X Y f g hX' hY'
  let I := {pq : ℕ × ℕ // pq.1 + pq.2 = 1}
  let T := fun i : I ↦ Modules.scalarCohomology f F i.val.1 ⊗[k]
    Modules.scalarCohomology g G i.val.2
  let px := structureSheafCohomologyPullback (pullback.fst f g) 1
  let py := structureSheafCohomologyPullback (pullback.snd f g) 1
  let Φ : (⨁ i : I, T i) →+ Sheaf.H (structureSheafAb (pullback f g)) 1 :=
    eP.toAddMonoidHom.comp e.toAddMonoidHom
  let P := fun z : ⨁ i : I, T i ↦ ∃ a b, px a + py b = Φ z
  have hz : P 0 := by refine ⟨0, 0, ?_⟩; simp [Φ]
  have ha (x y : ⨁ i : I, T i) (hx : P x) (hy : P y) : P (x + y) := by
    obtain ⟨a, b, hab⟩ := hx; obtain ⟨a', b', hab'⟩ := hy
    refine ⟨a + a', b + b', ?_⟩
    rw [px.map_add, py.map_add]
    calc
      px a + px a' + (py b + py b') = (px a + py b) + (px a' + py b') := by abel
      _ = Φ x + Φ y := congrArg₂ (· + ·) hab hab'
      _ = Φ (x + y) := (map_add Φ x y).symm
  have hp (i : I) (a : Modules.scalarCohomology f F i.val.1)
      (b : Modules.scalarCohomology g G i.val.2) : P (DirectSum.of T i (a ⊗ₜ[k] b)) := by
    have hi : i = ⟨(1, 0), rfl⟩ ∨ i = ⟨(0, 1), rfl⟩ := by
      rcases i with ⟨⟨p, q⟩, h⟩
      have : (p = 1 ∧ q = 0) ∨ (p = 0 ∧ q = 1) := by omega
      rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    rcases hi with rfl | rfl
    · refine ⟨eX (dY b • a), 0, ?_⟩
      change px (eX (dY b • a)) + py 0 = eP (e (DirectSum.of T _ (a ⊗ₜ[k] b)))
      rw [py.map_zero, add_zero]
      have h := congrArg eP (he ⟨(1, 0), rfl⟩ a b)
      exact (h10 a b).symm.trans (by
        simpa only [T, I, DirectSum.lof_eq_of, cast_eq, F, G] using h.symm)
    · refine ⟨0, eY (dX a • b), ?_⟩
      change px 0 + py (eY (dX a • b)) = eP (e (DirectSum.of T _ (a ⊗ₜ[k] b)))
      rw [px.map_zero, zero_add]
      have h := congrArg eP (he ⟨(0, 1), rfl⟩ a b)
      exact (h01 a b).symm.trans (by
        simpa only [T, I, DirectSum.lof_eq_of, cast_eq, F, G] using h.symm)
  have hspan (z : ⨁ i : I, T i) : P z := by
    induction z using DirectSum.induction_on with
    | zero => exact hz
    | of i t =>
      induction t using TensorProduct.induction_on with
      | zero => simpa using hz
      | tmul a b => exact hp i a b
      | add x y hx hy => simpa only [map_add] using ha (DirectSum.of T i x) (DirectSum.of T i y) hx hy
    | add x y hx hy => exact ha x y hx hy
  intro c
  obtain ⟨d, hd⟩ := eP.surjective c
  obtain ⟨z, hez⟩ := e.surjective d
  obtain ⟨a, b, hab⟩ := hspan z
  refine ⟨a, b, hab.trans ?_⟩
  change eP (e z) = c
  exact (congrArg eP hez).trans hd

end
end AlgebraicGeometry.Scheme
