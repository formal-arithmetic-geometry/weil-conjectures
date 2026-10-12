module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Cech
public import Sheaf.Paper.PowerSetComplexContractible
public import Mathlib.LinearAlgebra.DFinsupp

/-! # Tuple generators of the evaluated free Čech object

Source: Stacks Project, Tags 03AT and 03F5, the degreewise direct-sum decomposition.
(blueprint: lem-weil-pbc-free-cech-tuple-basis)
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite Simplicial

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (ι : Type u) (U₀ : X.Etale) (U : ι → X.Etale)
  (f : ∀ i : ι, U i ⟶ U₀) (O : X.Etaleᵒᵖ ⥤ RingCat.{u}) (W : X.Etale)

/-- The simplicial free presheaf module attached to the family.
Source: Stacks Project, Tag 03F5 (blueprint: lem-weil-pbc-free-cech-tuple-basis). -/
noncomputable abbrev freeCechModule : SimplicialObject (PresheafOfModules.{u} O) :=
  (FormalCoproduct.mk ι fun i ↦ Over.mk (f i)).cech ⋙
    (FormalCoproduct.eval (Over U₀) (PresheafOfModules.{u} O)).obj
      (Over.forget U₀ ⋙ yoneda ⋙ PresheafOfModules.free O)

/-- Lifts of a fixed map to the base, retaining their family indices.
Source: Stacks Project, Tag 03AT (blueprint: lem-weil-pbc-free-cech-tuple-basis). -/
abbrev freeCechLifts (φ : W ⟶ U₀) := Σ i : ι, {g : W ⟶ U i // g ≫ f i = φ}

/-- The generator associated to a tuple of lifts: map to their product in the over
category, take its free generator, and inject into the coproduct summand.
Source: Stacks Project, Tag 03AT (blueprint: lem-weil-pbc-free-cech-tuple-basis). -/
noncomputable def freeCechTupleGenerator (n : ℕ) (φ : W ⟶ U₀)
    (x : Fin (n + 1) → freeCechLifts X ι U₀ U f W φ) :
    ((freeCechModule X ι U₀ U f O).obj (op ⦋n⦌)).obj (op W) :=
  let i : Fin (n + 1) → ι := fun a ↦ (x a).1
  let g : Over.mk φ ⟶ ∏ᶜ (fun a ↦ Over.mk (f (i a))) :=
    Pi.lift (fun a ↦ Over.homMk (x a).2.1 (x a).2.2)
  ((Sigma.ι
    (fun j : Fin (n + 1) → ι ↦
      (PresheafOfModules.free O).obj
        (yoneda.obj ((∏ᶜ (fun a ↦ Over.mk (f (j a)))).left))) i).app (op W))
    (ModuleCat.freeMk g.left)

/-- Linear extension of the tuple generators, first within each block and then over
all maps to the base.
Source: Stacks Project, Tag 03AT (blueprint: lem-weil-pbc-free-cech-tuple-basis). -/
noncomputable def freeCechTupleMap (n : ℕ) :
    (Π₀ φ : W ⟶ U₀,
      Algebra.powerSetComplexObject (O.obj (op W)) (freeCechLifts X ι U₀ U f W φ) n) →ₗ[
        O.obj (op W)] ((freeCechModule X ι U₀ U f O).obj (op ⦋n⦌)).obj (op W) := by
  classical
  exact DFinsupp.lsum ℕ (fun φ ↦
    Finsupp.lift _ _ _ (freeCechTupleGenerator X ι U₀ U f O W n φ))

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of the linear extension on one block generator.
Source: Stacks Project, Tag 03AT (blueprint: lem-weil-pbc-free-cech-tuple-basis). -/
@[simp]
theorem freeCechTupleMap_single [DecidableEq (W ⟶ U₀)] (n : ℕ) (φ : W ⟶ U₀)
    (x : Fin (n + 1) → freeCechLifts X ι U₀ U f W φ) (r : O.obj (op W)) :
    freeCechTupleMap X ι U₀ U f O W n (DFinsupp.single φ (Finsupp.single x r)) =
      r • freeCechTupleGenerator X ι U₀ U f O W n φ x := by
  classical
  calc
    _ = (Finsupp.lift _ _ _ (freeCechTupleGenerator X ι U₀ U f O W n φ))
        (Finsupp.single x r) := DFinsupp.lsum_single ℕ
          (fun ψ : W ⟶ U₀ ↦ Finsupp.lift _ _ _
            (freeCechTupleGenerator X ι U₀ U f O W n ψ)) φ (Finsupp.single x r)
    _ = _ := by simp [Finsupp.lift_apply]

/-- The tuple-generator map is bijective in each degree.
Source: Stacks Project, Tag 03AT, the decomposition preceding the homotopy;
Tag 03F5, first proof, with coefficients in O(W).
Proof: Evaluation preserves coproducts of presheaf modules. Each evaluated free
representable is the free O(W)-module on morphisms from W. Its basis is thus the
pairs (i,g) with i : Fin (n+1) → ι and g : W → the product over U₀ of U(i(a)).
Send such a pair to the common composite φ and its tuple of projections. Conversely,
from φ and a tuple of lifts form the product map in Over U₀ by Pi.lift. The projection
and uniqueness identities for the product show these functions are inverse. The
free-module extension of this bijection and the regrouping of finite support by φ
are linear isomorphisms; their inverse is exactly the displayed tuple-generator map.
This also handles an empty family, when both bases are empty, and the zero ring,
when both modules are zero. No lift of an arbitrary φ is chosen.
(blueprint: lem-weil-pbc-free-cech-tuple-basis) -/
theorem freeCechTupleMap_bijective (n : ℕ) :
    Function.Bijective (freeCechTupleMap X ι U₀ U f O W n) := by sorry

end AlgebraicGeometry
