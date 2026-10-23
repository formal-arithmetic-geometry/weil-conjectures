module

public import WeilConjectures.TraceFormula.WeilTrace

@[expose] public section

universe u

open CategoryTheory Endofunctor MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing


variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k] {X : Over (Spec (.of k))}
  {e : X ≅ X} (n : ℕ) (x : Spec (.of (AlgebraicClosure k)) ⟶ X.left)
  (hx : x ≫ (e.powSucc n).hom.left = ((geometricFrobeniusField k).powSucc n).hom ≫ x)

set_option maxHeartbeats 4000000 in
lemma test13 (F : WeilSheaf ℓ e) :
    weilSheafStalkTrace ℓ n x hx F = categoricalTrace
      ((weilStalkComparison ℓ (e.powSucc n) ((geometricFrobeniusField k).powSucc n).hom x hx).hom.app
        F.carrier ≫ (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
          (WeilSheaf.powSucc ℓ F n).str.hom) := by
  unfold weilSheafStalkTrace
  rw [WeilSheaf.frobeniusStalk, WeilSheaf.powSuccStalkFunctor, Functor.comp_obj,
    WeilSheaf.stalkFunctor_obj_str, WeilSheaf.powSuccFunctor_obj]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
