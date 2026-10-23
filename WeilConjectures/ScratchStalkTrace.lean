module

public import WeilConjectures.TraceFormula.FiniteEtaleStalkTrace

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] {X Y : Over (Spec (.of k))}
  (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (σ : Spec (.of Ω) ⟶ Spec (.of Ω))

lemma weilStalkComparison_hom_app {Z : Over (Spec (.of k))} (e : Z ≅ Z)
    {x : Spec (.of Ω) ⟶ Z.left} (hx : x ≫ e.hom.left = σ ≫ x)
    (M : Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left)) :
    (weilStalkComparison ℓ e σ x hx).hom.app M =
      (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ).inv.app
          ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ x).inv.app M ≫
        (upperStarCongr (Profinite.padicAlgClRingObj ℓ) hx.symm).hom.app M ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) x e.hom.left).hom.app M :=
  rfl

lemma weilStalkTransport_eq {x x' : Spec (.of Ω) ⟶ X.left}
    (h : x ≫ eX.hom.left = σ ≫ x') (F : WeilSheaf ℓ eX) :
    weilStalkTransport ℓ eX σ h F =
      (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ).inv.app _ ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ x').inv.app _ ≫
        (upperStarCongr (Profinite.padicAlgClRingObj ℓ) h.symm).hom.app F.carrier ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) x eX.hom.left).hom.app _ ≫
        (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map F.str.hom := by
  rw [weilStalkTransport, upperStarCongr, eqToIso.hom, eqToHom_app]

lemma weilStalkTransport_self' {x : Spec (.of Ω) ⟶ X.left} (h : x ≫ eX.hom.left = σ ≫ x)
    (F : WeilSheaf ℓ eX) :
    weilStalkTransport ℓ eX σ h F = stalkFrobenius ℓ σ eX h F.str.hom := by
  rw [weilStalkTransport_eq, stalkFrobenius, weilStalkComparison_hom_app]
  simp only [Category.assoc]

end AlgebraicGeometry.ProEtale.CondensedRing
