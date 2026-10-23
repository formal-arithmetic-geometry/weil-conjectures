module

public import WeilConjectures.TraceFormula.HomologyWeilLowerShriek

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)

theorem nonempty_weilLowerShriek_iso_weilLowerStar' [IsProper f.left]
    (K : WeilBoundedConstructible ℓ eX.hom) :
    Nonempty ((weilLowerShriek ℓ eX eY hf).obj K ≅ (weilLowerStar ℓ eX eY f hf).obj K) := by
  refine ⟨IsoAlgebra.isoMk ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).app
    K.carrier) ?_⟩
  rw [← IsoAlgebra.str_hom, ← IsoAlgebra.str_hom, weilLowerShriek_obj_str, weilLowerStar_obj_str]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, asIso_hom, Category.assoc]
  have hn := (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.naturality
    K.str.hom
  rw [hn, ← Category.assoc, ← Category.assoc, weilLowerShriekComparison_hom,
    boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isProper]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
