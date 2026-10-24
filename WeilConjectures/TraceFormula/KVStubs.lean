module

public import WeilConjectures.TraceFormula.KunnethVerdierOpen

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y Z : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom]

theorem exceptionalKunnethMapRestriction (j : Z ⟶ Y) [IsOpenImmersion j.left]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) : ExceptionalKunnethMapRestriction ℓ j M :=
  sorry

theorem isIso_kunnethVerdierMap_lowerShriek_iff_of_isClosedImmersion (g : Z ⟶ Y)
    [IsClosedImmersion g.left] (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (N' : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (kunnethVerdierMap ℓ (Y := Y) M
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ g).obj N')) ↔
      IsIso (kunnethVerdierMap ℓ (Y := Z) M N') :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
