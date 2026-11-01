/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.SwapEvPairing
public import WeilConjectures.TraceFormula.OrdinaryKunneth

/-!

# The exceptional Künneth map and restriction to an open subscheme: statement

For an open immersion `j : U ⟶ Y` of separated `k`-schemes of finite type, the identifications
`L(𝟙 × j)^* (M ⊠ ω_Y) ≅ M ⊠ ω_U`
(`AlgebraicGeometry.ProEtale.CondensedRing.exceptionalKunnethSourceRestrictionIso`) and
`L(𝟙 × j)^* Rp_X^! M ≅ Rp_X^! M`
(`AlgebraicGeometry.ProEtale.CondensedRing.exceptionalKunnethTargetRestrictionIso`), and the
statement `AlgebraicGeometry.ProEtale.CondensedRing.ExceptionalKunnethMapRestriction` that the
exceptional Künneth map is compatible with them. It is used as a hypothesis in
`WeilConjectures.TraceFormula.KunnethVerdierOpen` and proved in
`WeilConjectures.TraceFormula.ExceptionalKunnethRestriction`. Also the compatibility of the
pullbacks with the Koszul braidings,
`AlgebraicGeometry.ProEtale.CondensedRing.μ_boundedConstructibleUpperStar_braiding`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

-- see the implementation notes of `WeilConjectures.TraceFormula.KunnethVerdierOpen`
attribute [local instance 2000] MonoidalCategory.toMonoidalCategoryStruct

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y U : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom]

omit [Fact ℓ.Prime] [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] in
/-- The product `𝟙 × j : X ⨯ U ⟶ X ⨯ Y` of an open immersion `j` is an open immersion, being the
base change of `j` along the second projection. -/
instance isOpenImmersion_prodMap_left (j : U ⟶ Y) [IsOpenImmersion j.left] :
    IsOpenImmersion (prod.map (𝟙 X) j).left :=
  MorphismProperty.of_isPullback ((IsPullback.of_prod_snd_with_id j X).map (Over.forget _))
    (inferInstanceAs (IsOpenImmersion j.left))

/-! ### The compatibility of the exceptional Künneth map with restriction -/

/-- The restriction `Lj^* ω_Y ≅ ω_U` of the dualizing complex to an open subscheme: the inverse
of `Rj^! ≅ Lj^*` followed by `Rj^! ω_Y ≅ ω_U`. -/
noncomputable def dualizingComplexUpperStarIso (j : U ⟶ Y) [IsOpenImmersion j.left] :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
        (dualizingComplex' ℓ Y) ≅ dualizingComplex' ℓ U :=
  (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j).symm.app _ ≪≫
    dualizingComplexComp ℓ j

/-- The restriction to `X ⨯ U` of the source of the exceptional Künneth map:
`L(𝟙 × j)^* (M ⊠ ω_Y) ≅ M ⊠ ω_U`, from the monoidal structure of `L(𝟙 × j)^*`, the composition
isomorphisms of the pullbacks and `Lj^* ω_Y ≅ ω_U`. -/
noncomputable def exceptionalKunnethSourceRestrictionIso (j : U ⟶ Y) [IsOpenImmersion j.left]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j)).obj
        (externalProduct ℓ M (dualizingComplex' ℓ Y)) ≅
      externalProduct ℓ M (dualizingComplex' ℓ U) :=
  (Functor.Monoidal.μIso _ _ _).symm ≪≫
    tensorIso ((prodMapUpperStarFstIso ℓ j).app M)
      ((prodMapUpperStarSndIso ℓ j).app _ ≪≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.snd : X ⨯ U ⟶ U)).mapIso (dualizingComplexUpperStarIso ℓ j))

/-- The restriction to `X ⨯ U` of the target of the exceptional Künneth map:
`L(𝟙 × j)^* Rp_X^! M ≅ R(𝟙 × j)^! Rp_X^! M ≅ R((𝟙 × j) ≫ p_X)^! M = Rp_X^! M`. -/
noncomputable def exceptionalKunnethTargetRestrictionIso (j : U ⟶ Y) [IsOpenImmersion j.left]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j)).obj
        ((boundedConstructibleUpperShriek ℓ
          (prod.fst : X ⨯ Y ⟶ X)).obj M) ≅
      (boundedConstructibleUpperShriek ℓ
        (prod.fst : X ⨯ U ⟶ X)).obj M :=
  (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ (prod.map (𝟙 X) j)).symm.app _ ≪≫
    ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ (prod.map (𝟙 X) j) prod.fst).app M).symm ≪≫
    eqToIso (by rw [prod.map_fst, Category.comp_id])

/-- **Compatibility of the exceptional Künneth map with restriction to `X ⨯ U`** (a consequence
of the coherence of the six functors, used here as a hypothesis): under the identifications
`exceptionalKunnethSourceRestrictionIso` and `exceptionalKunnethTargetRestrictionIso`, the
restriction `L(𝟙 × j)^* α^Y_M` of the exceptional Künneth map is `α^U_M`. -/
def ExceptionalKunnethMapRestriction (j : U ⟶ Y) [IsOpenImmersion j.left]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) : Prop :=
  (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j)).map
      (exceptionalKunnethMap ℓ (Y := Y) M) ≫ (exceptionalKunnethTargetRestrictionIso ℓ j M).hom =
    (exceptionalKunnethSourceRestrictionIso ℓ j M).hom ≫ exceptionalKunnethMap ℓ (Y := U) M

/-- The pullback `Lf^*` on bounded constructible complexes is compatible with the Koszul
braidings, in terms of its tensor structure. -/
lemma μ_boundedConstructibleUpperStar_braiding {A B : Over (Spec (.of k))}
    [LocallyOfFiniteType A.hom] [QuasiCompact A.hom] [IsSeparated A.hom]
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom] (f : A ⟶ B)
    (K M : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Functor.LaxMonoidal.μ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f)
        K M ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).map (β_ K M).hom =
      (β_ ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj K)
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj M)).hom ≫
        Functor.LaxMonoidal.μ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f)
          M K := by
  rw [← cancel_mono (Functor.OplaxMonoidal.δ
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f) M K),
    Category.assoc, Category.assoc, boundedConstructibleUpperStar_map_braiding_hom_δ,
    Functor.Monoidal.μ_δ, Category.comp_id, Functor.Monoidal.μ_δ_assoc]

end AlgebraicGeometry.ProEtale.CondensedRing
