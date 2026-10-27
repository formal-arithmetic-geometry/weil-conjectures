module

public import Sheaf.AlgebraicGeometry.AdmissibleModificationLimitSiteData

/-! # Canonical coefficient exchange for admissible modifications
Source: ILO XX 4.4, printed pp.373–374.
(blueprint: def-per-admissible-modification-coefficient-data).
-/

@[expose] public section

set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

/-- Higher-direct-image exchange on abelian sheaves, computed as homology of the
canonical derived exchange and the canonical exact-pullback comparisons.
Source: ILO XX 4.4, page 373; Stacks 03Q9.
(blueprint: def-per-admissible-modification-coefficient-data). -/
@[irreducible] def admissibleHigherExchange {U V X Y : Scheme.{u}}
    {a : V ⟶ U} {j' : V ⟶ Y} {j : U ⟶ X} {b : Y ⟶ X}
    (sq : CommSq a j' j b) (q : ℕ) (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (Etale.upperStar AddCommGrpCat.{u + 1} b).obj
        (((Etale.lowerStar AddCommGrpCat.{u + 1} j).rightDerived q).obj F) ⟶
      ((Etale.lowerStar AddCommGrpCat.{u + 1} j').rightDerived q).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} a).obj F) :=
  (Etale.upperStar AddCommGrpCat.{u + 1} b).map
      (Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso
        (Etale.lowerStar AddCommGrpCat.{u + 1} j) F q).inv ≫
    (Functor.mapDerivedCategoryPlusHomologyFunctorIso
      (Etale.upperStar AddCommGrpCat.{u + 1} b) q).hom.app _ ≫
    (DerivedCategory.Plus.homologyFunctor _ q).map
      ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
    (DerivedCategory.Plus.homologyFunctor _ q).map
      ((Etale.lowerStar AddCommGrpCat.{u + 1} j').rightDerivedFunctorPlus.map
        ((Functor.mapDerivedCategoryPlusSingleFunctor
          (Etale.upperStar AddCommGrpCat.{u + 1} a) 0).hom.app F)) ≫
    (Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso
      (Etale.lowerStar AddCommGrpCat.{u + 1} j') _ q).hom

/-- The specified open embeddings into the blowups, exhibiting the common open
as the full inverse image of the open in the base. Source: ILO XX 4.4, page 373.
(blueprint: def-per-admissible-modification-coefficient-data). -/
structure AdmissibleOpenEmbeddings {A : Type u} [CommRing A] (I : Ideal A)
    (U : (Spec (CommRingCat.of A)).Opens) where
  j (J : AdmissibleModification I) : U.toScheme ⟶ AffineBlowup J.val
  cartesian (J : AdmissibleModification I) :
    IsPullback (𝟙 U.toScheme) (j J) U.ι (AffineBlowup.toSpec J.val)
  openImmersion (J : AdmissibleModification I) : IsOpenImmersion (j J)
  naturality {J K : AdmissibleModification I} (f : J ⟶ K) :
    j J ≫ f.hom.left = j K

/-- The closed immersion of a closed fibre into its blowup, with the chosen
pullback used in `admissibleClosedFibres`. Source: ILO XX 4.4, page 373.
(blueprint: def-per-admissible-modification-coefficient-data). -/
def admissibleClosedImmersion {A : Type u} [CommRing A] (I : Ideal A)
    (J : AdmissibleModification I) :
    (admissibleClosedFibres I).obj J ⟶ AffineBlowup J.val :=
  pullback.fst (AffineBlowup.toSpec J.val)
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))

/-- Pullback transport induced by a specified comparison of site functors,
normalized as the mate of restriction of sheaves. Source: ILO XX 4.4, pages 373–374.
(blueprint: def-per-admissible-modification-coefficient-data). -/
@[irreducible] def admissibleInverseTransport {X Y : Scheme.{u}}
    {C : Type (u + 1)} [SmallCategory C] (τ : GrothendieckTopology C)
    (vX : X.Etale ⥤ C) (vY : Y.Etale ⥤ C)
    [vX.IsContinuous X.smallEtaleTopology τ] [vY.IsContinuous Y.smallEtaleTopology τ]
    (c : X ⟶ Y) (e : c.Etale ⋙ vX ≅ vY) :
    Etale.upperStar AddCommGrpCat.{u + 1} c ⋙
        Functor.sheafPullbackConstruction.sheafPullback vX AddCommGrpCat.{u + 1}
          X.smallEtaleTopology τ ≅
      Functor.sheafPullbackConstruction.sheafPullback vY AddCommGrpCat.{u + 1}
        Y.smallEtaleTopology τ :=
  (conjugateIsoEquiv
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous vY
      AddCommGrpCat.{u + 1} Y.smallEtaleTopology τ)
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} c).comp
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous vX
        AddCommGrpCat.{u + 1} X.smallEtaleTopology τ))).symm
      (Functor.sheafPushforwardContinuousComp' (eFG := e) AddCommGrpCat.{u + 1}
        Y.smallEtaleTopology X.smallEtaleTopology τ).symm

/-- The local coefficient exchange, followed by the projection to the common
limit site. It applies both to domination and to completion.
Source: ILO XX 4.4, (**) and its limit, pages 373–374.
(blueprint: def-per-admissible-modification-coefficient-data). -/
@[irreducible] def admissibleLocalCoefficientMap {U V B₀ B₁ Z₀ Z₁ : Scheme.{u}}
    {C : Type (u + 1)} [SmallCategory C] {τ : GrothendieckTopology C}
    (p₀ : Sheaf Z₀.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf τ AddCommGrpCat.{u + 1})
    (p₁ : Sheaf Z₁.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf τ AddCommGrpCat.{u + 1})
    {a : V ⟶ U} {b : B₁ ⟶ B₀} {c : Z₁ ⟶ Z₀}
    {j₀ : U ⟶ B₀} {j₁ : V ⟶ B₁} {i₀ : Z₀ ⟶ B₀} {i₁ : Z₁ ⟶ B₁}
    (sqU : CommSq a j₁ j₀ b) (sqZ : CommSq c i₁ i₀ b)
    (transport : Etale.upperStar AddCommGrpCat.{u + 1} c ⋙ p₁ ≅ p₀)
    (q : ℕ) (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    p₀.obj ((Etale.upperStar AddCommGrpCat.{u + 1} i₀).obj
      (((Etale.lowerStar AddCommGrpCat.{u + 1} j₀).rightDerived q).obj F)) ⟶
    p₁.obj ((Etale.upperStar AddCommGrpCat.{u + 1} i₁).obj
      (((Etale.lowerStar AddCommGrpCat.{u + 1} j₁).rightDerived q).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} a).obj F))) :=
  transport.inv.app _ ≫
    p₁.map ((Etale.squareUpperStarIso AddCommGrpCat.{u + 1} sqZ).inv.app _) ≫
    p₁.map ((Etale.upperStar AddCommGrpCat.{u + 1} i₁).map
      (admissibleHigherExchange sqU q F))

/-- The finite-stage coefficient functor `p_J⁻¹ i_J⁻¹ R^q j_{J*}`.
Source: ILO XX 4.4, (**)lim, page 373.
(blueprint: def-per-admissible-modification-coefficient-data). -/
def admissibleCoefficientFunctor {A : Type u} [CommRing A] {I : Ideal A}
    {C : Type (u + 1)} [SmallCategory C] {τ : GrothendieckTopology C}
    (P : AdmissibleLimitSite I C τ) {U : (Spec (CommRingCat.of A)).Opens}
    (j : AdmissibleOpenEmbeddings I U) (q : ℕ) (J : AdmissibleModification I) :
    Sheaf U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf τ AddCommGrpCat.{u + 1} :=
  (Etale.lowerStar AddCommGrpCat.{u + 1} (j.j J)).rightDerived q ⋙
    Etale.upperStar AddCommGrpCat.{u + 1} (admissibleClosedImmersion I J) ⋙ P.inverseAb J

/-- The actual exchange transition on the coefficient sheaves for a domination.
The identity pullback on the common open is removed by its canonical unit comparison.
Source: ILO XX 4.4, (**)lim, page 373.
(blueprint: def-per-admissible-modification-coefficient-data). -/
@[irreducible] def admissibleCoefficientTransition {A : Type u} [CommRing A] {I : Ideal A}
    {C : Type (u + 1)} [SmallCategory C] {τ : GrothendieckTopology C}
    (P : AdmissibleLimitSite I C τ) {U : (Spec (CommRingCat.of A)).Opens}
    (j : AdmissibleOpenEmbeddings I U) (q : ℕ)
    {J K : AdmissibleModification I} (f : J ⟶ K)
    (F : Sheaf U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (admissibleCoefficientFunctor P j q K).obj F ⟶
      (admissibleCoefficientFunctor P j q J).obj F :=
  admissibleLocalCoefficientMap (P.inverseAb K) (P.inverseAb J)
      (a := 𝟙 U.toScheme) (b := f.hom.left) (c := (admissibleClosedFibres I).map f)
      ⟨by simpa using (j.naturality f).symm⟩
      ⟨by
        exact pullback.lift_fst
          (f := AffineBlowup.toSpec K.val)
          (g := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
          (pullback.fst (AffineBlowup.toSpec J.val)
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫ f.hom.left)
          (pullback.snd (AffineBlowup.toSpec J.val)
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) _⟩
      (P.inverseComparison f) q F ≫
    (P.inverseAb J).map
      ((Etale.upperStar AddCommGrpCat.{u + 1} (admissibleClosedImmersion I J)).map
        (((Etale.lowerStar AddCommGrpCat.{u + 1} (j.j J)).rightDerived q).map
          ((Etale.upperStarId AddCommGrpCat.{u + 1} U.toScheme).hom.app F)))

/-- The canonical map on derived global sections for inverse image, followed by
homology. This is the ordinary étale cohomology pullback with the recorded derived
cohomology convention. Source: ILO XX 4.4, arrow (*), page 373.
(blueprint: def-per-admissible-modification-coefficient-data). -/
@[irreducible] def admissibleCohomologyPullback {X Y : Scheme.{u}} (g : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    (Etale.cohomology AddCommGrpCat.{u + 1} Y n).obj
        ((DerivedCategory.singleFunctor _ 0).obj F) ⟶
      (Etale.cohomology AddCommGrpCat.{u + 1} X n).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj F)) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).map
    ((Etale.rightDerivedGlobalSections AddCommGrpCat.{u + 1} Y).map
        ((Etale.mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app
          ((DerivedCategory.singleFunctor _ 0).obj F)) ≫
      (Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        AddCommGrpCat.{u + 1} g).hom.app _ ≫
      (Etale.rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
        ((Functor.mapDerivedCategorySingleFunctor
          (Etale.upperStar AddCommGrpCat.{u + 1} g) 0).hom.app F))


/-- The ideal induced on the adic completion. Source: ILO XX 4.4, page 374.
(blueprint: def-per-admissible-modification-coefficient-data). -/
def admissibleCompletionIdeal {A : Type u} [CommRing A] (I : Ideal A) :
    Ideal (AdicCompletion I A) :=
  I.map (algebraMap A (AdicCompletion I A))

/-- The affine completion morphism on spectra. Source: ILO XX 4.4, page 374.
(blueprint: def-per-admissible-modification-coefficient-data). -/
def admissibleCompletionBase {A : Type u} [CommRing A] (I : Ideal A) :
    Spec (CommRingCat.of (AdicCompletion I A)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion I A)))

/-- The open of the completed base lying over `U`. Source: ILO XX 4.4, page 374.
(blueprint: def-per-admissible-modification-coefficient-data). -/
def admissibleCompletionOpen {A : Type u} [CommRing A] (I : Ideal A)
    (U : (Spec (CommRingCat.of A)).Opens) :
    (Spec (CommRingCat.of (AdicCompletion I A))).Opens :=
  (admissibleCompletionBase I) ⁻¹ᵁ U

/-- The canonical map from the completed open to the original open. Source: ILO XX 4.4.
(blueprint: def-per-admissible-modification-coefficient-data). -/
def admissibleCompletionOpenMap {A : Type u} [CommRing A] (I : Ideal A)
    (U : (Spec (CommRingCat.of A)).Opens) :
    (admissibleCompletionOpen I U).toScheme ⟶ U.toScheme :=
  Scheme.Hom.resLE (admissibleCompletionBase I) U (admissibleCompletionOpen I U) le_rfl

end

end AlgebraicGeometry
