module

public import Sheaf.Paper.ClosedTestScalarComparisonMaps

/-! # Normalized scalar diagrams on closed-test section models

Source: Stacks Project, Tags 070I, 070Y, 0D6F and 09BL
(blueprint: def-sfb-closed-test-scalar-model-diagrams).

Every arrow is a specified unit, restriction, resolution comparison or exact pullback
compositor. The predicates spell out the diagrams, without assuming them to commute.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ClosedTestScalarModelCoherence
open ClosedTestKInjectiveSectionModels
open ClosedTestDerivedExchangeModel (restrict restrictPush scalarUnit adj pullComp)
variable {Λ S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj S] [IsCommMonObj S]
  (c : Λ ⟶ S) [IsMonHom c]
/-- The canonical inclusion of the closed test fibre into the pullback test over XZ.
Source: Stacks 09BL (blueprint: def-sfb-closed-test-scalar-model-diagrams). -/
def fibreSectionArrow (A : Type u) [CommRing A] (a : Ideal A)
    {X XZ : Scheme.{u}} {f : X ⟶ Spec (.of A)}
    {h : XZ ⟶ X} {fZ : XZ ⟶ Spec (.of (A ⧸ a))}
    (w : IsPullback h fZ f (closedMap A a))
    (V : (Spec (.of (A ⧸ a))).AffineProEt) :
    testFibre fZ (closedTest A a V) ⟶ testFibre h (testFibre f (liftedTest A a V)) :=
  MorphismProperty.Over.homMk
    (pullback.lift (testArrow A a w V) (testFibre fZ (closedTest A a V)).hom
      (pullback.lift_snd _ _ _)) (pullback.lift_snd _ _ _)

/-- The chain restriction Q(j(T0) composed with the actual inverse-image unit section).
Source: Stacks 09BL (blueprint: def-sfb-closed-test-scalar-model-diagrams). -/
def chainRestriction (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (A : Type u) [CommRing A] (a : Ideal A)
    {X XZ : Scheme.{u}} {f : X ⟶ Spec (.of A)}
    {h : XZ ⟶ X} {fZ : XZ ⟶ Spec (.of (A ⧸ a))}
    (w : IsPullback h fZ f (closedMap A a))
    (V : (Spec (.of (A ⧸ a))).AffineProEt)
    (L : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)) ℤ)
    (J : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology XZ) Ab.{u + 1}) (condensedRingObj R XZ)) ℤ)
    (j : (complexes (CondensedRing.upperStar R h)).obj L ⟶ J) :=
  DerivedCategory.Q.map
    ((NatTrans.mapHomologicalComplex
        (sectionArrow R h (testFibre f (liftedTest A a V))
          (testFibre fZ (closedTest A a V)) (fibreSectionArrow A a w V)) (.up ℤ)).app L ≫
      (complexes (evaluation R (testFibre fZ (closedTest A a V)))).map j)

/-- The normalized source-model comparison, in the forward unit direction. Its inverse
is exactly the closed-unit inverse followed by the direct-image section identity.
Source: Stacks 09BL, 070Y (blueprint: def-sfb-closed-test-scalar-model-diagrams). -/
def sourceModel (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (A : Type u) [CommRing A] (a : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (V : (Spec (.of (A ⧸ a))).AffineProEt)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)))
    (L : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)) ℤ)
    (e : DerivedCategory.Q.obj L ≅ K) :=
  DerivedCategory.Q.map (closedUnitComplex R A a V
      ((complexes (CondensedRing.lowerStar R f)).obj L)) ≫
    (evaluation R (closedTest A a V)).rightDerivedFunctorUnitQ
      ((complexes (CondensedRing.upperStar R (closedMap A a))).obj
        ((complexes (CondensedRing.lowerStar R f)).obj L)) ≫
    (evaluation R (closedTest A a V)).rightDerivedFunctor.map
      (exactRepresentative (CondensedRing.upperStar R (closedMap A a))
        (pushModel R f K L e))

/-- The target-model comparison, using the ordinary direct-image section identity.
Source: Stacks 0D6F, 070Y (blueprint: def-sfb-closed-test-scalar-model-diagrams). -/
def targetModel (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X Y : Scheme.{u}} (b : X ⟶ Y) (W : Y.ProEt)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)))
    (L : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)) ℤ)
    (e : DerivedCategory.Q.obj L ≅ K) :=
  (evaluation R W).rightDerivedFunctorUnitQ
      ((complexes (CondensedRing.lowerStar R b)).obj L) ≫
    (evaluation R W).rightDerivedFunctor.map (pushModel R b K L e)

/-- The forward coefficient arrow between actual section models. The only inverse is
an R-K-injective computation isomorphism, never a scalar comparison.
Source: Stacks 070Y (blueprint: def-sfb-closed-test-scalar-model-diagrams). -/
def modelCoefficient {X : Scheme.{u}} (W : X.ProEt)
    (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X)))
    (L : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X)) ℤ)
    (e : DerivedCategory.Q.obj L ≅ N)
    (P : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
    [P.IsKInjective] (d : DerivedCategory.Q.obj P ≅ (restrict c X).obj N) :=
  (evaluation S W).rightDerivedFunctorUnitQ L ≫
    (evaluation S W).rightDerivedFunctor.map e.hom ≫
    (gamma c W).app N ≫
    (evaluation Λ W).rightDerivedFunctor.map d.inv ≫
    ((evaluation Λ W).rightDerivedFunctorObjQIso P).hom

/-- Scalar comparison on the source derived sections, using forward gamma and delta.
Source: Stacks 070Y, 09T5 (blueprint: def-sfb-closed-test-scalar-model-diagrams). -/
def sourceCoefficient (A : Type u) [CommRing A] (a : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (V : (Spec (.of (A ⧸ a))).AffineProEt)
    (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X))) :=
  (gamma c (closedTest A a V)).app
      ((CondensedRing.upperStar S (closedMap A a)).mapDerivedCategory.obj
        ((CondensedRing.moduleObjectDerivedPushforward S f).obj N)) ≫
    (evaluation Λ (closedTest A a V)).rightDerivedFunctor.map
      ((CondensedRing.derivedComapUpperStarIso c (closedMap A a)).hom.app
          ((CondensedRing.moduleObjectDerivedPushforward S f).obj N) ≫
        (CondensedRing.upperStar Λ (closedMap A a)).mapDerivedCategory.map
          ((restrictPush c f).app N))

/-- Scalar comparison on the target derived sections, using forward gamma and delta.
Source: Stacks 070Y, 09T5 (blueprint: def-sfb-closed-test-scalar-model-diagrams). -/
def targetCoefficient {X XZ Z : Scheme.{u}} (h : XZ ⟶ X) (fZ : XZ ⟶ Z) (W : Z.ProEt)
    (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X))) :=
  (gamma c W).app ((CondensedRing.moduleObjectDerivedPushforward S fZ).obj
      ((CondensedRing.upperStar S h).mapDerivedCategory.obj N)) ≫
    (evaluation Λ W).rightDerivedFunctor.map
      ((restrictPush c fZ).app ((CondensedRing.upperStar S h).mapDerivedCategory.obj N) ≫
        (CondensedRing.moduleObjectDerivedPushforward Λ fZ).map
          ((CondensedRing.derivedComapUpperStarIso c h).hom.app N))

/-- A pair of actual K-injective representatives and the specified pullback resolution.
This packages only the resolutions quantified over in the statement; it contains no
coherence assumptions. Source: Stacks 070Y
(blueprint: def-sfb-closed-test-scalar-model-diagrams). -/
structure TestModel (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X XZ : Scheme.{u}} (h : XZ ⟶ X)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))) where
  I : CochainComplex
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)) ℤ
  iKInjective : I.IsKInjective
  e : DerivedCategory.Q.obj I ≅ K
  J : CochainComplex
    (Mod (Sheaf (Scheme.ProEt.topology XZ) Ab.{u + 1}) (condensedRingObj R XZ)) ℤ
  jKInjective : J.IsKInjective
  j : (complexes (CondensedRing.upperStar R h)).obj I ⟶ J
  jQuasiIso : QuasiIso j

attribute [instance] TestModel.iKInjective TestModel.jKInjective TestModel.jQuasiIso

/-- The existing normalized representative of the inverse image.
Source: Stacks 070Y (blueprint: def-sfb-closed-test-scalar-model-diagrams). -/
abbrev TestModel.pullIso {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {X XZ : Scheme.{u}} {h : XZ ⟶ X}
    {K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))}
    (M : TestModel R h K) :=
  pullRepresentative R h K M.I M.e M.J M.j

/-- Scalar restriction on localized derived sections, with its actual coefficient compositor.
Source: Stacks 0D6F (blueprint: def-sfb-closed-test-scalar-model-diagrams). -/
def localizedCoefficient {X : Scheme.{u}} (W : X.ProEt)
    (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X))) :=
  (gamma c (Scheme.ProEt.mk (𝟙 W.left))).app
      ((CondensedRing.upperStar S W.hom).mapDerivedCategory.obj N) ≫
    (evaluation Λ (Scheme.ProEt.mk (𝟙 W.left))).rightDerivedFunctor.map
      ((CondensedRing.derivedComapUpperStarIso c W.hom).hom.app N)

/-- The coefficient arrow on the target representative, including the specified
pullback/scalar identification. Source: Stacks 070Y, 0D6D
(blueprint: def-sfb-closed-test-scalar-model-diagrams). -/
def targetModelCoefficient {X XZ : Scheme.{u}} (h : XZ ⟶ X) (W : XZ.ProEt)
    (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X)))
    (M : TestModel S h N) (P : TestModel Λ h ((restrict c X).obj N)) :=
  modelCoefficient c W ((CondensedRing.upperStar S h).mapDerivedCategory.obj N)
    M.J M.pullIso P.J
    (P.pullIso ≪≫ (CondensedRing.derivedComapUpperStarIso c h).symm.app N)

section ClosedModels
variable (A : Type u) [CommRing A] (a : Ideal A)
  {X XZ : Scheme.{u}} (f : X ⟶ Spec (.of A))
  (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ a)))
  (w : IsPullback h fZ f (closedMap A a))
  (V : (Spec (.of (A ⧸ a))).AffineProEt)

/-- Scalar squares for the two normalized models, their chain restriction and their
localized-section comparisons, for every supplied pair of resolutions.
Source: Stacks 09BL, 0D6F, 070Y
(blueprint: def-sfb-closed-test-scalar-model-diagrams). -/
def ModelCoherence
    (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X)))
    (M : TestModel S h N) (P : TestModel Λ h ((restrict c X).obj N)) : Prop :=
  IsIso (sourceModel S A a f V N M.I M.e) ∧
  IsIso (sourceModel Λ A a f V ((restrict c X).obj N) P.I P.e) ∧
  IsIso (targetModel S fZ (closedTest A a V)
    ((CondensedRing.upperStar S h).mapDerivedCategory.obj N) M.J M.pullIso) ∧
  IsIso (targetModel Λ fZ (closedTest A a V)
    ((CondensedRing.upperStar Λ h).mapDerivedCategory.obj
      ((restrict c X).obj N)) P.J P.pullIso) ∧
  IsIso (localizationModel S (testFibre f (liftedTest A a V)) N M.I M.e) ∧
  IsIso (localizationModel Λ (testFibre f (liftedTest A a V))
    ((restrict c X).obj N) P.I P.e) ∧
  IsIso (localizationModel S (testFibre fZ (closedTest A a V))
    ((CondensedRing.upperStar S h).mapDerivedCategory.obj N) M.J M.pullIso) ∧
  IsIso (localizationModel Λ (testFibre fZ (closedTest A a V))
    ((CondensedRing.upperStar Λ h).mapDerivedCategory.obj
      ((restrict c X).obj N)) P.J P.pullIso) ∧
  (modelCoefficient c (testFibre f (liftedTest A a V)) N M.I M.e P.I P.e ≫
      sourceModel Λ A a f V ((restrict c X).obj N) P.I P.e =
    sourceModel S A a f V N M.I M.e ≫ sourceCoefficient c A a f V N) ∧
  (targetModelCoefficient c h (testFibre fZ (closedTest A a V)) N M P ≫
      targetModel Λ fZ (closedTest A a V)
        ((CondensedRing.upperStar Λ h).mapDerivedCategory.obj
          ((restrict c X).obj N)) P.J P.pullIso =
    targetModel S fZ (closedTest A a V)
        ((CondensedRing.upperStar S h).mapDerivedCategory.obj N) M.J M.pullIso ≫
      targetCoefficient c h fZ (closedTest A a V) N) ∧
  (chainRestriction S A a w V M.I M.J M.j ≫
      targetModelCoefficient c h (testFibre fZ (closedTest A a V)) N M P =
    modelCoefficient c (testFibre f (liftedTest A a V)) N M.I M.e P.I P.e ≫
      chainRestriction Λ A a w V P.I P.J P.j) ∧
  (modelCoefficient c (testFibre f (liftedTest A a V)) N M.I M.e P.I P.e ≫
      localizationModel Λ (testFibre f (liftedTest A a V))
        ((restrict c X).obj N) P.I P.e =
    localizationModel S (testFibre f (liftedTest A a V)) N M.I M.e ≫
      localizedCoefficient c (testFibre f (liftedTest A a V)) N) ∧
  (targetModelCoefficient c h (testFibre fZ (closedTest A a V)) N M P ≫
      localizationModel Λ (testFibre fZ (closedTest A a V))
        ((CondensedRing.upperStar Λ h).mapDerivedCategory.obj
          ((restrict c X).obj N)) P.J P.pullIso =
    localizationModel S (testFibre fZ (closedTest A a V))
        ((CondensedRing.upperStar S h).mapDerivedCategory.obj N) M.J M.pullIso ≫
      localizedCoefficient c (testFibre fZ (closedTest A a V))
        ((CondensedRing.upperStar S h).mapDerivedCategory.obj N) ≫
      (localizedSections Λ (testFibre fZ (closedTest A a V))).map
        ((CondensedRing.derivedComapUpperStarIso c h).hom.app N))

/-- The cospan naturality for an actual derived module map. The left leg is the
specified map K to Res N; the right leg is forward gamma, never its inverse.
Source: Stacks 070I, 070Y (blueprint: def-sfb-closed-test-scalar-model-diagrams). -/
def MapCoherence
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X)))
    (α : K ⟶ (restrict c X).obj N) : Prop :=
  ((evaluation Λ (testFibre f (liftedTest A a V))).rightDerivedFunctor.map α ≫
      (derivedSectionArrow Λ h (testFibre f (liftedTest A a V))
        (testFibre fZ (closedTest A a V)) (fibreSectionArrow A a w V)).app
          ((restrict c X).obj N) =
    (derivedSectionArrow Λ h (testFibre f (liftedTest A a V))
        (testFibre fZ (closedTest A a V)) (fibreSectionArrow A a w V)).app K ≫
      (evaluation Λ (testFibre fZ (closedTest A a V))).rightDerivedFunctor.map
        ((CondensedRing.upperStar Λ h).mapDerivedCategory.map α)) ∧
  ((derivedSectionArrow S h (testFibre f (liftedTest A a V))
        (testFibre fZ (closedTest A a V)) (fibreSectionArrow A a w V)).app N ≫
      (gamma c (testFibre fZ (closedTest A a V))).app
        ((CondensedRing.upperStar S h).mapDerivedCategory.obj N) ≫
      (evaluation Λ (testFibre fZ (closedTest A a V))).rightDerivedFunctor.map
        ((CondensedRing.derivedComapUpperStarIso c h).hom.app N) =
    (gamma c (testFibre f (liftedTest A a V))).app N ≫
      (derivedSectionArrow Λ h (testFibre f (liftedTest A a V))
        (testFibre fZ (closedTest A a V)) (fibreSectionArrow A a w V)).app
          ((restrict c X).obj N))
end ClosedModels

/-- A model map induced by an actual derived morphism, using the computation unit.
It depends only on that morphism, hence also identifies homotopic representatives.
Source: Stacks 070I (blueprint: def-sfb-closed-test-scalar-model-diagrams). -/
def modelMap (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X : Scheme.{u}} (W : X.ProEt)
    {K N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))}
    (I J : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)) ℤ)
    (e : DerivedCategory.Q.obj I ≅ K) (d : DerivedCategory.Q.obj J ≅ N)
    [J.IsKInjective] (α : K ⟶ N) :=
  (evaluation R W).rightDerivedFunctorUnitQ I ≫
    (evaluation R W).rightDerivedFunctor.map (e.hom ≫ α ≫ d.inv) ≫
    ((evaluation R W).rightDerivedFunctorObjQIso J).hom

section ModelMaps
variable (A : Type u) [CommRing A] (a : Ideal A)
  {X XZ : Scheme.{u}} (f : X ⟶ Spec (.of A))
  (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ a)))
  (w : IsPullback h fZ f (closedMap A a))
  (V : (Spec (.of (A ⧸ a))).AffineProEt)

/-- Naturality of both normalized section-model comparisons and chain restriction for
an arbitrary actual derived map, including every choice of its two resolution models.
Source: Stacks 070I, 09BL, 0D6F
(blueprint: def-sfb-closed-test-scalar-model-diagrams). -/
def ModelMapCoherence
    {K N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))}
    (α : K ⟶ N) (M : TestModel Λ h K) (P : TestModel Λ h N) : Prop :=
  (modelMap Λ (testFibre f (liftedTest A a V)) M.I P.I M.e P.e α ≫
      sourceModel Λ A a f V N P.I P.e =
    sourceModel Λ A a f V K M.I M.e ≫
      (evaluation Λ (closedTest A a V)).rightDerivedFunctor.map
        ((CondensedRing.upperStar Λ (closedMap A a)).mapDerivedCategory.map
          ((CondensedRing.moduleObjectDerivedPushforward Λ f).map α))) ∧
  (modelMap Λ (testFibre fZ (closedTest A a V)) M.J P.J M.pullIso P.pullIso
        ((CondensedRing.upperStar Λ h).mapDerivedCategory.map α) ≫
      targetModel Λ fZ (closedTest A a V)
        ((CondensedRing.upperStar Λ h).mapDerivedCategory.obj N) P.J P.pullIso =
    targetModel Λ fZ (closedTest A a V)
        ((CondensedRing.upperStar Λ h).mapDerivedCategory.obj K) M.J M.pullIso ≫
      (evaluation Λ (closedTest A a V)).rightDerivedFunctor.map
        ((CondensedRing.moduleObjectDerivedPushforward Λ fZ).map
          ((CondensedRing.upperStar Λ h).mapDerivedCategory.map α))) ∧
  (chainRestriction Λ A a w V M.I M.J M.j ≫
      modelMap Λ (testFibre fZ (closedTest A a V)) M.J P.J M.pullIso P.pullIso
        ((CondensedRing.upperStar Λ h).mapDerivedCategory.map α) =
    modelMap Λ (testFibre f (liftedTest A a V)) M.I P.I M.e P.e α ≫
      chainRestriction Λ A a w V P.I P.J P.j) ∧
  (modelMap Λ (testFibre f (liftedTest A a V)) M.I P.I M.e P.e α ≫
      localizationModel Λ (testFibre f (liftedTest A a V)) N P.I P.e =
    localizationModel Λ (testFibre f (liftedTest A a V)) K M.I M.e ≫
      (localizedSections Λ (testFibre f (liftedTest A a V))).map α) ∧
  (modelMap Λ (testFibre fZ (closedTest A a V)) M.J P.J M.pullIso P.pullIso
        ((CondensedRing.upperStar Λ h).mapDerivedCategory.map α) ≫
      localizationModel Λ (testFibre fZ (closedTest A a V))
        ((CondensedRing.upperStar Λ h).mapDerivedCategory.obj N) P.J P.pullIso =
    localizationModel Λ (testFibre fZ (closedTest A a V))
        ((CondensedRing.upperStar Λ h).mapDerivedCategory.obj K) M.J M.pullIso ≫
      (localizedSections Λ (testFibre fZ (closedTest A a V))).map
        ((CondensedRing.upperStar Λ h).mapDerivedCategory.map α))
end ModelMaps

end AlgebraicGeometry.ProEtale.ClosedTestScalarModelCoherence
