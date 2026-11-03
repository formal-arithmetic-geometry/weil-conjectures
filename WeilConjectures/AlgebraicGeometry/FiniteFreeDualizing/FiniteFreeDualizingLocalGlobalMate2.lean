/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DualizingOpenMate.DualizingOpenMate
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
public import WeilConjectures.AlgebraicGeometry.Proper.ProperFiniteCoefficientExtension
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.Ordered.OrderedAffineTraceNormalForm
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumCounitScalar
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartExceptionalScalar
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartIdentityScalar

/-! # Local and global finite-free dualizing mates

Source: blueprint/latest, lem-coef-finite-free-extension.proof.md, paragraph 1
(local closed-embedding computation and coefficient-linear affine counit), and paragraph 3
(equality by transposition) (blueprint: lem-coef-finite-free-dualizing-local-global-mate).

The affine space is the existing ordered coordinate tower, canonically isomorphic to affine
space. Its right functor and adjunction are the Kummer-trace-normalized ones. In particular
`orderedAffineRightIso` identifies its value at the coefficient unit with the ordinary
Tate power shifted by twice the dimension. All right adjoints below are quantified with
their adjunctions: no extra choice of a dualizing object or of its counit is made.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.FiniteFreeDualizing

/-- Closed compact support with the identity open part is ordinary derived direct image.
Source: parent proof paragraph 1, closed-embedding computation
(blueprint: lem-coef-finite-free-dualizing-local-global-mate). -/
def closedSupportIso (R : Type (u + 1)) [CommRing R]
    {V T : Scheme.{u}} (i : V ⟶ T) [IsClosedImmersion i] :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R)
        (Compactification.ofIsProper i) ≅
      (lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor :=
  Functor.isoWhiskerRight
      (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} R) V) _ ≪≫
    Functor.leftUnitor _

/-- The canonical compact-support comparison from a closed chart followed by the ordered
coordinate tower. The first factor removes the identity open part, the second uses the
existing ordered affine comparison, and the last three use compatible composition and
common refinement. Source: parent proof paragraph 1, local closed-embedding computation
(blueprint: lem-coef-finite-free-dualizing-local-global-mate). -/
def chartLeftIso (R : Type (u + 1)) [CommRing R] [Finite R]
    {V S : Scheme.{u}} [IsNoetherian V] [IsNoetherian S]
    (r : ℕ) (i : V ⟶ affineTraceTower S r) [IsClosedImmersion i]
    (c : Compactification (affineTraceProjection S r))
    (d : Compactification (i ≫ affineTraceProjection S r)) :
    (lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor ⋙ affineTraceLeft R S r ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) d :=
  let e := d.ofComp c
  Functor.isoWhiskerRight (closedSupportIso R i).symm _ ≪≫
    Functor.isoWhiskerLeft _ (ProEtale.reductionEtaleAffineLeftIso R S r c) ≪≫
    Functor.isoWhiskerRight
      (rightDerivedLowerShriekOfCompactificationIso R
        (Compactification.ofIsProper i) e.restrict) _ ≪≫
    rightDerivedLowerShriekOfCompactificationCompIso R c e ≪≫
    rightDerivedLowerShriekOfCompactificationIso R (c.comp e) d

/-- The ordinary closed-shriek scalar mate, transposed from the inverse ordinary
proper direct-image comparison followed by scalar extension of the exceptional counit.
Source: parent proof paragraph 1, closed exceptional comparison with the same counit map
(blueprint: lem-coef-finite-free-dualizing-local-global-mate). -/
def closedMate {R A : Type (u + 1)} [CommRing R] [CommRing A] [Finite R] [Finite A]
    (φ : R →+* A) {V T : Scheme.{u}} [IsNoetherian V] [IsNoetherian T]
    (i : V ⟶ T) [IsClosedImmersion i]
    (HR : DerivedCategoryModule R T ⥤ DerivedCategoryModule R V)
    (HA : DerivedCategoryModule A T ⥤ DerivedCategoryModule A V)
    (aR : (lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor ⊣ HR)
    (aA : (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor ⊣ HA)
    (M : DerivedCategoryModule R T) :
    (scalarExtension φ V).obj (HR.obj M) ⟶ HA.obj ((scalarExtension φ T).obj M) :=
  letI := (properFiniteCoefficientExtension φ i).1 (HR.obj M)
  aA.homEquiv _ _
    (inv ((scalarMate φ i).app (HR.obj M)) ≫ (scalarExtension φ T).map (aR.counit.app M))

/-- Counit-preserving restriction to a closed affine chart. The right adjoint on the chart
is the composite of the ordered normalized affine adjunction and the ordinary closed
adjunction. The unique locality isomorphism supplies its restriction comparison.
Source: parent proof paragraphs 1 and 3
(blueprint: lem-coef-finite-free-dualizing-local-global-mate). -/
def chartRestrictionIso (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hR : (N : R) = 0)
    (t : OrdinaryFiniteTwistTransport R N hR)
    (P : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum R N hR t T hT)
    {V X S : Scheme.{u}} [IsNoetherian V] [IsNoetherian X] [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (f : X ⟶ S) (v : V ⟶ X)
    [Etale v] [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (r : ℕ) (i : V ⟶ affineTraceTower S r) [IsClosedImmersion i]
    (h : v ≫ f = i ≫ affineTraceProjection S r)
    (cf : Compactification f) (cq : Compactification (affineTraceProjection S r))
    (cg : Compactification (i ≫ affineTraceProjection S r))
    (Hf : DerivedCategoryModule R S ⥤ DerivedCategoryModule R X)
    (Hi : DerivedCategoryModule R (affineTraceTower S r) ⥤ DerivedCategoryModule R V)
    (af : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cf ⊣ Hf)
    (ai : (lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor ⊣ Hi) :
    Hf ⋙ (upperStar (ModuleCat.{u + 1} R) v).mapDerivedCategory ≅
      affineTraceRight R N hR S r ⋙ Hi :=
  (existsUnique_etaleAmbientAdjointLocalityIso R v f cf (cg.copy h) Hf
    (affineTraceRight R N hR S r ⋙ Hi) af
    ((ai.comp (affineTraceAdjunction R N hR t P S hS r)).ofNatIsoLeft
      (chartLeftIso R r i cq cg))).choose

/-- The affine coefficient map at the coefficient unit. The recursive scalar comparison
is ordinary Tate balancing in the ordered Kummer normal form; its last factor identifies
scalar extension of the coefficient unit with the new coefficient unit.
Source: parent proof paragraph 1, Tate and coefficient-linear affine counit sentence
(blueprint: lem-coef-finite-free-dualizing-local-global-mate). -/
def affineUnitScalarIso
    {R A : Type (u + 1)} [CommRing R] [CommRing A]
    (φ : R →+* A) (N : ℕ) (hR : (N : R) = 0) (hA : (N : A) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (r : ℕ) :
    (scalarExtension φ (affineTraceTower S r)).obj
        ((affineTraceRight R N hR S r).obj (constantComplex R S)) ≅
      (affineTraceRight A N hA S r).obj (constantComplex A S) :=
  ProEtale.reductionEtaleAffineScalarIso φ S N hR hA hS r (constantComplex R S) ≪≫
    (affineTraceRight A N hA S r).mapIso (ExceptionalCoefficients.unitIso φ S)

private theorem normalized_right_scalar
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {G J : D ⥤ C} {F' : C' ⥤ D'} {G' J' : D' ⥤ C'}
    (g : F ⊣ G) (j : F ⊣ J) (g' : F' ⊣ G') (j' : F' ⊣ J')
    (S : C ⥤ C') (T : D ⥤ D') (b : F ⋙ T ⟶ S ⋙ F')
    (e : G ≅ J) (e' : G' ≅ J')
    (he : ∀ K, F.map (e.hom.app K) ≫ j.counit.app K = g.counit.app K)
    (he' : ∀ K, F'.map (e'.hom.app K) ≫ j'.counit.app K = g'.counit.app K)
    (K : D) (K' : D') (u : T.obj K ⟶ K')
    (q : S.obj (G.obj K) ⟶ G'.obj K')
    (a : S.obj (J.obj K) ⟶ J'.obj K')
    (hq : b.app (G.obj K) ≫ F'.map q ≫ g'.counit.app K' =
      T.map (g.counit.app K) ≫ u)
    (hb : Epi (b.app (G.obj K)))
    (ha : b.app (J.obj K) ≫ F'.map a ≫ j'.counit.app K' =
      T.map (j.counit.app K) ≫ u) :
    S.map (e.hom.app K) ≫ a = q ≫ e'.hom.app K' := by
  have := hb
  apply (j'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  apply (cancel_epi (b.app (G.obj K))).mp
  rw [he', hq]
  have hn := b.naturality (e.hom.app K)
  change T.map (F.map _) ≫ b.app (J.obj K) =
    b.app (G.obj K) ≫ F'.map (S.map _) at hn
  rw [← reassoc_of% hn, ha, ← T.map_comp_assoc, he]

private theorem compose_unit_counit
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E] [Category C'] [Category D'] [Category E']
    {L : C ⥤ D} {R : D ⥤ C} {M : D ⥤ E} {Q : E ⥤ D}
    {L' : C' ⥤ D'} {R' : D' ⥤ C'} {M' : D' ⥤ E'} {Q' : E' ⥤ D'}
    (a : L ⊣ R) (b : M ⊣ Q) (a' : L' ⊣ R') (b' : M' ⊣ Q')
    (S : C ⥤ C') (T : D ⥤ D') (U : E ⥤ E')
    (β : L ⋙ T ⟶ S ⋙ L') (γ : M ⋙ U ⟶ T ⋙ M')
    (K : E) (K' : E') (u : U.obj K ⟶ K')
    (r : S.obj (R.obj (Q.obj K)) ⟶ R'.obj (T.obj (Q.obj K)))
    (q : T.obj (Q.obj K) ⟶ Q'.obj K')
    (hr : β.app (R.obj (Q.obj K)) ≫ L'.map r ≫ a'.counit.app (T.obj (Q.obj K)) =
      T.map (a.counit.app (Q.obj K)))
    (hq : γ.app (Q.obj K) ≫ M'.map q ≫ b'.counit.app K' =
      U.map (b.counit.app K) ≫ u) :
    (scalarComposite β γ).app (R.obj (Q.obj K)) ≫
      (L' ⋙ M').map (r ≫ R'.map q) ≫ (a'.comp b').counit.app K' =
      U.map ((a.comp b).counit.app K) ≫ u := by
  simp only [scalarComposite, Adjunction.comp_counit_app, Functor.comp_map,
    Functor.map_comp, Category.assoc]
  have hn := a'.counit.naturality q
  simp only [Functor.comp_map, Functor.id_map] at hn
  have hn' := congrArg M'.map hn
  simp only [Functor.map_comp] at hn'
  rw [reassoc_of% hn']
  have hr' := congrArg M'.map hr
  simp only [Functor.map_comp] at hr'
  rw [reassoc_of% hr']
  have hm := γ.naturality (a.counit.app (Q.obj K))
  simp only [Functor.comp_map] at hm
  rw [← reassoc_of% hm, hq, ← U.map_comp_assoc]

private theorem transport_unit_counit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F H : C ⥤ D} {J : D ⥤ C} {F' H' : C' ⥤ D'} {J' : D' ⥤ C'}
    (a : H ⊣ J) (a' : H' ⊣ J') (e : H ≅ F) (e' : H' ≅ F')
    (S : C ⥤ C') (T : D ⥤ D')
    (β : F ⋙ T ⟶ S ⋙ F') (γ : H ⋙ T ⟶ S ⋙ H')
    (K : D) (K' : D') (u : T.obj K ⟶ K')
    (r : S.obj (J.obj K) ⟶ J'.obj K')
    (hs : ∀ X, T.map (e.hom.app X) ≫ β.app X = γ.app X ≫ e'.hom.app (S.obj X))
    (hc : γ.app (J.obj K) ≫ H'.map r ≫ a'.counit.app K' =
      T.map (a.counit.app K) ≫ u) :
    β.app (J.obj K) ≫ F'.map r ≫ (a'.ofNatIsoLeft e').counit.app K' =
      T.map ((a.ofNatIsoLeft e).counit.app K) ≫ u := by
  apply (cancel_epi (T.map (e.hom.app (J.obj K)))).mp
  simp only [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  rw [reassoc_of% (hs (J.obj K))]
  have hn := e'.inv.naturality r
  rw [reassoc_of% hn]
  simp only [Iso.hom_inv_id_app_assoc, ← T.map_comp_assoc]
  exact hc

private theorem closed_support_scalar
    {R A : Type (u + 1)} [CommRing R] [CommRing A] [Finite R] [Finite A]
    (φ : R →+* A) {V T : Scheme.{u}} (i : V ⟶ T) [IsClosedImmersion i]
    (M : DerivedCategoryModule R V) :
    (scalarExtension φ T).map ((closedSupportIso R i).hom.app M) ≫
        (scalarMate φ i).app M =
      (compactScalarMap φ (Compactification.ofIsProper i)).app M ≫
        (closedSupportIso A i).hom.app ((scalarExtension φ V).obj M) := by
  have hn := (scalarMate φ i).naturality
    ((mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} R) V).hom.app M)
  simp only [Functor.comp_map, Functor.id_obj] at hn
  have ho := congrArg (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor.map
    (identity_open_scalar φ V M)
  simp only [Functor.map_comp] at ho
  dsimp only [compactScalarMap, ExceptionalCoefficients.compactSupportMap,
    Compactification.ofIsProper]
  simp only [closedSupportIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.map_comp, Category.assoc]
  change (scalarExtension φ T).map
      ((lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor.map
        ((mapDerivedCategoryOpenImmersionLowerShriekId
          (ModuleCat.{u + 1} R) V).hom.app M)) ≫
      (scalarExtension φ T).map (𝟙 _) ≫ (scalarMate φ i).app M =
    (scalarMate φ i).app _ ≫
      (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor.map
        ((ExceptionalCoefficients.openIso φ (𝟙 V)).hom.app M) ≫
      (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor.map
        ((mapDerivedCategoryOpenImmersionLowerShriekId
          (ModuleCat.{u + 1} A) V).hom.app _) ≫ 𝟙 _
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  rw [ho, ← hn]

private theorem chart_left_scalar
    {R A : Type (u + 1)} [CommRing R] [CommRing A] [Finite R] [Finite A]
    (φ : R →+* A) {V S : Scheme.{u}} [IsNoetherian V] [IsNoetherian S]
    (r : ℕ) (i : V ⟶ affineTraceTower S r) [IsClosedImmersion i]
    (c : Compactification (affineTraceProjection S r))
    (d : Compactification (i ≫ affineTraceProjection S r))
    (M : DerivedCategoryModule R V) :
    (scalarExtension φ S).map ((chartLeftIso R r i c d).hom.app M) ≫
        (compactScalarMap φ d).app M =
      (affineLeftScalar φ S r).app
          ((lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor.obj M) ≫
        (affineTraceLeft A S r).map ((scalarMate φ i).app M) ≫
        (chartLeftIso A r i c d).hom.app ((scalarExtension φ V).obj M) := by
  have : IsNoetherian (affineTraceTower S r) := affineTraceNoetherian S r
  let e := d.ofComp c
  have hs (L : DerivedCategoryModule R V) :
      (scalarExtension φ (affineTraceTower S r)).map
          ((closedSupportIso R i).inv.app L) ≫
        (compactScalarMap φ (Compactification.ofIsProper i)).app L =
      (scalarMate φ i).app L ≫
        (closedSupportIso A i).inv.app ((scalarExtension φ V).obj L) := by
    apply (cancel_mono ((closedSupportIso A i).hom.app _)).mp
    rw [Category.assoc, ← closed_support_scalar]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
    exact (Category.comp_id _).symm
  have hf := composite_left_scalar
    (scalarExtension φ V) (scalarExtension φ (affineTraceTower S r))
    (scalarExtension φ S) (scalarMate φ i)
    (compactScalarMap φ (Compactification.ofIsProper i))
    (affineLeftScalar φ S r) (compactScalarMap φ c)
    (closedSupportIso R i).symm (closedSupportIso A i).symm
    (ProEtale.reductionEtaleAffineLeftIso R S r c)
    (ProEtale.reductionEtaleAffineLeftIso A S r c)
    hs (affine_left_scalar φ S r c) M
  have hf' := composite_left_scalar
    (scalarExtension φ V) (scalarExtension φ (affineTraceTower S r))
    (scalarExtension φ S)
    (compactScalarMap φ (Compactification.ofIsProper i)) (compactScalarMap φ e.restrict)
    (compactScalarMap φ c) (compactScalarMap φ c)
    (rightDerivedLowerShriekOfCompactificationIso R (Compactification.ofIsProper i)
      e.restrict)
    (rightDerivedLowerShriekOfCompactificationIso A (Compactification.ofIsProper i)
      e.restrict) (Iso.refl _) (Iso.refl _)
    (ordinaryChartCompactificationScalar φ (Compactification.ofIsProper i) e.restrict)
    (by intro L; simp) M
  have ht := ordinaryChartCompactTowerScalar φ i (affineTraceProjection S r) c e M
  have hr := ordinaryChartCompactificationScalar φ (c.comp e) d M
  simp only [chartLeftIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Iso.symm_hom, Functor.map_comp, Category.assoc]
  erw [hr, reassoc_of% ht]
  simp only [Iso.refl_hom, NatTrans.id_app, Category.comp_id] at hf'
  erw [reassoc_of% hf']
  simp only [Functor.map_comp, Category.assoc, Iso.symm_hom] at hf
  erw [reassoc_of% hf]
  rfl

/-- The global finite-free counit transpose equals the closed chart mate after the unique
counit-preserving locality identifications. Quantifying over every affine etale chart
also asserts that all its chart maps are restrictions of this one global morphism;
restriction again to an overlap therefore gives the same morphism by either chart.

Source: parent lem-coef-finite-free-extension.proof.md, paragraphs 1 and 3
(blueprint: lem-coef-finite-free-dualizing-local-global-mate).

Proof: (1) finite-free proper comparison and exact open balancing make the canonical
compact-support coefficient comparison invertible on every unbounded input. For a closed
map the inverse direct-image comparison and the exceptional counit give `closedMate`.
(2) The scalar squares commute with direct-image and open composition, restriction
exchange, and graph-normalized etale sum extension. Paste these squares along the
canonical common-refinement and composition maps. (3) Transpose under etale sum extension
and the global compact-support adjunction: the restriction of the global mate is the
mate for the restricted structural morphism, with the locality counit normalization.
(4) On the ordered affine tower, root-of-unity balancing and coefficient-linearity of
the normalized affine counit identify this mate at the unit with `affineUnitScalarIso`.
(5) Compose the closed and affine adjunctions. Their scalar square is the paste of the
two constituent squares, so its mate is the closed mate followed by the closed right
adjoint applied to the affine scalar isomorphism. Its transpose is exactly that in
(3); injectivity of the adjunction Hom bijection proves the displayed equality.
(6) Pull these equalities back to any overlap: each chart map is already the restriction
of the same global map. This does not assert descent or uniqueness for arbitrary derived
morphisms from their values on a cover. -/
theorem localGlobal_mate
    {R A : Type (u + 1)} [CommRing R] [CommRing A] [Finite R] [Finite A]
    (φ : R →+* A) (hfree : @Module.Free R A _ _ (Module.compHom A φ))
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0) (hA : (N : A) = 0)
    (tR : OrdinaryFiniteTwistTransport R N hR)
    (tA : OrdinaryFiniteTwistTransport A N hA)
    (PR : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum R N hR tR T hT)
    (PA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA tA T hT)
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (f : X ⟶ S)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (cf : Compactification f)
    (HR : DerivedCategoryModule R S ⥤ DerivedCategoryModule R X)
    (HA : DerivedCategoryModule A S ⥤ DerivedCategoryModule A X)
    (aR : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cf ⊣ HR)
    (aA : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf ⊣ HA) :
    (∀ L : DerivedCategoryModule R X,
      IsIso (ExceptionalCoefficients.compactSupportMap φ cf L)) ∧
    ∀ {V : Scheme.{u}} [IsNoetherian V] [IsAffine V]
      (v : V ⟶ X) [Etale v] [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
      (r : ℕ) (i : V ⟶ affineTraceTower S r) [IsClosedImmersion i]
      (h : v ≫ f = i ≫ affineTraceProjection S r)
      (cq : Compactification (affineTraceProjection S r))
      (cg : Compactification (i ≫ affineTraceProjection S r))
      (IR : DerivedCategoryModule R (affineTraceTower S r) ⥤ DerivedCategoryModule R V)
      (IA : DerivedCategoryModule A (affineTraceTower S r) ⥤ DerivedCategoryModule A V)
      (bR : (lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor ⊣ IR)
      (bA : (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor ⊣ IA),
      letI : IsNoetherian (affineTraceTower S r) := affineTraceNoetherian S r
      (scalarPullbackIso φ v).inv.app (HR.obj (constantComplex R S)) ≫
        (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.map
          (DualizingOpenMate.globalMate φ cf HR HA aR aA) ≫
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v).hom.app
          (HA.obj (constantComplex A S)) ≫
        (chartRestrictionIso A N hA tA PA hS f v r i h cf cq cg HA IA aA bA).hom.app
          (constantComplex A S) =
      (scalarExtension φ V).map
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} R) v).hom.app
              (HR.obj (constantComplex R S)) ≫
            (chartRestrictionIso R N hR tR PR hS f v r i h cf cq cg HR IR aR bR).hom.app
              (constantComplex R S)) ≫
        closedMate φ i IR IA bR bA
          ((affineTraceRight R N hR S r).obj (constantComplex R S)) ≫
        IA.map (affineUnitScalarIso φ N hR hA S hS r).hom := by
  refine ⟨fun L ↦ compactScalarMap_isIso φ cf L, ?_⟩
  intro V _ _ v _ _ _ _ r i _ h cq cg IR IA bR bA
  let : IsNoetherian (affineTraceTower S r) := affineTraceNoetherian S r
  obtain ⟨nR⟩ := nonempty_etaleCompactSupportNormalization R
  obtain ⟨nA⟩ := nonempty_etaleCompactSupportNormalization A
  let FR := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cf
  let FA := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf
  let sR := derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) v
    inferInstance
  let sA := derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v
    inferInstance
  let eR := etaleAmbientLeftComparison R nR v f cf (cg.copy h)
  let eA := etaleAmbientLeftComparison A nA v f cf (cg.copy h)
  let dR := affineTraceAdjunction R N hR tR PR S hS r
  let dA := affineTraceAdjunction A N hA tA PA S hS r
  let jR := (bR.comp dR).ofNatIsoLeft (chartLeftIso R r i cq cg)
  let jA := (bA.comp dA).ofNatIsoLeft (chartLeftIso A r i cq cg)
  let gR := (sR.comp aR).ofNatIsoLeft eR
  let gA := (sA.comp aA).ofNatIsoLeft eA
  let lR := chartRestrictionIso R N hR tR PR hS f v r i h cf cq cg HR IR aR bR
  let lA := chartRestrictionIso A N hA tA PA hS f v r i h cf cq cg HA IA aA bA
  let K := constantComplex R S
  let K' := constantComplex A S
  let u : (scalarExtension φ S).obj K ⟶ K' :=
    (ExceptionalCoefficients.unitIso φ S).hom
  let q := (properOpenCoefficientPullbackIso φ v).inv.app (HR.obj K) ≫
    (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.map
      (DualizingOpenMate.globalMate φ cf HR HA aR aA)
  let a := closedMate φ i IR IA bR bA ((affineTraceRight R N hR S r).obj K) ≫
    IA.map (affineUnitScalarIso φ N hR hA S hS r).hom
  have hglobal : (compactScalarMap φ cf).app (HR.obj K) ≫
      FA.map (DualizingOpenMate.globalMate φ cf HR HA aR aA) ≫ aA.counit.app K' =
      (scalarExtension φ S).map (aR.counit.app K) ≫ u := by
    have hi : IsIso (ExceptionalCoefficients.compactSupportMap φ cf (HR.obj K)) :=
      compactScalarMap_isIso φ cf (HR.obj K)
    have he := (aA.homEquiv _ _).symm_apply_apply
      (ExceptionalCoefficients.comparisonInverse φ cf (HR.obj K) ≫
        (scalarExtension φ S).map (aR.counit.app K) ≫ u)
    change FA.map (DualizingOpenMate.globalMate φ cf HR HA aR aA) ≫ _ = _ at he
    simp only [Functor.id_obj] at he
    change FA.map (DualizingOpenMate.globalMate φ cf HR HA aR aA) ≫
      aA.counit.app K' = _ at he
    rw [he]
    simp only [ExceptionalCoefficients.comparisonInverse, dif_pos hi,
      compactScalarMap, IsIso.hom_inv_id_assoc]
  have hq := compose_unit_counit sR aR sA aA
    (scalarExtension φ V) (scalarExtension φ X) (scalarExtension φ S)
    (ProEtale.CoefficientCompatibility.sumCoefficientIso φ v).hom (compactScalarMap φ cf)
    K K' u ((properOpenCoefficientPullbackIso φ v).inv.app (HR.obj K))
    (DualizingOpenMate.globalMate φ cf HR HA aR aA)
    (firstDerived_eq_second φ v (HR.obj K)) hglobal
  have hq' := transport_unit_counit (sR.comp aR) (sA.comp aA) eR eA
    (scalarExtension φ V) (scalarExtension φ S) (compactScalarMap φ (cg.copy h))
    (scalarComposite (ProEtale.CoefficientCompatibility.sumCoefficientIso φ v).hom
      (compactScalarMap φ cf)) K K' u q
    (fun L ↦ by simpa only [eR, eA, scalarComposite, Category.assoc] using
      ambient_left_scalar φ nR nA v f cf (cg.copy h) L) hq
  have hclosed : (scalarMate φ i).app
        (IR.obj ((affineTraceRight R N hR S r).obj K)) ≫
      (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor.map
        (closedMate φ i IR IA bR bA ((affineTraceRight R N hR S r).obj K)) ≫
      bA.counit.app ((scalarExtension φ (affineTraceTower S r)).obj
        ((affineTraceRight R N hR S r).obj K)) =
      (scalarExtension φ (affineTraceTower S r)).map
        (bR.counit.app ((affineTraceRight R N hR S r).obj K)) := by
    let W := (affineTraceRight R N hR S r).obj K
    let hi : IsIso ((scalarMate φ i).app (IR.obj W)) :=
      (properFiniteCoefficientExtension φ i).1 (IR.obj W)
    have he := (bA.homEquiv ((scalarExtension φ V).obj (IR.obj W))
      ((scalarExtension φ (affineTraceTower S r)).obj W)).symm_apply_apply
      ((@asIso _ _ _ _ ((scalarMate φ i).app (IR.obj W)) hi).inv ≫
        (scalarExtension φ (affineTraceTower S r)).map (bR.counit.app W))
    change (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor.map
      (closedMate φ i IR IA bR bA W) ≫ _ = _ at he
    change (scalarMate φ i).app (IR.obj W) ≫
      (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor.map
        (closedMate φ i IR IA bR bA W) ≫ _ = _
    rw [he]
    exact (Iso.hom_inv_id_assoc
      (@asIso _ _ _ _ ((scalarMate φ i).app (IR.obj W)) hi) _)
  have haffine : (affineLeftScalar φ S r).app
        ((affineTraceRight R N hR S r).obj K) ≫
      (affineTraceLeft A S r).map (affineUnitScalarIso φ N hR hA S hS r).hom ≫
      dA.counit.app K' = (scalarExtension φ S).map (dR.counit.app K) ≫ u := by
    have hn := dA.counit.naturality u
    simp only [Functor.comp_map, Functor.id_map] at hn
    simp only [affineUnitScalarIso, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
      Category.assoc]
    change (affineTraceLeft A S r).map ((affineTraceRight A N hA S r).map
      (ExceptionalCoefficients.unitIso φ S).hom) ≫ dA.counit.app K' = _ at hn
    rw [hn]
    have hc := affine_scalar_counit φ N hN hR hA S hS tR tA PR PA r K
    change (affineLeftScalar φ S r).app _ ≫ (affineTraceLeft A S r).map _ ≫
      dA.counit.app ((scalarExtension φ S).obj K) = _ at hc
    simpa only [Category.assoc, K, dR] using congrArg (fun z ↦ z ≫ u) hc
  have ha := compose_unit_counit bR dR bA dA
    (scalarExtension φ V) (scalarExtension φ (affineTraceTower S r))
    (scalarExtension φ S) (scalarMate φ i) (affineLeftScalar φ S r) K K' u
    (closedMate φ i IR IA bR bA ((affineTraceRight R N hR S r).obj K))
    (affineUnitScalarIso φ N hR hA S hS r).hom hclosed haffine
  have ha' := transport_unit_counit (bR.comp dR) (bA.comp dA)
    (chartLeftIso R r i cq cg) (chartLeftIso A r i cq cg)
    (scalarExtension φ V) (scalarExtension φ S) (compactScalarMap φ cg)
    (scalarComposite (scalarMate φ i) (affineLeftScalar φ S r)) K K' u a
    (fun L ↦ by
      dsimp only [scalarComposite]
      simpa only [Category.assoc] using chart_left_scalar φ r i cq cg L) ha
  have hlR (L : DerivedCategoryModule R S) :
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cg).map
        (lR.hom.app L) ≫ jR.counit.app L = gR.counit.app L := by
    have hh := (existsUnique_etaleAmbientAdjointLocalityIso R v f cf
      (cg.copy h) HR (affineTraceRight R N hR S r ⋙ IR) aR jR).choose_spec.1 nR L
    convert hh using 1 <;>
      simp only [lR, chartRestrictionIso, jR, gR, eR, sR,
        Compactification.copy, Functor.comp_obj, Adjunction.ofNatIsoLeft_counit,
        Adjunction.comp_counit_app, NatTrans.comp_app, Functor.whiskerLeft_app]
  have hlA (L : DerivedCategoryModule A S) :
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).map
        (lA.hom.app L) ≫ jA.counit.app L = gA.counit.app L := by
    have hh := (existsUnique_etaleAmbientAdjointLocalityIso A v f cf
      (cg.copy h) HA (affineTraceRight A N hA S r ⋙ IA) aA jA).choose_spec.1 nA L
    convert hh using 1 <;>
      simp only [lA, chartRestrictionIso, jA, gA, eA, sA,
        Compactification.copy, Functor.comp_obj, Adjunction.ofNatIsoLeft_counit,
        Adjunction.comp_counit_app, NatTrans.comp_app, Functor.whiskerLeft_app]
  have hb := compactScalarMap_isIso φ cg
    ((HR ⋙ (upperStar (ModuleCat.{u + 1} R) v).mapDerivedCategory).obj K)
  have he := normalized_right_scalar gR jR gA jA
    (scalarExtension φ V) (scalarExtension φ S) (compactScalarMap φ cg)
    lR lA hlR hlA K K' u q a hq' (by infer_instance) ha'
  have hn := (leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} A) v).hom.naturality
      (DualizingOpenMate.globalMate φ cf HR HA aR aA)
  have hh := congrArg (fun z ↦ (scalarExtension φ V).map
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} R) v).hom.app
      (HR.obj K)) ≫ z) he.symm
  simp only [q, properOpenCoefficientPullbackIso, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Iso.symm_inv,
    Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp] at hh
  rw [← reassoc_of% hn] at hh
  exact hh

end AlgebraicGeometry.Etale.FiniteFreeDualizing
