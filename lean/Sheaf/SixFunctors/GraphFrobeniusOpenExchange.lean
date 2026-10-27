/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.SixFunctors.SelectedSchemeGaloisComparison
public import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
public import Sheaf.AlgebraicGeometry.FrobeniusOpenSquare
import Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction
import Sheaf.SixFunctors.SchemeGaloisPullbackNaturality

/-!
# Open extension commutes with the canonical scheme/Galois comparison

Source: main-20261015, `sec-trace-formula/sk-d-weil/`
`prop-trf-graph-frobenius-operator.proof.md`, Step 2
(blueprint: lem-trf-graph-frobenius-open-exchange).

The equation is stated in the functor category after restriction to D^b_ctf(X,A).
Thus it includes naturality in M. Scheme and Galois maps are morphisms of schemes;
no linearity over k is imposed on the Galois maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.TraceFormulaCoefficientConventions

/-- The open immersion obtained by geometric base change of the given model open.
Source: blueprint graph-Frobenius-operator proof, Step 2
(blueprint: lem-trf-graph-frobenius-open-exchange). -/
abbrev graphFrobeniusBaseChangedOpen (T : TraceFormulaCoefficientConventions.{u})
    (Y₀ : Over (Spec (CommRingCat.of T.datum.k₀))) (j₀ : T.X₀ ⟶ Y₀) :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap T.datum.k₀ T.datum.k)))).map j₀).left

/-- The base-changed map is open by the existing base-change theorem for morphism
properties, applied to the given open immersion. This registers the constructed map,
without imposing a new hypothesis.
Source: blueprint graph-Frobenius-operator proof, Step 2; Mathlib overPullbackMap
(blueprint: lem-trf-graph-frobenius-open-exchange). -/
noncomputable instance graphFrobeniusBaseChangedOpen_isOpenImmersion
    (T : TraceFormulaCoefficientConventions.{u})
    (Y₀ : Over (Spec (CommRingCat.of T.datum.k₀)))
    (j₀ : T.X₀ ⟶ Y₀) [IsOpenImmersion j₀.left] :
    IsOpenImmersion (T.graphFrobeniusBaseChangedOpen Y₀ j₀) :=
  MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
    (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) j₀ inferInstance

/-- The canonical exchange for the m-fold scheme-Frobenius open square.
Source: blueprint graph-Frobenius-operator proof, Step 2;
`lem-trf-frobenius-open-square` and `lem-trf-open-square-exchange`
(blueprint: lem-trf-graph-frobenius-open-exchange). -/
def graphFrobeniusSchemeExchange (T : TraceFormulaCoefficientConventions.{u})
    (Y₀ : Over (Spec (CommRingCat.of T.datum.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (j₀ : T.X₀ ⟶ Y₀) [IsOpenImmersion j₀.left] (m : ℕ) :
    sfIntrinsicDerivedOpen T.coefficientRing (T.graphFrobeniusBaseChangedOpen Y₀ j₀) ⋙
        proEtaleConstantRingDerivedPullback T.coefficientRing
          (T.datum.schemeFrobeniusIterate Y₀ m) ≅
      proEtaleConstantRingDerivedPullback T.coefficientRing
          (T.datum.schemeFrobeniusIterate T.X₀ m) ⋙
        sfIntrinsicDerivedOpen T.coefficientRing (T.graphFrobeniusBaseChangedOpen Y₀ j₀) :=
  constantOpenSquareExchange T.coefficients.l T.coefficientField T.level T.level_pos
    (T.datum.schemeFrobeniusIterate T.X₀ m) _ _
    (T.datum.schemeFrobeniusIterate Y₀ m)
    (T.datum.frobenius_open_square T.X₀ Y₀ j₀ m).1

/-- The canonical exchange for the m-fold geometric-Galois-Frobenius open square.
Source: blueprint graph-Frobenius-operator proof, Step 2;
`lem-trf-frobenius-open-square` and `lem-trf-open-square-exchange`
(blueprint: lem-trf-graph-frobenius-open-exchange). -/
def graphFrobeniusGaloisExchange (T : TraceFormulaCoefficientConventions.{u})
    (Y₀ : Over (Spec (CommRingCat.of T.datum.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (j₀ : T.X₀ ⟶ Y₀) [IsOpenImmersion j₀.left] (m : ℕ) :
    sfIntrinsicDerivedOpen T.coefficientRing (T.graphFrobeniusBaseChangedOpen Y₀ j₀) ⋙
        proEtaleConstantRingDerivedPullback T.coefficientRing
          (HPow.hPow (α := End (T.datum.geometricFiber Y₀).left)
            (T.datum.geometricGaloisFrobenius Y₀) m) ≅
      proEtaleConstantRingDerivedPullback T.coefficientRing
          (HPow.hPow (α := End (T.datum.geometricFiber T.X₀).left)
            (T.datum.geometricGaloisFrobenius T.X₀) m) ⋙
        sfIntrinsicDerivedOpen T.coefficientRing (T.graphFrobeniusBaseChangedOpen Y₀ j₀) :=
  constantOpenSquareExchange T.coefficients.l T.coefficientField T.level T.level_pos
    (HPow.hPow (α := End (T.datum.geometricFiber T.X₀).left)
      (T.datum.geometricGaloisFrobenius T.X₀) m) _ _
    (HPow.hPow (α := End (T.datum.geometricFiber Y₀).left)
      (T.datum.geometricGaloisFrobenius Y₀) m)
    (T.datum.frobenius_open_square T.X₀ Y₀ j₀ m).2.1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derivedId_hom_Q {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj K) =
      (𝟭 C).mapDerivedCategoryFactors.hom.app K := by
  have hf := congr_app (congrArg Iso.hom (Functor.mapDerivedCategoryIdIso_factorsh C))
    ((HomotopyCategory.quotient C (.up ℤ)).obj K)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.mapDerivedCategoryFactorsh_hom_app,
    Functor.mapHomotopyCategoryIdIso_hom_app] at hf
  have h₁ : ((𝟭 C).mapHomotopyCategoryFactors (.up ℤ)).inv.app K = 𝟙 _ := rfl
  have h₂ : (Functor.mapHomologicalComplexIdIso C (.up ℤ)).hom.app K = 𝟙 _ := rfl
  rw [h₁, h₂] at hf
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.comp_id] at hf
  have he : (DerivedCategory.quotientCompQhIso C).inv.app
      (((𝟭 C).mapHomologicalComplex (.up ℤ)).obj K) = 𝟙 _ := rfl
  rw [he] at hf
  erw [Category.id_comp, Category.comp_id, Category.comp_id] at hf
  exact hf

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exactDerivedAdjunction_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) (G : D ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (adj : F ⊣ G) :
    let : CatCommSq (F.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q F.mapDerivedCategory :=
        ⟨F.mapDerivedCategoryFactors.symm⟩
    let : CatCommSq (G.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
        ⟨G.mapDerivedCategoryFactors.symm⟩
    ((adj.mapHomologicalComplex (.up ℤ)).localization
      DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
      DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
      F.mapDerivedCategory G.mapDerivedCategory).unit =
    (Functor.mapDerivedCategoryIdIso C).inv ≫
      Localization.liftNatTrans DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
        ((𝟭 C).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
        ((F ⋙ G).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
        (𝟭 C).mapDerivedCategory (F ⋙ G).mapDerivedCategory
        (Functor.whiskerRight (NatTrans.mapHomologicalComplex adj.unit (.up ℤ))
          DerivedCategory.Q) ≫ (Functor.mapDerivedCategoryCompIso F G).hom := by
  let : CatCommSq (F.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q F.mapDerivedCategory :=
    ⟨F.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (G.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
    ⟨G.mapDerivedCategoryFactors.symm⟩
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
  intro K
  simp only [Adjunction.localization_unit_app, NatTrans.comp_app, Iso.symm_hom]
  apply (cancel_mono (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
    G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K))).1
  have hc := Functor.mapDerivedCategoryCompIso_fac F G K
  have hid : DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app K) =
        𝟙 _ := by
    change DerivedCategory.Q.map (𝟙 _) = 𝟙 _
    exact CategoryTheory.Functor.map_id _ _
  rw [hid] at hc
  erw [Category.comp_id] at hc
  simp only [Category.assoc]
  erw [hc]
  simp only [Localization.liftNatTrans_app]
  change _ = (Functor.mapDerivedCategoryIdIso C).inv.app _ ≫
    ((𝟭 C).mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app K) ≫
      (F ⋙ G).mapDerivedCategoryFactors.inv.app K) ≫
      (F ⋙ G).mapDerivedCategoryFactors.hom.app K
  rw [← derivedId_hom_Q]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  erw [← G.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
  rfl

private theorem derivedOpenAdjunction_unit (A : Type u) [CommRing A] [Finite A]
    {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] :
    (exceptionalOpenAdjunction j A).unit = sfIntrinsicDerivedOpenUnit A j := by
  exact exactDerivedAdjunction_unit _ _ (sfIntrinsicOpenAdjunction A j)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem constantExchange_inverse_unit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (gU : U ⟶ U) (g : Y ⟶ Y) (sq : IsPullback gU j j g)
    (K : proEtaleDerivedCategory U (Padic.coefficientExtensionRing l E n)) :
    let := Padic.finite_coefficientExtensionRing l E n hn
    let A := Padic.coefficientExtensionRing l E n
    (sfIntrinsicDerivedOpenUnit A j).app
        ((proEtaleConstantRingDerivedPullback A gU).obj K) ≫
      (sfIntrinsicDerivedPullback A j).map
        ((constantOpenSquareExchange l E n hn gU j j g sq).inv.app K) =
    (proEtaleConstantRingDerivedPullback A gU).map
        ((sfIntrinsicDerivedOpenUnit A j).app K) ≫
      (constantIntrinsicSquarePullback A gU j j g sq.w).hom.app
        ((sfIntrinsicDerivedOpen A j).obj K) := by
  let := Padic.finite_coefficientExtensionRing l E n hn
  let A := Padic.coefficientExtensionRing l E n
  let data := Classical.choice (proEtale_openSquareExchange l E n hn)
  have h : (sfIntrinsicDerivedOpenUnit A j).app
        ((sfIntrinsicDerivedPullback A gU).obj K) ≫
      (sfIntrinsicDerivedPullback A j).map ((data.exchange gU j j g sq).inv.app K) =
    (sfIntrinsicDerivedPullback A gU).map ((sfIntrinsicDerivedOpenUnit A j).app K) ≫
      (sfIntrinsicDerivedSquarePullback A gU j j g sq.w).hom.app
        ((sfIntrinsicDerivedOpen A j).obj K) := by
    rw [← data.restriction gU j j g sq K]
    dsimp only [A]
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  dsimp only [A] at h ⊢
  dsimp only [constantOpenSquareExchange, constantIntrinsicSquarePullback]
  simp only [Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_inv, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  have hu := (sfIntrinsicDerivedOpenUnit A j).naturality
    ((openSquareDerivedPullbackModel A gU).hom.app K)
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← reassoc_of% hu]
  erw [reassoc_of% h]
  rw [← (openSquareDerivedPullbackModel A gU).hom.naturality_assoc]


-- Naturality of the open exchange follows by transposing its inverse through the
-- open adjunction. This calculation does not require full faithfulness.
private theorem exchange_naturality_of_mates
    {C D : Type*} [Category C] [Category D]
    {J : C ⥤ D} {R : D ⥤ C} (adj : J ⊣ R)
    (η : 𝟭 C ⟶ J ⋙ R) (hη : adj.unit = η)
    {P Q : D ⥤ D} {p q : C ⥤ C}
    (c : P ⟶ Q) (d : p ⟶ q)
    (sP : R ⋙ p ⟶ P ⋙ R) (sQ : R ⋙ q ⟶ Q ⋙ R)
    (bP : J ⋙ P ≅ p ⋙ J) (bQ : J ⋙ Q ≅ q ⋙ J)
    (hP : ∀ M, η.app (p.obj M) ≫ R.map (bP.inv.app M) =
      p.map (η.app M) ≫ sP.app (J.obj M))
    (hQ : ∀ M, η.app (q.obj M) ≫ R.map (bQ.inv.app M) =
      q.map (η.app M) ≫ sQ.app (J.obj M))
    (hc : sP ≫ Functor.whiskerRight c R = Functor.whiskerLeft R d ≫ sQ) :
    Functor.whiskerLeft J c ≫ bQ.hom = bP.hom ≫ Functor.whiskerRight d J := by
  apply NatTrans.ext
  funext M
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  apply (cancel_epi (bP.inv.app M)).1
  simp only [← Category.assoc, bP.inv_hom_id_app, Category.id_comp]
  apply (cancel_mono (bQ.inv.app M)).1
  simp only [Category.assoc, bQ.hom_inv_id_app, Category.comp_id]
  apply (adj.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, hη, Functor.map_comp]
  rw [← Category.assoc, hP, Category.assoc]
  have hcM := congr_app hc (J.obj M)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] at hcM
  have hd : p.map (η.app M) ≫ d.app (R.obj (J.obj M)) =
      d.app M ≫ q.map (η.app M) := d.naturality (η.app M)
  rw [hcM, ← Category.assoc, hd, Category.assoc, ← hQ, ← Category.assoc]
  simpa only [Functor.id_map, Functor.comp_map, Category.assoc] using
    congrArg (fun f ↦ f ≫ R.map (bQ.inv.app M)) (η.naturality (d.app M))

/-- Open extension commutes with the specified scheme/Galois comparison, naturally on
D^b_ctf(X,A), for every positive iterate m. The functor-category equality evaluates at M
as kappa_Y(j_!M) followed by b_g equals b_Phi followed by j_!(kappa_X(M)).
Source: main-20261015, graph-Frobenius-operator proof, Step 2
(blueprint: lem-trf-graph-frobenius-open-exchange).

Proof, following the seven steps of the node:
1. For Z = X,Y put H_Z = F_Z^(a*m), P_Z = L(Phi_Z^m)^*, G_Z = L(g_Z^m)^*.
   The recorded factorization and inverse arithmetic/geometric Galois maps give
   Phi_Z^m = H_Z followed by g_Z^m. The comparison is c_Z followed by tau_Z at G_Z.
2. Fix canonical constant-section coefficient maps. On pure tensors the ordinary
   composition sends (v tensor a) tensor b to v tensor c_h(a)b. Both reassociations
   of three pullbacks give v tensor c_h(c_k(a))c_h(b)d. Fibre-product reassociation
   has the same projections. These formulas survive restriction to the open and exact
   termwise descent by the localization universal property, and coincide with the
   canonical K-flat comparison of the recorded pullback-composition theorem.
3. Write r = Lj^*. The Cartesian squares give alpha_P and alpha_G. Pullback naturality
   of the absolute-Frobenius trivialization, with exponent a*m, gives
   tau_X at rN composed after alpha_T = r(tau_Y at N). Composition coherence gives
   c_X at rN after alpha_P = T_X(alpha_G) after alpha_T at G_Y N after r(c_Y).
4. Substitute kappa = tau after c and use naturality of tau_X to obtain
   kappa_X at rN after alpha_P = alpha_G after r(kappa_Y at N).
5. Use the canonical open unit and its inverse nu. Identity normalization of the
   canonical exchanges gives nu after r(b_P) = P_X(nu) after alpha_P, and the same
   formula with G. The coordinate transport preserves precisely these units.
6. Put L = b_G after kappa_Y and R = j_!(kappa_X) after b_P. Apply Step 4 at j_!M,
   naturality of kappa_X for nu_M, and Step 5. Both nu after r(L) and nu after r(R)
   equal kappa_X after P_X(nu_M) after alpha_P. Cancel the invertible nu to get r(L)=r(R).
7. Precompose L and R by b_P inverse. They are maps between two objects in the image
   of j_!. Derived full faithfulness of open extension, via the open unit, detects
   their equality after r. Cancel b_P inverse to obtain L=R. All comparisons and
   exchanges are natural transformations, and restriction to D^b_ctf gives the displayed
   equality in its functor category. The argument applies to arbitrary m ≥ 1.
The not-yet-stated proof dependency lem-sf-open-tensor-normalization supplies the derived
open-unit isomorphism and full faithfulness in Steps 5 and 7; its import is deferred. -/
theorem graphFrobenius_open_exchange (T : TraceFormulaCoefficientConventions.{u})
    (Y₀ : Over (Spec (CommRingCat.of T.datum.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (j₀ : T.X₀ ⟶ Y₀) [IsOpenImmersion j₀.left] (m : ℕ) (hm : 1 ≤ m) :
    Functor.whiskerLeft T.boundedConstructibleFiniteTor.ι
        (Functor.whiskerLeft
            (sfIntrinsicDerivedOpen T.coefficientRing (T.graphFrobeniusBaseChangedOpen Y₀ j₀))
            (T.selectedSchemeGaloisComparison Y₀ m hm).hom ≫
          (T.graphFrobeniusGaloisExchange Y₀ j₀ m).hom) =
      Functor.whiskerLeft T.boundedConstructibleFiniteTor.ι
        ((T.graphFrobeniusSchemeExchange Y₀ j₀ m).hom ≫
          Functor.whiskerRight (T.selectedSchemeGaloisComparison T.X₀ m hm).hom
            (sfIntrinsicDerivedOpen T.coefficientRing
              (T.graphFrobeniusBaseChangedOpen Y₀ j₀))) := by
  apply congrArg (Functor.whiskerLeft T.boundedConstructibleFiniteTor.ι)
  let sqP := (T.datum.frobenius_open_square T.X₀ Y₀ j₀ m).1
  let sqG := (T.datum.frobenius_open_square T.X₀ Y₀ j₀ m).2.1
  apply exchange_naturality_of_mates
    (exceptionalOpenAdjunction (T.graphFrobeniusBaseChangedOpen Y₀ j₀) T.coefficientRing)
    (sfIntrinsicDerivedOpenUnit T.coefficientRing (T.graphFrobeniusBaseChangedOpen Y₀ j₀))
    (derivedOpenAdjunction_unit T.coefficientRing (T.graphFrobeniusBaseChangedOpen Y₀ j₀))
    (T.selectedSchemeGaloisComparison Y₀ m hm).hom
    (T.selectedSchemeGaloisComparison T.X₀ m hm).hom
    (constantIntrinsicSquarePullback T.coefficientRing
      (T.datum.schemeFrobeniusIterate T.X₀ m) _ _
      (T.datum.schemeFrobeniusIterate Y₀ m) sqP.w).hom
    (constantIntrinsicSquarePullback T.coefficientRing
      (HPow.hPow (α := End (T.datum.geometricFiber T.X₀).left)
        (T.datum.geometricGaloisFrobenius T.X₀) m) _ _
      (HPow.hPow (α := End (T.datum.geometricFiber Y₀).left)
        (T.datum.geometricGaloisFrobenius Y₀) m) sqG.w).hom
    (T.graphFrobeniusSchemeExchange Y₀ j₀ m) (T.graphFrobeniusGaloisExchange Y₀ j₀ m)
  · intro M
    exact constantExchange_inverse_unit T.coefficients.l T.coefficientField T.level
      T.level_pos _ _ _ sqP M
  · intro M
    exact constantExchange_inverse_unit T.coefficients.l T.coefficientField T.level
      T.level_pos _ _ _ sqG M
  · exact T.datum.canonicalSchemeGaloisComparison_pullback T.X₀ Y₀ j₀ T.coefficientRing
      T.comparisonCoefficientAnnihilator m hm sqP.w sqG.w

end WeilConjectures.TraceFormulaCoefficientConventions
