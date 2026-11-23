/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedBaseChangeMap
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedOrdinaryComparisons
import WeilConjectures.Algebra.Homology.DerivedCategory.IsIsoEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalDerivedPullbackNormalization
import all WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
import all WeilConjectures.SixFunctors.PurCompactSupport.ScalarGeometricPullComposition
import WeilConjectures.Tactic.TransportExact

/-!
# Proper base change for complete complexes

Let `f : X ⟶ Y` be proper, `g : Y' ⟶ Y` arbitrary and `X' = X ×_Y Y'` with projections
`f' : X' ⟶ Y'` and `g' : X' ⟶ X`. For a quotient-tower complete `K` on `X` whose reductions
`K_n` have bounded below étale origin:

* `Rf_* K` is complete (`AlgebraicGeometry.Scheme.AdicCoefficientDatum.push_complete`);
* `ĝ^* Rf_* K ≅ Rlim_n g^* Rf_* K_n`
  (`AlgebraicGeometry.Scheme.AdicCoefficientDatum.completedPullPushIso`);
* `Rf'_* ĝ'^* K ≅ Rlim_n Rf'_* g'^* K_n`
  (`AlgebraicGeometry.Scheme.AdicCoefficientDatum.pushCompletedPullIso`);
* under these, the derived limit of the finite base change maps is an isomorphism
  `ĝ^* Rf_* K ≅ Rf'_* ĝ'^* K`
  (`AlgebraicGeometry.Scheme.AdicCoefficientDatum.isIso_completedBaseChangeMap`).

## Implementation details

The completed pullback `ĝ^*` is by definition the derived limit of the pullback of the reduction
tower, and the reduction tower of `Rf_* K` is the tower `(Rf_{n*} K_n)_n` through the
projection-formula isomorphisms (`AlgebraicGeometry.Scheme.AdicCoefficientDatum.towerProjection`);
the direct image commutes with derived limits of towers
(`AlgebraicGeometry.Scheme.AdicCoefficientDatum.directImageRlimIso`).

The last point reduces, by conservativity of the evaluations of derived towers, to finite-level
proper base change (`AlgebraicGeometry.Scheme.AdicCoefficientDatum.finiteExchange_isIso`),
once the reduction of the integral base change map is identified with the finite base change
map (`AlgebraicGeometry.Scheme.AdicCoefficientDatum.finiteProjection_comp_finiteExchange`).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe t

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)

/-! ### Reduction of the integral exchange

The finite base change map and the reduction of the integral one are both mates of the
canonical pullback comparisons around the square. Reduction `d.reduction` commutes with
pullback through `d.chi`, which is the scalar/pullback comparison `scalarPull` of the reduction
of coefficients, and `scalarPull` is compatible with the composition of pullbacks
(`WeilConjectures.PurCompactSupport.scalarPull_geometric_composition`). Hence the reductions of
the two pullback comparisons around the square agree, and transposing along the finite
adjunctions gives the compatibility of the four arrows. -/

/-- Transposing a square of reduction comparisons along the pullback/direct image adjunctions:
if reduction intertwines the pullback comparisons `c` and `cn` around a square, then the
finite mate of `cn`, precomposed with the finite projection map of `f`, is the reduction of the
integral mate of `c`, followed by the finite projection map of `f'`. -/
private theorem mateEquiv_reduction_comp
    {DY DX DY' DX' EY EX EY' EX' : Type*} [Category DY] [Category DX] [Category DY']
    [Category DX'] [Category EY] [Category EX] [Category EY'] [Category EX']
    {fU : DY ⥤ DX} {fP : DX ⥤ DY} {f'U : DY' ⥤ DX'} {f'P : DX' ⥤ DY'}
    {gU : DY ⥤ DY'} {g'U : DX ⥤ DX'}
    {fnU : EY ⥤ EX} {fnP : EX ⥤ EY} {f'nU : EY' ⥤ EX'} {f'nP : EX' ⥤ EY'}
    {gnU : EY ⥤ EY'} {g'nU : EX ⥤ EX'}
    {eY : DY ⥤ EY} {eX : DX ⥤ EX} {eY' : DY' ⥤ EY'} {eX' : DX' ⥤ EX'}
    (af : fU ⊣ fP) (af' : f'U ⊣ f'P) (an : fnU ⊣ fnP) (an' : f'nU ⊣ f'nP)
    (c : gU ⋙ f'U ⟶ fU ⋙ g'U) (cn : gnU ⋙ f'nU ⟶ fnU ⋙ g'nU)
    (sf : fU ⋙ eX ≅ eY ⋙ fnU) (sf' : f'U ⋙ eX' ≅ eY' ⋙ f'nU)
    (sg : gU ⋙ eY' ≅ eY ⋙ gnU) (sg' : g'U ⋙ eX' ≅ eX ⋙ g'nU)
    (hsq : ∀ L : DY, eX'.map (c.app L) ≫ sg'.hom.app (fU.obj L) ≫ g'nU.map (sf.hom.app L) =
      sf'.hom.app (gU.obj L) ≫ f'nU.map (sg.hom.app L) ≫ cn.app (eY.obj L))
    (K : DX) :
    gnU.map (an.homEquiv _ _ (sf.inv.app (fP.obj K) ≫ eX.map (af.counit.app K))) ≫
        (mateEquiv an an' cn).app (eX.obj K) =
      sg.inv.app (fP.obj K) ≫ eY'.map ((mateEquiv af af' c).app K) ≫
        an'.homEquiv _ _ (sf'.inv.app (f'P.obj (g'U.obj K)) ≫
          eX'.map (af'.counit.app (g'U.obj K))) ≫
        f'nP.map (sg'.hom.app K) := by
  set P := an.homEquiv _ _ (sf.inv.app (fP.obj K) ≫ eX.map (af.counit.app K))
  set Q := sf'.inv.app (f'P.obj (g'U.obj K)) ≫ eX'.map (af'.counit.app (g'U.obj K))
  have h1 := mateEquiv_counit an an' cn (eX.obj K)
  have h2 : fnU.map P ≫ an.counit.app (eX.obj K) =
      sf.inv.app (fP.obj K) ≫ eX.map (af.counit.app K) :=
    (an.homEquiv_counit (g := P)).symm.trans (Equiv.symm_apply_apply _ _)
  have h3 : f'nU.map (an'.homEquiv _ _ Q) ≫ an'.counit.app _ = Q :=
    (an'.homEquiv_counit (g := an'.homEquiv _ _ Q)).symm.trans (Equiv.symm_apply_apply _ _)
  have h4 := mateEquiv_counit af af' c K
  have hcn := cn.naturality P
  have hsf' := sf'.inv.naturality ((mateEquiv af af' c).app K)
  have hsg' := sg'.hom.naturality (af.counit.app K)
  have hL : eX'.map (c.app (fP.obj K)) ≫ sg'.hom.app (fU.obj (fP.obj K)) =
      sf'.hom.app _ ≫ f'nU.map (sg.hom.app _) ≫ cn.app _ ≫
        g'nU.map (sf.inv.app (fP.obj K)) := by
    rw [← reassoc_of% (hsq (fP.obj K)), ← g'nU.map_comp, Iso.hom_inv_id_app]
    simp
  dsimp only [Functor.comp_obj, Functor.comp_map] at h1 h4 hcn hsf' hsg'
  apply (an'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [h1, an'.counit_naturality]
  erw [reassoc_of% h3]
  rw [reassoc_of% hcn, ← g'nU.map_comp, h2]
  simp only [Q, Category.assoc]
  rw [reassoc_of% hsf', ← eX'.map_comp_assoc, h4]
  simp only [Functor.map_comp, Category.assoc]
  erw [hsg']
  rw [reassoc_of% hL]
  simp

/-- If reduction is compatible with two composites of pullbacks `q₁ ≅ gU ⋙ f'U` and
`q₂ ≅ fU ⋙ g'U`, and with an identification `q₁ ≅ q₂`, then it intertwines the resulting
comparison `gU ⋙ f'U ≅ fU ⋙ g'U` with its finite analogue. -/
private theorem reduction_square_of_comp
    {DY DX DY' DX' EY EX EY' EX' : Type*} [Category DY] [Category DX] [Category DY']
    [Category DX'] [Category EY] [Category EX] [Category EY'] [Category EX']
    {fU : DY ⥤ DX} {f'U : DY' ⥤ DX'} {gU : DY ⥤ DY'} {g'U : DX ⥤ DX'}
    {q₁ q₂ : DY ⥤ DX'}
    {fnU : EY ⥤ EX} {f'nU : EY' ⥤ EX'} {gnU : EY ⥤ EY'} {g'nU : EX ⥤ EX'}
    {qn₁ qn₂ : EY ⥤ EX'}
    {eY : DY ⥤ EY} {eX : DX ⥤ EX} {eY' : DY' ⥤ EY'} {eX' : DX' ⥤ EX'}
    (sf : fU ⋙ eX ≅ eY ⋙ fnU) (sf' : f'U ⋙ eX' ≅ eY' ⋙ f'nU)
    (sg : gU ⋙ eY' ≅ eY ⋙ gnU) (sg' : g'U ⋙ eX' ≅ eX ⋙ g'nU)
    (s₁ : q₁ ⋙ eX' ≅ eY ⋙ qn₁) (s₂ : q₂ ⋙ eX' ≅ eY ⋙ qn₂)
    (G₁ : q₁ ≅ gU ⋙ f'U) (G₂ : q₂ ≅ fU ⋙ g'U) (Gn₁ : qn₁ ≅ gnU ⋙ f'nU)
    (Gn₂ : qn₂ ≅ fnU ⋙ g'nU) (m : q₁ ≅ q₂) (mn : qn₁ ≅ qn₂)
    (h₁ : ∀ L, eX'.map (G₁.inv.app L) ≫ s₁.hom.app L =
      sf'.hom.app (gU.obj L) ≫ f'nU.map (sg.hom.app L) ≫ Gn₁.inv.app (eY.obj L))
    (h₂ : ∀ L, eX'.map (G₂.inv.app L) ≫ s₂.hom.app L =
      sg'.hom.app (fU.obj L) ≫ g'nU.map (sf.hom.app L) ≫ Gn₂.inv.app (eY.obj L))
    (hm : Functor.whiskerRight m.hom eX' ≫ s₂.hom = s₁.hom ≫ Functor.whiskerLeft eY mn.hom)
    (L : DY) :
    eX'.map ((G₁.inv ≫ m.hom ≫ G₂.hom).app L) ≫ sg'.hom.app (fU.obj L) ≫
        g'nU.map (sf.hom.app L) =
      sf'.hom.app (gU.obj L) ≫ f'nU.map (sg.hom.app L) ≫
        (Gn₁.inv ≫ mn.hom ≫ Gn₂.hom).app (eY.obj L) := by
  have h₂' : eX'.map (G₂.hom.app L) ≫ sg'.hom.app (fU.obj L) ≫ g'nU.map (sf.hom.app L) =
      s₂.hom.app L ≫ Gn₂.hom.app (eY.obj L) := by
    calc _ = eX'.map (G₂.hom.app L) ≫ (sg'.hom.app (fU.obj L) ≫ g'nU.map (sf.hom.app L) ≫
          Gn₂.inv.app (eY.obj L)) ≫ Gn₂.hom.app (eY.obj L) := by simp
      _ = eX'.map (G₂.hom.app L) ≫ (eX'.map (G₂.inv.app L) ≫ s₂.hom.app L) ≫
          Gn₂.hom.app (eY.obj L) := by rw [h₂]
      _ = _ := by
        rw [← Category.assoc, ← Category.assoc, ← eX'.map_comp, Iso.hom_inv_id_app]
        simp
  have hmL := congrArg (fun t ↦ t.app L) hm
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hmL
  simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [h₂', reassoc_of% hmL, reassoc_of% (h₁ L)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The geometric pullback compositor is the canonical derived pullback comparison. -/
private theorem geometricPullComposition_eq
    (R : WeilConjectures.PurCompactSupport.Coefficients.{t}) {U V W : Scheme.{t}}
    (h : U ⟶ V) (k : V ⟶ W)
    (hc : R.pull (h ≫ k) = proEtaleRingCompositeCoefficients h k
      (R.ring W) (R.ring V) (R.ring U) (R.pull k) (R.pull h)) :
    WeilConjectures.PurCompactSupport.geometricPullComposition R h k hc =
      eqToIso (congrArg (proEtaleRingDerivedPullback (h ≫ k) (R.ring W) (R.ring U)) hc) ≪≫
        proEtaleCanonicalDerivedPullbackComparison h k (R.ring W) (R.ring V) (R.ring U)
          (R.pull k) (R.pull h) := by
  have hd := (WeilConjectures.PurCompactSupport.modulePushComposition_existsUnique
    R h k hc).exists.choose_spec
  rw [proEtaleCanonicalDerivedPullback_normalization h k (R.ring W) (R.ring V) (R.ring U)
    (R.pull k) (R.pull h) (R.pull (h ≫ k)) hc.symm _ hd]
  unfold WeilConjectures.PurCompactSupport.geometricPullComposition
  congr 2

/-- The pullback comparison around the square is the composite of the two geometric pullback
compositors with the identification of the two composites `X' ⟶ Y`. -/
private theorem ambientRingedPullbackComparison_eq
    (R : WeilConjectures.PurCompactSupport.Coefficients.{t})
    {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (h₁ : R.pull (f' ≫ g) = proEtaleRingCompositeCoefficients f' g
      (R.ring Y) (R.ring Y') (R.ring X') (R.pull g) (R.pull f'))
    (h₂ : R.pull (g' ≫ f) = proEtaleRingCompositeCoefficients g' f
      (R.ring Y) (R.ring X) (R.ring X') (R.pull f) (R.pull g'))
    (hc : HEq (proEtaleRingCompositeCoefficients g' f (R.ring Y) (R.ring X) (R.ring X')
        (R.pull f) (R.pull g'))
      (proEtaleRingCompositeCoefficients f' g (R.ring Y) (R.ring Y') (R.ring X')
        (R.pull g) (R.pull f'))) :
    proEtaleAmbientRingedPullbackComparison sq (R.ring X) (R.ring Y) (R.ring X') (R.ring Y')
        (R.pull f) (R.pull g) (R.pull g') (R.pull f') hc =
      (WeilConjectures.PurCompactSupport.geometricPullComposition R f' g h₁).symm ≪≫
        eqToIso (congrArg (fun q : X' ⟶ Y ↦ WeilConjectures.PurCompactSupport.pull R q)
          sq.w.symm) ≪≫
        WeilConjectures.PurCompactSupport.geometricPullComposition R g' f h₂ := by
  rw [geometricPullComposition_eq, geometricPullComposition_eq]
  apply Iso.ext
  simp only [proEtaleAmbientRingedPullbackComparison, Iso.trans_hom, Iso.symm_hom,
    Iso.trans_inv, eqToIso.hom, eqToIso.inv, Category.assoc, eqToHom_trans_assoc]

/-- `scalarPull` is compatible with the identification of pullbacks along equal morphisms. -/
private theorem scalarPull_eqToIso
    {R S : WeilConjectures.PurCompactSupport.Coefficients.{t}}
    (a : WeilConjectures.PurCompactSupport.Change R S) {U V : Scheme.{t}} {q₁ q₂ : U ⟶ V}
    (w : q₁ = q₂) :
    Functor.whiskerRight
        (eqToIso (congrArg (fun q : U ⟶ V ↦ WeilConjectures.PurCompactSupport.pull R q) w)).hom
        (pbcDerivedExtend (a.map U)) ≫ (WeilConjectures.PurCompactSupport.scalarPull a q₂).hom =
      (WeilConjectures.PurCompactSupport.scalarPull a q₁).hom ≫
        Functor.whiskerLeft (pbcDerivedExtend (a.map V))
          (eqToIso (congrArg (fun q : U ⟶ V ↦ WeilConjectures.PurCompactSupport.pull S q)
            w)).hom := by
  subst w
  simp

/-- Reduction along a coefficient change intertwines the pullback comparisons around a
cartesian square. -/
private theorem scalarPull_ambientRingedPullbackComparison
    {R S : WeilConjectures.PurCompactSupport.Coefficients.{t}}
    (a : WeilConjectures.PurCompactSupport.Change R S) {X' X Y' Y : Scheme.{t}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (h₁R : R.pull (f' ≫ g) = proEtaleRingCompositeCoefficients f' g
      (R.ring Y) (R.ring Y') (R.ring X') (R.pull g) (R.pull f'))
    (h₂R : R.pull (g' ≫ f) = proEtaleRingCompositeCoefficients g' f
      (R.ring Y) (R.ring X) (R.ring X') (R.pull f) (R.pull g'))
    (h₁S : S.pull (f' ≫ g) = proEtaleRingCompositeCoefficients f' g
      (S.ring Y) (S.ring Y') (S.ring X') (S.pull g) (S.pull f'))
    (h₂S : S.pull (g' ≫ f) = proEtaleRingCompositeCoefficients g' f
      (S.ring Y) (S.ring X) (S.ring X') (S.pull f) (S.pull g'))
    (hcR : HEq (proEtaleRingCompositeCoefficients g' f (R.ring Y) (R.ring X) (R.ring X')
        (R.pull f) (R.pull g'))
      (proEtaleRingCompositeCoefficients f' g (R.ring Y) (R.ring Y') (R.ring X')
        (R.pull g) (R.pull f')))
    (hcS : HEq (proEtaleRingCompositeCoefficients g' f (S.ring Y) (S.ring X) (S.ring X')
        (S.pull f) (S.pull g'))
      (proEtaleRingCompositeCoefficients f' g (S.ring Y) (S.ring Y') (S.ring X')
        (S.pull g) (S.pull f')))
    (L : DerivedCategory (pbcModules Y (R.ring Y))) :
    (pbcDerivedExtend (a.map X')).map
        ((proEtaleAmbientRingedPullbackComparison sq (R.ring X) (R.ring Y) (R.ring X')
          (R.ring Y') (R.pull f) (R.pull g) (R.pull g') (R.pull f') hcR).hom.app L) ≫
      (WeilConjectures.PurCompactSupport.scalarPull a g').hom.app
        ((WeilConjectures.PurCompactSupport.pull R f).obj L) ≫
      (WeilConjectures.PurCompactSupport.pull S g').map
        ((WeilConjectures.PurCompactSupport.scalarPull a f).hom.app L) =
    (WeilConjectures.PurCompactSupport.scalarPull a f').hom.app
        ((WeilConjectures.PurCompactSupport.pull R g).obj L) ≫
      (WeilConjectures.PurCompactSupport.pull S f').map
        ((WeilConjectures.PurCompactSupport.scalarPull a g).hom.app L) ≫
      (proEtaleAmbientRingedPullbackComparison sq (S.ring X) (S.ring Y) (S.ring X')
          (S.ring Y') (S.pull f) (S.pull g) (S.pull g') (S.pull f') hcS).hom.app
        ((pbcDerivedExtend (a.map Y)).obj L) := by
  open WeilConjectures.PurCompactSupport in
  rw [ambientRingedPullbackComparison_eq R sq h₁R h₂R hcR,
    ambientRingedPullbackComparison_eq S sq h₁S h₂S hcS]
  simp only [Iso.trans_hom, Iso.symm_hom]
  -- `transport_exact` keeps the kernel from unfolding the two spellings of the derived
  -- categories of modules.
  have key := reduction_square_of_comp (scalarPull a f) (scalarPull a f') (scalarPull a g)
    (scalarPull a g') (scalarPull a (f' ≫ g)) (scalarPull a (g' ≫ f))
    (geometricPullComposition R f' g h₁R) (geometricPullComposition R g' f h₂R)
    (geometricPullComposition S f' g h₁S) (geometricPullComposition S g' f h₂S)
    (eqToIso (congrArg (fun q : X' ⟶ Y ↦ pull R q) sq.w.symm))
    (eqToIso (congrArg (fun q : X' ⟶ Y ↦ pull S q) sq.w.symm))
    (fun L ↦ by transport_exact scalarPull_geometric_composition a f' g h₁R h₁S L)
    (fun L ↦ by transport_exact scalarPull_geometric_composition a g' f h₂R h₂S L)
    (by transport_exact scalarPull_eqToIso a sq.w.symm) L
  transport_exact key

/-- The completed coefficients of `d`. -/
private def adicIntegralCoefficients : WeilConjectures.PurCompactSupport.Coefficients.{t} where
  ring := d.completedRing
  pull g := d.integralRingIso g

/-- The coefficients of `d` at level `n`. -/
private def adicFiniteCoefficients (n : ℕ) :
    WeilConjectures.PurCompactSupport.Coefficients.{t} where
  ring W := d.finiteRing W n
  pull g := d.finiteRingIso g n

/-- Reduction of the completed coefficients of `d` to level `n`. -/
private def adicReductionChange (n : ℕ) :
    WeilConjectures.PurCompactSupport.Change (adicIntegralCoefficients d)
      (adicFiniteCoefficients d n) where
  map W := d.projection W n
  square g := d.projection_comm g n

/-- `chi` is the inverse of the scalar/pullback comparison of the reduction of coefficients. -/
private theorem chi_eq_scalarPull_symm {U V : Scheme.{t}} (g : U ⟶ V) (n : ℕ) :
    d.chi g n =
      (WeilConjectures.PurCompactSupport.scalarPull (adicReductionChange d n) g).symm := by
  have h : (d.chi g n).symm =
      WeilConjectures.PurCompactSupport.scalarPull (adicReductionChange d n) g :=
    Iso.ext (WeilConjectures.PurCompactSupport.scalarPull_eq_mate (adicReductionChange d n) g).symm
  exact congrArg Iso.symm h


/-- At every finite level `n`, the finite base change map
`g_n^* Rf_{n*} K_n ⟶ Rf'_{n*} g'_n^* K_n` is the reduction of the integral base change map
`Lg^* Rf_* K ⟶ Rf'_* Lg'^* K`, modulo the projection-formula identifications
`(Rf_* K)_n ≅ Rf_{n*} K_n` and the reduction/pullback comparisons. -/
theorem AdicCoefficientDatum.finiteProjection_comp_finiteExchange (K : d.derived X) (n : ℕ) :
    (d.finitePull g n).map (d.finiteProjection f K n) ≫
        (d.finiteExchange sq n).app ((d.reduction X n).obj K) =
      (d.chi g n).hom.app ((d.push f).obj K) ≫
        (d.reduction Y' n).map ((d.integralExchange sq).app K) ≫
        d.finiteProjection f' ((d.pull g').obj K) n ≫
        (d.finitePush f' n).map (d.delta (g' := g') K n).hom := by
  open WeilConjectures.PurCompactSupport in
  have hsq := scalarPull_ambientRingedPullbackComparison (adicReductionChange d n) sq
    (d.integralRingIso_comp f' g) (d.integralRingIso_comp g' f)
    (fourCornersFinite_comp d f' g n) (fourCornersFinite_comp d g' f n)
    (d.integral_coherent sq) (d.finite_coherent sq n)
  open WeilConjectures.PurCompactSupport in
  have key := mateEquiv_reduction_comp
    (proEtaleRingDerivedAdjunction f (d.completedRing Y) (d.completedRing X) (d.integralRingIso f))
    (proEtaleRingDerivedAdjunction f' (d.completedRing Y') (d.completedRing X')
      (d.integralRingIso f'))
    (proEtaleRingDerivedAdjunction f (d.finiteRing Y n) (d.finiteRing X n) (d.finiteRingIso f n))
    (proEtaleRingDerivedAdjunction f' (d.finiteRing Y' n) (d.finiteRing X' n)
      (d.finiteRingIso f' n))
    (proEtaleAmbientRingedPullbackComparison sq (d.completedRing X) (d.completedRing Y)
      (d.completedRing X') (d.completedRing Y') (d.integralRingIso f) (d.integralRingIso g)
      (d.integralRingIso g') (d.integralRingIso f') (d.integral_coherent sq)).hom
    (proEtaleAmbientRingedPullbackComparison sq (d.finiteRing X n) (d.finiteRing Y n)
      (d.finiteRing X' n) (d.finiteRing Y' n) (d.finiteRingIso f n) (d.finiteRingIso g n)
      (d.finiteRingIso g' n) (d.finiteRingIso f' n) (d.finite_coherent sq n)).hom
    (scalarPull (adicReductionChange d n) f) (scalarPull (adicReductionChange d n) f')
    (scalarPull (adicReductionChange d n) g) (scalarPull (adicReductionChange d n) g')
    (fun L ↦ by transport_exact hsq L) K
  simp only [AdicCoefficientDatum.finiteProjection, AdicCoefficientDatum.delta,
    chi_eq_scalarPull_symm, Iso.symm_hom, Iso.app_hom]
  transport_exact key

/-- For proper `f`, the reduction of the integral base change map at a level whose reduction has
bounded below étale origin is an isomorphism. -/
theorem AdicCoefficientDatum.isIso_reduction_map_integralExchange [IsProper f]
    (K : d.derived X) (n : ℕ)
    (W : FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1)) ((d.reduction X n).obj K)) :
    IsIso ((d.reduction Y' n).map ((d.integralExchange sq).app K)) := by
  have := d.finiteExchange_isIso sq K n W
  have := d.finiteProjection_isIso f K n
  have := d.finiteProjection_isIso f' ((d.pull g').obj K) n
  have h := d.finiteProjection_comp_finiteExchange sq K n
  have : IsIso ((d.chi g n).hom.app ((d.push f).obj K) ≫
      (d.reduction Y' n).map ((d.integralExchange sq).app K) ≫
        d.finiteProjection f' ((d.pull g').obj K) n ≫
        (d.finitePush f' n).map (d.delta (g' := g') K n).hom) := by
    rw [← h]
    infer_instance
  have : IsIso ((d.reduction Y' n).map ((d.integralExchange sq).app K) ≫
      d.finiteProjection f' ((d.pull g').obj K) n ≫
        (d.finitePush f' n).map (d.delta (g' := g') K n).hom) :=
    IsIso.of_isIso_comp_left ((d.chi g n).hom.app ((d.push f).obj K)) _
  exact IsIso.of_isIso_comp_right _
    (d.finiteProjection f' ((d.pull g').obj K) n ≫
      (d.finitePush f' n).map (d.delta (g' := g') K n).hom)

/-- A morphism of complexes over the completed coefficients whose reductions are all invertible
has an invertible reduction tower. -/
theorem AdicCoefficientDatum.isIso_completedReductionTower_map {T : Scheme.{t}}
    {M N : d.derived T} (φ : M ⟶ N) (h : ∀ n : ℕ, IsIso ((d.reduction T n).map φ)) :
    IsIso ((completedReductionTower T d).map φ) := by
  have he (n : ℕ) : IsIso ((reductionTowerDerivedEvaluation T
      (reductionModuleRing T (d.completedRing T)) n).map
        ((completedReductionTower T d).map φ)) := by
    have hn := (completedReductionEvaluation T d n).naturality φ
    have : IsIso ((reductionDerivedRestrict T (d.projection T n)).map
        ((d.reduction T n).map φ)) := by
      have := h n
      infer_instance
    have : IsIso ((completedReductionEvaluation T d n).app M ≫
        (reductionDerivedRestrict T (d.projection T n)).map ((d.reduction T n).map φ)) := by
      infer_instance
    have : IsIso ((reductionTowerDerivedEvaluation T
        (reductionModuleRing T (d.completedRing T)) n).map
          ((completedReductionTower T d).map φ) ≫
        (completedReductionEvaluation T d n).app N) := by
      erw [hn]
      exact this
    exact IsIso.of_isIso_comp_right _ ((completedReductionEvaluation T d n).app N)
  exact DerivedCategory.isIso_of_isIso_evaluation (C := ringedSiteModules.{t + 1}
    (reductionModuleRing T (d.completedRing T))) ((completedReductionTower T d).map φ)
    (fun n ↦ he n.unop)

/-- For proper `f`, the strict tower of finite base change maps is an isomorphism of derived
towers when every reduction of `K` has bounded below étale origin. -/
theorem AdicCoefficientDatum.isIso_towerV' [IsProper f] (K : d.derived X)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) :
    IsIso (d.towerV' sq K) := by
  have : IsIso ((completedReductionTower Y' d).map ((d.integralExchange sq).app K)) :=
    d.isIso_completedReductionTower_map _
      fun n ↦ d.isIso_reduction_map_integralExchange sq K n (W n)
  have : IsIso (d.towerV sq K) := by
    unfold AdicCoefficientDatum.towerV
    infer_instance
  unfold AdicCoefficientDatum.towerV'
  infer_instance

/-- The canonical isomorphism `ĝ^* Rf_* K ≅ Rlim_n g^* Rf_* K_n`. -/
def AdicCoefficientDatum.completedPullPushIso (K : d.derived X) :
    (d.completedPull g).obj ((d.push f).obj K) ≅
      (completedRlim Y' (d.completedRing Y')).obj
        ((d.towerPull g).obj ((d.towerPush f).obj ((completedReductionTower X d).obj K))) :=
  (completedRlim Y' (d.completedRing Y')).mapIso
    (d.towerH (f := f) (f' := f') (g := g) (g' := g') K)

/-- The canonical isomorphism `Rf'_* ĝ'^* K ≅ Rlim_n Rf'_* g'^* K_n`. -/
def AdicCoefficientDatum.pushCompletedPullIso (K : d.derived X) :
    (d.push f').obj ((d.completedPull g').obj K) ≅
      (completedRlim Y' (d.completedRing Y')).obj
        ((d.towerPush f').obj ((d.towerPull g').obj ((completedReductionTower X d).obj K))) :=
  (d.directImageRlimIso f').app ((d.towerPull g').obj ((completedReductionTower X d).obj K))

/-- The completed base change map is the derived limit of the tower of finite base change maps,
transported along `completedPullPushIso` and `pushCompletedPullIso`. -/
lemma AdicCoefficientDatum.completedExchange_eq (K : d.derived X) :
    d.completedExchange sq K =
      (d.completedPullPushIso (f' := f') (g' := g') K).hom ≫
        (completedRlim Y' (d.completedRing Y')).map (d.towerV' sq K) ≫
        (d.pushCompletedPullIso (g' := g') K).inv := by
  simp [AdicCoefficientDatum.completedExchange, AdicCoefficientDatum.completedPullPushIso,
    AdicCoefficientDatum.pushCompletedPullIso]

/-- For proper `f` and complete `K` whose reductions `K_n` have bounded below étale origin, the
derived limit of the finite base change maps `g^* Rf_* K_n ⟶ Rf'_* g'^* K_n` is an isomorphism,
and so is the completed base change map `ĝ^* Rf_* K ⟶ Rf'_* ĝ'^* K`. -/
theorem AdicCoefficientDatum.isIso_completedBaseChangeMap [IsProper f] (K : d.derived X)
    (hK : d.TowerComplete X K)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) :
    IsIso ((completedRlim Y' (d.completedRing Y')).map (d.towerV' sq K)) ∧
      IsIso (d.completedBaseChangeMap sq K hK W) := by
  have := d.isIso_towerV' sq K W
  refine ⟨inferInstance, ?_⟩
  change IsIso (d.completedExchange sq K)
  rw [d.completedExchange_eq sq K]
  infer_instance

/-- **Proper base change for complete complexes**: let `f` be proper and `K` complete with
reductions of bounded below étale origin. Then `Rf_* K` is complete; under the canonical
isomorphisms `ĝ^* Rf_* K ≅ Rlim_n g^* Rf_* K_n` (`completedPullPushIso`) and
`Rf'_* ĝ'^* K ≅ Rlim_n Rf'_* g'^* K_n` (`pushCompletedPullIso`) the completed base change map
`ĝ^* Rf_* K ⟶ Rf'_* ĝ'^* K` is the derived limit of the finite base change maps; and both
are isomorphisms. -/
theorem AdicCoefficientDatum.properBaseChange_complete [IsProper f] (K : d.derived X)
    (hK : d.TowerComplete X K)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) :
    d.TowerComplete Y ((d.push f).obj K) ∧
      d.completedBaseChangeMap sq K hK W =
        (d.completedPullPushIso (f' := f') (g' := g') K).hom ≫
          (completedRlim Y' (d.completedRing Y')).map (d.towerV' sq K) ≫
          (d.pushCompletedPullIso (g' := g') K).inv ∧
      IsIso ((completedRlim Y' (d.completedRing Y')).map (d.towerV' sq K)) ∧
      IsIso (d.completedBaseChangeMap sq K hK W) :=
  ⟨d.push_complete f K hK, d.completedExchange_eq sq K,
    (d.isIso_completedBaseChangeMap sq K hK W).1, (d.isIso_completedBaseChangeMap sq K hK W).2⟩

end AlgebraicGeometry.Scheme
