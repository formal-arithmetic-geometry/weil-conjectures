/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleCtfChartDomain
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientCompatibility
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
import WeilConjectures.AlgebraicGeometry.Affine.AffineLineCanonicalScalarCounit
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate
import WeilConjectures.AlgebraicGeometry.P1.P1CounitScalar
import WeilConjectures.AlgebraicGeometry.Affine.AffineCompactificationComparisonNormalization
import WeilConjectures.AlgebraicGeometry.Ordered.OrderedAffineTraceNormalForm
import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceTopTrace
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalConservativity
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization

/-! # The ordered affine counit under coefficient extension

Source: main-20261015, reduction-exceptional proof, Charts
(blueprint: lem-sp-affine-counit-scalar).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

open MonoidalCategory
open scoped CategoryTheory.Functor

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension derivedTensor upperStar lowerStar

attribute [local instance] cachedEtaleGroth cachedEtaleSheafify
  cachedEtaleMonoidalPreadditive cachedEtaleCoproducts cachedEtaleColimits
  cachedEtaleFlatResolution cachedEtaleInjectiveResolution cachedEtaleExactColimits
  cachedEtaleTensor4 cachedEtaleTensor12 cachedEtaleTensor23
  cachedEtaleTensorColimits cachedEtaleTensorFlipColimits

private theorem right_exchange_rec_eq {C C' : ℕ → Type*}
    [∀ d, Category (C d)] [∀ d, Category (C' d)]
    (R : ∀ d, C d ⥤ C (d + 1)) (R' : ∀ d, C' d ⥤ C' (d + 1))
    (B : ∀ d, C d ⥤ C' d)
    (r : ∀ d K, (B (d + 1)).obj ((R d).obj K) ≅ (R' d).obj ((B d).obj K))
    (d : ℕ) (K : C 0) :
    (Nat.rec (motive := fun n ↦ ∀ K : C 0,
      (B n).obj ((affineTraceRightTower R n).obj K) ≅
        (affineTraceRightTower R' n).obj ((B 0).obj K))
      (fun _ ↦ Iso.refl _) (fun n ih K ↦ r n _ ≪≫ (R' n).mapIso (ih K)) d K) =
      affineTraceRightExchangeTower R R' B r d K := by
  induction d with
  | zero => rfl
  | succ d ih =>
    dsimp only [affineTraceRightExchangeTower]
    rw [ih]

private theorem tower_counit_scalar {C C' : ℕ → Type*}
    [∀ d, Category (C d)] [∀ d, Category (C' d)]
    {L : ∀ d, C (d + 1) ⥤ C d} {L' : ∀ d, C' (d + 1) ⥤ C' d}
    {R : ∀ d, C d ⥤ C (d + 1)} {R' : ∀ d, C' d ⥤ C' (d + 1)}
    (a : ∀ d, L d ⊣ R d) (a' : ∀ d, L' d ⊣ R' d)
    (B : ∀ d, C d ⥤ C' d) (e : ∀ d, L d ⋙ B d ⟶ B (d + 1) ⋙ L' d)
    (r : ∀ d K, (B (d + 1)).obj ((R d).obj K) ≅ (R' d).obj ((B d).obj K))
    (K : C 0)
    (h : ∀ d, (e d).app ((R d).obj ((affineTraceRightTower R d).obj K)) ≫
      (L' d).map (r d ((affineTraceRightTower R d).obj K)).hom ≫
        (a' d).counit.app ((B d).obj ((affineTraceRightTower R d).obj K)) =
        (B d).map ((a d).counit.app ((affineTraceRightTower R d).obj K))) (d : ℕ) :
    (affineTraceExchangeTower L L' B e d).app ((affineTraceRightTower R d).obj K) ≫
      (affineTraceLeftTower L' d).map (affineTraceRightExchangeTower R R' B r d K).hom ≫
      (affineTraceAdjunctionTower a' d).counit.app ((B 0).obj K) =
    (B 0).map ((affineTraceAdjunctionTower a d).counit.app K) := by
  induction d with
  | zero =>
    rw [affineTraceExchangeTower_zero]
    change 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = (B 0).map (𝟙 K)
    simp
  | succ d ih =>
    let M := (affineTraceRightTower R d).obj K
    let q := affineTraceRightExchangeTower R R' B r d K
    have hn := (a' d).counit.naturality q.hom
    simp only [Functor.comp_map, Functor.id_map] at hn
    have hi : (e d).app ((R d).obj M) ≫
        (L' d).map ((r d M).hom ≫ (R' d).map q.hom) ≫
        (a' d).counit.app ((affineTraceRightTower R' d).obj ((B 0).obj K)) =
        (B d).map ((a d).counit.app M) ≫ q.hom := by
      rw [Functor.map_comp, Category.assoc, hn]
      simpa only [Category.assoc] using
        congrArg (fun z ↦ z ≫ q.hom) (h d)
    rw [affineTraceExchangeTower_succ, affineTraceAdjunctionTower_counit_succ,
      affineTraceAdjunctionTower_counit_succ]
    change (_ ≫ (affineTraceLeftTower L' d).map ((e d).app ((R d).obj M))) ≫
      (affineTraceLeftTower L' d).map
        ((L' d).map ((r d M).hom ≫ (R' d).map q.hom)) ≫
      (affineTraceLeftTower L' d).map
        ((a' d).counit.app ((affineTraceRightTower R' d).obj ((B 0).obj K))) ≫
      (affineTraceAdjunctionTower a' d).counit.app ((B 0).obj K) = _
    have hi' := congrArg (fun z ↦ (affineTraceLeftTower L' d).map z) hi
    simp only [Functor.map_comp, Category.assoc] at hi'
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hi']
    have he := (affineTraceExchangeTower L L' B e d).naturality ((a d).counit.app M)
    simp only [Functor.comp_map] at he
    change _ ≫ (affineTraceExchangeTower L L' B e d).app M =
      (affineTraceExchangeTower L L' B e d).app
        ((L d).obj ((affineTraceRightTower R (d + 1)).obj K)) ≫ _ at he
    rw [← Category.assoc, ← Category.assoc, ← he]
    simp only [Category.assoc]
    rw [ih, ← Functor.map_comp]

private theorem affine_right_domain (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (A : Type (u + 1)) [CommRing A] [Finite A] (n : ℕ)
    (hA : ((ell ^ n : ℕ) : A) = 0) (S : Scheme.{u})
    [S.Over (Spec (.of k))] [LocallyOfFiniteType (S ↘ Spec (.of k))]
    [QuasiCompact (S ↘ Spec (.of k))] [IsSeparated (S ↘ Spec (.of k))]
    (hS : IsUnit ((ell ^ n : ℕ) : Γ(S, ⊤))) (d : ℕ)
    (K : DerivedCategoryModule A S)
    (hK : ProEtale.AdjunctionTransfer.etaleProperty A S K) :
    ProEtale.AdjunctionTransfer.etaleProperty A (affineTraceTower S d)
      ((affineTraceRight A (ell ^ n) hA S d).obj K) := by
  cases d with
  | zero => exact hK
  | succ d =>
    let : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian
      (S ↘ Spec (.of k))
    let : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (S ↘ Spec (.of k))
    let : IsNoetherian S := ⟨⟩
    let X := affineTraceTower S (d + 1)
    let : X.Over (Spec (.of k)) := ⟨affineTraceProjection S (d + 1) ≫ (S ↘ Spec (.of k))⟩
    let : (affineTraceProjection S (d + 1)).IsOver (Spec (.of k)) := ⟨rfl⟩
    have := affineTraceProjection_locallyOfFiniteType S (d + 1)
    have := affineTraceProjection_quasiCompact S (d + 1)
    have := affineTraceProjection_isSeparated S (d + 1)
    have : LocallyOfFiniteType (X ↘ Spec (.of k)) := by
      change LocallyOfFiniteType (affineTraceProjection S (d + 1) ≫ (S ↘ Spec (.of k)))
      infer_instance
    have : QuasiCompact (X ↘ Spec (.of k)) := by
      change QuasiCompact (affineTraceProjection S (d + 1) ≫ (S ↘ Spec (.of k)))
      infer_instance
    have : IsSeparated (X ↘ Spec (.of k)) := by
      change IsSeparated (affineTraceProjection S (d + 1) ≫ (S ↘ Spec (.of k)))
      infer_instance
    have h := (ProEtale.AdjunctionTransfer.etaleCtfChartDomain ell k hk
      (Fact.out : ringChar k ≠ ell) A n hA (𝟙 S) (Compactification.ofIsProper (𝟙 S))
      (affineTraceProjection S (d + 1))).2.2.2.1
        (d + 1) (2 * ((d + 1 : ℕ) : ℤ)) K hK
    let e := (orderedAffineRightIso A (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hA S hS (d + 1)).app K
    let L := (_root_.DerivedCategory.singleFunctor
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj
      (Scheme.finiteEtaleTateTwist X (ell ^ n) A hA (d + 1))
    let e' : (orderedAffineRight A (ell ^ n) hA S (d + 1)).obj K ≅
        (ProEtale.AdjunctionTransfer.etaleChartOperation A (ell ^ n) hA
          (affineTraceProjection S (d + 1)) (d + 1)
          (2 * ((d + 1 : ℕ) : ℤ))).obj K :=
      (shiftFunctor _ (2 * ((d + 1 : ℕ) : ℤ))).mapIso
        (((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).app
          ((ordinaryFinitePullback A (affineTraceProjection S (d + 1))).obj K)).app L ≪≫
          ((derivedTensor (ModuleCat.{u + 1} A) X).obj L).mapIso
            ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
              (affineTraceProjection S (d + 1))).app K))
    let v := e ≪≫ e'
    refine ⟨?_, (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso v.symm h.2⟩
    obtain ⟨hc, a, b, hab, hz⟩ := h.1
    refine ⟨fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      ?_, a, b, hab, fun q hq ↦ (hz q hq).of_iso
        ((_root_.DerivedCategory.homologyFunctor _ q).mapIso v)⟩
    have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc q)
    exact Scheme.IsConstructibleSheaf.of_iso
      ((_root_.DerivedCategory.homologyFunctor _ q).mapIso v).symm

private theorem coefficient_map_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategoryModule A X) :
    ProEtale.CoefficientCompatibility.etaleCoefficientMap φ c M =
      (compactScalarMap φ c).app M := by
  have hi : ((ExceptionalCoefficients.openIso φ c.i).app M).inv =
      (properOpenCoefficientOpenIso φ c.i M).inv :=
    compactScalarOpen_normalization φ c.i M
  have he := Iso.ext_inv hi
  unfold ProEtale.CoefficientCompatibility.etaleCoefficientMap compactScalarMap
    ExceptionalCoefficients.compactSupportMap
  rw [← he]
  rfl

private theorem ordered_coefficient_map_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (S : Scheme.{u}) (d : ℕ) (M : DerivedCategoryModule A (affineTraceTower S d)) :
    orderedAffineCoefficientMap φ S d M =
      (affineTraceExchangeTower
        (fun r ↦ affineTraceLineLeft A (affineTraceTower S r))
        (fun r ↦ affineTraceLineLeft B (affineTraceTower S r))
        (fun r ↦ scalarExtension φ (affineTraceTower S r))
        (fun r ↦ compactScalarMap φ (affineTraceLineCompactification
          (affineTraceTower S r))) d).app M := by
  induction d with
  | zero =>
    rw [orderedAffineCoefficientMap, affineTraceExchangeTower_zero]
    rfl
  | succ d ih =>
    rw [orderedAffineCoefficientMap, affineTraceExchangeTower_succ, ← ih,
      coefficient_map_eq]

private theorem affine_tower_scalar
    (ell p n : ℕ) [Fact ell.Prime] (hp : 0 < p) (hEll : p ≠ ell)
    (k : Type u) [Field k] [CharP k p] (hk : Finite k ∨ IsAlgClosed k)
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (hA : ((ell ^ n : ℕ) : A) = 0) (hB : ((ell ^ n : ℕ) : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))] (hS : IsUnit ((ell ^ n : ℕ) : Γ(S, ⊤)))
    (d : ℕ) (K : DerivedCategoryModule A S)
    (hK : ProEtale.AdjunctionTransfer.etaleProperty A S K) :
    orderedAffineCoefficientMap φ S d ((affineTraceRight A (ell ^ n) hA S d).obj K) ≫
      (affineTraceLeft B S d).map
        (ProEtale.reductionEtaleAffineScalarIso φ S (ell ^ n) hA hB hS d K).hom ≫
      (affineTraceAdjunction B (ell ^ n) hB
        (projectiveLineTraceTransport _ (pow_pos (Fact.out : ell.Prime).pos n) B hB)
        (projectiveLineTraceDatum _ (pow_pos (Fact.out : ell.Prime).pos n) B hB)
        S hS d).counit.app ((scalarExtension φ S).obj K) =
    (scalarExtension φ S).map
      ((affineTraceAdjunction A (ell ^ n) hA
        (projectiveLineTraceTransport _ (pow_pos (Fact.out : ell.Prime).pos n) A hA)
        (projectiveLineTraceDatum _ (pow_pos (Fact.out : ell.Prime).pos n) A hA)
        S hS d).counit.app K) := by
  rw [ordered_coefficient_map_eq]
  have hr : ProEtale.reductionEtaleAffineScalarIso φ S (ell ^ n) hA hB hS d K =
      affineTraceRightExchangeTower
        (fun r ↦ affineTraceLineRight A (ell ^ n) hA (affineTraceTower S r))
        (fun r ↦ affineTraceLineRight B (ell ^ n) hB (affineTraceTower S r))
        (fun r ↦ scalarExtension φ (affineTraceTower S r))
        (fun r ↦ ProEtale.reductionEtaleLineScalarIso φ (affineTraceTower S r)
          (ell ^ n) hA hB (affineTraceInvertible _ S hS r)) d K := by
    unfold ProEtale.reductionEtaleAffineScalarIso
    exact right_exchange_rec_eq
      (C := fun r ↦ DerivedCategoryModule A (affineTraceTower S r))
      (C' := fun r ↦ DerivedCategoryModule B (affineTraceTower S r))
      (fun r ↦ affineTraceLineRight A (ell ^ n) hA (affineTraceTower S r))
      (fun r ↦ affineTraceLineRight B (ell ^ n) hB (affineTraceTower S r))
      (fun r ↦ scalarExtension φ (affineTraceTower S r))
      (fun r ↦ ProEtale.reductionEtaleLineScalarIso φ (affineTraceTower S r)
        (ell ^ n) hA hB (affineTraceInvertible _ S hS r)) d K
  rw [hr]
  unfold affineTraceAdjunction
  apply tower_counit_scalar
  intro r
  let T := affineTraceTower S r
  let : IsNoetherian T := affineTraceNoetherian S r
  let : T.Over (Spec (.of k)) := ⟨affineTraceProjection S r ≫ (S ↘ Spec (.of k))⟩
  let : (affineTraceProjection S r).IsOver (Spec (.of k)) := ⟨rfl⟩
  let : LocallyOfFiniteType (T ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (affineTraceProjection S r ≫ (S ↘ Spec (.of k)))
    infer_instance
  let : QuasiCompact (T ↘ Spec (.of k)) := by
    change QuasiCompact (affineTraceProjection S r ≫ (S ↘ Spec (.of k)))
    infer_instance
  let : IsSeparated (T ↘ Spec (.of k)) := by
    change IsSeparated (affineTraceProjection S r ≫ (S ↘ Spec (.of k)))
    infer_instance
  rw [← coefficient_map_eq]
  exact affineLineCanonicalScalarCounit ell p n hp hEll k φ hA hB T
    (affineTraceInvertible _ S hS r) _ _ _ _ _
    (affine_right_domain ell k hk A n hA S hS r K hK)

private theorem compactification_counit_transport
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L Lc : C ⥤ D} {R : D ⥤ C} {L' Lc' : E ⥤ F} {R' : F ⥤ E}
    (a : L ⊣ R) (a' : L' ⊣ R') (U : C ⥤ E) (V : D ⥤ F)
    (e : L ≅ Lc) (e' : L' ≅ Lc') (K : D)
    (b : V.obj (L.obj (R.obj K)) ⟶ L'.obj (U.obj (R.obj K)))
    (bc : V.obj (Lc.obj (R.obj K)) ⟶ Lc'.obj (U.obj (R.obj K)))
    (r : U.obj (R.obj K) ≅ R'.obj (V.obj K))
    (sq : V.map (e.hom.app (R.obj K)) ≫ bc = b ≫ e'.hom.app (U.obj (R.obj K)))
    (hc : b ≫ L'.map r.hom ≫ a'.counit.app (V.obj K) = V.map (a.counit.app K)) :
    bc ≫ Lc'.map r.hom ≫ e'.inv.app (R'.obj (V.obj K)) ≫
      a'.counit.app (V.obj K) = V.map (e.inv.app (R.obj K) ≫ a.counit.app K) := by
  apply (cancel_epi (V.map (e.hom.app (R.obj K)))).mp
  simp only [Functor.map_comp]
  rw [← Category.assoc, sq]
  have hn := e'.inv.naturality r.hom
  simp only [Category.assoc]
  rw [reassoc_of% hn]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  simpa only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id,
    Category.id_comp] using hc

/-- Transport the specified ordered affine counit to the fixed compactification.
Source: main-20261015, reduction-exceptional proof, Charts
(blueprint: lem-sp-affine-counit-scalar). -/
def affineScalarCompactificationCounit (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (c : Compactification (affineTraceProjection S d)) (K : DerivedCategoryModule A S) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
      ((affineTraceRight A N hA S d).obj K) ⟶ K :=
  (ProEtale.reductionEtaleAffineLeftIso A S d c).inv.app _ ≫
    (affineTraceAdjunction A N hA (projectiveLineTraceTransport N hN A hA)
      (projectiveLineTraceDatum N hN A hA) S hS d).counit.app K

/-- The actual affine counit commutes with the specified compactification scalar map.
Source: main-20261015, reduction-exceptional proof, Charts
(blueprint: lem-sp-affine-counit-scalar).
Proof: (1) Transport the supplied chart-domain theorem through the ordered right
normal form to show that every coordinate input is ctf. (2) Apply
lem-sp-affine-line-canonical-scalar-counit at each coordinate. Induction on the
literal recursive adjunction tower, using counit naturality, gives the ordered
scalar-counit equation. A separate induction identifies the recursive right
comparison with reductionEtaleAffineScalarIso. (3) Use
lem-sp-ordered-compactification-scalar-square and
lem-sp-affine-compactification-normalization to obtain the coefficient square for
the actual ambient left comparisons. Its inputs are bounded below by (1) and by
the scalar-extension clause of the compactification square. (4) Precompose with
scalar extension of the A-left comparison. Substitute the square of (3) and use
naturality of the inverse B-left comparison. Cancel its isomorphism and apply the
tower equation from (2). This includes the identity tower, zero input and empty
base; no coefficient flatness or finite projective dimension is assumed. -/
theorem affine_counit_scalar (ell p : ℕ) [Fact ell.Prime]
    (_hp : 0 < p) (_hEll : p ≠ ell) (k : Type u) [Field k] [CharP k p]
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (n : ℕ) (hA : ((ell ^ n : ℕ) : A) = 0)
    (hB : ((ell ^ n : ℕ) : B) = 0)
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))] (d : ℕ)
    (c : Compactification (affineTraceProjection S d))
    (K : DerivedCategoryModule A S) (_hK : ProEtale.AdjunctionTransfer.etaleProperty A S K) :
    ∃ (hNoeth : IsNoetherian S) (hS : IsUnit ((ell ^ n : ℕ) : Γ(S, ⊤))),
      ProEtale.CoefficientCompatibility.etaleCoefficientMap φ c
          ((affineTraceRight A (ell ^ n) hA S d).obj K) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
          (ProEtale.reductionEtaleAffineScalarIso φ S (ell ^ n) hA hB hS d K).hom ≫
        @affineScalarCompactificationCounit.{u} (ell ^ n)
          (pow_pos (Fact.out : ell.Prime).pos n) B _ _ hB S hNoeth hS d c
          ((scalarExtension φ S).obj K) =
      (scalarExtension φ S).map (@affineScalarCompactificationCounit.{u} (ell ^ n)
        (pow_pos (Fact.out : ell.Prime).pos n) A _ _ hA S hNoeth hS d c K) := by
  have hchar : ringChar k = p := ringChar.eq k p
  let : Fact (ringChar k).Prime := ⟨by
    rw [hchar]
    exact (CharP.char_is_prime_or_zero k p).resolve_right (Nat.ne_of_gt _hp)⟩
  let : Fact (ringChar k ≠ ell) := ⟨by simpa only [hchar] using _hEll⟩
  let : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian
    (S ↘ Spec (.of k))
  let : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (S ↘ Spec (.of k))
  let : IsNoetherian S := ⟨⟩
  obtain ⟨hS, _, _⟩ := p1_counit_scalar ell p n _hp _hEll k φ hA hB S
  refine ⟨inferInstance, hS, ?_⟩
  let M := (affineTraceRight A (ell ^ n) hA S d).obj K
  have hM := affine_right_domain ell k A n hA S hS d K _hK
  let P := (ProEtale.AdjunctionTransfer.etaleToPlus A (affineTraceTower S d)).obj ⟨M, hM⟩
  obtain ⟨hMB, hs, _⟩ := orderedCompactification_scalar_square ell k φ n hA hB S d c P hM
  have hs' : (scalarExtension φ S).map
        ((ProEtale.reductionEtaleAffineLeftIso A S d c).hom.app M) ≫
      ProEtale.CoefficientCompatibility.etaleCoefficientMap φ c M =
    orderedAffineCoefficientMap φ S d M ≫
      (ProEtale.reductionEtaleAffineLeftIso B S d c).hom.app
        ((scalarExtension φ (affineTraceTower S d)).obj M) := by
    change (scalarExtension φ S).map
        ((ProEtale.reductionEtaleAffineLeftIso A S d c).hom.app P.obj) ≫
      ProEtale.CoefficientCompatibility.etaleCoefficientMap φ c P.obj =
      orderedAffineCoefficientMap φ S d P.obj ≫
        (ProEtale.reductionEtaleAffineLeftIso B S d c).hom.app
          ((scalarExtension φ (affineTraceTower S d)).obj P.obj)
    rw [affineCompactificationComparison_normalization A k S d c P,
      affineCompactificationComparison_normalization B k S d c
        ⟨(scalarExtension φ (affineTraceTower S d)).obj P.obj, hMB⟩]
    exact hs
  unfold affineScalarCompactificationCounit
  exact compactification_counit_transport _ _ _ _ _ _ K _ _ _ hs'
    (affine_tower_scalar ell p n _hp _hEll k φ hA hB S hS d K _hK)

end AlgebraicGeometry.Etale
