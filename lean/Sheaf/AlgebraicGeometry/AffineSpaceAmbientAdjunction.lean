/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import WeilConjectures.Compactification.Affine
import Sheaf.AlgebraicGeometry.ProjectiveLineFullAdjunction
import Sheaf.AlgebraicGeometry.AffineTraceRightNormalForm

/-!
# Affine-space ambient adjunction

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/cor-amb-affine-space-adjunction.md
(blueprint: cor-amb-affine-space-adjunction).

Both functors act on the entire ordinary unbounded small-etale derived categories.
The compactification instance comes from the existing relative projective compactification.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

attribute [local instance] Sheaf.monoidalCategory

-- Identify the ordered tower compactification with the chosen compact supports.
private noncomputable def ambientTowerLeftIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) :
    affineTraceLeft A S d ≅
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d) := by
  induction d with
  | zero => exact (unboundedEtaleLowerShriekId A S).symm
  | succ d ih =>
    letI := affineTraceNoetherian S d
    exact Functor.isoWhiskerRight
        (rightDerivedLowerShriekIso A
          (affineTraceLineCompactification (affineTraceTower S d))) _ ≪≫
      Functor.isoWhiskerLeft _ ih ≪≫
      unboundedEtaleLowerShriekCompIso A
        (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
        (affineTraceProjection S d)

@[irreducible]
private noncomputable def ambientTwistedPullbackComp
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    {X T S : Scheme.{u}} (f : X ⟶ T) (p : T ⟶ S) (q : X ⟶ S) (w : f ≫ p = q)
    [(upperStar B f).PreservesFlat]
    (L : DerivedCategory (Sheaf T.smallEtaleTopology B))
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (e : (upperStar B f).leftDerivedFunctor.obj L ≅ M) (n : ℤ) :
    (((upperStar B p).leftDerivedFunctor ⋙ derivedTensorRight B T L) ⋙
        shiftFunctor _ n) ⋙ (upperStar B f).leftDerivedFunctor ≅
      ((upperStar B q).leftDerivedFunctor ⋙ derivedTensorRight B X M) ⋙
        shiftFunctor _ n := by
  letI := commShiftLeftDerivedUpperStar B f
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((upperStar B f).leftDerivedFunctor.commShiftIso n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _
          (derivedTensorRightCompLeftDerivedUpperStarIso B f L ≪≫
            Functor.isoWhiskerLeft _ ((derivedTensorRightFunctor B X).mapIso e)) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (leftDerivedUpperStarComp B f p q w.symm).symm _) _

@[irreducible]
private noncomputable def ambientSinglePullback
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    {X T : Scheme.{u}} (f : X ⟶ T)
    (F : Sheaf T.smallEtaleTopology B) (G : Sheaf X.smallEtaleTopology B)
    (e : (upperStar B f).obj F ≅ G) :
    (upperStar B f).leftDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj F) ≅
      (DerivedCategory.singleFunctor _ 0).obj G :=
  (singleFunctorCompLeftDerivedUpperStarIso B f).app F ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso e

@[irreducible]
private noncomputable def ambientRightTransport
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    {X T S : Scheme.{u}} (f : X ⟶ T) (p : T ⟶ S) (q : X ⟶ S) (w : f ≫ p = q)
    [(upperStar B f).PreservesFlat]
    (R : DerivedCategory (Sheaf S.smallEtaleTopology B) ⥤
      DerivedCategory (Sheaf T.smallEtaleTopology B))
    (L : DerivedCategory (Sheaf T.smallEtaleTopology B))
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (e : (upperStar B f).leftDerivedFunctor.obj L ≅ M) (n : ℤ)
    (r : R ≅ (upperStar B p).leftDerivedFunctor ⋙ derivedTensorRight B T L ⋙
      shiftFunctor _ n) :
    R ⋙ (upperStar B f).leftDerivedFunctor ≅
      ((upperStar B q).mapDerivedCategory ⋙ derivedTensorRight B X M) ⋙
        shiftFunctor _ n := by
  -- Keep the associativity comparison explicit to avoid unfolding derived tensor.
  exact Functor.isoWhiskerRight (r ≪≫ (Functor.associator _ _ _).symm) _ ≪≫
    ambientTwistedPullbackComp B f p q w L M e n ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory B q)
        (derivedTensorRight B X M)) _

/-- Ordinary compact supports for affine `d`-space are left adjoint to exact inverse image,
followed by the finite torsion Tate twist `(d)` and cohomological shift `[2d]`.
Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/cor-amb-affine-space-adjunction.md
(blueprint: cor-amb-affine-space-adjunction).

Proof:
1. Factor affine `r`-space over `S` into the successive affine-line projections, using
   the polynomial-coordinate identifications of `def-sbc-affine-space`. They are separated
   and finite type (`def-weil-finite-type-morphism`, `def-weil-proper-morphism`), so every
   intermediate scheme is Noetherian (`lem-weil-pbc-finite-type-over-noetherian`). Units
   remain units under pullback. The standard affine chart and projective-space properness
   (`lemma-nagata-relative-affine-space-open-immersion` and
   `lemma-nagata-projective-space-base-change-proper`) give compactifications
   (`def-asd-compactifiable`) with Noetherian ambient schemes.
2. The affine-line chart `j` is etale (`lem-weil-pbc-open-immersion-etale`), separated, and
   finite type: on either projective chart its inverse image is the whole chart or a
   principal open. Thus `lem-amb-etale-adjoint-locality` gives `Dj_!` left adjoint to `j^*`
   on the entire unbounded categories. Its extension is ordinary open extension by zero
   by `def-weil-pbc-etale-sum-extension`.
3. For the projective-line projection `q`, compact supports are `Rq_* Dj_!`
   (`def-amb-etale-compact-support`, `lem-amb-unbounded-compact-support-comparisons`).
   Apply `thm-amb-p1-adjunction` and the preceding open adjunction to obtain natural Hom
   bijections with target `j^*(q^*K(1)[2])`. Move the twist through inverse image by
   `lem-asd-etale-finite-twist-pullback`; inverse-image composition and exactness
   (`lem-weil-pbc-inverse-image-composition-module-linear`,
   `prop-weil-pbc-inverse-image-modules-exact`) identify this with `p_1^*K(1)[2]`.
   These are the composite adjunction bijections of `def-weil-pbc-composite-adjunction`.
4. Each nonnegative Tate sheaf is flat (`lem-asd-finite-etale-twist-line`), so tensoring
   a K-flat resolution with it computes ordinary termwise tensor as well as derived
   tensor (`def-kun-derived-tensor`). Regroup the degree-zero Tate factors using
   `def-asd-finite-etale-tate-twist`, with the scalar unit when the exponent is zero.
   These chain isomorphisms are natural. Even shifts have sign one and add, giving
   `(K(r)[2r])(1)[2]` naturally isomorphic to `K(r+1)[2r+2]`, without boundedness.
5. In dimension zero the affine projection is canonically the identity. Compactification
   independence identifies its compact supports with the identity, and the scalar-unit
   and zero-shift identifications identify its right adjoint with the identity. Use the
   identity adjunction (`def-weil-pbc-composite-adjunction`).
6. Induct on `d`. Compose the preceding adjunction with the affine-line adjunction over
   affine `d`-space, using `lem-amb-unbounded-compact-support-comparisons` to identify
   the composite compact supports. Exact inverse-image composition and pullback of
   twists identify the reversed composite right adjoint with `p_(d+1)^*(-)(d+1)[2d+2]`,
   by step 4. Every comparison is natural in both unrestricted derived arguments. -/
theorem nonempty_affineSpaceAmbientAdjunction (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    Nonempty
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
          (AffineSpace (ULift.{u} (Fin d)) S ↘ S) ⊣
        ((upperStar (ModuleCat.{u + 1} A)
            (AffineSpace (ULift.{u} (Fin d)) S ↘ S)).mapDerivedCategory ⋙
          derivedTensorRight (ModuleCat.{u + 1} A) (AffineSpace (ULift.{u} (Fin d)) S)
            ((DerivedCategory.singleFunctor _ 0).obj
              (Scheme.finiteEtaleTateTwist (AffineSpace (ULift.{u} (Fin d)) S) N A hA d))) ⋙
          shiftFunctor _ (2 * (d : ℤ))) := by
  classical
  let T := affineTraceTower S d
  let X := AffineSpace (ULift.{u} (Fin d)) S
  let e : T ≅ X := affineTraceAffineSpaceIso S d
  let f : X ⟶ T := e.inv
  let : IsIso f := inferInstanceAs (IsIso e.inv)
  let p := affineTraceProjection S d
  let q := AffineSpace (ULift.{u} (Fin d)) S ↘ S
  let : IsNoetherian T := affineTraceNoetherian S d
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  have he : e.hom ≫ q = p := AffineSpace.homOfVector_over _ _
  have hp : f ≫ p = q := by
    rw [← he]
    exact e.inv_hom_id_assoc q
  let a (r : ℕ) :
      affineTraceLineLeft A (affineTraceTower S r) ⊣
        affineTraceLineRight A N hA (affineTraceTower S r) := by
    letI := affineTraceNoetherian S r
    let adj := (exists_projectiveLineFullAdjunction N hN A hA
      (affineTraceTower S r) (affineTraceInvertible N S hS r)).choose
    exact (affineTraceOpenAdjunction A (affineTraceTower S r)).comp adj
  let towerAdj := (affineTraceAdjunctionTower a d).ofNatIsoLeft
    (ambientTowerLeftIso A S d)
  obtain ⟨normalization⟩ := nonempty_etaleCompactSupportNormalization A
  let adjF₀ := derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) f inferInstance
  let adjF₁ := adjF₀.ofNatIsoLeft
    (normalization.comparison f (HasCompactification.compactification f)).symm
  let adjF := adjF₁.ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm
  let adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) q ⊣
      affineTraceRight A N hA S d ⋙ ordinaryFinitePullback A f :=
    (adjF.comp towerAdj).ofNatIsoLeft
      (unboundedEtaleLowerShriekCompIso A f p ≪≫ unboundedEtaleLowerShriekCongr A hp)
  let t := Scheme.finiteEtaleTwistPullbackData A N hN hA
  have hT : IsUnit (N : Γ(T, ⊤)) := affineTraceInvertible N S hS d
  have hX : IsUnit (N : Γ(X, ⊤)) := affineTracePullbackInvertible N f hT
  let rightIso := (affineTraceRight_normalForm A N hN hA S hS d).1.some
  let twistIso := ambientSinglePullback (ModuleCat.{u + 1} A) f
    (Scheme.finiteEtaleTateSheaf A N T hA (d : ℤ))
    (Scheme.finiteEtaleTateTwist X N A hA d) (t.c f hT hX (d : ℤ))
  let finalRight := ambientRightTransport (ModuleCat.{u + 1} A) f p q hp
    (affineTraceRight A N hA S d)
    ((DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateSheaf A N T hA (d : ℤ)))
    ((DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateTwist X N A hA d))
    twistIso (2 * (d : ℤ)) rightIso
  exact ⟨adj.ofNatIsoRight finalRight⟩

end AlgebraicGeometry.Etale
