/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.AlgebraicGeometry.EtaleProEtaleExceptionalTransport
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedOpenCounitSiteTransport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift
public import WeilConjectures.Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
public import WeilConjectures.SixFunctors.Etale.Derived.Supports
public import Mathlib.Algebra.FiveLemma
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleExceptionalObjectComparison
public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenCoverShriekTriangle
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
public import WeilConjectures.AlgebraicGeometry.Affine.AffineDualizingCoefficient
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Stalk
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenCoverShriekTriangle
public import WeilConjectures.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization.OrdinaryAffineCounitTensorMaps
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryAffineCounitTensorNormalization
import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceTopTrace

/-! # Local computation of the finite Brown adjoint

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-coefficients-constructible/
sec-n-brown/sk-thm-existence/sk-lem-sp-finite-existence/_section.md, Lemma
sk-lem-sp-finite-existence, entire statement (blueprint: sk-lem-sp-finite-existence).

The helpers give coordinates for the actual counits, not extra choices of maps.
The affine coordinate tower is canonically affine d-space by `affineTraceAffineSpaceIso`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteBrown

end AlgebraicGeometry.ProEtale.FiniteBrown

namespace AlgebraicGeometry.ProEtale.FiniteBrown

end AlgebraicGeometry.ProEtale.FiniteBrown

namespace AlgebraicGeometry.ProEtale.FiniteBrown

section Witnesses
variable (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
  {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))]
  [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  [IsNoetherian X] [IsNoetherian Y]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [Smooth f] (c : Compactification f)

/-- The chart and coefficient-transfer fields from proof steps 2--3.
Source: det-sp-finite-existence-chart (G10 of sk-lem-geo-affine-local),
sk-prop-sp-et-proet, and the chart-normalization declarations.
(blueprint: sk-lem-sp-finite-existence). -/
structure FiniteBrownChartData
    (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [Smooth f] (c : Compactification f)
    (B : BrownData ell n hn k f c) (d : ℕ) where
  /-- Left compact supports preserve finite ctf on every open used in descent. -/
  support_preserves : ∀ (W : X.Opens) (M : D (Coeff ell n) W.toScheme),
    ctf (Coeff ell n) W.toScheme M →
      ctf (Coeff ell n) Y ((support (Coeff ell n) (c.precomp W.ι)).obj M)
  /-- Finite site comparison on the input category. -/
  comparison_preserves : ∀ M : (ectf (Coeff ell n) Y).FullSubcategory,
    ctf (Coeff ell n) Y ((nu (Coeff ell n) Y).obj M.obj)
  /-- The input comparison is an equivalence, so chart naturality covers every input. -/
  comparison_equivalence :
    (finiteComparison (Coeff ell n) Y comparison_preserves).IsEquivalence
  /-- The same ordered finite-torsion twist transport and normalized P1 data as in the
  affine integration construction; no fresh projection counit is chosen. -/
  twistTransport : Etale.OrdinaryFiniteTwistTransport (Coeff ell n) (ell ^ n)
    (CharP.cast_eq_zero (Coeff ell n) (ell ^ n))
  /-- The normalized line adjunctions that define integration. -/
  lineData : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit ((ell ^ n : ℕ) : Γ(T, ⊤))),
    Etale.OrdinaryFiniteP1Datum (Coeff ell n) (ell ^ n)
      (CharP.cast_eq_zero (Coeff ell n) (ell ^ n)) twistTransport T hT
  /-- The coefficient exponent is invertible on the base; this follows from p ≠ ell. -/
  exponent_unit : IsUnit ((ell ^ n : ℕ) : Γ(Y, ⊤))
  /-- The integration morphism at the unit is an isomorphism. -/
  integration_isIso : IsIso
    (Etale.affineTraceCounit (Coeff ell n) (ell ^ n) (CharP.cast_eq_zero (Coeff ell n) (ell ^ n))
      twistTransport lineData Y exponent_unit d)
  /-- Canonical inverse projection formula followed by tensor of integration. Its
  forward arrow is fixed to compactSupportProjectionMap, excluding arbitrary source maps. -/
  projection_normalization : ∀ (hN : 0 < ell ^ n)
      (K : (ectf (Coeff ell n) Y).FullSubcategory),
    ∃ Q : (((Etale.derivedTensor (ModuleCat.{u + 1} (Coeff ell n)) Y).obj K.obj).obj
        ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (Coeff ell n))
          (affineTraceProjection Y d)).obj
          (Etale.SectionLocalDualizingComparisons.tateObject (Coeff ell n) (ell ^ n)
            (CharP.cast_eq_zero (Coeff ell n) (ell ^ n)) (affineTraceTower Y d) d))) ≅
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (Coeff ell n))
        (affineTraceProjection Y d)).obj
        (((Etale.derivedTensor (ModuleCat.{u + 1} (Coeff ell n))
          (affineTraceTower Y d)).obj
          ((Etale.upperStar (ModuleCat.{u + 1} (Coeff ell n))
            (affineTraceProjection Y d)).mapDerivedCategory.obj K.obj)).obj
          (Etale.SectionLocalDualizingComparisons.tateObject (Coeff ell n) (ell ^ n)
            (CharP.cast_eq_zero (Coeff ell n) (ell ^ n)) (affineTraceTower Y d) d)),
      Q.hom = Etale.compactSupportProjectionMap (Coeff ell n) (affineTraceProjection Y d)
        (Etale.SectionLocalDualizingComparisons.tateObject (Coeff ell n) (ell ^ n)
          (CharP.cast_eq_zero (Coeff ell n) (ell ^ n)) (affineTraceTower Y d) d) K.obj ∧
      Etale.OrdinaryAffineCounitTensorNormalization.counit (Coeff ell n) (ell ^ n) hN
        (CharP.cast_eq_zero (Coeff ell n) (ell ^ n)) twistTransport lineData Y exponent_unit d
          K.obj = Q.inv ≫
        ((Etale.derivedTensor (ModuleCat.{u + 1} (Coeff ell n)) Y).obj K.obj).map
          (Etale.OrdinaryAffineCounitTensorNormalization.trace (Coeff ell n) (ell ^ n) hN
            (CharP.cast_eq_zero (Coeff ell n) (ell ^ n))
            twistTransport lineData Y exponent_unit d) ≫
          (Etale.derivedTensorSingleUnitIso K.obj).hom
  /-- Local natural purity comparison and its literal sum-then-integration counit.
  The canonical tower is identified with affine d-space by affineTraceAffineSpaceIso.
  Separatedness of e follows from the separated standing setting (proof step 2). -/
  chart : ∀ (W : X.Opens) (e : W.toScheme ⟶ affineTraceTower Y d) [Etale e]
      [IsSeparated e] (hcomp : W.ι ≫ f = e ≫ affineTraceProjection Y d),
    letI : IsNoetherian W.toScheme := noetherianOpen W
    ∃ cp : Compactification (affineTraceProjection Y d),
    ∃ hM : ∀ K : (ectf (Coeff ell n) Y).FullSubcategory,
      _root_.DerivedCategory.TStructure.t.plus
        (((Etale.upperStar (ModuleCat.{u + 1} (Coeff ell n)) e).mapDerivedCategory).obj
          ((Etale.affineTraceRight (Coeff ell n) (ell ^ n)
            (CharP.cast_eq_zero (Coeff ell n) (ell ^ n)) Y d).obj K.obj)),
    ∃ α : finiteComparison (Coeff ell n) Y comparison_preserves ⋙ B.right ⋙
        star (Coeff ell n) W.ι ≅ chartModel ell n Y d e,
      (∀ K, ctf (Coeff ell n) W.toScheme ((chartModel ell n Y d e).obj K)) ∧
      (∀ K,
        (support (Coeff ell n) c).map ((bang (Coeff ell n) W.ι).map (α.hom.app K)) ≫
          chartCounit ell n twistTransport lineData f c W.ι d e hcomp cp exponent_unit K
            (hM K) =
        (support (Coeff ell n) c).map
          (openCounit (Coeff ell n) W
            (B.right.obj ((finiteComparison (Coeff ell n) Y comparison_preserves).obj K))) ≫
          B.counit.app ((finiteComparison (Coeff ell n) Y comparison_preserves).obj K))
  /-- Restriction of the same Brown adjoint represents the induced local counit on every
  open, including overlaps and all their further restrictions. -/
  localRepresents : ∀ (W : X.Opens) (K : (ctf (Coeff ell n) Y).FullSubcategory),
    ctf (Coeff ell n) W.toScheme ((star (Coeff ell n) W.ι).obj (B.right.obj K)) ∧
    ∀ M : (ctf (Coeff ell n) W.toScheme).FullSubcategory,
      Function.Bijective
        (fun a : M.obj ⟶ (star (Coeff ell n) W.ι).obj (B.right.obj K) ↦
          (support (Coeff ell n) c).map
            (((derivedOpenImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} (Coeff ell n)) W.ι).homEquiv M.obj
                (B.right.obj K)).symm a) ≫ B.counit.app K)
  /-- Every vertex of the signed open-cover triangle is finite ctf. -/
  openTerm_ctf : ∀ (W : X.Opens) (N : D (Coeff ell n) X), ctf (Coeff ell n) X N →
    ctf (Coeff ell n) X (openTerm (Coeff ell n) W N) ∧
      ctf (Coeff ell n) W.toScheme ((star (Coeff ell n) W.ι).obj N)


structure FiniteBrownLocalUniqueData
    (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [Smooth f] (c : Compactification f)
    (B : BrownData ell n hn k f c) (d : ℕ) where
  /-- Every overlap comparison is the unique isomorphism preserving the restricted counit.
  The restriction of the same Brown datum is a representing pair; these comparisons
  therefore satisfy the cocycle identity after further restriction. -/
  localUnique : ∀ (W : X.Opens) (K : D (Coeff ell n) Y)
      (H H' : D (Coeff ell n) W.toScheme),
    ctf (Coeff ell n) W.toScheme H → ctf (Coeff ell n) W.toScheme H' →
    ∀ (ε : (support (Coeff ell n) c).obj ((bang (Coeff ell n) W.ι).obj H) ⟶
        K)
      (ε' : (support (Coeff ell n) c).obj ((bang (Coeff ell n) W.ι).obj H') ⟶
        K),
    (∀ M : (ctf (Coeff ell n) W.toScheme).FullSubcategory,
      Function.Bijective (fun a : M.obj ⟶ H ↦
        (support (Coeff ell n) c).map ((bang (Coeff ell n) W.ι).map a) ≫ ε)) →
    (∀ M : (ctf (Coeff ell n) W.toScheme).FullSubcategory,
      Function.Bijective (fun a : M.obj ⟶ H' ↦
        (support (Coeff ell n) c).map ((bang (Coeff ell n) W.ι).map a) ≫ ε')) →
    ∃! a : H ≅ H',
      (support (Coeff ell n) c).map ((bang (Coeff ell n) W.ι).map a.hom) ≫ ε' = ε

/-- The signed open-cover triangle supplied by proof step 5.
(blueprint: sk-lem-sp-finite-existence). -/
structure FiniteBrownMayerVietorisData
    (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [Smooth f] (c : Compactification f)
    (B : BrownData ell n hn k f c) (d : ℕ) where
  /-- The exact signed triangle, with all arrows constructed from actual open counits. -/
  mayerVietoris : ∀ (U V : X.Opens) (_hcover : U ⊔ V = ⊤)
      (N : D (Coeff ell n) X), ctf (Coeff ell n) X N →
    ∃ δ : N ⟶ (openTerm (Coeff ell n) (U ⊓ V) N)⟦(1 : ℤ)⟧,
      Triangle.mk
        (biprod.lift (openMap (Coeff ell n) (U ⊓ V) U inf_le_left N)
          (-openMap (Coeff ell n) (U ⊓ V) V inf_le_right N))
        (biprod.desc (openCounit (Coeff ell n) U N) (openCounit (Coeff ell n) V N)) δ ∈
        distTriang (D (Coeff ell n) X)

/-- The finite-cover local representability and gluing field supplied by proof step 6.
(blueprint: sk-lem-sp-finite-existence). -/
structure FiniteBrownGluingData
    (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [Smooth f] (c : Compactification f)
    (B : BrownData ell n hn k f c) (d : ℕ) where
  /-- Local chart Hom bijections for this prescribed global counit imply its representing
  property, then the unique counit-preserving identification with the Brown object. -/
  gluing : ∀ (U V : X.Opens) (_hcover : U ⊔ V = ⊤)
      (K : (ctf (Coeff ell n) Y).FullSubcategory)
      (H : D (Coeff ell n) X), ctf (Coeff ell n) X H →
    ∀ ε : (support (Coeff ell n) c).obj H ⟶ K.obj,
    (∀ (W : X.Opens), W = U ∨ W = V ∨ W = U ⊓ V →
      ∀ M : (ctf (Coeff ell n) W.toScheme).FullSubcategory,
        Function.Bijective (fun a : M.obj ⟶ (star (Coeff ell n) W.ι).obj H ↦
          (support (Coeff ell n) c).map
            (((derivedOpenImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} (Coeff ell n)) W.ι).homEquiv M.obj H).symm a) ≫ ε)) →
      (∀ M : (ctf (Coeff ell n) X).FullSubcategory,
        Function.Bijective (fun a : M.obj ⟶ H ↦ (support (Coeff ell n) c).map a ≫ ε)) ∧
      ∃! a : H ≅ B.right.obj K,
        (support (Coeff ell n) c).map a.hom ≫ B.counit.app K = ε

end Witnesses

end AlgebraicGeometry.ProEtale.FiniteBrown
