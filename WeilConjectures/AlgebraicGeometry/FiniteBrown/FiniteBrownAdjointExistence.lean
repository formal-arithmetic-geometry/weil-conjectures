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

/-- Ordinary finite coefficients. Source: the unit's coefficient convention
(blueprint: sk-lem-sp-finite-existence). -/
abbrev Coeff (ell n : ℕ) := ULift.{u + 1} (ZMod (ell ^ n))

/-- The ordinary pro-etale ambient category. Source: the unit's coefficient convention
(blueprint: sk-lem-sp-finite-existence). -/
abbrev D (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))

/-- The ordinary etale ambient category. Source: finite site comparison
(blueprint: sk-lem-sp-finite-existence). -/
abbrev E (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  Etale.DerivedCategoryModule A T

/-- The intrinsic bounded constructible finite-Tor predicate, reused without alteration.
Source: finite-coefficient interpretation (blueprint: sk-lem-sp-finite-existence). -/
abbrev ctf (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) :=
  exceptionalTransportProEtaleObjects A T

/-- The corresponding etale predicate. Source: finite site comparison
(blueprint: sk-lem-sp-finite-existence). -/
abbrev ectf (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) :=
  exceptionalTransportEtaleObjects A T

/-- Actual comparison inverse image on derived categories. Source: finite site transfer
(blueprint: sk-lem-sp-finite-existence). -/
abbrev nu (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory

/-- Actual exact derived inverse image. Source: the chart formula
(blueprint: sk-lem-sp-finite-existence). -/
abbrev star (A : Type (u + 1)) [CommRing A] {T S : Scheme.{u}} (f : T ⟶ S) :=
  (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory

/-- Actual exact open extension. Source: Stacks 0GKK
(blueprint: sk-lem-sp-finite-existence). -/
abbrev bang (A : Type (u + 1)) [CommRing A] {T S : Scheme.{u}}
    (j : T ⟶ S) [IsOpenImmersion j] :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory

/-- Fixed-compactification compact supports. Source: representing-pair convention
(blueprint: sk-lem-sp-finite-existence). -/
abbrev support (A : Type (u + 1)) [CommRing A] {T S : Scheme.{u}}
    {f : T ⟶ S} (c : Compactification f) :=
  rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c

/-- Extension of restriction to an open. Source: Stacks 0GKK
(blueprint: sk-lem-sp-finite-existence). -/
def openTerm (A : Type (u + 1)) [CommRing A] {X : Scheme.{u}}
    (W : X.Opens) (N : D A X) : D A X :=
  (bang A W.ι).obj ((star A W.ι).obj N)

/-- The actual open-adjunction counit. Source: the signed triangle
(blueprint: sk-lem-sp-finite-existence). -/
def openCounit (A : Type (u + 1)) [CommRing A] {X : Scheme.{u}}
    (W : X.Opens) (N : D A X) : openTerm A W N ⟶ N :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) W.ι).counit.app N

/-- The counit-induced inclusion from a smaller open. Its transpose is the inverse of
restriction of open extension, followed by the inverse-image composition comparison.
Source: Stacks 0GKK, canonical `(1,-1)` arrow (blueprint: sk-lem-sp-finite-existence). -/
def openMap (A : Type (u + 1)) [CommRing A] {X : Scheme.{u}}
    (W U : X.Opens) (h : W ≤ U) (N : D A X) : openTerm A W N ⟶ openTerm A U N := by
  let t := X.homOfLE h
  let r : (star A W.ι).obj (openTerm A U N) ≅ (star A W.ι).obj N :=
    (mapDerivedCategoryOpenImmersionLowerShriekCompUpperStarIsoOfFac
      (ModuleCat.{u + 1} A) U.ι t W.ι (by simp [t])).app ((star A U.ι).obj N) ≪≫
    ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        ((upperStarComp (ModuleCat.{u + 1} A) t U.ι).symm) ≪≫
      Functor.mapDerivedCategoryNatIso
        (eqToIso (by simp [t]))).app N
  exact ((derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) W.ι).homEquiv _ _).symm r.inv

/-- Canonical etale chart compact-support composition coordinates, including the fixed
compactification and the ordered affine tower. No isomorphism is chosen from existence.
Source: det-sp-finite-existence-chart, compact-support compositor
(blueprint: sk-lem-sp-finite-existence). -/
def etaleChartLeft (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y U : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian U]
    (f : X ⟶ Y) (c : Compactification f) (j : U ⟶ X) [IsOpenImmersion j]
    (d : ℕ) (e : U ⟶ affineTraceTower Y d) [Etale e] [IsSeparated e]
    (hcomp : j ≫ f = e ≫ affineTraceProjection Y d)
    (cp : Compactification (affineTraceProjection Y d)) :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory ⋙
        Etale.affineTraceLeft A Y d := by
  letI := affineTraceNoetherian Y d
  let cj : Compactification (e ≫ affineTraceProjection Y d) :=
    (c.precomp j).copy hcomp.symm
  exact Etale.etaleAmbientLeftComparison A (Etale.canonicalEtaleCompactSupportNormalization A)
      j f c (c.precomp j) ≪≫
    (Iso.refl _) ≪≫
    (Etale.etaleAmbientLeftComparison A (Etale.canonicalEtaleCompactSupportNormalization A)
      e (affineTraceProjection Y d) cp cj).symm ≪≫
    Functor.isoWhiskerLeft _
      ((Etale.affineDualizingTowerComparison A Y d) ≪≫
        (Etale.rightDerivedLowerShriekIso A cp).symm).symm

/-- Canonical finite site transfer of the chart left comparison at a bounded-below
etale input. Source: the unit's finite site transfer, retaining actual counits
(blueprint: sk-lem-sp-finite-existence). -/
def chartLeft (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y U : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian U]
    (f : X ⟶ Y) (c : Compactification f) (j : U ⟶ X) [IsOpenImmersion j]
    (d : ℕ) (e : U ⟶ affineTraceTower Y d) [Etale e] [IsSeparated e]
    (hcomp : j ≫ f = e ≫ affineTraceProjection Y d)
    (cp : Compactification (affineTraceProjection Y d))
    (M : E A U) (hM : _root_.DerivedCategory.TStructure.t.plus M) :
    (support A c).obj ((bang A j).obj ((nu A U).obj M)) ≅
      (nu A Y).obj ((Etale.affineTraceLeft A Y d).obj
        ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e
          inferInstance).mapDerivedCategory.obj M)) :=
  (support A c).mapIso
      ((mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} A) j).app M).symm ≪≫
    (rightDerivedLowerShriekOfCompactificationComparisonIso
      (ModuleCat.{u + 1} A) c).app
        ((Etale.openImmersionLowerShriek
          (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus.obj
          ⟨M, hM⟩) ≪≫
    (nu A Y).mapIso ((etaleChartLeft A f c j d e hcomp cp).app M)

end AlgebraicGeometry.ProEtale.FiniteBrown

namespace AlgebraicGeometry.ProEtale.FiniteBrown

/-- Brown restriction, expressed by its natural counit and the representing-pair Hom
bijections. The source full subcategory is the intrinsic finite ctf category.
Source: sk-prop-sf-existence and sk-def-sp-representing-pair
(blueprint: sk-lem-sp-finite-existence). -/
structure BrownData (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [Smooth f]
    (c : Compactification f) where
  /-- The restricted Brown right adjoint, viewed in the ambient category. -/
  right : (ctf (Coeff ell n) Y).FullSubcategory ⥤ D (Coeff ell n) X
  /-- Its natural counit. -/
  counit : right ⋙ support (Coeff ell n) c ⟶ (ctf (Coeff ell n) Y).ι
  /-- The right adjoint takes finite ctf objects to finite ctf objects. -/
  preserves : ∀ K, ctf (Coeff ell n) X (right.obj K)
  /-- Exactly the tests in the existing representing-pair definition. -/
  represents : ∀ K (M : D (Coeff ell n) X),
    DerivedCategory.boundedConstructibleIntrinsic (Coeff ell n) X M →
    (∃ a b : ℤ, a ≤ b ∧ _root_.DerivedCategory.torAmplitudeIn
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (Coeff ell n))) a b M) →
    Function.Bijective (fun b : M ⟶ right.obj K ↦
      (support (Coeff ell n) c).map b ≫ counit.app K)

/-- The existing representing pair attached to a Brown datum; this is real structure data.
Source: sk-def-sp-representing-pair (blueprint: sk-lem-sp-finite-existence). -/
def BrownData.pair (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [Smooth f]
    (c : Compactification f) (B : BrownData ell n hn k f c)
    (K : (ctf (Coeff ell n) Y).FullSubcategory) :
    FiniteRepresentingPair ell n f c K.obj where
  object := B.right.obj K
  counit := B.counit.app K
  map_bijective := B.represents K

/-- The actual comparison functor restricted to the finite ctf subcategories, using its
preservation proof rather than new coefficient data. Source: finite site transfer
(blueprint: sk-lem-sp-finite-existence). -/
def finiteComparison (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (h : ∀ M : (ectf A T).FullSubcategory, ctf A T ((nu A T).obj M.obj)) :=
  (ctf A T).lift ((ectf A T).ι ⋙ nu A T) h

/-- The displayed etale pullback, finite Tate twist and shift, pulled to the pro-etale
site. The input finite site equivalence makes this exactly e* p* K(d)[2d] for every
pro-etale finite ctf K; no antecedent is assumed in the theorem.
Source: det-sp-finite-existence-chart (blueprint: sk-lem-sp-finite-existence). -/
def chartModel (ell n : ℕ) [Fact ell.Prime] (Y : Scheme.{u}) (d : ℕ)
    {U : Scheme.{u}} (e : U ⟶ affineTraceTower Y d) :=
  (ectf (Coeff ell n) Y).ι ⋙
    (Etale.upperStar (ModuleCat.{u + 1} (Coeff ell n))
      (affineTraceProjection Y d)).mapDerivedCategory ⋙
    Etale.derivedTensorRight (ModuleCat.{u + 1} (Coeff ell n)) (affineTraceTower Y d)
      (Etale.SectionLocalDualizingComparisons.tateObject (Coeff ell n) (ell ^ n)
        (CharP.cast_eq_zero (Coeff ell n) (ell ^ n)) (affineTraceTower Y d) d) ⋙
    (Etale.upperStar (ModuleCat.{u + 1} (Coeff ell n)) e).mapDerivedCategory ⋙
    nu (Coeff ell n) U

/-- Normalized chart counit: canonical compact-support comparison, mapped etale sum
counit, and the actual ordered affine integration counit, in that order.
Source: det-sp-finite-existence-chart, displayed composite
(blueprint: sk-lem-sp-finite-existence). -/
def chartCounit (ell n : ℕ) [Fact ell.Prime]
    (t : Etale.OrdinaryFiniteTwistTransport (Coeff ell n) (ell ^ n)
      (CharP.cast_eq_zero (Coeff ell n) (ell ^ n)))
    (P : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit ((ell ^ n : ℕ) : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum (Coeff ell n) (ell ^ n)
        (CharP.cast_eq_zero (Coeff ell n) (ell ^ n)) t T hT)
    {X Y U : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian U]
    (f : X ⟶ Y) (c : Compactification f) (j : U ⟶ X) [IsOpenImmersion j]
    (d : ℕ) (e : U ⟶ affineTraceTower Y d) [Etale e] [IsSeparated e]
    (hcomp : j ≫ f = e ≫ affineTraceProjection Y d)
    (cp : Compactification (affineTraceProjection Y d))
    (hY : IsUnit ((ell ^ n : ℕ) : Γ(Y, ⊤)))
    (K : (ectf (Coeff ell n) Y).FullSubcategory)
    (hM : _root_.DerivedCategory.TStructure.t.plus
      (((Etale.upperStar (ModuleCat.{u + 1} (Coeff ell n)) e).mapDerivedCategory).obj
        ((Etale.affineTraceRight (Coeff ell n) (ell ^ n)
          (CharP.cast_eq_zero (Coeff ell n) (ell ^ n)) Y d).obj K.obj))) :
    (support (Coeff ell n) c).obj ((bang (Coeff ell n) j).obj
      ((chartModel ell n Y d e).obj K)) ⟶ (nu (Coeff ell n) Y).obj K.obj :=
  (support (Coeff ell n) c).map
      ((bang (Coeff ell n) j).map
        ((nu (Coeff ell n) U).map
          ((Etale.upperStar (ModuleCat.{u + 1} (Coeff ell n)) e).mapDerivedCategory.map
            (Etale.OrdinaryAffineCounitTensorNormalization.reassociation (Coeff ell n)
              (ell ^ n) (pow_pos (Fact.out : ell.Prime).pos n)
              (CharP.cast_eq_zero (Coeff ell n) (ell ^ n))
              t Y hY d K.obj).inv))) ≫
    (chartLeft (Coeff ell n) f c j d e hcomp cp _ hM).hom ≫
    (nu (Coeff ell n) Y).map
      ((Etale.affineTraceLeft (Coeff ell n) Y d).map
        ((Etale.derivedEtaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} (Coeff ell n)) e inferInstance).counit.app
            ((Etale.affineTraceRight (Coeff ell n) (ell ^ n)
              (CharP.cast_eq_zero (Coeff ell n) (ell ^ n)) Y d).obj K.obj)) ≫
        (Etale.affineTraceAdjunction (Coeff ell n) (ell ^ n)
          (CharP.cast_eq_zero (Coeff ell n) (ell ^ n)) t P Y hY d).counit.app K.obj)

end AlgebraicGeometry.ProEtale.FiniteBrown

namespace AlgebraicGeometry.ProEtale.FiniteBrown

/-- Every open of a Noetherian scheme is Noetherian. This discharges the chart API's
Noetherian requirement rather than adding a hypothesis to the unit.
Source: chart-hypothesis check, proof step 2 (blueprint: sk-lem-sp-finite-existence). -/
abbrev noetherianOpen {X : Scheme.{u}} [IsNoetherian X] (W : X.Opens) :
    IsNoetherian W.toScheme := by
  exact ⟨⟩

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

/-- All clauses of the local Brown computation, with maps specified by the existing
adjunctions. The `localUnique` clause supplies overlap and triple-overlap coherence by
uniqueness of counit-preserving comparisons. The last clause uses the local Hom
bijections of the chart counits, including all shifts, rather than assuming global
representability. Source: the entire unit and its proof steps 1--7
(blueprint: sk-lem-sp-finite-existence). -/
structure ExistenceData (d : ℕ) where
  /-- Brown restriction to the finite ctf categories. -/
  brown : BrownData ell n hn k f c
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
    ∃ α : finiteComparison (Coeff ell n) Y comparison_preserves ⋙ brown.right ⋙
        star (Coeff ell n) W.ι ≅ chartModel ell n Y d e,
      (∀ K, ctf (Coeff ell n) W.toScheme ((chartModel ell n Y d e).obj K)) ∧
      (∀ K,
        (support (Coeff ell n) c).map ((bang (Coeff ell n) W.ι).map (α.hom.app K)) ≫
          chartCounit ell n twistTransport lineData f c W.ι d e hcomp cp exponent_unit K
            (hM K) =
        (support (Coeff ell n) c).map
          (openCounit (Coeff ell n) W
            (brown.right.obj ((finiteComparison (Coeff ell n) Y comparison_preserves).obj K))) ≫
          brown.counit.app ((finiteComparison (Coeff ell n) Y comparison_preserves).obj K))
  /-- Restriction of the same Brown adjoint represents the induced local counit on every
  open, including overlaps and all their further restrictions. -/
  localRepresents : ∀ (W : X.Opens) (K : (ctf (Coeff ell n) Y).FullSubcategory),
    ctf (Coeff ell n) W.toScheme ((star (Coeff ell n) W.ι).obj (brown.right.obj K)) ∧
    ∀ M : (ctf (Coeff ell n) W.toScheme).FullSubcategory,
      Function.Bijective
        (fun a : M.obj ⟶ (star (Coeff ell n) W.ι).obj (brown.right.obj K) ↦
          (support (Coeff ell n) c).map
            (((derivedOpenImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} (Coeff ell n)) W.ι).homEquiv M.obj
                (brown.right.obj K)).symm a) ≫ brown.counit.app K)
  /-- Every vertex of the signed open-cover triangle is finite ctf. -/
  openTerm_ctf : ∀ (W : X.Opens) (N : D (Coeff ell n) X), ctf (Coeff ell n) X N →
    ctf (Coeff ell n) X (openTerm (Coeff ell n) W N) ∧
      ctf (Coeff ell n) W.toScheme ((star (Coeff ell n) W.ι).obj N)
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
  /-- The exact signed triangle, with all arrows constructed from actual open counits. -/
  mayerVietoris : ∀ (U V : X.Opens) (_hcover : U ⊔ V = ⊤)
      (N : D (Coeff ell n) X), ctf (Coeff ell n) X N →
    ∃ δ : N ⟶ (openTerm (Coeff ell n) (U ⊓ V) N)⟦(1 : ℤ)⟧,
      Triangle.mk
        (biprod.lift (openMap (Coeff ell n) (U ⊓ V) U inf_le_left N)
          (-openMap (Coeff ell n) (U ⊓ V) V inf_le_right N))
        (biprod.desc (openCounit (Coeff ell n) U N) (openCounit (Coeff ell n) V N)) δ ∈
        distTriang (D (Coeff ell n) X)
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
      ∃! a : H ≅ brown.right.obj K,
        (support (Coeff ell n) c).map a.hom ≫ brown.counit.app K = ε

end Witnesses

end AlgebraicGeometry.ProEtale.FiniteBrown
