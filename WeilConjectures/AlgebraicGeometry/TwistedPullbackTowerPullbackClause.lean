/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.TwistedPullbackTowerDomainDefinitions
import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerBoundsOperations
import WeilConjectures.Algebra.Homology.KFlatResolutionGeneral
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleConstructibility

/-! # Uniform pullback clause for strict towers

The following declaration isolates a proper subset of the five bounds clauses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTwistedTowerDomain

private theorem support_of_torAmplitude (X : Scheme.{u}) (A : Type u) [CommRing A]
    (K : proEtaleDerivedCategory X A) (a b : ℤ)
    (h : HasProEtaleTorAmplitude X A K a b) :
    proEtaleCohomologicalSupport K ⊆ Set.Icc a b := by
  classical
  let R : Sheaf (ProEt.topology X) CommRingCat.{u + 1} := proEtaleConstantRing X A
  let C := SheafOfModules.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{u} _
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} R
  let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  have := SheafOfModules.tensorPreadditive.{u + 1, u, u + 1} R
  have : (DerivedCategory.Q (C := C)).EssSurj :=
    Localization.essSurj _ (HomologicalComplex.quasiIso C (.up ℤ))
  let L := (DerivedCategory.Q (C := C)).objPreimage K
  let e : DerivedCategory.Q.obj L ≅ K :=
    (DerivedCategory.Q (C := C)).objObjPreimageIso K
  obtain ⟨P, f, hP, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionGeneral.{u + 1, u} (R := R) L
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso C f).2 hf
  let et : AlgebraicGeometry.Scheme.derivedTensor X A L
      ((HomologicalComplex.single C (.up ℤ) 0).obj (MonoidalCategory.tensorUnit C))
      P f hf hP ≅ K :=
    DerivedCategory.Q.mapIso (HomologicalComplex.rightUnitor P) ≪≫
      asIso (DerivedCategory.Q.map f) ≪≫ e
  intro i hi
  by_contra hout
  have hoff : i < a ∨ b < i := by
    change ¬ (a ≤ i ∧ i ≤ b) at hout
    omega
  have hz := h.2 L P ⟨e⟩ f hf hP (MonoidalCategory.tensorUnit C) i hoff
  exact hi (hz.of_iso ((DerivedCategory.homologyFunctor C i).mapIso et.symm))

private theorem tor_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {M N : proEtaleDerivedCategory T A} (e : M ≅ N) (a z : ℤ)
    (h : HasProEtaleTorAmplitude T A M a z) : HasProEtaleTorAmplitude T A N a z := by
  refine ⟨h.1, ?_⟩
  intro L P hL f hf hP Q i hi
  obtain ⟨eL⟩ := hL
  exact h.2 L P ⟨eL ≪≫ e.symm⟩ f hf hP Q i hi

private theorem finite_ctf_iso (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    {M N : proEtaleDerivedCategory T A} (e : M ≅ N)
    (h : spFiniteConstructibleTor T A M) : spFiniteConstructibleTor T A N := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨a, z, haz, hz⟩ := h.1
    exact ⟨a, z, haz, fun i hi ↦ (hz i hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso e).symm⟩
  · intro i
    have hc := h.2.1 i
    rw [proEtaleModuleRestriction_constructible_iff T A _] at hc ⊢
    exact ProEtale.isConstructible_of_iso
      ((proEtaleModuleRestriction T A).mapIso
        ((DerivedCategory.homologyFunctor _ i).mapIso e)) hc
  · obtain ⟨a, z, hz⟩ := h.2.2
    exact ⟨a, z, tor_iso T A e a z hz⟩

/-- Uniform finite-level pullback bounds for the tower-domain construction.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gamma.proof.md, paragraph (2), clause 1.
(blueprint: lem-stage3-twisted-pullback-pullback-clause).

Proof:

The structure maps of $X,Y$ to $\operatorname{Spec}k$ are locally of finite type and
quasi-compact, so $X$ and $Y$ are Noetherian. The finite-field datum gives $k$ characteristic
$p$, and $\ell\ne p$.

Write $C$ for the realization $\widetilde K$ of $K$. Fix $n$. The specified evaluation
comparison of the realization [def-sp-tower-shriek-realization] identifies $C_n$ with the level
$K_n$ of $K\in\mathcal C_Y$ [sk-def-sp-normalized-towers]; bounded intrinsic constructibility,
cohomological boundedness and the existence of a Tor interval are invariant under isomorphism
in the finite-coefficient pro-etale derived category (homology is transported by the homology
functor, constructibility through the restriction to modules
[lem-weil-pbc-proetale-constant-module-constructibility], each tensor test by composing the
representing isomorphism). So $C_n$ is bounded constructible of finite Tor amplitude. The
assumed Tor interval $[a,z]$ of $C_n$ gives cohomological support in $[a,z]$: choose a K-flat
resolution $P\to L$ of a complex $L$ representing $C_n$ and take the test module to be the unit
in [def-weil-proetale-tor-amplitude]; by the right unitor
[lem-sf-ringed-derived-closed-symmetric-monoidal] the test object is $C_n$ itself, so
$\mathcal H^i(C_n)=0$ for $i\notin[a,z]$. Thus $\operatorname{Bounds}_Y(C;a,z;a,z)$.

The first clause of [lem-route-elementary-tower-bounds], applied to $f$ over $k$ with the
Noetherian $X,Y$, gives $\operatorname{Bounds}_X(f_\bullet^*C;a,z;a,z)$, and
$f_\bullet^*C$ is by definition $B$. -/
theorem twisted_pullback_pullback_clause
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b) (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X Y : Over (Spec (CommRingCat.of D.k))) [IsSeparated X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (f : X ⟶ Y)
    [IsSeparated f.left] (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (w : SpChartAdmissibility.Twists l E X.left)
    (K : SpTowerCalculus.C l E b q Y.left) (a z : ℤ) (haz : a ≤ z)
    (hTor : ∀ n : ℕ, HasProEtaleTorAmplitude Y.left (SpTowerShriek.R l E n)
      ((SpTowerShriek.Ev l E Y.left n).obj
        ((SpTowerGamma.realization l E b q Y.left).obj K)) a z) :
    SpChartAdmissibility.bounds l E X.left (B l E b o q f.left K) a z a z := by
  classical
  letI := isNoetherian_of_locallyOfFiniteType X.hom
  letI := isNoetherian_of_locallyOfFiniteType Y.hom
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  letI : Fact D.p.Prime := ⟨D.prime⟩
  letI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
      (D.card_base.trans D.cardinality_eq))
  letI : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let C := (SpTowerGamma.realization l E b q Y.left).obj K
  have hC : SpChartAdmissibility.bounds l E Y.left C a z a z := by
    intro n
    let e := (SpTowerCalculus.levelComparison l E b q Y.left n).app K.obj
    exact ⟨finite_ctf_iso Y.left _ e.symm (K.property.1 n),
      support_of_torAmplitude Y.left _ _ a z (hTor n), hTor n⟩
  exact (SpChartAdmissibility.elementary_tower_bounds l E D.p D.k hl b o).1
    X Y f C a z a z hC

end AlgebraicGeometry.ProEtale.SpTwistedTowerDomain
