/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedFiniteCohomologyTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedGeometricFrobeniusTransport
public import WeilConjectures.PoincareDuality.CondensedFrobeniusOperators.FiniteStrictWeilComplex.TraceFormulaFiniteStrictWeilComplex
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.SchemeFrobenius
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusFactorization
public import WeilConjectures.AlgebraicGeometry.Morphisms.Frobenius
public import WeilConjectures.AlgebraicGeometry.SixFunctors.AbsoluteFrobeniusSite
public import WeilConjectures.AlgebraicGeometry.SixFunctors.FrobeniusTrivializationPullback
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.Topology.Homeomorph.Defs
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.RingTheory.WittVector.Frobenius
public import Mathlib.Tactic.Ring
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalPullbackComposition
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.AbsoluteFrobenius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.IsoId
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FrobeniusNaturality
import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalAdjunctionUnit
import WeilConjectures.CategoryTheory.FrobeniusCancellation

/-!
# Normalized scheme/Galois comparison

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-frobenius/sk-def-sf-weil-complexes/prop-trf-scheme-galois-comparison.md`
(blueprint: prop-trf-scheme-galois-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

-- Fix the native site size before synthesizing derived module instances.
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace WeilConjectures.CondensedFrobeniusOperators
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport

private def expansion (f g t : End X) (e : t = f ≫ g) : P t ≅ P g ⋙ P f :=
  eqToIso (congrArg P e) ≪≫ c f g

private theorem expansion_coherence
    (hc : ∀ (f g h : End X) (K : C),
      (c f (g ≫ h)).hom.app K ≫ (P f).map ((c g h).hom.app K) =
        (eqToIso (congrArg P (Category.assoc f g h).symm)).hom.app K ≫
          (c (f ≫ g) h).hom.app K ≫ (c f g).hom.app ((P h).obj K))
    (f g h fg gh t : End X) (efg : fg = f ≫ g) (egh : gh = g ≫ h)
    (et : t = f ≫ gh) (et' : t = fg ≫ h) (K : C) :
    (expansion P c f gh t et).hom.app K ≫
        (P f).map ((expansion P c g h gh egh).hom.app K) =
      (expansion P c fg h t et').hom.app K ≫
        (expansion P c f g fg efg).hom.app ((P h).obj K) := by
  subst fg
  subst gh
  cases et
  simpa only [expansion, eqToIso_refl, Iso.refl_trans, Iso.trans_hom,
    NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Category.assoc] using hc f g h K

private theorem expansion_refl (f g : End X) :
    expansion P c f g (f ≫ g) rfl = c f g := by
  simp only [expansion, eqToIso_refl, Iso.refl_trans]

private theorem interchange_expansion
    (hc : ∀ (f g h : End X) (K : C),
      (c f (g ≫ h)).hom.app K ≫ (P f).map ((c g h).hom.app K) =
        (eqToIso (congrArg P (Category.assoc f g h).symm)).hom.app K ≫
          (c (f ≫ g) h).hom.app K ≫ (c f g).hom.app ((P h).obj K))
    (g h k : End X) (w : h ≫ g = g ≫ h) (K : C) :
    (c g (h ≫ k)).hom.app K ≫ (P g).map ((c h k).hom.app K) ≫
        (c g h).inv.app ((P k).obj K) ≫
        (eqToIso (congrArg P w.symm)).hom.app ((P k).obj K) ≫
        (c h g).hom.app ((P k).obj K) =
      (expansion P c h (g ≫ k) (g ≫ h ≫ k)
        (by rw [← Category.assoc, ← w, Category.assoc])).hom.app K ≫
        (P h).map ((c g k).hom.app K) := by
  let t := g ≫ h ≫ k
  have et : t = (h ≫ g) ≫ k := by dsimp [t]; rw [← Category.assoc, w]
  have et' : t = h ≫ g ≫ k := by rw [et, Category.assoc]
  have h₁ := expansion_coherence P c hc g h k (h ≫ g) (h ≫ k) t
    w rfl rfl et K
  have h₂ := expansion_coherence P c hc h g k (h ≫ g) (g ≫ k) t
    rfl rfl et' et K
  dsimp only [t] at h₁ h₂
  simp only [expansion_refl] at h₁ h₂
  rw [reassoc_of% h₁]
  simp only [expansion, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
    Category.assoc] at h₁ h₂ ⊢
  simp only [Iso.hom_inv_id_app_assoc, eqToHom_app, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  simpa only [eqToHom_app] using h₂.symm

/-- Cancelling a natural, multiplicative trivialization in two commuting
factorizations is compatible with the canonical pullback composition maps.
Source: blueprint `prop-trf-scheme-galois-comparison`, proof paragraph 2
(blueprint: lem-trf-factorization-trivialization-multiplication).
Proof: expand both factorizations using the composition comparisons. Their
associativity identifies the two expansions of three consecutive factors. The
naturality square for the second trivialization moves it through the first
Galois pullback. Naturality of the first trivialization then moves it through
that square. Apply the addition law for the two trivializations, and cancel the
Galois composition comparison. All steps are equations of natural transformations,
so extensionality in the object proves the identity. -/
private theorem factorizationTrivialization_multiplication
    (hc : ∀ (f g h : End X) (K : C),
      (c f (g ≫ h)).hom.app K ≫ (P f).map ((c g h).hom.app K) =
        (eqToIso (congrArg P (Category.assoc f g h).symm)).hom.app K ≫
          (c (f ≫ g) h).hom.app K ≫ (c f g).hom.app ((P h).obj K))
    (f g h k : End X) (w : h ≫ g = g ≫ h)
    (t : P f ≅ 𝟭 C) (s : P h ≅ 𝟭 C) (z : P (f ≫ h) ≅ 𝟭 C)
    (hz : ∀ K : C, z.hom.app K =
      (c f h).hom.app K ≫ t.hom.app ((P h).obj K) ≫ s.hom.app K)
    (hs : ∀ K : C,
      (c g h).inv.app K ≫ (eqToIso (congrArg P w.symm)).hom.app K ≫
          (c h g).hom.app K ≫ s.hom.app ((P g).obj K) =
        (P g).map (s.hom.app K)) :
    ∀ K : C,
      (eqToIso (congrArg P
        (show (f ≫ g) ≫ (h ≫ k) = (f ≫ h) ≫ (g ≫ k) by
          simp only [Category.assoc]; rw [← Category.assoc g h k, ← w,
            Category.assoc]))).hom.app K ≫
          (c (f ≫ h) (g ≫ k)).hom.app K ≫ z.hom.app ((P (g ≫ k)).obj K) =
        (c (f ≫ g) (h ≫ k)).hom.app K ≫
          (c f g).hom.app ((P (h ≫ k)).obj K) ≫
          t.hom.app ((P g).obj ((P (h ≫ k)).obj K)) ≫
          (P g).map ((c h k).hom.app K ≫ s.hom.app ((P k).obj K)) ≫
          (c g k).inv.app K := by
  intro K
  let b := g ≫ h ≫ k
  let total := (f ≫ g) ≫ (h ≫ k)
  have eb : b = h ≫ g ≫ k := by
    dsimp [b]
    rw [← Category.assoc, ← w, Category.assoc]
  have et : total = f ≫ b := Category.assoc _ _ _
  have et' : total = (f ≫ h) ≫ (g ≫ k) := by
    rw [et, eb, ← Category.assoc]
  have h₁ := expansion_coherence P c hc f g (h ≫ k) (f ≫ g) b total
    rfl rfl et rfl K
  have h₂ := expansion_coherence P c hc f h (g ≫ k) (f ≫ h) b total
    rfl eb et et' K
  dsimp only [b, total] at h₁ h₂
  simp only [expansion_refl] at h₁ h₂
  have hswap := interchange_expansion P c hc g h k w K
  have hh : (c g (h ≫ k)).hom.app K ≫
      (P g).map ((c h k).hom.app K ≫ s.hom.app ((P k).obj K)) =
    (expansion P c h (g ≫ k) b eb).hom.app K ≫
      (P h).map ((c g k).hom.app K) ≫ s.hom.app ((P g).obj ((P k).obj K)) := by
    rw [Functor.map_comp, ← hs ((P k).obj K)]
    simpa only [Category.assoc] using
      congrArg (· ≫ s.hom.app ((P g).obj ((P k).obj K))) hswap
  have nt := t.hom.naturality
    ((P g).map ((c h k).hom.app K ≫ s.hom.app ((P k).obj K)))
  have nt₁ := t.hom.naturality (s.hom.app ((P g).obj ((P k).obj K)))
  have nt₂ := t.hom.naturality ((P h).map ((c g k).hom.app K))
  have ns := s.hom.naturality ((c g k).hom.app K)
  simp only [Functor.id_map] at nt nt₁ nt₂ ns
  symm
  rw [← reassoc_of% nt, ← reassoc_of% h₁]
  rw [← Functor.map_comp_assoc, hh]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% nt₁, reassoc_of% nt₂, reassoc_of% ns,
    Iso.hom_inv_id_app, Category.comp_id]
  rw [reassoc_of% h₂, ← hz]
  simp only [expansion, Iso.trans_hom, NatTrans.comp_app, Category.assoc]

private noncomputable def factorizationComparison
    (H G T : End X) (w : T = H ≫ G) (t : P H ≅ 𝟭 C) : P T ≅ P G :=
  eqToIso (congrArg P w) ≪≫ c H G ≪≫ Functor.isoWhiskerLeft (P G) t ≪≫
    Functor.rightUnitor _

private theorem factorizationComparison_multiplicative
    (hc : ∀ (f g h : End X) (K : C),
      (c f (g ≫ h)).hom.app K ≫ (P f).map ((c g h).hom.app K) =
        (eqToIso (congrArg P (Category.assoc f g h).symm)).hom.app K ≫
          (c (f ≫ g) h).hom.app K ≫ (c f g).hom.app ((P h).obj K))
    (H₁ H₂ H₃ G₁ G₂ G₃ T₁ T₂ T₃ : End X)
    (w₁ : T₁ = H₁ ≫ G₁) (w₂ : T₂ = H₂ ≫ G₂) (w₃ : T₃ = H₃ ≫ G₃)
    (hT : T₁ ≫ T₂ = T₃) (hG : G₁ ≫ G₂ = G₃) (hH : H₁ ≫ H₂ = H₃)
    (comm : H₂ ≫ G₁ = G₁ ≫ H₂)
    (t₁ : P H₁ ≅ 𝟭 C) (t₂ : P H₂ ≅ 𝟭 C) (t₃ : P H₃ ≅ 𝟭 C)
    (ht : t₃.hom = eqToHom (congrArg P hH.symm) ≫ (c H₁ H₂).hom ≫
      Functor.whiskerLeft (P H₂) t₁.hom ≫ (Functor.rightUnitor _).hom ≫ t₂.hom)
    (hn : (c G₁ H₂).inv ≫ eqToHom (congrArg P comm.symm) ≫ (c H₂ G₁).hom ≫
      Functor.whiskerLeft (P G₁) t₂.hom ≫ (Functor.rightUnitor _).hom =
        Functor.whiskerRight t₂.hom (P G₁) ≫ (Functor.leftUnitor _).hom) :
    (factorizationComparison P c H₃ G₃ T₃ w₃ t₃).hom =
      eqToHom (congrArg P hT.symm) ≫ (c T₁ T₂).hom ≫
        Functor.whiskerLeft (P T₂) (factorizationComparison P c H₁ G₁ T₁ w₁ t₁).hom ≫
        Functor.whiskerRight (factorizationComparison P c H₂ G₂ T₂ w₂ t₂).hom (P G₁) ≫
        (c G₁ G₂).inv ≫ eqToHom (congrArg P hG) := by
  rcases w₁ with rfl
  rcases w₂ with rfl
  rcases hT with rfl
  rcases hH with rfl
  rcases hG with rfl
  have ht' (K : C) := NatTrans.congr_app ht K
  have hn' (K : C) := NatTrans.congr_app hn K
  simp only [NatTrans.comp_app, eqToHom_refl,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.rightUnitor_hom_app,
    Functor.leftUnitor_hom_app, Functor.id_obj, Functor.comp_obj,
    Category.comp_id, Category.id_comp] at ht' hn'
  apply NatTrans.ext
  funext K
  have h := factorizationTrivialization_multiplication P c hc H₁ G₁ H₂ G₂ comm
    t₁ t₂ t₃ ht' hn' K
  simpa only [factorizationComparison, Iso.trans_hom, eqToIso.hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.rightUnitor_hom_app, eqToHom_refl,
    NatTrans.id_app, Functor.comp_obj, Functor.id_obj,
    Category.id_comp, Category.comp_id, Category.assoc] using h

private lemma reverse_transport {C : Type*} [Category C] {A B Z : C}
    (e : A = B) {f : A ⟶ Z} {g : B ⟶ Z} (h : f = eqToHom e ≫ g) :
    g = eqToHom e.symm ≫ f := by
  cases e
  simpa only [eqToHom_refl, Category.id_comp] using h.symm

private theorem trivialization_interchange
    {C : Type*} [Category C] {A B : C ⥤ C} (a : A ≅ 𝟭 C) (b : B ≅ 𝟭 C) :
    Functor.whiskerRight b.hom A ≫ A.leftUnitor.hom ≫ a.hom =
      Functor.whiskerLeft B a.hom ≫ B.rightUnitor.hom ≫ b.hom := by
  apply NatTrans.ext
  funext K
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app, Functor.id_obj,
    Functor.comp_obj, Functor.id_map, Category.id_comp] using
    a.hom.naturality (b.hom.app K)

private lemma derivedTrivialization_composite
    (a : H ≅ J) (b : J ≅ F ⋙ G) (eF : F ≅ 𝟭 C) (eG : G ≅ 𝟭 C)
    (eH : H ≅ 𝟭 C)
    (h : a ≪≫ b ≪≫ Functor.isoWhiskerRight eF G ≪≫ G.leftUnitor ≪≫ eG = eH) :
    (Functor.leftDerivedFunctorIdIso eH).hom =
      (H.leftDerivedFunctorNatIso a).hom ≫ (J.leftDerivedFunctorNatIso b).hom ≫
        (F.leftDerivedFunctorCompIso G).hom ≫
        Functor.whiskerRight (Functor.leftDerivedFunctorIdIso eF).hom G.leftDerivedFunctor ≫
        G.leftDerivedFunctor.leftUnitor.hom ≫ (Functor.leftDerivedFunctorIdIso eG).hom := by
  have hh := Functor.leftDerivedFunctorIdIso_comp eF eG (a ≪≫ b)
  have he : (a ≪≫ b) ≪≫ Functor.isoWhiskerRight eF G ≪≫ G.leftUnitor ≪≫ eG = eH := by
    simpa only [Iso.trans_assoc] using h
  rw [he] at hh
  have hh' := congrArg Iso.hom hh.symm
  simpa only [Functor.leftDerivedFunctorNatIso_trans, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Category.assoc] using hh'

/-- Characteristic-p witness on the geometric fibre.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-frobenius/
sk-def-sf-weil-complexes/prop-trf-scheme-galois-comparison.proof.md`
(blueprint: prop-trf-scheme-galois-comparison). -/
abbrev finiteFiberCharacteristic (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) :=
  F.model_characteristic (pullback.fst Y₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap F.k₀ F.k))) ≫ Y₀.hom)

/-- The factorization used by the specified comparison, for every positive iterate.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-def-sf-weil-complexes/prop-trf-scheme-galois-comparison.proof.md`
(blueprint: lem-trf-condensed-scheme-galois-comparison-add).
Proof: cancel the arithmetic Galois power from absoluteFrobenius_factorization using
its inverse geometric Galois power; Iso.pow_hom_eq_pow identifies the resulting power. -/
theorem finiteComparisonFactorization (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (m : ℕ) (hm : 1 ≤ m) :
    F.schemeFrobeniusIterate Y₀ m =
      (F.geometricFiber Y₀).left.iterateFrobenius F.prime
        (finiteFiberCharacteristic F Y₀) (F.a * m) ≫
      ((geometricFrobeniusGeometry F Y₀).h.pow m).hom := by
  let X := (F.geometricFiber Y₀).left
  let G : End X := (End.of (F.geometricGaloisFrobenius Y₀)) ^ m
  have h := (F.absoluteFrobenius_factorization Y₀ m hm).1
  have hi : ((End.of (F.arithmeticGaloisFrobenius Y₀)) ^ m) ≫ G = 𝟙 X := by
    change (End.of (F.geometricFrobenius Y₀).inv ^ m) ≫
      (End.of (F.geometricFrobenius Y₀).hom ^ m) = 𝟙 X
    have cancel (e : X ≅ X) (j : ℕ) :
        (End.of e.inv ^ j) ≫ (End.of e.hom ^ j) = 𝟙 X := by
      induction j with
      | zero => simp only [pow_zero, End.one_def, Category.id_comp]
      | succ j ih =>
        rw [pow_succ (End.of e.inv), pow_succ' (End.of e.hom)]
        change (e.inv ≫ (End.of e.inv ^ j)) ≫
          ((End.of e.hom ^ j) ≫ e.hom) = 𝟙 X
        rw [Category.assoc, ← Category.assoc (End.of e.inv ^ j), ih,
          Category.id_comp, e.inv_hom_id]
    exact cancel (F.geometricFrobenius Y₀) m
  have hw : F.schemeFrobeniusIterate Y₀ m =
      X.iterateFrobenius F.prime (finiteFiberCharacteristic F Y₀) (F.a * m) ≫ G := by
    rw [show X.iterateFrobenius F.prime (finiteFiberCharacteristic F Y₀) (F.a * m) =
      F.schemeFrobeniusIterate Y₀ m ≫
        (End.of (F.arithmeticGaloisFrobenius Y₀)) ^ m from h,
      Category.assoc, hi, Category.comp_id]
  simpa only [G, X, geometricFrobeniusGeometry, Iso.pow_hom_eq_pow,
    WeilConjectures.FiniteFieldDatum.geometricGaloisFrobenius] using hw

/-- The normalized condensed comparison: the actual factorization compositor followed
by the relative-Frobenius trivialization at exponent a*m. No comparison is free data.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-def-sf-weil-complexes/prop-trf-scheme-galois-comparison.proof.md`
(blueprint: lem-trf-condensed-scheme-galois-comparison-add). -/
noncomputable def schemeGaloisComparisonFunctor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (m : ℕ) (hm : 1 ≤ m) :
    (L Λ (F.schemeFrobeniusIterate Y₀ m)) ≅
      (L Λ
        ((geometricFrobeniusGeometry F Y₀).h.pow m).hom) := by
  let g := ((geometricFrobeniusGeometry F Y₀).h.pow m).hom
  let H := (F.geometricFiber Y₀).left.iterateFrobenius F.prime
    (finiteFiberCharacteristic F Y₀) (F.a * m)
  let t := Functor.leftDerivedFunctorIdIso
    (upperStarIterateFrobeniusIso Λ F.prime (finiteFiberCharacteristic F Y₀) (F.a * m))
  exact eqToIso (congrArg (L Λ) (finiteComparisonFactorization F Y₀ m hm)) ≪≫
    leftDerivedUpperStarComp Λ H g ≪≫
    Functor.isoWhiskerLeft (L Λ g) t ≪≫ Functor.rightUnitor _

/-- The reviewed finite-quotient specialization of the coefficient-independent
factorization/compositor/trivialization construction.
Source: prop-trf-scheme-galois-comparison (blueprint: prop-trf-scheme-galois-comparison). -/
noncomputable def finiteSchemeGaloisComparisonFunctor
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (n : ℕ) (_hn : 1 ≤ n)
    (m : ℕ) (hm : 1 ≤ m) :
    (L (finiteCoefficient ell E n) (F.schemeFrobeniusIterate Y₀ m)) ≅
      (L (finiteCoefficient ell E n)
        ((geometricFrobeniusGeometry F Y₀).h.pow m).hom) :=
  schemeGaloisComparisonFunctor (finiteCoefficient ell E n) F Y₀ m hm

private lemma moduleFrobenius_add (m n : ℕ) :
    upperStarCongr Λ (iterateFrobenius_add hp X hX m n) ≪≫
      upperStarComp Λ (X.iterateFrobenius hp hX m) (X.iterateFrobenius hp hX n) ≪≫
      Functor.isoWhiskerRight (upperStarIterateFrobeniusIso Λ hp hX n) _ ≪≫
      Functor.leftUnitor _ ≪≫ upperStarIterateFrobeniusIso Λ hp hX m =
      upperStarIterateFrobeniusIso Λ hp hX (m + n) := by
  apply Iso.ext
  apply (conjugateEquiv Adjunction.id (upperStarLowerStarAdjunction Λ _)).injective
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom]
  rw [← conjugateEquiv_comp _
      (upperStarLowerStarAdjunction Λ (X.iterateFrobenius hp hX m ≫
        X.iterateFrobenius hp hX n)),
    ← conjugateEquiv_comp _ ((upperStarLowerStarAdjunction Λ _).comp
      (upperStarLowerStarAdjunction Λ (X.iterateFrobenius hp hX m))),
    ← conjugateEquiv_comp _ (Adjunction.id.comp
      (upperStarLowerStarAdjunction Λ (X.iterateFrobenius hp hX m))),
    ← conjugateEquiv_comp _ (upperStarLowerStarAdjunction Λ (X.iterateFrobenius hp hX m)),
    conjugateEquiv_leftUnitor_hom, conjugateEquiv_whiskerRight]
  have h₁ := congrArg Iso.hom (conjugateIsoEquiv_upperStarComp Λ
    (X.iterateFrobenius hp hX m) (X.iterateFrobenius hp hX n))
  have h₂ := congrArg Iso.hom (conjugateIsoEquiv_upperStarCongr Λ
    (iterateFrobenius_add hp X hX m n))
  simp only [conjugateIsoEquiv_apply_hom] at h₁ h₂
  rw [h₁, h₂]
  refine NatTrans.ext (funext fun M ↦ Mod.hom_ext _ _ ?_)
  simp only [Iso.symm_hom, NatTrans.comp_app, Mod.comp_hom', Functor.rightUnitor_inv_app,
    Functor.whiskerLeft_app,
    conjugateEquiv_upperStarIterateFrobeniusIso_hom_app_hom,
    lowerStarComp_hom_app_hom, lowerStarCongr_inv_app_hom,
    Category.id_comp, Category.assoc, lowerStar_obj_X]
  have h := congrArg (fun e ↦ e.inv.app M.X)
    (ProEtale.lowerStarIterateFrobeniusIso_add Ab.{u + 1} hp hX n m)
  simpa only [Iso.trans_inv, NatTrans.comp_app, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Functor.rightUnitor_inv_app,
    Category.comp_id, Category.id_comp, Category.assoc] using h

private lemma derivedFrobenius_add_raw (m n : ℕ) :
    (Functor.leftDerivedFunctorIdIso
      (upperStarIterateFrobeniusIso Λ hp hX (m + n))).hom =
      ((upperStar Λ (X.iterateFrobenius hp hX (m + n))).leftDerivedFunctorNatIso
        (upperStarCongr Λ (iterateFrobenius_add hp X hX m n))).hom ≫
      ((upperStar Λ (X.iterateFrobenius hp hX m ≫
        X.iterateFrobenius hp hX n)).leftDerivedFunctorNatIso
        (upperStarComp Λ (X.iterateFrobenius hp hX m)
          (X.iterateFrobenius hp hX n))).hom ≫
      ((upperStar Λ (X.iterateFrobenius hp hX n)).leftDerivedFunctorCompIso
        (upperStar Λ (X.iterateFrobenius hp hX m))).hom ≫
      Functor.whiskerRight
        (Functor.leftDerivedFunctorIdIso (upperStarIterateFrobeniusIso Λ hp hX n)).hom
        (upperStar Λ (X.iterateFrobenius hp hX m)).leftDerivedFunctor ≫
      (Functor.leftUnitor _).hom ≫
      (Functor.leftDerivedFunctorIdIso (upperStarIterateFrobeniusIso Λ hp hX m)).hom := by
  exact derivedTrivialization_composite
    (C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (upperStarCongr Λ (iterateFrobenius_add hp X hX m n))
    (upperStarComp Λ (X.iterateFrobenius hp hX m) (X.iterateFrobenius hp hX n))
    (upperStarIterateFrobeniusIso Λ hp hX n)
    (upperStarIterateFrobeniusIso Λ hp hX m)
    (upperStarIterateFrobeniusIso Λ hp hX (m + n))
    (moduleFrobenius_add (X := X) Λ hp hX m n)

private lemma nativeDerived_congr {f g : End X} (e : f = g) :
    (upperStar Λ f).leftDerivedFunctorNatIso (upperStarCongr Λ e) =
      eqToIso (congrArg (L Λ) e) := by
  cases e
  simp only [CondensedRing.upperStarCongr, eqToIso_refl,
    Functor.leftDerivedFunctorNatIso_refl]

private lemma derivedFrobenius_add (m n : ℕ) :
    (Functor.leftDerivedFunctorIdIso
      (upperStarIterateFrobeniusIso Λ hp hX (m + n))).hom =
      eqToHom (congrArg (L Λ) (iterateFrobenius_add hp X hX m n)) ≫
        (leftDerivedUpperStarComp Λ (X.iterateFrobenius hp hX m)
          (X.iterateFrobenius hp hX n)).hom ≫
        Functor.whiskerRight
          (Functor.leftDerivedFunctorIdIso
            (upperStarIterateFrobeniusIso Λ hp hX n)).hom
          (L Λ (X.iterateFrobenius hp hX m)) ≫
        (Functor.leftUnitor _).hom ≫
        (Functor.leftDerivedFunctorIdIso
          (upperStarIterateFrobeniusIso Λ hp hX m)).hom := by
  have hh := derivedFrobenius_add_raw (X := X) Λ hp hX m n
  rw [nativeDerived_congr Λ (iterateFrobenius_add hp X hX m n)] at hh
  simpa only [CondensedRing.leftDerivedUpperStarComp, Iso.trans_hom, eqToIso.hom,
    Category.assoc] using hh

/-- The normalized comparisons form the multiplicative positive-iterate family.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-def-sf-weil-complexes/prop-trf-scheme-galois-comparison.proof.md`.
(blueprint: lem-trf-coefficient-independent-comparison-add).
Proof: relative Frobenius maps compose to the corresponding power map. Apply the
canonical inverse-image compositors and their associativity to the sectionwise
relative-Frobenius trivializations; their unit normalizations identify the result
with the trivialization at exponent a*(m+n). The two scheme powers add exponents. -/
theorem schemeGaloisComparison_add
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (m r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r) :
    let P := fun j => F.schemeFrobeniusIterate Y₀ j
    let G := fun j => ((geometricFrobeniusGeometry F Y₀).h.pow j).hom
    let κ := fun j hj => (schemeGaloisComparisonFunctor Λ F Y₀ j hj).hom
    ∃ hP : P m ≫ P r = P (m + r), ∃ hG : G m ≫ G r = G (m + r),
      κ (m + r) (by omega) =
        eqToHom (congrArg (L Λ) hP.symm) ≫
        (leftDerivedUpperStarComp Λ (P m) (P r)).hom ≫
        Functor.whiskerLeft (L Λ (P r)) (κ m hm) ≫
        Functor.whiskerRight (κ r hr) (L Λ (G m)) ≫
        (leftDerivedUpperStarComp Λ (G m) (G r)).inv ≫
        eqToHom (congrArg (L Λ) hG) := by
  let X := (F.geometricFiber Y₀).left
  let P := fun j ↦ F.schemeFrobeniusIterate Y₀ j
  let G : ℕ → End X := fun j ↦ ((geometricFrobeniusGeometry F Y₀).h.pow j).hom
  let H := fun j ↦ X.iterateFrobenius F.prime (finiteFiberCharacteristic F Y₀) (F.a * j)
  let t : ∀ j, L Λ (H j) ≅ 𝟭 (D Λ X) := fun j ↦ Functor.leftDerivedFunctorIdIso
    (upperStarIterateFrobeniusIso Λ F.prime (finiteFiberCharacteristic F Y₀) (F.a * j))
  have hP : P m ≫ P r = P (m + r) := by
    change ((End.of (F.schemeFrobenius Y₀)) ^ r) *
      ((End.of (F.schemeFrobenius Y₀)) ^ m) =
        (End.of (F.schemeFrobenius Y₀)) ^ (m + r)
    rw [← pow_add, Nat.add_comm]
  have hG : G m ≫ G r = G (m + r) := by
    simp only [G, geometricFrobeniusGeometry, Iso.pow_hom_eq_pow]
    change ((End.of (F.geometricFrobenius Y₀).hom) ^ r) *
      ((End.of (F.geometricFrobenius Y₀).hom) ^ m) =
        (End.of (F.geometricFrobenius Y₀).hom) ^ (m + r)
    rw [← pow_add, Nat.add_comm]
  have hH : H m ≫ H r = H (m + r) := by
    dsimp [H]
    rw [Nat.mul_add, Scheme.iterateFrobenius_add]
  have comm : H r ≫ G m = G m ≫ H r :=
    (Scheme.comp_iterateFrobenius F.prime (G m)
      (finiteFiberCharacteristic F Y₀) (finiteFiberCharacteristic F Y₀) (F.a * r)).symm
  have ht : (t (m + r)).hom = eqToHom (congrArg (L Λ) hH.symm) ≫
      (leftDerivedUpperStarComp Λ (H m) (H r)).hom ≫
      Functor.whiskerLeft (L Λ (H r)) (t m).hom ≫
      (Functor.rightUnitor _).hom ≫ (t r).hom := by
    have add (k : ℕ) (e : k = F.a * m + F.a * r)
        (he : X.iterateFrobenius F.prime (finiteFiberCharacteristic F Y₀) k =
          H m ≫ H r) :
        (Functor.leftDerivedFunctorIdIso
          (upperStarIterateFrobeniusIso Λ F.prime (finiteFiberCharacteristic F Y₀) k)).hom =
          eqToHom (congrArg (L Λ) he) ≫
          (leftDerivedUpperStarComp Λ (H m) (H r)).hom ≫
          Functor.whiskerRight (t r).hom (L Λ (H m)) ≫
          (Functor.leftUnitor _).hom ≫ (t m).hom := by
      subst k
      simpa only [H, t, X, WeilConjectures.FiniteFieldDatum.geometricFiber,
        Over.pullback_obj_left] using
        derivedFrobenius_add (X := X) Λ F.prime
        (finiteFiberCharacteristic F Y₀) (F.a * m) (F.a * r)
    have hh := add (F.a * (m + r)) (Nat.mul_add F.a m r) hH.symm
    change (t (m + r)).hom = _ at hh
    rw [hh]
    simpa only [Category.assoc] using congrArg
      (fun w ↦ eqToHom (congrArg (L Λ) hH.symm) ≫
        (leftDerivedUpperStarComp Λ (H m) (H r)).hom ≫ w)
      (trivialization_interchange (t m) (t r))
  have hnaturality : (leftDerivedUpperStarComp Λ (G m) (H r)).inv ≫
      eqToHom (congrArg (L Λ) comm.symm) ≫
      (leftDerivedUpperStarComp Λ (H r) (G m)).hom ≫
      Functor.whiskerLeft (L Λ (G m)) (t r).hom ≫ (Functor.rightUnitor _).hom =
      Functor.whiskerRight (t r).hom (L Λ (G m)) ≫ (Functor.leftUnitor _).hom := by
    apply NatTrans.ext
    funext K
    have hh := leftDerivedUpperStarComp_hom_app_comp_map_upperStarIterateFrobeniusIso
      Λ F.prime (finiteFiberCharacteristic F Y₀) (finiteFiberCharacteristic F Y₀)
      (F.a * r) (G m) K
    change (leftDerivedUpperStarComp Λ (G m) (H r)).hom.app K ≫
      (L Λ (G m)).map ((t r).hom.app K) =
      eqToHom _ ≫ (leftDerivedUpperStarComp Λ (H r) (G m)).hom.app K ≫
        (t r).hom.app ((L Λ (G m)).obj K) at hh
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.rightUnitor_hom_app, Functor.leftUnitor_hom_app,
      Functor.comp_obj, Functor.id_obj, Category.comp_id, eqToHom_app]
    calc
      (leftDerivedUpperStarComp Λ (G m) (H r)).inv.app K ≫
          eqToHom _ ≫ (leftDerivedUpperStarComp Λ (H r) (G m)).hom.app K ≫
            (t r).hom.app ((L Λ (G m)).obj K) =
        (leftDerivedUpperStarComp Λ (G m) (H r)).inv.app K ≫
          ((leftDerivedUpperStarComp Λ (G m) (H r)).hom.app K ≫
            (L Λ (G m)).map ((t r).hom.app K)) := by rw [hh]
      _ = (L Λ (G m)).map ((t r).hom.app K) := by
        exact Iso.inv_hom_id_app_assoc _ _ _
  refine ⟨hP, hG, ?_⟩
  have h := factorizationComparison_multiplicative
    (B := Scheme.{u}) (X := X) (C := D Λ X)
    (fun f : End X ↦ L Λ f) (fun f g ↦ leftDerivedUpperStarComp Λ f g)
    (fun f g h K ↦ by
      have hh := leftDerivedUpperStarComp_assoc_app Λ f g h K
      have hr := reverse_transport
        (congrArg (fun w ↦ (L Λ w).obj K) (Category.assoc f g h)) hh
      simpa only [eqToIso.hom, eqToHom_app, Category.assoc] using hr)
    (H m) (H r) (H (m + r)) (G m) (G r) (G (m + r))
    (P m) (P r) (P (m + r))
    (finiteComparisonFactorization F Y₀ m hm)
    (finiteComparisonFactorization F Y₀ r hr)
    (finiteComparisonFactorization F Y₀ (m + r) (by omega))
    hP hG hH comm (t m) (t r) (t (m + r)) ht hnaturality
  simpa only [P, G, H, t, X, WeilConjectures.FiniteFieldDatum.geometricFiber,
    Over.pullback_obj_left,
    schemeGaloisComparisonFunctor, factorizationComparison,
    Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, Category.assoc] using h

/-- The normalized comparisons form the multiplicative positive-iterate family.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-def-sf-weil-complexes/prop-trf-scheme-galois-comparison.proof.md`.
(blueprint: lem-trf-condensed-scheme-galois-comparison-add).
Proof: relative Frobenius maps compose to the corresponding power map. Apply the
canonical inverse-image compositors and their associativity to the sectionwise
relative-Frobenius trivializations; their unit normalizations identify the result
with the trivialization at exponent a*(m+n). The two scheme powers add exponents. -/
theorem finiteSchemeGaloisComparison_add
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ F.p) (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (n : ℕ) (hn : 1 ≤ n) (m r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r) :
    let Λ := finiteCoefficient ell E n
    let P := fun j => F.schemeFrobeniusIterate Y₀ j
    let G := fun j => ((geometricFrobeniusGeometry F Y₀).h.pow j).hom
    let κ := fun j hj => (finiteSchemeGaloisComparisonFunctor F Y₀ ell E n hn j hj).hom
    ∃ hP : P m ≫ P r = P (m + r), ∃ hG : G m ≫ G r = G (m + r),
      κ (m + r) (by omega) =
        eqToHom (congrArg (L Λ) hP.symm) ≫
        (leftDerivedUpperStarComp Λ (P m) (P r)).hom ≫
        Functor.whiskerLeft (L Λ (P r)) (κ m hm) ≫
        Functor.whiskerRight (κ r hr) (L Λ (G m)) ≫
        (leftDerivedUpperStarComp Λ (G m) (G r)).inv ≫
        eqToHom (congrArg (L Λ) hG) := by
  let Λ := finiteCoefficient ell E n
  let X := (F.geometricFiber Y₀).left
  let P := fun j ↦ F.schemeFrobeniusIterate Y₀ j
  let G : ℕ → End X := fun j ↦ ((geometricFrobeniusGeometry F Y₀).h.pow j).hom
  let H := fun j ↦ X.iterateFrobenius F.prime (finiteFiberCharacteristic F Y₀) (F.a * j)
  let t : ∀ j, L Λ (H j) ≅ 𝟭 (D Λ X) := fun j ↦ Functor.leftDerivedFunctorIdIso
    (upperStarIterateFrobeniusIso Λ F.prime (finiteFiberCharacteristic F Y₀) (F.a * j))
  have hP : P m ≫ P r = P (m + r) := by
    change ((End.of (F.schemeFrobenius Y₀)) ^ r) *
      ((End.of (F.schemeFrobenius Y₀)) ^ m) =
        (End.of (F.schemeFrobenius Y₀)) ^ (m + r)
    rw [← pow_add, Nat.add_comm]
  have hG : G m ≫ G r = G (m + r) := by
    simp only [G, geometricFrobeniusGeometry, Iso.pow_hom_eq_pow]
    change ((End.of (F.geometricFrobenius Y₀).hom) ^ r) *
      ((End.of (F.geometricFrobenius Y₀).hom) ^ m) =
        (End.of (F.geometricFrobenius Y₀).hom) ^ (m + r)
    rw [← pow_add, Nat.add_comm]
  have hH : H m ≫ H r = H (m + r) := by
    dsimp [H]
    rw [Nat.mul_add, Scheme.iterateFrobenius_add]
  have comm : H r ≫ G m = G m ≫ H r :=
    (Scheme.comp_iterateFrobenius F.prime (G m)
      (finiteFiberCharacteristic F Y₀) (finiteFiberCharacteristic F Y₀) (F.a * r)).symm
  have ht : (t (m + r)).hom = eqToHom (congrArg (L Λ) hH.symm) ≫
      (leftDerivedUpperStarComp Λ (H m) (H r)).hom ≫
      Functor.whiskerLeft (L Λ (H r)) (t m).hom ≫
      (Functor.rightUnitor _).hom ≫ (t r).hom := by
    have add (k : ℕ) (e : k = F.a * m + F.a * r)
        (he : X.iterateFrobenius F.prime (finiteFiberCharacteristic F Y₀) k =
          H m ≫ H r) :
        (Functor.leftDerivedFunctorIdIso
          (upperStarIterateFrobeniusIso Λ F.prime (finiteFiberCharacteristic F Y₀) k)).hom =
          eqToHom (congrArg (L Λ) he) ≫
          (leftDerivedUpperStarComp Λ (H m) (H r)).hom ≫
          Functor.whiskerRight (t r).hom (L Λ (H m)) ≫
          (Functor.leftUnitor _).hom ≫ (t m).hom := by
      subst k
      simpa only [H, t, X, WeilConjectures.FiniteFieldDatum.geometricFiber,
        Over.pullback_obj_left] using
        derivedFrobenius_add (X := X) Λ F.prime
        (finiteFiberCharacteristic F Y₀) (F.a * m) (F.a * r)
    have hh := add (F.a * (m + r)) (Nat.mul_add F.a m r) hH.symm
    change (t (m + r)).hom = _ at hh
    rw [hh]
    simpa only [Category.assoc] using congrArg
      (fun w ↦ eqToHom (congrArg (L Λ) hH.symm) ≫
        (leftDerivedUpperStarComp Λ (H m) (H r)).hom ≫ w)
      (trivialization_interchange (t m) (t r))
  have hnaturality : (leftDerivedUpperStarComp Λ (G m) (H r)).inv ≫
      eqToHom (congrArg (L Λ) comm.symm) ≫
      (leftDerivedUpperStarComp Λ (H r) (G m)).hom ≫
      Functor.whiskerLeft (L Λ (G m)) (t r).hom ≫ (Functor.rightUnitor _).hom =
      Functor.whiskerRight (t r).hom (L Λ (G m)) ≫ (Functor.leftUnitor _).hom := by
    apply NatTrans.ext
    funext K
    have hh := leftDerivedUpperStarComp_hom_app_comp_map_upperStarIterateFrobeniusIso
      Λ F.prime (finiteFiberCharacteristic F Y₀) (finiteFiberCharacteristic F Y₀)
      (F.a * r) (G m) K
    change (leftDerivedUpperStarComp Λ (G m) (H r)).hom.app K ≫
      (L Λ (G m)).map ((t r).hom.app K) =
      eqToHom _ ≫ (leftDerivedUpperStarComp Λ (H r) (G m)).hom.app K ≫
        (t r).hom.app ((L Λ (G m)).obj K) at hh
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.rightUnitor_hom_app, Functor.leftUnitor_hom_app,
      Functor.comp_obj, Functor.id_obj, Category.comp_id, eqToHom_app]
    calc
      (leftDerivedUpperStarComp Λ (G m) (H r)).inv.app K ≫
          eqToHom _ ≫ (leftDerivedUpperStarComp Λ (H r) (G m)).hom.app K ≫
            (t r).hom.app ((L Λ (G m)).obj K) =
        (leftDerivedUpperStarComp Λ (G m) (H r)).inv.app K ≫
          ((leftDerivedUpperStarComp Λ (G m) (H r)).hom.app K ≫
            (L Λ (G m)).map ((t r).hom.app K)) := by rw [hh]
      _ = (L Λ (G m)).map ((t r).hom.app K) := by
        exact Iso.inv_hom_id_app_assoc _ _ _
  refine ⟨hP, hG, ?_⟩
  have h := factorizationComparison_multiplicative
    (B := Scheme.{u}) (X := X) (C := D Λ X)
    (fun f : End X ↦ L Λ f) (fun f g ↦ leftDerivedUpperStarComp Λ f g)
    (fun f g h K ↦ by
      have hh := leftDerivedUpperStarComp_assoc_app Λ f g h K
      have hr := reverse_transport
        (congrArg (fun w ↦ (L Λ w).obj K) (Category.assoc f g h)) hh
      simpa only [eqToIso.hom, eqToHom_app, Category.assoc] using hr)
    (H m) (H r) (H (m + r)) (G m) (G r) (G (m + r))
    (P m) (P r) (P (m + r))
    (finiteComparisonFactorization F Y₀ m hm)
    (finiteComparisonFactorization F Y₀ r hr)
    (finiteComparisonFactorization F Y₀ (m + r) (by omega))
    hP hG hH comm (t m) (t r) (t (m + r)) ht hnaturality
  simpa only [P, G, H, t, Λ, X, WeilConjectures.FiniteFieldDatum.geometricFiber,
    Over.pullback_obj_left,
    finiteSchemeGaloisComparisonFunctor, schemeGaloisComparisonFunctor, factorizationComparison,
    Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, Category.assoc] using h

/-- Evaluation of the normalized natural comparison on a finite strict Weil carrier.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-frobenius/
sk-def-sf-weil-complexes/prop-trf-scheme-galois-comparison.proof.md`.
(blueprint: prop-trf-scheme-galois-comparison). -/
noncomputable def finiteSchemeGaloisComparison
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ F.p) (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (n : ℕ) (hn : 1 ≤ n) (K : FiniteStrictWeilComplex F Y₀ ell E n hn)
    (m : ℕ) (hm : 1 ≤ m) :
    (L (finiteCoefficient ell E n) (F.schemeFrobeniusIterate Y₀ m)).obj K.carrier.obj ≅
      (L (finiteCoefficient ell E n)
        ((geometricFrobeniusGeometry F Y₀).h.pow m).hom).obj K.carrier.obj :=
  (finiteSchemeGaloisComparisonFunctor F Y₀ ell E n hn m hm).app K.carrier.obj

end WeilConjectures.CondensedFrobeniusOperators
