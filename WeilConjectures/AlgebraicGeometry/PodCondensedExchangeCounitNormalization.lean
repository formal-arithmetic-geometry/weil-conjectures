/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DetThmSfCtfStabilityInternalHom
public import WeilConjectures.AlgebraicGeometry.PodCtfAdjunctions
public import WeilConjectures.AlgebraicGeometry.CompletedCondensedCoefficients
public import WeilConjectures.SixFunctors.CondensedCompactSupportComposition
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.PoincareDuality.Abstract
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingInputs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ModCondensedCachedInstances

/-! Native condensed tensor--Hom exchange and identity-point normalization.
Source: latest blueprint, thm-pod-identification-of-the-comparison.proof.md,
paragraphs two and three and final inverse identification
(blueprint: lem-pod-condensed-exchange-counit-normalization). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Preservation certificates for the actual native operations. The exceptional
functor is a right adjoint of the actual restricted compact-support functor, hence
is determined together with its counit up to unique compatible isomorphism.
Source: restricted adjunctions (blueprint: lem-pod-condensed-exchange-counit-normalization). -/
structure NativeRestrictions {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) where
  pull_mem : ∀ K, dctfPred Λ Y K →
    dctfPred Λ X ((upperStar Λ f).leftDerivedFunctor.obj K)
  direct_mem : ∀ K, dctfPred Λ X K →
    dctfPred Λ Y ((lowerStar Λ f).rightDerivedFunctor.obj K)
  support_mem : ∀ K, dctfPred Λ X K →
    dctfPred Λ Y ((rightDerivedLowerShriekOfCompactification Λ c).obj K)
  tensor_mem : ∀ (Z : Scheme.{u}), (Z = X ∨ Z = Y) →
    ∀ K L, dctfPred Λ Z K → dctfPred Λ Z L →
      dctfPred Λ Z (((derivedTensor Λ Z).obj K).obj L)
  hom_mem : ∀ (Z : Scheme.{u}), (Z = X ∨ Z = Y) →
    ∀ K L, dctfPred Λ Z K → dctfPred Λ Z L →
      dctfPred Λ Z (((derivedHom Λ Z).obj (op K)).obj L)
  exceptional : (dctfPred Λ Y).FullSubcategory ⥤ (dctfPred Λ X).FullSubcategory
  adj : (dctfPred Λ Y).lift
      ((dctfPred Λ X).ι ⋙ rightDerivedLowerShriekOfCompactification Λ c)
      (fun K => support_mem K.obj K.property) ⊣ exceptional

namespace NativeRestrictions
variable {Λ} {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  (R : NativeRestrictions Λ c)

/-- Actual restricted pullback. Source: ordinary adjunction
(blueprint: lem-pod-condensed-exchange-counit-normalization). -/
def pull := (dctfPred Λ X).lift
  ((dctfPred Λ Y).ι ⋙ (upperStar Λ f).leftDerivedFunctor)
  (fun K => R.pull_mem K.obj K.property)
/-- Actual restricted direct image. Source: ordinary adjunction
(blueprint: lem-pod-condensed-exchange-counit-normalization). -/
def direct := (dctfPred Λ Y).lift
  ((dctfPred Λ X).ι ⋙ (lowerStar Λ f).rightDerivedFunctor)
  (fun K => R.direct_mem K.obj K.property)
/-- Actual restricted compact-support functor. Source: exceptional adjunction
(blueprint: lem-pod-condensed-exchange-counit-normalization). -/
def support := (dctfPred Λ Y).lift
  ((dctfPred Λ X).ι ⋙ rightDerivedLowerShriekOfCompactification Λ c)
  (fun K => R.support_mem K.obj K.property)
/-- The ordinary adjunction with exactly its ambient units and counits.
Source: restricted adjunctions (blueprint: lem-pod-condensed-exchange-counit-normalization). -/
def ordinaryAdj : R.pull ⊣ R.direct :=
  (derivedUpperStarLowerStarAdjunction Λ f).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (Iso.refl _) (Iso.refl _)
/-- Left tensor restricted by full inclusion. Source: closed adjunction
(blueprint: lem-pod-condensed-exchange-counit-normalization). -/
def tensor (Z : Scheme.{u}) (hZ : Z = X ∨ Z = Y) (K : (dctfPred Λ Z).FullSubcategory) :=
  (dctfPred Λ Z).lift ((dctfPred Λ Z).ι ⋙ (derivedTensor Λ Z).obj K.obj)
    (fun L => R.tensor_mem Z hZ K.obj L.obj K.property L.property)
/-- Internal Hom restricted by full inclusion. Source: closed adjunction
(blueprint: lem-pod-condensed-exchange-counit-normalization). -/
def hom (Z : Scheme.{u}) (hZ : Z = X ∨ Z = Y) (K : (dctfPred Λ Z).FullSubcategory) :=
  (dctfPred Λ Z).lift ((dctfPred Λ Z).ι ⋙ (derivedHom Λ Z).obj (op K.obj))
    (fun L => R.hom_mem Z hZ K.obj L.obj K.property L.property)
/-- Restricted left-tensor--Hom adjunction; its evaluation is the ambient evaluation.
Source: specified closed adjunction (blueprint: lem-pod-condensed-exchange-counit-normalization). -/
def closedAdj (Z : Scheme.{u}) (hZ : Z = X ∨ Z = Y) (K : (dctfPred Λ Z).FullSubcategory) :
    R.tensor Z hZ K ⊣ R.hom Z hZ K :=
  (derivedTensorHomAdjunction Λ K.obj).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (Iso.refl _) (Iso.refl _)
/-- The native forward compact-support projection, on the full finite-Tor domain.
Source: fourth arrow (blueprint: lem-pod-condensed-exchange-counit-normalization). -/
def projection (M : (dctfPred Λ X).FullSubcategory)
    (T : (dctfPred Λ Y).FullSubcategory) :
    (R.tensor Y (Or.inr rfl) (R.support.obj M)).obj T ⟶
      R.support.obj ((R.tensor X (Or.inl rfl) M).obj (R.pull.obj T)) :=
  ObjectProperty.homMk (exceptionalProjectionMorphismOfCompactification Λ c M.obj T.obj)
/-- Source functor D=Rf_*RHom(M,Rf^!-). Source: displayed objects
(blueprint: lem-pod-condensed-exchange-counit-normalization). -/
def source (M : (dctfPred Λ X).FullSubcategory) :=
  R.exceptional ⋙ R.hom X (Or.inl rfl) M ⋙ R.direct
/-- Target functor H=RHom(Rf_!M,-). Source: displayed objects
(blueprint: lem-pod-condensed-exchange-counit-normalization). -/
def target (M : (dctfPred Λ X).FullSubcategory) := R.hom Y (Or.inr rfl) (R.support.obj M)
/-- The literal counit--evaluation pairing p in the statement.
Source: third paragraph (blueprint: lem-pod-condensed-exchange-counit-normalization). -/
def pairing (M : (dctfPred Λ X).FullSubcategory)
    (N : (dctfPred Λ Y).FullSubcategory) :
    (R.tensor Y (Or.inr rfl) (R.support.obj M)).obj ((R.source M).obj N) ⟶ N :=
  R.projection M ((R.source M).obj N) ≫
    R.support.map ((R.tensor X (Or.inl rfl) M).map
      (R.ordinaryAdj.counit.app ((R.hom X (Or.inl rfl) M).obj (R.exceptional.obj N))) ≫
        (R.closedAdj X (Or.inl rfl) M).counit.app (R.exceptional.obj N)) ≫ R.adj.counit.app N
/-- The actual tensor--Hom transpose of p. Source: alpha=curry(p)
(blueprint: lem-pod-condensed-exchange-counit-normalization). -/
def alpha (M : (dctfPred Λ X).FullSubcategory)
    (N : (dctfPred Λ Y).FullSubcategory) :=
  (R.closedAdj Y (Or.inr rfl) (R.support.obj M)).homEquiv _ N (R.pairing M N)
/-- The literal composite of the five arrows, before requiring invertibility.
Source: displayed Hom chain (blueprint: lem-pod-condensed-exchange-counit-normalization). -/
def chain (M : (dctfPred Λ X).FullSubcategory)
    (N T : (dctfPred Λ Y).FullSubcategory) (t : T ⟶ (R.source M).obj N) :=
  (R.closedAdj Y (Or.inr rfl) (R.support.obj M)).homEquiv T N
    (R.projection M T ≫ (R.adj.homEquiv _ N).symm
      (((R.closedAdj X (Or.inl rfl) M).homEquiv _ _).symm
        ((R.ordinaryAdj.homEquiv T _).symm t)))
end NativeRestrictions
end AlgebraicGeometry.ProEtale.CondensedRing

-- These identities are proved for arbitrary categories before specializing to Dctf.
namespace PodPointNormalization
universe uC vC uD vD
section
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  {F : C ⥤ D} {G : D ⥤ C} {S H : D ⥤ D}
  (a : F ⊣ G) (b : S ⊣ H) (e : S ≅ 𝟭 D)
/-- Transporting the left adjoint to the identity makes its counit the
right-adjoint uniqueness comparison. -/
private theorem identityCounit (L : D) :
    ((b.ofNatIsoLeft e).rightAdjointUniq Adjunction.id).hom.app L =
      e.inv.app (H.obj L) ≫ b.counit.app L := by
  have h := (b.ofNatIsoLeft e).rightAdjointUniq_hom_app_counit Adjunction.id L
  simpa [Adjunction.ofNatIsoLeft_counit] using h

/-- The mate of the compact-support unitor is the right adjoint applied to
its identity-adjunction counit comparison. Check this after untransposing. -/
private theorem identityMate (L : D) :
    (conjugateIsoEquiv (a.comp b) a
      (Functor.isoWhiskerLeft F e ≪≫ Functor.rightUnitor F).symm).hom.app L =
      G.map (((b.ofNatIsoLeft e).rightAdjointUniq Adjunction.id).hom.app L) := by
  rw [identityCounit]
  apply (a.homEquiv _ _).symm.injective
  change F.map _ ≫ a.counit.app L = F.map _ ≫ a.counit.app L
  rw [conjugateIsoEquiv_apply_hom, conjugateEquiv_counit]
  simp only [Iso.symm_hom, Iso.trans_inv, Functor.rightUnitor_inv_app,
    Functor.isoWhiskerLeft_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.comp_obj, Category.id_comp, Adjunction.comp_counit_app]
  have hn := e.inv.naturality (a.counit.app (H.obj L))
  dsimp at hn
  rw [← Category.assoc, ← hn, Category.assoc, ← a.counit_naturality]
  rfl
end

/-- A natural square becomes the required square of inverses by cancellation. -/
private theorem inverse_square {C : Type uC} [Category.{vC} C]
    {F G : C ⥤ C} {A B : C} (v : A ⟶ B)
    (a : F.obj A ⟶ G.obj A) (b : F.obj B ⟶ G.obj B) [IsIso b]
    (r : G.obj A ⟶ F.obj A) (hr : r ≫ a = 𝟙 _)
    (hn : F.map v ≫ b = a ≫ G.map v) :
    r ≫ F.map v = G.map v ≫ inv b := by
  apply (cancel_mono b).1
  rw [Category.assoc, hn, ← Category.assoc, hr]
  simp

end PodPointNormalization

namespace AlgebraicGeometry.ProEtale.CondensedRing.NativeRestrictions
variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
  {c : Compactification f} (R : NativeRestrictions Λ c)

/-- The five actual bijections, with the fourth precomposing by the native forward
projection. Source: displayed chain
(blueprint: lem-pod-condensed-exchange-counit-normalization). -/
def homEquiv (hP : ∀ M T, IsIso (R.projection M T))
    (M : (dctfPred Λ X).FullSubcategory)
    (N T : (dctfPred Λ Y).FullSubcategory) :
    (T ⟶ (R.source M).obj N) ≃ (T ⟶ (R.target M).obj N) :=
  letI := hP M T
  ((R.ordinaryAdj.homEquiv T _).symm.trans
    ((R.closedAdj X (Or.inl rfl) M).homEquiv _ _).symm).trans
      (((R.adj.homEquiv _ N).symm.trans
        (Iso.homCongr (asIso (R.projection M T)).symm (Iso.refl N))).trans
          ((R.closedAdj Y (Or.inr rfl) (R.support.obj M)).homEquiv T N))

/-- The reverse tensor--Hom exchange is represented by the inverse of the literal
five-arrow equivalence evaluated at the identity. Source: canonical Verdier exchange
(blueprint: lem-pod-condensed-exchange-counit-normalization). -/
def reverseExchange (hP : ∀ M T, IsIso (R.projection M T))
    (M : (dctfPred Λ X).FullSubcategory)
    (N : (dctfPred Λ Y).FullSubcategory) :
    (R.target M).obj N ⟶ (R.source M).obj N :=
  (R.homEquiv hP M N _).symm (𝟙 _)

/-- The complete exchange assertion, with actual maps, every finite-Tor domain,
and naturality in the coefficient object and the test object. Source: all clauses
before the point specialization
(blueprint: lem-pod-condensed-exchange-counit-normalization). -/
def ExchangeLaws : Prop :=
  ∃ hP : ∀ M T, IsIso (R.projection M T),
    ∀ M : (dctfPred Λ X).FullSubcategory,
      (∀ N, IsIso (R.alpha M N)) ∧
      (∀ N T t, R.homEquiv hP M N T t = t ≫ R.alpha M N) ∧
      (∀ (N T T' : (dctfPred Λ Y).FullSubcategory)
        (a : T' ⟶ T) (t : T ⟶ (R.source M).obj N),
        R.homEquiv hP M N T' (a ≫ t) = a ≫ R.homEquiv hP M N T t) ∧
      (∀ (N N' : (dctfPred Λ Y).FullSubcategory) (v : N ⟶ N'),
        (R.source M).map v ≫ R.alpha M N' =
          R.alpha M N ≫ (R.target M).map v) ∧
      (∀ N, R.reverseExchange hP M N ≫ R.alpha M N = 𝟙 _) ∧
      (∀ N, R.alpha M N ≫ R.reverseExchange hP M N = 𝟙 _)

end AlgebraicGeometry.ProEtale.CondensedRing.NativeRestrictions

namespace AlgebraicGeometry.ProEtale.CondensedRing
open WeilConjectures

/-- Native condensed tensor--Hom exchange with its literal counit representative.
Source: latest blueprint thm-pod-identification-of-the-comparison.proof.md,
second and third paragraphs and final inverse identification
(blueprint: lem-pod-condensed-exchange-counit-normalization).

Proof: the algebraically closed base has ell-cohomological dimension zero. Direct
finite-Tor stability puts pullback, tensor, both direct images and exceptional
inverse image in the stated full categories; internal-Hom stability applies to
both displayed pairs. Restrict the ordinary and closed adjunctions by full
inclusion and the exceptional adjunction on the localizing closure. The native
projection is invertible for the constructible first input and finite-Tor second
input. Composing the five actual Hom equivalences gives the mate isomorphism.
On a map t, their first two steps are ordinary counit after pullback of t and
then evaluation after tensoring by M; the third is compact-support pushforward
and exceptional counit, and the fourth precomposes with the forward projection.
Projection naturality moves t out of this pairing. Target currying then gives
t followed by alpha=curry(p). The units and counits of the same adjunctions
prove naturality in N and T. Reversing the five equivalences on the identity
gives the two inverse identities. All operations remain native to Lambda. -/
theorem pod_condensed_exchange_counit_normalization
    (D : FiniteFieldDatum.{u}) (A : D.CoefficientDatum)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ (E : PadicAlgCl.FiniteIntermediateField A.l)
        (π : PadicAlgCl.integers A.l E) (m : ℕ),
        Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers A.l E) ∧
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
          (completedResidue A.l E π m)))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField A.l,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj A.l E))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField A.l,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj A.l)))
    {X Y : Over (Spec (CommRingCat.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (c : Compactification f.left) :
    Nonempty (NativeRestrictions Λ c) ∧
      ∀ R : NativeRestrictions Λ c, R.ExchangeLaws := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing.NativeRestrictions
variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] {X s : Scheme.{u}} {f : X ⟶ s}
  {c : Compactification f}

/-- The actual unital compact-support comparison on the full finite-Tor category.
Source: unital condensed composition
(blueprint: lem-pod-condensed-exchange-counit-normalization). -/
def identitySupport (R₀ : NativeRestrictions Λ (Compactification.ofIsProper (𝟙 s))) :
    R₀.support ≅ 𝟭 (dctfPred Λ s).FullSubcategory :=
  Functor.fullyFaithfulCancelRight (dctfPred Λ s).ι
    (Functor.isoWhiskerLeft (dctfPred Λ s).ι (CompactSupportComposition.identity Λ s) ≪≫
      Functor.rightUnitor _)

/-- Conjugating the identity compact-support comparison gives precisely the
counit-compatible identity exceptional comparison. Source: identity point
(blueprint: lem-pod-condensed-exchange-counit-normalization). -/
def identityExceptional (R₀ : NativeRestrictions Λ (Compactification.ofIsProper (𝟙 s))) :
    R₀.exceptional ≅ 𝟭 (dctfPred Λ s).FullSubcategory :=
  (R₀.adj.ofNatIsoLeft R₀.identitySupport).rightAdjointUniq Adjunction.id

/-- The exceptional composition comparison for composing f with the identity is
its specified mate, including the actual compact-support unitor.
Source: identity compositor (blueprint: lem-pod-condensed-exchange-counit-normalization). -/
def exceptionalIdentityComposition (R : NativeRestrictions Λ c)
    (R₀ : NativeRestrictions Λ (Compactification.ofIsProper (𝟙 s))) :
    R₀.exceptional ⋙ R.exceptional ≅ R.exceptional :=
  conjugateIsoEquiv (R.adj.comp R₀.adj) R.adj
    (Functor.isoWhiskerLeft R.support R₀.identitySupport ≪≫ Functor.rightUnitor _).symm

/-- Point-normalization equations: the identity counit is u, its exceptional mate
is f^!u with the stated counit equation, and the canonical Verdier exchange is the
inverse five-Hom chain followed by this mate, equal to rho followed by alpha inverse.
Source: final two paragraphs (blueprint: lem-pod-condensed-exchange-counit-normalization). -/
def PointLaws (R : NativeRestrictions Λ c)
    (R₀ : NativeRestrictions Λ (Compactification.ofIsProper (𝟙 s)))
    (L : (dctfPred Λ s).FullSubcategory) : Prop :=
  ∃ hP : ∀ M T, IsIso (R.projection M T),
    let u := R₀.identityExceptional.app L
    let cmp := (R.exceptionalIdentityComposition R₀).hom.app L
    u.hom = (R₀.identitySupport.inv.app (R₀.exceptional.obj L) ≫
      R₀.adj.counit.app L) ∧
    cmp = R.exceptional.map u.hom ∧
    R.support.map cmp ≫ R.adj.counit.app L =
      R.adj.counit.app (R₀.exceptional.obj L) ≫ u.hom ∧
    ∀ M : (dctfPred Λ X).FullSubcategory,
      ∃ hα : IsIso (R.alpha M L),
      letI := hα
      R.reverseExchange hP M (R₀.exceptional.obj L) ≫
        R.direct.map ((R.hom X (Or.inl rfl) M).map cmp) =
      (R.target M).map u.hom ≫ inv (R.alpha M L)

variable (R : NativeRestrictions Λ c)
  (R₀ : NativeRestrictions Λ (Compactification.ofIsProper (𝟙 s)))

private theorem identity_formula (L : (dctfPred Λ s).FullSubcategory) :
    (R₀.identityExceptional.app L).hom =
      R₀.identitySupport.inv.app (R₀.exceptional.obj L) ≫ R₀.adj.counit.app L :=
  PodPointNormalization.identityCounit R₀.adj R₀.identitySupport L
private theorem composition_formula (L : (dctfPred Λ s).FullSubcategory) :
    (R.exceptionalIdentityComposition R₀).hom.app L =
      R.exceptional.map (R₀.identityExceptional.app L).hom :=
  PodPointNormalization.identityMate R.adj R₀.adj R₀.identitySupport L
private theorem point_laws (h : R.ExchangeLaws) (L : (dctfPred Λ s).FullSubcategory) :
    R.PointLaws R₀ L := by
  obtain ⟨hP, h⟩ := h
  refine ⟨hP, identity_formula R₀ L, composition_formula R R₀ L, ?_, ?_⟩
  · rw [composition_formula]
    exact R.adj.counit.naturality (R₀.identityExceptional.app L).hom
  · intro M
    obtain ⟨hi, _, _, hn, hr, _⟩ := h M
    refine ⟨hi L, ?_⟩
    have := hi L
    rw [composition_formula]
    change R.reverseExchange hP M (R₀.exceptional.obj L) ≫
        (R.source M).map (R₀.identityExceptional.app L).hom = _
    exact PodPointNormalization.inverse_square (R₀.identityExceptional.app L).hom
      (R.alpha M (R₀.exceptional.obj L)) (R.alpha M L)
      (R.reverseExchange hP M (R₀.exceptional.obj L))
      (hr (R₀.exceptional.obj L)) (hn _ _ (R₀.identityExceptional.app L).hom)

end AlgebraicGeometry.ProEtale.CondensedRing.NativeRestrictions

namespace AlgebraicGeometry.ProEtale.CondensedRing
open WeilConjectures

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

open scoped ZeroObject

private abbrev nativeModules (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)

omit [IsCommMonObj Λ] in
private theorem regular_finitelyPresented : Mod.IsFinitelyPresented Λ (Mod.regular Λ) := by
  let e : Mod.finiteFree Λ 1 ≅ Mod.regular Λ := biproductUniqueIso _
  exact ⟨1, 0, 0, ⟨e.symm ≪≫ (cokernelZeroIsoTarget (X := Mod.finiteFree Λ 0)).symm⟩⟩

omit [IsCommMonObj Λ] in
private theorem zero_finitelyPresented : Mod.IsFinitelyPresented Λ (0 : Mod _ Λ) := by
  exact ⟨0, 0, 𝟙 _, ⟨(isZero_zero _).iso (isZero_cokernel_of_epi (𝟙 _))⟩⟩

private instance pointBraided (X : Scheme.{u}) :
    (upperStarFromPoint X).Braided where
  toMonoidal := inferInstance
  braided := Functor.LaxBraided.braided

private theorem model_regular {X S : Scheme.{u}} (f : X ⟶ S) :
    HasFiniteConstantLocalModel Λ X
      ((CondensedRing.upperStar Λ f).obj (Mod.regular (condensedRingObj Λ S))) := by
  refine ⟨.singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨Mod.regular Λ, regular_finitelyPresented Λ, ⟨?_⟩⟩
  exact (CondensedRing.upperStar Λ (𝟙 X)).mapIso
      (Functor.Monoidal.εIso (CondensedRing.upperStar Λ f)).symm ≪≫
    (Functor.Monoidal.εIso (CondensedRing.upperStar Λ (𝟙 X))).symm ≪≫
    Functor.Monoidal.εIso ((upperStarFromPoint X).mapMod Λ)

private theorem model_zero {X S : Scheme.{u}} (f : X ⟶ S) :
    HasFiniteConstantLocalModel Λ X
      ((CondensedRing.upperStar Λ f).obj (0 : nativeModules Λ S)) := by
  refine ⟨.singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨0, zero_finitelyPresented Λ, ⟨?_⟩⟩
  exact ((CondensedRing.upperStar Λ (𝟙 X)).map_isZero
    ((CondensedRing.upperStar Λ f).map_isZero (isZero_zero _))).iso
      (((upperStarFromPoint X).mapMod Λ).map_isZero (isZero_zero _))

private def oneStratum (X : Scheme.{u}) : Scheme.Stratification X :=
  { n := 1
    stratum := fun _ ↦ Set.univ
    isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
    isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
    iUnion_stratum_eq_univ := Set.iUnion_const _
    pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
    domain := fun _ ↦ X
    immersion := fun _ ↦ 𝟙 X
    range_immersion := fun _ ↦ Set.range_id' }

private theorem regular_constructible (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    IsConstantModelConstructible Λ X (Mod.regular (condensedRingObj Λ X)) := by
  have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  rw [IsConstantModelConstructible, if_pos hX]
  exact ⟨oneStratum X, fun _ ↦ model_regular Λ (𝟙 X)⟩

private theorem zero_constructible (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    IsConstantModelConstructible Λ X (0 : nativeModules Λ X) := by
  have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  rw [IsConstantModelConstructible, if_pos hX]
  exact ⟨oneStratum X, fun _ ↦ model_zero Λ (𝟙 X)⟩

set_option maxHeartbeats 800000 in
-- The homology comparison elaborates through the internal module category.
/-- The coefficient sheaf in degree zero has a finite constant model.
Source: the coefficient-unit assertion in proof step 1
(blueprint: lem-pod-condensed-exchange-counit-normalization).
Proof: use the one-stratum partition and the identity cover. The scalar model is the
regular coefficient module, with its rank-one finite presentation. Monoidality of
inverse image identifies both pullbacks of this regular module. The single complex
is bounded, has this module as its zeroth cohomology and zero cohomology otherwise. -/
private theorem coefficientUnit_boundedConstructible (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    constantModelBoundedConstructible Λ X
      ((DerivedCategory.singleFunctor (nativeModules Λ X) 0).obj
        (Mod.regular (condensedRingObj Λ X))) := by
  let C := nativeModules Λ X
  have := (constantModelConstructibleFiniteTor_wellDefined Λ X).1
  refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app _).symm
      (regular_constructible Λ X)
  · have hz : IsZero ((DerivedCategory.homologyFunctor C n).obj
        ((DerivedCategory.singleFunctor (nativeModules Λ X) 0).obj
          (Mod.regular (condensedRingObj Λ X)))) := by
      rcases lt_or_gt_of_ne hn with h | h
      · exact (DerivedCategory.isGE_iff ((DerivedCategory.singleFunctor (nativeModules Λ X) 0).obj
        (Mod.regular (condensedRingObj Λ X))) 0).1 inferInstance n h
      · exact (DerivedCategory.isLE_iff ((DerivedCategory.singleFunctor (nativeModules Λ X) 0).obj
        (Mod.regular (condensedRingObj Λ X))) 0).1 inferInstance n h
    exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X)
      ((isZero_zero _).iso hz) (zero_constructible Λ X)

/-- The derived unit is the regular module in degree zero. Its tensor with
any degree-zero module is that module, so the Tor interval is [0,0]. -/
private theorem native_unit_mem (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    dctfPred Λ X (𝟙_ (moduleDerived Λ X)) := by
  let C := nativeModules Λ X
  have hb := coefficientUnit_boundedConstructible Λ X
  have := (constantModelConstructibleFiniteTor_wellDefined Λ X).2.1
  refine ⟨(constantModelBoundedConstructible Λ X).prop_of_iso
    (DerivedCategory.singleFunctorObjUnitIso C) hb, 0, 0, ?_⟩
  intro N
  exact (DerivedCategory.homologyConcentratedIn 0 0).prop_of_iso
    (λ_ ((DerivedCategory.singleFunctor C 0).obj N)).symm
    ⟨inferInstance, inferInstance⟩

/-- Identity-point normalization of the same native tensor--Hom exchange.
The coefficient unit is the monoidal unit in the ordinary derived module category.
Source: blueprint proof, final inverse identification
(blueprint: lem-pod-condensed-exchange-counit-normalization).

Proof: the constant free rank-one coefficient module has Tor amplitude [0,0]
and is constructible. The compact-support identity comparison is unital.
Conjugating it with the exceptional and identity adjunctions gives the canonical
isomorphism u, whose component is the exceptional counit after the left identity
comparison. Mate pasting identifies the exceptional composition comparison c
with f^!u; its counit equation is the composite-counit formula. The Verdier map
is the inverse five-Hom exchange at omega_s followed by f_*RHom(M,c).
Naturality of alpha for u gives alpha_Lambda J = rho alpha_omega, and multiplying
by the two inverses proves e = rho followed by alpha_Lambda inverse. -/
theorem pod_condensed_exchange_point_normalization
    (D : FiniteFieldDatum.{u}) (A : D.CoefficientDatum)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ (E : PadicAlgCl.FiniteIntermediateField A.l)
        (π : PadicAlgCl.integers A.l E) (m : ℕ),
        Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers A.l E) ∧
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
          (completedResidue A.l E π m)))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField A.l,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj A.l E))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField A.l,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj A.l)))
    (X : Over (Spec (CommRingCat.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (c : Compactification X.hom)
    (R : NativeRestrictions Λ c)
    (R₀ : NativeRestrictions Λ
      (Compactification.ofIsProper (𝟙 (Spec (CommRingCat.of D.k))))) :
    ∃ hL : dctfPred Λ (Spec (CommRingCat.of D.k))
        (𝟙_ (moduleDerived Λ (Spec (CommRingCat.of D.k)))),
      R.PointLaws R₀ ⟨_, hL⟩ := by
  refine ⟨native_unit_mem Λ _, ?_⟩
  let Y : Over (Spec (CommRingCat.of D.k)) := Over.mk (𝟙 _)
  let : LocallyOfFiniteType Y.hom := inferInstanceAs (LocallyOfFiniteType (𝟙 _))
  let : QuasiCompact Y.hom := inferInstanceAs (QuasiCompact (𝟙 _))
  let : IsSeparated Y.hom := inferInstanceAs (IsSeparated (𝟙 _))
  let f : X ⟶ Y := Over.homMk X.hom
  let : LocallyOfFiniteType f.left := inferInstanceAs (LocallyOfFiniteType X.hom)
  let : QuasiCompact f.left := inferInstanceAs (QuasiCompact X.hom)
  let : IsSeparated f.left := inferInstanceAs (IsSeparated X.hom)
  have h : R.ExchangeLaws :=
    (pod_condensed_exchange_counit_normalization D A Λ hΛ f c).2 R
  exact NativeRestrictions.point_laws R R₀ h _
end AlgebraicGeometry.ProEtale.CondensedRing
