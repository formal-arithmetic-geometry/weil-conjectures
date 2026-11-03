/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.SixFunctors.Etale.EtaleFiniteCoefficientHomArrow
public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientSiteHomArrow
public import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescentData
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom

import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomEtaleIso
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomDomainCalculus
import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescent
import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomIntrinsicTensorComposition
import all WeilConjectures.SixFunctors.Etale.EtaleFiniteCoefficientHomArrow
import all WeilConjectures.SixFunctors.Finite.Hom.FiniteHomSiteEquationDescent
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomComparisonTower

/-! # Constructible internal Hom and finite coefficient change

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-tower/thm-coef-finite-hom.md
(blueprint: thm-coef-finite-hom).

The indices `n`, `m`, `r` denote the positive exponents `n + 1`, `m + 1`, `r + 1`.
The finite coefficient constructions are the published evaluation transposes on the
ordinary derived categories of the two small sites. The pro-etale presentation uses
modules over the constant ring sheaf, without derived completion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u a b c d e f

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

private theorem prod_isIso
    {C : Type a} {D : Type b} [Category.{c} C] [Category.{d} D]
    {X Y : C} {U V : D} (f : X ⟶ Y) (g : U ⟶ V) [IsIso f] [IsIso g] :
    IsIso (Prod.mkHom f g) :=
  (isIso_prod_iff (f := Prod.mkHom f g)).mpr ⟨inferInstance, inferInstance⟩

attribute [local instance] prod_isIso

private theorem etaleTensor_eq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (n : ℕ) :
    (finiteHomEtaleClosed l E X n).tensor =
      Functor.uncurry.obj (Etale.derivedTensor (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X) := by
  have hc := (finiteHomEtaleData_existsUnique l E X).choose_spec.1.closed n
  change HEq (finiteHomEtaleClosed l E X n)
    (finiteHomEtaleClosedGeneral (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X) at hc
  rw [eq_of_heq hc]
  exact finiteHomClosedGeneral_tensor_uncurry _ X

private theorem scalarTensorSquare
    {A : Type a} {B : Type b} {D : Type c}
    [Category.{d} A] [Category.{e} B] [Category.{f} D]
    (T : A × A ⥤ A) (T' : B × B ⥤ B) (T'' : D × D ⥤ D)
    (F : A ⥤ B) (G : B ⥤ D) (J : A ⥤ D) (α : F ⋙ G ≅ J)
    (μ : T ⋙ F ≅ F.prod F ⋙ T') (ν : T' ⋙ G ≅ G.prod G ⋙ T'')
    (ξ : T ⋙ J ≅ J.prod J ⋙ T'')
    {I : A} {I' : B} {I'' : D} {U : Type e} {V W : Type f}
    (e₀ : U) (e₁ : V) (e₂ : W)
    (h : FiniteHomDomainScalarComposition T T' T'' I I' I'' F G J α
      (fun P Q ↦ μ.app (P, Q)) (fun P Q ↦ ν.app (P, Q))
      (fun P Q ↦ ξ.app (P, Q)) e₀ e₁ e₂) :
    ∀ P Q : A,
      G.map (μ.hom.app (P, Q)) ≫ ν.hom.app (F.obj P, F.obj Q) ≫
          T''.map (Prod.mkHom (α.hom.app P) (α.hom.app Q)) =
        α.hom.app (T.obj (P, Q)) ≫ ξ.hom.app (P, Q) := by
  obtain ⟨δ, δ', δ'', ε, ε', ε'', hδ, hδ', hδ'', _, _, _, hc, _⟩ := h
  intro P Q
  have hh := hc P Q
  rw [eq_of_heq (hδ P Q), eq_of_heq (hδ' _ _), eq_of_heq (hδ'' P Q)] at hh
  exact hh.symm

private theorem transportTensorCoherence
    {A : Type a} {B : Type b} {D : Type c}
    [Category.{d} A] [Category.{e} B] [Category.{f} D]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B} {HD : Dᵒᵖ × D ⥤ D}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (SD : CoefficientClosedStructure HD) (F : A ⥤ B) (G : B ⥤ D) (J : A ⥤ D)
    (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (ν : SB.tensor ⋙ G ≅ G.prod G ⋙ SD.tensor)
    (ξ : SA.tensor ⋙ J ≅ J.prod J ⋙ SD.tensor) (α : F ⋙ G ≅ J)
    (T : A × A ⥤ A) (T' : B × B ⥤ B) (T'' : D × D ⥤ D)
    (hT : SA.tensor = T) (hT' : SB.tensor = T') (hT'' : SD.tensor = T'')
    (μ' : T ⋙ F ≅ F.prod F ⋙ T') (ν' : T' ⋙ G ≅ G.prod G ⋙ T'')
    (ξ' : T ⋙ J ≅ J.prod J ⋙ T'')
    (hμ : HEq μ μ') (hν : HEq ν ν') (hξ : HEq ξ ξ')
    (hc : ∀ X Y : A,
      G.map (μ'.hom.app (X, Y)) ≫ ν'.hom.app (F.obj X, F.obj Y) ≫
          T''.map (Prod.mkHom (α.hom.app X) (α.hom.app Y)) =
        α.hom.app (T.obj (X, Y)) ≫ ξ'.hom.app (X, Y)) :
    ∀ X Y : A,
      G.map (μ.hom.app (X, Y)) ≫ ν.hom.app (F.obj X, F.obj Y) ≫
          SD.tensor.map (Prod.mkHom (α.hom.app X) (α.hom.app Y)) =
        α.hom.app (SA.tensor.obj (X, Y)) ≫ ξ.hom.app (X, Y) := by
  cases hT
  cases hT'
  cases hT''
  cases eq_of_heq hμ
  cases eq_of_heq hν
  cases eq_of_heq hξ
  exact hc


/-- The evaluation-defined coefficient comparison is an isomorphism between finite-Tor
bounded constructible objects, naturally in both arguments, preserving transposes and
internal composition, with the quotient-tower and site-comparison equations.

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-tower/thm-coef-finite-hom.md
and thm-coef-finite-hom.proof.md (blueprint: thm-coef-finite-hom).

Proof:
1. The ordinary etale domain calculus supplies finite-Tor constructible endpoints.
2. The existing etale invertibility lemma proves invertibility of the prescribed
   evaluation transpose by locally closed lisse-projective generators, normalized
   comparison words, and the thick isomorphism locus.
3. Site descent supplies finite-Tor etale origins and the canonical Hom site square.
   Transport endpoint properties across its isomorphisms. Cancel the invertible
   factors in the square and use naturality to transfer invertibility to arbitrary
   pro-etale objects.
4. Generic closed-adjunction calculus gives naturality and transpose compatibility;
   strong monoidality and two evaluations give internal composition compatibility.
5. Transport the etale tensor-coherence equation from its native tensor into the
   published closed record. The scalar-Hom tower identity proves the etale formula;
   the intrinsic tensor-composition square proves the pro-etale formula. Site descent
   already supplies the stated canonical square.
-/
theorem finiteCoefficientHom
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    {n m : ℕ} (h : m ≤ n) :
    (∀ K M : finiteHomEtale l E X n,
      finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X K →
      finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X M →
      finiteTorConstructibleEtale l E (m + 1) (Nat.succ_pos m) X
          ((finiteHomEtaleReduction l E X h).obj
            ((finiteHomEtaleInternalHom l E X n).obj (op K, M))) ∧
        finiteTorConstructibleEtale l E (m + 1) (Nat.succ_pos m) X
          ((finiteHomEtaleInternalHom l E X m).obj
            (op ((finiteHomEtaleReduction l E X h).obj K),
              (finiteHomEtaleReduction l E X h).obj M)) ∧
        IsIso (etaleFiniteHomCanonical l E X h K M)) ∧
    (∀ K M : normalizedDVRDerived l E X n,
      finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X K →
      finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X M →
      finiteTorConstructible l E (m + 1) (Nat.succ_pos m) X
          ((coefficientFiniteQuotientDerived l E X h).obj
            ((coefficientFiniteInternalHom l E X n).obj (op K, M))) ∧
        finiteTorConstructible l E (m + 1) (Nat.succ_pos m) X
          ((coefficientFiniteInternalHom l E X m).obj
            (op ((coefficientFiniteQuotientDerived l E X h).obj K),
              (coefficientFiniteQuotientDerived l E X h).obj M)) ∧
        IsIso (proEtaleFiniteHomCanonical l E X h K M)) ∧
    CoefFiniteHomLawsOn (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
      (finiteHomEtaleReduction l E X h) (finiteHomEtaleTensor l E X h)
      (finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X) ∧
    CoefFiniteHomLawsOn (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
      (coefficientFiniteQuotientDerived l E X h) (coefFiniteHomProTensor l E X h)
      (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X) ∧
    (∀ (r : ℕ) (k : r ≤ m) (K M : finiteHomEtale l E X n),
      finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X K →
      finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X M →
      (finiteHomEtaleAssoc l E X h k).hom.app
          ((finiteHomEtaleInternalHom l E X n).obj (op K, M)) ≫
        etaleFiniteHomCanonical l E X (k.trans h) K M =
      (finiteHomEtaleReduction l E X k).map (etaleFiniteHomCanonical l E X h K M) ≫
        etaleFiniteHomCanonical l E X k
          ((finiteHomEtaleReduction l E X h).obj K)
          ((finiteHomEtaleReduction l E X h).obj M) ≫
        (finiteHomEtaleInternalHom l E X r).map
          (Prod.mkHom ((finiteHomEtaleAssoc l E X h k).inv.app K).op
            ((finiteHomEtaleAssoc l E X h k).hom.app M))) ∧
    (∀ (r : ℕ) (k : r ≤ m) (K M : normalizedDVRDerived l E X n),
      finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X K →
      finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X M →
      (finiteHomIntrinsicAssoc l E X h k).hom.app
          ((coefficientFiniteInternalHom l E X n).obj (op K, M)) ≫
        proEtaleFiniteHomCanonical l E X (k.trans h) K M =
      (coefficientFiniteQuotientDerived l E X k).map
          (proEtaleFiniteHomCanonical l E X h K M) ≫
        proEtaleFiniteHomCanonical l E X k
          ((coefficientFiniteQuotientDerived l E X h).obj K)
          ((coefficientFiniteQuotientDerived l E X h).obj M) ≫
        (coefficientFiniteInternalHom l E X r).map
          (Prod.mkHom ((finiteHomIntrinsicAssoc l E X h k).inv.app K).op
            ((finiteHomIntrinsicAssoc l E X h k).hom.app M))) ∧
    CoefFiniteHomSquare l E X h := by
  obtain ⟨hd, βet, βpro, hβet, hβpro, hν, hall⟩ :=
    coefFiniteHomSiteDescent D l _hl E X
  have hsquare := (hall n m h).2.2.2.2.1
  obtain ⟨sF, sG, sU, sV, ht, hu⟩ := (hall n m h).1
  have lawsE :
      CoefFiniteHomLawsOn (finiteHomEtaleClosed l E X n)
        (finiteHomEtaleClosed l E X m) (finiteHomEtaleReduction l E X h)
        (finiteHomEtaleTensor l E X h)
        (finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X) := by
    refine ⟨?_, ?_, ?_⟩
    · intro K M K' M' _ _ _ _ f g
      exact scalarBaseChangeHom_naturality _ _ _ _ K M K' M' f g
    · intro K M _ _ T f
      exact comparison_transpose _ _ _ _ T K M f
    · intro K L M _ _ _
      exact comparison_composition _ _ _ _ sF K L M
  have lawsI :
      CoefFiniteHomLawsOn (finiteIntrinsicClosed l E X n)
        (finiteIntrinsicClosed l E X m) (coefficientFiniteQuotientDerived l E X h)
        (coefFiniteHomProTensor l E X h)
        (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X) := by
    refine ⟨?_, ?_, ?_⟩
    · intro K M K' M' _ _ _ _ f g
      exact scalarBaseChangeHom_naturality _ _ _ _ K M K' M' f g
    · intro K M _ _ T f
      exact comparison_transpose _ _ _ _ T K M f
    · intro K L M _ _ _
      exact comparison_composition _ _ _ _ sG K L M
  have he : ∀ K M : finiteHomEtale l E X n,
      finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X K →
      finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X M →
      finiteTorConstructibleEtale l E (m + 1) (Nat.succ_pos m) X
        ((finiteHomEtaleReduction l E X h).obj
          ((finiteHomEtaleInternalHom l E X n).obj (op K, M))) ∧
      finiteTorConstructibleEtale l E (m + 1) (Nat.succ_pos m) X
        ((finiteHomEtaleInternalHom l E X m).obj
          (op ((finiteHomEtaleReduction l E X h).obj K),
            (finiteHomEtaleReduction l E X h).obj M)) ∧
      IsIso (etaleFiniteHomCanonical l E X h K M) := by
    intro K M hK hM
    have hh := finiteHomDomain_endpoints D l _hl E X h K M hK.1 hM.1 hK.2 hM.2
    exact ⟨hh.1, hh.2, finiteHomEtale_isIso D l _hl E X h K M hK hM⟩
  refine ⟨he, ?_, lawsE, lawsI, ?_, ?_, hsquare⟩
  · intro K M hK hM
    let F := finiteHomEtaleReduction l E X h
    let G := coefficientFiniteQuotientDerived l E X h
    let U := finiteHomNu l E X n
    let V := finiteHomNu l E X m
    let Hn := coefficientFiniteInternalHom l E X n
    let Hm := coefficientFiniteInternalHom l E X m
    let α := coefFiniteHomSiteIso l E X h
    let :
        (finiteTorConstructible l E (m + 1) (Nat.succ_pos m) X).IsClosedUnderIsomorphisms :=
      (finite_ctf_isTriangulated l E (m + 1) (Nat.succ_pos m) X).1
    obtain ⟨K', hK', ⟨eK⟩⟩ := (hd n).2.2.1 K hK
    obtain ⟨M', hM', ⟨eM⟩⟩ := (hd n).2.2.1 M hM
    obtain ⟨hsource, htarget, hv⟩ := he K' M' hK' hM'
    have hνn := (hsquare K' M' hK' hM').1
    have hνm := (hsquare K' M' hK' hM').2.1
    have hsq := (hsquare K' M' hK' hM').2.2
    let := hv
    let := hνn
    let := hνm
    let eH : Hn.obj (op (U.obj K'), U.obj M') ≅ Hn.obj (op K, M) :=
      Hn.mapIso (Iso.prod eK.symm.op eM)
    let eSource : V.obj (F.obj ((finiteHomEtaleInternalHom l E X n).obj (op K', M'))) ≅
        G.obj (Hn.obj (op K, M)) :=
      α.app _ ≪≫ G.mapIso (asIso (finiteHomSiteHom l E X n K' M')) ≪≫ G.mapIso eH
    let dK : V.obj (F.obj K') ≅ G.obj K := α.app K' ≪≫ G.mapIso eK
    let dM : V.obj (F.obj M') ≅ G.obj M := α.app M' ≪≫ G.mapIso eM
    let eTarget : V.obj ((finiteHomEtaleInternalHom l E X m).obj
        (op (F.obj K'), F.obj M')) ≅ Hm.obj (op (G.obj K), G.obj M) :=
      asIso (finiteHomSiteHom l E X m (F.obj K') (F.obj M')) ≪≫
        Hm.mapIso (Iso.prod dK.symm.op dM)
    refine ⟨(finiteTorConstructible l E (m + 1) (Nat.succ_pos m) X).prop_of_iso
      eSource ((hd m).2.2.2.2 _ hsource).1,
      (finiteTorConstructible l E (m + 1) (Nat.succ_pos m) X).prop_of_iso
        eTarget ((hd m).2.2.2.2 _ htarget).1, ?_⟩
    have hi : IsIso (proEtaleFiniteHomCanonical l E X h (U.obj K') (U.obj M')) := by
      have : IsIso ((coefFiniteHomSiteIso l E X h).hom.app
          ((finiteHomEtaleInternalHom l E X n).obj (op K', M')) ≫
          G.map (finiteHomSiteHom l E X n K' M') ≫
          proEtaleFiniteHomCanonical l E X h (U.obj K') (U.obj M')) := by
        rw [hsq]
        infer_instance
      have : IsIso (G.map (finiteHomSiteHom l E X n K' M') ≫
          proEtaleFiniteHomCanonical l E X h (U.obj K') (U.obj M')) :=
        IsIso.of_isIso_comp_left ((coefFiniteHomSiteIso l E X h).hom.app _) _
      exact IsIso.of_isIso_comp_left (G.map (finiteHomSiteHom l E X n K' M')) _
    let := hi
    have hn := scalarBaseChangeHom_naturality (finiteIntrinsicClosed l E X n)
      (finiteIntrinsicClosed l E X m) G (coefFiniteHomProTensor l E X h)
      (U.obj K') (U.obj M') K M eK.inv eM.hom
    have : IsIso (G.map (Hn.map (Prod.mkHom eK.inv.op eM.hom)) ≫
        proEtaleFiniteHomCanonical l E X h K M) := by
      change IsIso (G.map ((coefficientFiniteInternalHom l E X n).map
        (Prod.mkHom eK.inv.op eM.hom)) ≫
        coefficientBaseChangeHom (finiteIntrinsicClosed l E X n)
          (finiteIntrinsicClosed l E X m) G (coefFiniteHomProTensor l E X h) K M)
      rw [hn]
      change IsIso (proEtaleFiniteHomCanonical l E X h (U.obj K') (U.obj M') ≫
        (coefficientFiniteInternalHom l E X m).map
          (Prod.mkHom (G.map eK.inv).op (G.map eM.hom)))
      infer_instance
    exact IsIso.of_isIso_comp_left (G.map (Hn.map (Prod.mkHom eK.inv.op eM.hom))) _
  · intro r k K M _ _
    apply Eq.symm
    apply scalarBaseChangeHom_tower
      (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
      (finiteHomEtaleClosed l E X r)
      (finiteHomEtaleReduction l E X h) (finiteHomEtaleReduction l E X k)
      (finiteHomEtaleReduction l E X (k.trans h))
      (finiteHomEtaleTensor l E X h) (finiteHomEtaleTensor l E X k)
      (finiteHomEtaleTensor l E X (k.trans h)) (finiteHomEtaleAssoc l E X h k)
    apply transportTensorCoherence _ _ _ _ _ _ _ _ _ _ _ _ _
      (etaleTensor_eq l E X n) (etaleTensor_eq l E X m) (etaleTensor_eq l E X r)
      (Etale.ExceptionalCoefficients.tensorIso (finiteHomQuotient l E h) X)
      (Etale.ExceptionalCoefficients.tensorIso (finiteHomQuotient l E k) X)
      (Etale.ExceptionalCoefficients.tensorIso (finiteHomQuotient l E (k.trans h)) X)
      ((finiteHomEtaleData_existsUnique l E X).choose_spec.1.tensor n m h)
      ((finiteHomEtaleData_existsUnique l E X).choose_spec.1.tensor m r k)
      ((finiteHomEtaleData_existsUnique l E X).choose_spec.1.tensor n r (k.trans h))
    exact scalarTensorSquare _ _ _ _ _ _ _
      (Etale.ExceptionalCoefficients.tensorIso (finiteHomQuotient l E h) X)
      (Etale.ExceptionalCoefficients.tensorIso (finiteHomQuotient l E k) X)
      (Etale.ExceptionalCoefficients.tensorIso (finiteHomQuotient l E (k.trans h)) X) _ _ _
      (finiteHomDomain_scalarCoherence D l _hl E X h k).1
  · intro r k K M _ _
    exact (scalarBaseChangeHom_tower (finiteIntrinsicClosed l E X n)
      (finiteIntrinsicClosed l E X m) (finiteIntrinsicClosed l E X r)
      (coefficientFiniteQuotientDerived l E X h) (coefficientFiniteQuotientDerived l E X k)
      (coefficientFiniteQuotientDerived l E X (k.trans h))
      (coefFiniteHomProTensor l E X h) (coefFiniteHomProTensor l E X k)
      (coefFiniteHomProTensor l E X (k.trans h)) (finiteHomIntrinsicAssoc l E X h k)
      (finiteHomIntrinsic_tensorComposition l E X h k) K M).symm

end WeilConjectures
