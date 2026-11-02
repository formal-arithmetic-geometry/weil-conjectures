/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import WeilConjectures.CategoryTheory.Principal.PrincipalPowerQuotients
import WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralScalarRegular
import WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralProjectionDivisibility
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Sites.LeftExact
import WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralFiniteQuotientHomExt

/-! # Regular scalars and finite quotients of completed coefficients

Source: blueprint, sec-smooth-purity, sk-lem-sp-tower proof, first paragraph,
and coefficient setup in sk-def-sp-coefficient-towers; Stacks Tags 00WK and 00YR.
(blueprint: lem-sp-completed-coefficient-regular-quotients).

Natural level n denotes exponent n+1. The commutative-ring objects below retain the
underlying ring sheaves of the recorded coefficient towers. Quotients are the existing
sheafifications of sectionwise principal-power quotients.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{t})

/-- A constant integral scalar as a compatible section of the actual completed ring.
Source: blueprint, coefficient setup, constant scalar convention
(blueprint: lem-sp-completed-coefficient-regular-quotients). -/
def spCompletedScalarSection (a : Padic.coefficientExtensionIntegers l E) :
    ((completedIntegralCommRingSheafUnrestricted l E T).obj ⋙
      forget CommRingCat.{max u (t + 1)}).sections :=
  (Functor.sectionsFunctor T.ProEtᵒᵖ).map
    (Functor.whiskerRight (integralConstantToCompletionOfUniverses l E T).hom
      (forget RingCat.{max u (t + 1)}))
    ((Functor.sectionsFunctor T.ProEtᵒᵖ).map
      (Functor.whiskerRight (toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)))))
        (forget CommRingCat.{max u (t + 1)}))
      ⟨fun _ ↦ ULift.up a, fun _ ↦ rfl⟩)

/-- The recorded ell-power constant coefficient sheaf, retaining commutativity.
Source: blueprint, coefficient towers, R_(n+1)
(blueprint: lem-sp-completed-coefficient-regular-quotients). -/
def spEllCommRingSheaf (n : ℕ) :
    Sheaf (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)} :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).obj
    (CommRingCat.of (ULift.{t + 1}
      (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))))

private theorem constRing_surj {C : Type*} [Category* C]
    (J : GrothendieckTopology C) [HasSheafify J CommRingCat.{u}]
    [HasSheafify J (Type u)] [J.PreservesSheafification (forget CommRingCat.{u})]
    [J.HasSheafCompose (forget CommRingCat.{u})]
    {A B : CommRingCat.{u}} (f : A ⟶ B) (hf : Function.Surjective f)
    (U : Cᵒᵖ) :
    Function.Surjective (((constantSheaf J CommRingCat.{u}).map f).hom.app U) := by
  classical
  let e := constantCommuteCompose J (forget CommRingCat.{u})
  let s' := (constantSheaf J (Type u)).map (TypeCat.ofHom (Function.surjInv hf))
  have hs : s' ≫ (constantSheaf J (Type u)).map ((forget _).map f) = 𝟙 _ := by
    rw [← Functor.map_comp]
    trans (constantSheaf J (Type u)).map (𝟙 ((forget CommRingCat.{u}).obj B))
    · congr 1
      ext x
      exact Function.surjInv_eq hf x
    exact (constantSheaf J (Type u)).map_id _
  let r := e.hom.app B ≫ s' ≫ e.inv.app A
  have hr : r ≫ (sheafCompose J (forget CommRingCat.{u})).map
      ((constantSheaf J CommRingCat.{u}).map f) = 𝟙 _ := by
    dsimp only [r]
    rw [Category.assoc, Category.assoc]
    change e.hom.app B ≫ s' ≫ e.inv.app A ≫
      (constantSheaf J CommRingCat.{u} ⋙ sheafCompose J (forget CommRingCat.{u})).map f = _
    rw [← e.inv.naturality f]
    change e.hom.app B ≫ s' ≫
      (constantSheaf J (Type u)).map ((forget _).map f) ≫ e.inv.app B = _
    rw [← Category.assoc s', hs, Category.id_comp, e.hom_inv_id_app B]
  intro x
  refine ⟨r.hom.app U x, ?_⟩
  exact congrArg (fun h ↦ h.hom.app U x) hr

private def scalarHom (U : T.ProEtᵒᵖ) :
    Padic.coefficientExtensionIntegers l E →+*
      (completedIntegralCommRingSheafUnrestricted l E T).obj.obj U :=
  ((integralConstantToCompletionOfUniverses l E T).hom.app U).hom.comp
    (((toSheafify (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U).hom.comp
      ULift.ringEquiv.symm.toRingHom)

private abbrev constO :=
  (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)}).obj
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)))

private def constMap : constO l E T ⟶ completedIntegralCommRingSheafUnrestricted l E T where
  hom :=
    { app U :=
        letI := completedIntegralCoefficientCommRingUnrestricted l E T U
        CommRingCat.ofHom ((integralConstantToCompletionOfUniverses l E T).hom.app U).hom
      naturality := by
        intro U V f
        apply (forget₂ CommRingCat RingCat).map_injective
        exact (integralConstantToCompletionOfUniverses l E T).hom.naturality f }

private def constQuot (I : Ideal (Padic.coefficientExtensionIntegers l E)) :
    constO l E T ⟶ (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)}).obj
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E ⧸ I))) :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).map
    (CommRingCat.ofHom (RingHom.ulift (Ideal.Quotient.mk I)))

private theorem uniformizer_normalized (n : ℕ) :
    constMap l E T ≫ completedIntegralCommRingProjectionUnrestricted l E T n =
      constQuot l E T (Padic.coefficientExtensionIdeal l E (n + 1)) := by
  ext U x
  exact congrArg (fun h ↦ h.hom.app U x)
    (limit.lift_π (integralConstantConeOfUniverses l E T) (op n))

private theorem projection_scalar {I : Ideal (Padic.coefficientExtensionIntegers l E)}
    (p : completedIntegralCommRingSheafUnrestricted l E T ⟶
      (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)}).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E ⧸ I))))
    (hp : constMap l E T ≫ p = constQuot l E T I)
    (U : T.ProEtᵒᵖ) (a : Padic.coefficientExtensionIntegers l E) :
    (p.hom.app U) (scalarHom l E T U a) =
      (toSheafify (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E ⧸ I))))).app U
          (ULift.up (Ideal.Quotient.mk I a)) := by
  have hc := congrArg (fun h ↦ h.hom.app U
    ((toSheafify (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U
        (ULift.up a))) hp
  let φ : CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)) ⟶
      CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E ⧸ I)) :=
    CommRingCat.ofHom (RingHom.ulift (Ideal.Quotient.mk I))
  have hn := congrArg (fun h ↦ h.app U (ULift.up a))
    (toSheafify_naturality (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).map φ))
  exact hc.trans hn.symm

private theorem projection_surjective {I : Ideal (Padic.coefficientExtensionIntegers l E)}
    (p : completedIntegralCommRingSheafUnrestricted l E T ⟶
      (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)}).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E ⧸ I))))
    (hp : constMap l E T ≫ p = constQuot l E T I) (U : T.ProEtᵒᵖ) :
    Function.Surjective (p.hom.app U) := by
  have : EssentiallySmall.{max u (t + 1)} T.ProEt := essentiallySmallSelf _
  have hs : Function.Surjective ((constQuot l E T I).hom.app U) := by
    let φ : CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)) ⟶
        CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E ⧸ I)) :=
      CommRingCat.ofHom (RingHom.ulift (Ideal.Quotient.mk I))
    have hsφ : Function.Surjective φ := by
      intro b
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective b.down
      exact ⟨ULift.up a, ULift.ext _ _ ha⟩
    exact constRing_surj (Scheme.ProEt.topology T) φ hsφ U
  intro x
  obtain ⟨a, ha⟩ := hs x
  exact ⟨(constMap l E T).hom.app U a,
    (congrArg (fun h ↦ h.hom.app U a) hp).trans ha⟩

private theorem scalar_killed {I : Ideal (Padic.coefficientExtensionIntegers l E)}
    (p : completedIntegralCommRingSheafUnrestricted l E T ⟶
      (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)}).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E ⧸ I))))
    (hp : constMap l E T ≫ p = constQuot l E T I)
    (U : T.ProEtᵒᵖ) (a : Padic.coefficientExtensionIntegers l E) (m : ℕ)
    (ha : a ^ m ∈ I) : (p.hom.app U) (scalarHom l E T U a ^ m) = 0 := by
  rw [← map_pow, projection_scalar l E T p hp]
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  exact map_zero _

private theorem uniformizer_kernel (n : ℕ) (U : T.ProEtᵒᵖ) :
    RingHom.ker ((completedIntegralCommRingProjectionUnrestricted l E T n).hom.app U).hom =
      sectionPowerIdeal (completedIntegralCommRingSheafUnrestricted l E T)
        (spCompletedScalarSection l E T (Padic.coefficientExtensionUniformizer l E))
        (n + 1) U := by
  ext x
  change _ = 0 ↔ x ∈ Ideal.span {scalarHom l E T U
    (Padic.coefficientExtensionUniformizer l E) ^ (n + 1)}
  rw [Ideal.mem_span_singleton]
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := completedIntegralProjection_divisible l E T n U x hx
    exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    have hz := scalar_killed l E T _ (uniformizer_normalized l E T n) U
      (Padic.coefficientExtensionUniformizer l E) (n + 1)
      (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) (n + 1))
    change ((completedIntegralCommRingProjectionUnrestricted l E T n).hom.app U).hom
      (scalarHom l E T U (Padic.coefficientExtensionUniformizer l E) ^ (n + 1)) = 0 at hz
    rw [map_mul, hz, zero_mul]

private theorem normalized_ext {I : Ideal (Padic.coefficientExtensionIntegers l E)}
    (hI : ∃ k : ℕ, Padic.coefficientExtensionIdeal l E (k + 1) ≤ I)
    (f g : completedIntegralCommRingSheafUnrestricted l E T ⟶
      (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)}).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E ⧸ I))))
    (hf : constMap l E T ≫ f = constQuot l E T I)
    (hg : constMap l E T ≫ g = constQuot l E T I) : f = g := by
  let F := sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  have h := completedIntegralFiniteQuotientHom_ext l E T I hI (F.map f) (F.map g)
    (congrArg F.map hf) (congrArg F.map hg)
  ext U x
  exact congrArg (fun h ↦ h.hom.app U x) h

private theorem quotient_iso {C : Type t} [Category C]
    {J : GrothendieckTopology C} [HasSheafify J CommRingCat.{u}]
    (R H : Sheaf J CommRingCat.{u})
    (a : (R.obj ⋙ forget CommRingCat.{u}).sections) (n : ℕ) (p : R ⟶ H)
    (hs : ∀ U, Function.Surjective (p.hom.app U))
    (hk : ∀ U, RingHom.ker (p.hom.app U).hom = sectionPowerIdeal R a n U) :
    ∃ e : principalPowerRingQuotient R a n ≅ H,
      principalPowerRingProjection R a n ≫ e.hom = p := by
  let q : sectionPowerQuotientPresheaf R a n ⟶ H.obj :=
    { app U := CommRingCat.ofHom (Ideal.Quotient.lift _ (p.hom.app U).hom
        (by intro x hx; exact (show x ∈ RingHom.ker (p.hom.app U).hom by rwa [hk U])))
      naturality := by
        intro U V f
        ext x
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact congrArg (fun h ↦ h x) (p.hom.naturality f) }
  have hq : sectionPowerQuotientProjection R a n ≫ q = p.hom := by
    ext U x
    rfl
  have hi : IsIso q := by
    have : ∀ U, IsIso (q.app U) := by
      intro U
      apply (ConcreteCategory.isIso_iff_bijective _).2
      constructor
      · exact RingHom.lift_injective_of_ker_le_ideal _ _ (by rw [hk U])
      · intro y
        obtain ⟨x, rfl⟩ := hs U y
        exact ⟨Ideal.Quotient.mk _ x, rfl⟩
    exact NatIso.isIso_of_isIso_app q
  let e : principalPowerRingQuotient R a n ≅ H := by
    unfold principalPowerRingQuotient
    exact (presheafToSheaf J CommRingCat.{u}).mapIso (asIso q) ≪≫
      asIso ((sheafificationAdjunction J CommRingCat.{u}).counit.app H)
  refine ⟨e, ?_⟩
  apply Sheaf.hom_ext
  dsimp only [principalPowerRingProjection, e, Iso.trans_hom, Functor.mapIso_hom]
  change (sectionPowerQuotientProjection R a n ≫ toSheafify J _) ≫
    (sheafifyMap J q ≫ _) = p.hom
  rw [Category.assoc, ← Category.assoc (toSheafify J _),
    ← toSheafify_naturality, Category.assoc]
  simp only [asIso_hom, sheafificationAdjunction_counit_app_val]
  rw [toSheafify_sheafifyLift, Category.comp_id, hq]

end AlgebraicGeometry.ProEtale
