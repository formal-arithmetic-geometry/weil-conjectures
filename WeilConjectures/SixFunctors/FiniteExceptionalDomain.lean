/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpecifiedExceptionalClassHom
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.SfIntrinsicCompactSupport
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
public import WeilConjectures.Compactification.RefinementCategory

public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactifFiniteTor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekFiniteness
import Mathlib.Algebra.CharP.CharAndCard

/-! # Finite exceptional adjunction domain

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
prop-functor-package.proof.md, exceptional-adjunction sentence
(blueprint: lem-sf-package-finite-exceptional-domain).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

namespace FiniteExceptionalDomain

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- The full-subcategory restriction of the specified compactification candidate.
Source: current blueprint, package exceptional-adjunction sentence
(blueprint: lem-sf-package-finite-exceptional-domain). -/
def left (c : Compactification f)
    (h : ∀ K, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K)) :
    DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X ⥤
      DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) Y :=
  ObjectProperty.lift _
    ((DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).ι ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c)
    (fun K ↦ h K.obj K.property)

variable (c₀ : Compactification f)
  (G : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
  (adj : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c₀ ⊣ G)

/-- The full-subcategory restriction of the specified ordinary-etale adjoint transported
as nu_X^* G Rnu_Y,*. This composes the recorded comparison functors with that same adjoint.
Source: current blueprint, package exceptional-adjunction sentence
(blueprint: lem-sf-package-finite-exceptional-domain). -/
def right
    (h : ∀ L, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y L →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
        (((comparisonLowerStar (ModuleCat.{u + 1} Λ) Y).rightDerivedFunctor ⋙ G ⋙
          (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory).obj L)) :
    DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) Y ⥤
      DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X :=
  ObjectProperty.lift _
    ((DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).ι ⋙
      (comparisonLowerStar (ModuleCat.{u + 1} Λ) Y).rightDerivedFunctor ⋙ G ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory)
    (fun L ↦ h L.obj L.property)

variable [QuasiCompact f]

/-- The claimed restriction, retaining the existing class datum and all of its
normalizations. The ordinary-etale right adjoint is fixed at c₀. As in the recorded
ComparisonClassAdjunction, comparisons to the other compactifications normalize their
right functor to this same composite; the right comparisons are identities. This is
precisely that class datum restricted to the finite-Tor constructible domains.

The finite-stage etale-origin presentation of Dctf is the recorded
`DerivedCategory.constructibleFiniteTor`; finite constructible origin identifies it with
bounded complexes of intrinsically constructible cohomology and finite Tor amplitude.
Source: current blueprint, package exceptional-adjunction sentence
(blueprint: lem-sf-package-finite-exceptional-domain). -/
structure Restriction where
  /-- The natural Hom bijections on the larger bounded-below comparison class. -/
  classData : ComparisonClassAdjunction Λ f c₀ G adj
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X)
    _root_.DerivedCategory.TStructure.t.plus
  /-- Compact support preserves the finite-Tor constructible domain. -/
  preservesLeft (c : Compactification f) :
    ∀ K, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K)
  /-- The transported exceptional functor preserves that domain. -/
  preservesRight :
    ∀ L, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y L →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
        (((comparisonLowerStar (ModuleCat.{u + 1} Λ) Y).rightDerivedFunctor ⋙ G ⋙
          (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory).obj L)
  /-- The restricted natural Hom bijections form an adjunction. -/
  adjunction (c : Compactification f) :
    left Λ c (preservesLeft c) ⊣ right Λ G preservesRight
  /-- Its Hom equivalence is exactly the class-relative equivalence. -/
  homEquiv (c : Compactification f)
      (K : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X)
      (L : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) Y)
      (g : (left Λ c (preservesLeft c)).obj K ⟶ L) :
    ((adjunction c).homEquiv K L g).hom =
      classData.homEquiv c K.obj K.property.plusEtaleOrigin L.obj L.property.plus g.hom
  /-- The unit is the class unit, defined by transposing the identity. -/
  unit (c : Compactification f)
      (K : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X) :
    ((adjunction c).unit.app K).hom =
      classData.homEquiv c K.obj K.property.plusEtaleOrigin
        ((left Λ c (preservesLeft c)).obj K).obj
        ((left Λ c (preservesLeft c)).obj K).property.plus (𝟙 _)
  /-- The counit is the class counit, defined by inverse-transposing the identity. -/
  counit (c : Compactification f)
      (L : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) Y) :
    ((adjunction c).counit.app L).hom =
      (classData.homEquiv c ((right Λ G preservesRight).obj L).obj
        ((right Λ G preservesRight).obj L).property.plusEtaleOrigin
        L.obj L.property.plus).symm (𝟙 _)
  /-- Compact-support comparisons restrict to the finite-Tor categories. -/
  comparison (c₁ c₂ : Compactification f) :
    left Λ c₁ (preservesLeft c₁) ≅ left Λ c₂ (preservesLeft c₂)
  /-- Its components are the original class comparisons under the full inclusions. -/
  comparison_hom (c₁ c₂ : Compactification f)
      (K : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X) :
    ((comparison c₁ c₂).hom.app K).hom =
      (classData.comparison c₁ c₂).hom.app ⟨K.obj, K.property.plusEtaleOrigin⟩
  /-- Comparisons preserve the restricted natural Hom bijections. The right comparison
  is the identity, as in the original normalized class datum. -/
  comparison_homEquiv (c₁ c₂ : Compactification f)
      (K : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X)
      (L : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) Y)
      (g : (left Λ c₂ (preservesLeft c₂)).obj K ⟶ L) :
    (adjunction c₁).homEquiv K L ((comparison c₁ c₂).hom.app K ≫ g) =
      (adjunction c₂).homEquiv K L g
  /-- The original identity law on the constructible domains. -/
  comparison_id (c : Compactification f) : comparison c c = Iso.refl _
  /-- The original cocycle on the constructible domains. -/
  comparison_cocycle (c₁ c₂ c₃ : Compactification f) :
    comparison c₁ c₂ ≪≫ comparison c₂ c₃ = comparison c₁ c₃

/-- The restriction assertion at the actual positive quotient O_E/(varpi^n), for the
ordinary-etale right adjoint of the supplied compactification. Such a right adjoint
exists unconditionally; quantification over it permits exactly the choice in the node.
Its unit/counit are retained by adj, so uniqueness is uniqueness of adjoints with these
maps, rather than an arbitrary choice of a pro-etale functor or Hom equivalence.
Source: current blueprint, package exceptional-adjunction sentence
(blueprint: lem-sf-package-finite-exceptional-domain). -/
def Conclusion (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (c : Compactification f) : Prop :=
  haveI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  ∀ (G : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)))) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)))))
    (adj : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))) c ⊣ G),
    Nonempty (Restriction (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) c G adj)

private def restrictClass
    (B : ComparisonClassAdjunction Λ f c₀ G adj
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X)
      _root_.DerivedCategory.TStructure.t.plus)
    (hF : ∀ (c : Compactification f) K,
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K))
    (hG : ∀ L, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y L →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
        (((comparisonLowerStar (ModuleCat.{u + 1} Λ) Y).rightDerivedFunctor ⋙ G ⋙
          (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory).obj L)) :
    Restriction Λ c₀ G adj := by
  let e (c : Compactification f)
      (K : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X)
      (L : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) Y) :
      ((left Λ c (hF c)).obj K ⟶ L) ≃ (K ⟶ (right Λ G hG).obj L) :=
    { toFun := fun g ↦ ObjectProperty.homMk
        (B.homEquiv c K.obj K.property.plusEtaleOrigin L.obj L.property.plus g.hom)
      invFun := fun g ↦ ObjectProperty.homMk
        ((B.homEquiv c K.obj K.property.plusEtaleOrigin L.obj L.property.plus).symm g.hom)
      left_inv := fun g ↦ ObjectProperty.hom_ext _ (Equiv.symm_apply_apply _ g.hom)
      right_inv := fun g ↦ ObjectProperty.hom_ext _ (Equiv.apply_symm_apply _ g.hom) }
  let core (c : Compactification f) :
      Adjunction.CoreHomEquiv (left Λ c (hF c)) (right Λ G hG) :=
    { homEquiv := e c
      homEquiv_naturality_left_symm := by
        intro K' K L a g
        apply (e c K' L).injective
        rw [Equiv.apply_symm_apply]
        apply ObjectProperty.hom_ext _
        change a.hom ≫ g.hom =
          B.homEquiv c K'.obj K'.property.plusEtaleOrigin L.obj L.property.plus
            ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).map
              a.hom ≫ _)
        rw [B.naturality_left c K'.obj K.obj K'.property.plusEtaleOrigin
          K.property.plusEtaleOrigin L.obj L.property.plus]
        exact congrArg (a.hom ≫ ·) (Equiv.apply_symm_apply _ g.hom).symm
      homEquiv_naturality_right := by
        intro K L L' a b
        apply ObjectProperty.hom_ext _
        exact B.naturality_right c K.obj K.property.plusEtaleOrigin L.obj L'.obj
          L.property.plus L'.property.plus a.hom b.hom }
  let cmp (c d : Compactification f) : left Λ c (hF c) ≅ left Λ d (hF d) :=
    NatIso.ofComponents
      (fun K ↦ ObjectProperty.isoMk _
        ((B.comparison c d).app ⟨K.obj, K.property.plusEtaleOrigin⟩))
      (by
        intro K L a
        apply ObjectProperty.hom_ext _
        exact (B.comparison c d).hom.naturality
          (X := ⟨K.obj, K.property.plusEtaleOrigin⟩)
          (Y := ⟨L.obj, L.property.plusEtaleOrigin⟩) (ObjectProperty.homMk a.hom))
  refine
    { classData := B
      preservesLeft := hF
      preservesRight := hG
      adjunction := fun c ↦ Adjunction.mkOfHomEquiv (core c)
      homEquiv := ?_
      unit := ?_
      counit := ?_
      comparison := cmp
      comparison_hom := fun _ _ _ ↦ rfl
      comparison_homEquiv := ?_
      comparison_id := ?_
      comparison_cocycle := ?_ }
  · intro c K L g
    rw [Adjunction.mkOfHomEquiv_homEquiv]
    rfl
  · intro c K
    rw [Adjunction.mkOfHomEquiv_unit_app]
    rfl
  · intro c L
    rw [Adjunction.mkOfHomEquiv_counit_app]
    rfl
  · intro c d K L g
    simp only [Adjunction.mkOfHomEquiv_homEquiv]
    apply ObjectProperty.hom_ext _
    exact B.comparison_homEquiv c d K.obj K.property.plusEtaleOrigin
      L.obj L.property.plus g.hom
  · intro c
    ext K
    apply ObjectProperty.hom_ext _
    exact congrArg (fun t ↦ t.hom.app ⟨K.obj, K.property.plusEtaleOrigin⟩)
      (B.comparison_refl c)
  · intro c d z
    ext K
    apply ObjectProperty.hom_ext _
    exact congrArg (fun t ↦ t.hom.app ⟨K.obj, K.property.plusEtaleOrigin⟩)
      (B.comparison_trans c d z).symm

end FiniteExceptionalDomain

private theorem finiteCoefficient_invertibleExponent
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) :
    HasInvertibleExponent (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))
      (Spec (.of D.k)) := by
  have : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card, D.card_base, D.cardinality_eq])
  let : CharP D.k D.p := charP_of_injective_algebraMap
    (algebraMap D.k₀ D.k).injective D.p
  have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have hv : Padic.coefficientExtensionAbsoluteValue l E (D.p : E) = 1 := by
    have he := spectralNorm_extends (K := Padic l) (L := E) (D.p : Padic l)
    have hn : ‖(D.p : Padic l)‖ = 1 := Padic.norm_natCast_eq_one_iff.2
      ((Nat.coprime_primes (Fact.out : l.Prime) D.prime).2 hl)
    change spectralNorm (Padic l) E (D.p : E) = 1
    simpa only [map_natCast, hn] using he
  have hu : IsUnit (D.p : Padic.coefficientExtensionIntegers l E) :=
    (h.2.2.1 _).2 hv
  have hq : IsUnit (D.p : Padic.coefficientExtensionRing l E n) := by
    simpa using hu.map (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n))
  have : Invertible (D.p : ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) :=
    (show IsUnit (D.p : ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) by
      simpa using hq.map ULift.ringEquiv.symm.toRingHom).invertible
  exact HasInvertibleExponent.spec_of_charP _ D.p

/-- Finite-Tor constructible restriction of the specified finite class-relative adjunction.
Source: current blueprint, sec-six-functors/sk-thm-sf-package,
prop-functor-package.proof.md, exceptional-adjunction sentence (returned step 3)
(blueprint: lem-sf-package-finite-exceptional-domain).

Proof:
1. Properness and finite-type composition make the compactifying scheme finite type over k.
For a finite-Tor constructible K with interval [a,b], lem-trf-open-ctf preserves that interval
under j_!, and cor-sf-direct-image-ctf-proetale gives [a,b+2d] after Rp_*.
2. thm-sf-preservation-class(2) applies to the finite composite defining the exceptional
inverse image in def-weil-exceptional-inverse-image. Both functors therefore restrict to
full finite-Tor constructible subcategories. Uniqueness of the ordinary-etale adjoint
identifies any specified choice with this composite, compatibly with its adjunction maps.
3. lem-sf-proetale-constructible-origin(ii) makes K bounded below of etale origin, and L is
bounded below. The natural Hom bijection of thm-sf-ambient-adjoint-class(2) thus restricts
without changing Hom sets or composition. Retain its normalized class datum.
4. lem-weil-pbc-adjunction-of-natural-bijection gives the adjunction. Its unit is the image of
the identity under that bijection and its counit is the inverse image of the identity, so
these are precisely the class unit and counit under the full inclusions.
5. For every other compactification c', finite-type composition and
lem-kun-dimension-finite-type give a nonnegative finite bound d' (zero for the empty scheme).
Apply steps 1--4 to c'. The comparisons of thm-sf-ambient-adjoint-class(3) and their inverses
are arrows of the full subcategories. Their Hom compatibility, identity, and cocycle
equations are the same equations there, with the original fixed-right normalization.
No unbounded ambient pro-etale adjunction is used. -/
theorem finiteExceptionalDomain
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) [QuasiCompact c.i]
    (d : ℕ) (_hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞)) :
    FiniteExceptionalDomain.Conclusion l E n hn f c := by
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E n)
  have : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  have : HasInvertibleExponent A (Spec (.of D.k)) :=
    finiteCoefficient_invertibleExponent D l _hl E n hn
  have : HasInvertibleExponent A Y := .of_hom (Y ↘ Spec (.of D.k))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of D.k))
  let : HasCompactification f := ⟨⟨c⟩⟩
  intro G adj
  let adj₀ := (Etale.rightDerivedUpperShriekAdjunction A f).ofNatIsoLeft
    (Etale.rightDerivedLowerShriekIso A c).symm
  let eG := adj.rightAdjointUniq adj₀
  have hG : ∀ L, _root_.DerivedCategory.TStructure.t.plus L →
      _root_.DerivedCategory.TStructure.t.plus
        (G.obj ((comparisonLowerStar (ModuleCat.{u + 1} A) Y).rightDerivedFunctor.obj L)) := by
    intro L hL
    exact _root_.DerivedCategory.TStructure.t.plus.prop_of_iso (eG.app _).symm
      (Etale.plus_rightDerivedUpperShriek_obj _ f _
        (plus_rightDerivedFunctor_comparisonLowerStar_obj hL))
  obtain ⟨B₀⟩ := nonempty_fixedComparisonClassAdjunction_of_boundedBelow A c G adj hG
  let B : ComparisonClassAdjunction A f c G adj
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X)
      _root_.DerivedCategory.TStructure.t.plus :=
    { boundedBelow := B₀.boundedBelow
      homEquiv := B₀.homEquiv
      homEquiv_normalized := B₀.homEquiv_normalized
      naturality_left := B₀.naturality_left
      naturality_right := B₀.naturality_right
      comparison := B₀.comparison
      comparison_normalized := B₀.comparison_normalized
      comparison_refl := B₀.comparison_refl
      comparison_trans := B₀.comparison_trans
      comparison_homEquiv := B₀.comparison_homEquiv }
  refine ⟨FiniteExceptionalDomain.restrictClass A c G adj B ?_ ?_⟩
  · intro c' K hK
    exact constructibleFiniteTor_rightDerivedLowerShriekOfCompactification A
      (Y ↘ Spec (.of D.k)) c' hK
  · intro L hL
    exact (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X).prop_of_iso
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.mapIso
        (eG.app _)).symm
      (constructibleFiniteTor_rightDerivedUpperShriek A (Y ↘ Spec (.of D.k)) f hL)

end AlgebraicGeometry.ProEtale
