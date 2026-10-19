# AlgebraicGeometry.Scheme continuous coefficient definitions

## Reason

The completion, localization and invertibility statements use the continuous coefficient
objects previously defined in ContinuousCoefficientImmersionRestriction. Their new modules
cannot import that module when it imports their proofs. Move the existing definitions and
construction laws verbatim into ContinuousCoefficientBasic and publicly import that module
from the original module. This resolves the dependency cycle; it does not divide a slow proof.
All existing public declaration names, signatures, visibility and definition bodies are retained.
The new completion module locally marks the coefficient integer ring, uniformizer and ideal
irreducible. This prevents typeclass inference from unfolding their nested DVR witnesses;
these attributes do not escape the module and do not change any definition or signature.
The original theorem's signature and docstring are retained unchanged.

## Old

The original module's complete construction prelude, verbatim (the main theorem follows):

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Topology.ContinuousMap.Algebra
public import Sheaf.NumberTheory.Padics.CoefficientExtension
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr

/-!
# Continuous coefficient sheaves and immersion restriction

Source: Bhatt--Scholze, Lemmas 4.2.12 and 6.5.8(1), Definition 6.8.1,
Lemma 6.8.2 and the paragraph preceding Definition 6.8.6
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry Scheme

namespace AlgebraicGeometry.Scheme

/-- Continuous-function presheaf of commutative rings on schemes.

Source: Bhatt--Scholze, Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def continuousMapPresheafCommRing (T : Type v) [TopologicalSpace T]
    [CommRing T] [IsTopologicalRing T] : Scheme.{u}ᵒᵖ ⥤ CommRingCat.{max v u} where
  obj U := CommRingCat.of C(U.unop, T)
  map {U V} f := CommRingCat.ofHom {
    toFun := fun g => ContinuousMap.comp g f.unop.base.hom
    map_one' := by ext; rfl
    map_mul' := by intros; ext; rfl
    map_zero' := by ext; rfl
    map_add' := by intros; ext; rfl }

private theorem commRingForgetReflectsLimit {J : Type v} [Category J]
    (F : J ⥤ CommRingCat.{u}) (c : Limits.Cone F)
    (hc : Limits.IsLimit ((CategoryTheory.forget CommRingCat).mapCone c)) :
    Nonempty (Limits.IsLimit c) := by
  let ext (x y : c.pt) (h : ∀ j, c.π.app j x = c.π.app j y) : x = y := by
    apply (Limits.Types.isLimitEquivSections hc).injective
    exact Subtype.ext (funext h)
  let lift (s : Limits.Cone F) : s.pt ⟶ c.pt := CommRingCat.ofHom
    { toFun := hc.lift ((CategoryTheory.forget CommRingCat).mapCone s)
      map_one' := by
        apply ext
        intro j
        simpa using ConcreteCategory.congr_hom (hc.fac
          ((CategoryTheory.forget CommRingCat).mapCone s) j) (1 : s.pt)
      map_mul' := by
        intro x y
        apply ext
        intro j
        have hj (z : s.pt) : c.π.app j
            (hc.lift ((CategoryTheory.forget CommRingCat).mapCone s) z) = s.π.app j z :=
          ConcreteCategory.congr_hom (hc.fac
            ((CategoryTheory.forget CommRingCat).mapCone s) j) z
        simp only [map_mul]
        rw [hj, hj, hj, map_mul]
      map_zero' := by
        apply ext
        intro j
        simpa using ConcreteCategory.congr_hom (hc.fac
          ((CategoryTheory.forget CommRingCat).mapCone s) j) (0 : s.pt)
      map_add' := by
        intro x y
        apply ext
        intro j
        have hj (z : s.pt) : c.π.app j
            (hc.lift ((CategoryTheory.forget CommRingCat).mapCone s) z) = s.π.app j z :=
          ConcreteCategory.congr_hom (hc.fac
            ((CategoryTheory.forget CommRingCat).mapCone s) j) z
        simp only [map_add]
        rw [hj, hj, hj, map_add] }
  refine ⟨{ lift := lift, fac := ?_, uniq := ?_ }⟩
  · intro s j
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact ConcreteCategory.congr_hom (hc.fac ((CategoryTheory.forget CommRingCat).mapCone s) j) x
  · intro s m hm
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    apply ext
    intro j
    exact (congrArg (fun f : s.pt ⟶ _ ↦ f x) (hm j)).trans
      (ConcreteCategory.congr_hom (hc.fac ((CategoryTheory.forget CommRingCat).mapCone s) j) x).symm

/-- The continuous-function presheaf is a pro-etale sheaf.

Source: Bhatt--Scholze, Lemma 4.2.12 and Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction).
Proof: apply fpqc descent for continuous abelian functions and restrict to the weaker
pro-etale topology. The pointwise ring structure commutes with restriction; reflect
sheafhood through the ring forgetful functor. This is step 1 of the node. -/
theorem continuousMapPresheafCommRing_isSheaf (T : Type v)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    Presheaf.IsSheaf proetaleTopology (continuousMapPresheafCommRing T) := by
  have h : Presheaf.IsSheaf proetaleTopology
      (continuousMapPresheafCommRing T ⋙ CategoryTheory.forget _) :=
    Presheaf.IsSheaf.of_le proetaleTopology_le_fpqcTopology
      (isSheaf_fpqcTopology_continuousMapPresheaf T)
  rw [Presheaf.isSheaf_iff_isLimit] at h ⊢
  intro X S hS
  rcases h S hS with ⟨hc⟩
  exact commRingForgetReflectsLimit _ _ hc

/-- The continuous-function coefficient sheaf on the small pro-etale site.

Source: Bhatt--Scholze, Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def continuousCoefficientSheaf (X : Scheme.{u}) (T : Type v)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    Sheaf (ProEt.topology X) CommRingCat.{max v u} :=
  ((ProEt.forget X ⋙ Over.forget _).sheafPushforwardContinuous _ _ proetaleTopology).obj
    ⟨continuousMapPresheafCommRing T,
      continuousMapPresheafCommRing_isSheaf T⟩

/-- The coefficient extension field equipped with its spectral norm.

Source: Bhatt--Scholze, Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
@[instance_reducible]
noncomputable def coefficientExtensionNormedField (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] : NormedField E :=
  (Padic.coefficientExtensionAbsoluteValue l E).toNormedField

/-- Integral continuous coefficient sheaf `A_X`.

Source: Bhatt--Scholze, Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def integralCoefficientSheaf (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Sheaf (ProEt.topology X) CommRingCat.{u + 1} := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientSheaf X (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))

/-- Rational continuous coefficient sheaf `E_X`.

Source: Bhatt--Scholze, Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def rationalCoefficientSheaf (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Sheaf (ProEt.topology X) CommRingCat.{u + 1} := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientSheaf X (ULift.{u + 1, u} E)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- The finite quotient ring at positive level `n+1`, lifted to the pro-etale coefficient universe.
Source: Bhatt--Scholze, Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def finiteCoefficientRing (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))

/-- Quotient transition map for positive coefficient levels.
Source: Bhatt--Scholze, Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def finiteCoefficientRingMap (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {m n : ℕ} (h : n ≤ m) : finiteCoefficientRing l E m ⟶ finiteCoefficientRing l E n :=
  CommRingCat.ofHom <| RingHom.ulift <|
    Ideal.Quotient.factor (by
      simpa [Padic.coefficientExtensionIdeal] using
        (Ideal.pow_le_pow_right (I := Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
          Set (Padic.coefficientExtensionIntegers l E))) (Nat.succ_le_succ h)))

/-- The quotient maps satisfy the identity law after passing to constant sheaves.
Source: Bhatt--Scholze, Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction).
Proof: A quotient map induced by the identity acts identically on every representative;
quotient induction proves it is the identity ring map. Apply constantSheaf.map_id.
This is a construction law for node steps 2--4. -/
theorem finiteCoefficientTower_map_id (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕᵒᵖ) :
    (CategoryTheory.constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (finiteCoefficientRingMap l E (h := le_rfl)) =
      𝟙 ((CategoryTheory.constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj
        (finiteCoefficientRing l E n.unop)) := by
  have hmap : finiteCoefficientRingMap l E (h := le_rfl (a := n.unop)) =
      𝟙 (finiteCoefficientRing l E n.unop) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    rcases x with ⟨x⟩
    induction x using Quotient.inductionOn' with
    | h x => rfl
  rw [hmap, CategoryTheory.Functor.map_id]

/-- The quotient maps satisfy the composition law after passing to constant sheaves.
Source: Bhatt--Scholze, Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction).
Proof: Both quotient maps act identically on representatives of the valuation ring;
quotient induction proves their equality. Apply constantSheaf.map_comp.
This is a construction law for node steps 2--4. -/
theorem finiteCoefficientTower_map_comp (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (a b c : ℕᵒᵖ) (f : a ⟶ b) (g : b ⟶ c) :
    (CategoryTheory.constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (finiteCoefficientRingMap l E (f ≫ g).unop.le) =
      (CategoryTheory.constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (finiteCoefficientRingMap l E f.unop.le) ≫
      (CategoryTheory.constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (finiteCoefficientRingMap l E g.unop.le) := by
  rw [← CategoryTheory.Functor.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  rcases x with ⟨x⟩
  induction x using Quotient.inductionOn' with
  | h x => rfl

/-- The tower of finite constant coefficient sheaves.
Source: Bhatt--Scholze, Definition 6.8.1 and Lemma 6.8.2(1) (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def finiteCoefficientTower (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) CommRingCat.{u + 1} where
  obj n := (CategoryTheory.constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj
    (finiteCoefficientRing l E n.unop)
  map f := (CategoryTheory.constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
    (finiteCoefficientRingMap l E f.unop.le)
  map_id := by
    intro n
    exact finiteCoefficientTower_map_id l X E n
  map_comp := by
    intro a b c f g
    exact finiteCoefficientTower_map_comp l X E a b c f g

/-- The completed finite-level coefficient sheaf.
Source: Bhatt--Scholze, Lemma 6.8.2(1) (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def finiteCoefficientLimit (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  Limits.limit (finiteCoefficientTower l X E)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- Restriction of continuous functions as a ring homomorphism.
Source: Bhatt--Scholze, Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def continuousMapRestrictionRingHom (T : Type (u + 1))
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    {U V : Scheme.{u}} (f : V ⟶ U) : C(U, T) →+* C(V, T) :=
  { toFun := fun g => ContinuousMap.comp g f.base.hom
    map_one' := by ext; rfl
    map_mul' := by intros; ext; rfl
    map_zero' := by ext; rfl
    map_add' := by intros; ext; rfl }

/-- Restriction followed by sectionwise localization.
Source: Bhatt--Scholze, paragraph before Definition 6.8.6 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def localizedContinuousMapRestriction (X : Scheme.{u})
    (T : Type (u + 1)) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (s : T) {U V : X.ProEtᵒᵖ} (f : U ⟶ V) :
    Localization.Away (ContinuousMap.const U.unop.left s) →+*
      Localization.Away (ContinuousMap.const V.unop.left s) := by
  have hs : (continuousMapRestrictionRingHom T f.unop.left)
      (ContinuousMap.const U.unop.left s) = ContinuousMap.const V.unop.left s := by
    ext x
    rfl
  letI : IsLocalization.Away
      ((continuousMapRestrictionRingHom T f.unop.left)
        (ContinuousMap.const U.unop.left s))
      (Localization.Away (ContinuousMap.const V.unop.left s)) := hs ▸ inferInstance
  exact IsLocalization.Away.map
    (S := Localization.Away (ContinuousMap.const U.unop.left s))
    (Q := Localization.Away (ContinuousMap.const V.unop.left s))
    (continuousMapRestrictionRingHom T f.unop.left)
    (ContinuousMap.const U.unop.left s)

/-- Restriction-localization maps satisfy the identity law.
Source: Bhatt--Scholze, paragraph before Definition 6.8.6 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction).
Proof: The two ring maps agree on every integral numerator by identity precomposition;
the universal property of Localization.Away makes the ring maps equal.
This is a construction law for node steps 2--4. -/
theorem localizedContinuousMap_map_id (X : Scheme.{u})
    (T : Type (u + 1)) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (s : T) (U : X.ProEtᵒᵖ) :
    localizedContinuousMapRestriction X T s (𝟙 U) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (ContinuousMap.const U.unop.left s))
  apply RingHom.ext
  intro x
  simp only [localizedContinuousMapRestriction, IsLocalization.Away.map,
    IsLocalization.map_eq, RingHom.comp_apply, RingHom.id_apply]
  rfl

/-- Restriction-localization maps satisfy the composition law.
Source: Bhatt--Scholze, paragraph before Definition 6.8.6 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction).
Proof: Successive and composite precomposition agree on every numerator. The universal
property of Localization.Away gives equality on fractions, hence on the ring maps.
This is a construction law for node steps 2--4. -/
theorem localizedContinuousMap_map_comp (X : Scheme.{u})
    (T : Type (u + 1)) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (s : T) (U V W : X.ProEtᵒᵖ) (f : U ⟶ V) (g : V ⟶ W) :
    localizedContinuousMapRestriction X T s (f ≫ g) =
      RingHom.comp (localizedContinuousMapRestriction X T s g)
        (localizedContinuousMapRestriction X T s f) := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (ContinuousMap.const U.unop.left s))
  apply RingHom.ext
  intro x
  simp only [RingHom.comp_apply, localizedContinuousMapRestriction,
    IsLocalization.Away.map, IsLocalization.map_eq]
  rfl

/-- Sectionwise localization of the continuous-function presheaf on a small pro-etale site.
Source: Bhatt--Scholze, paragraph before Definition 6.8.6 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def localizedContinuousMapPresheaf (X : Scheme.{u})
    (T : Type (u + 1)) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (s : T) : X.ProEtᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj U := CommRingCat.of (Localization.Away
    (ContinuousMap.const U.unop.left s))
  map {U V} f := CommRingCat.ofHom (localizedContinuousMapRestriction X T s f)
  map_id := by
    intro U
    simpa using congrArg CommRingCat.ofHom (localizedContinuousMap_map_id X T s U)
  map_comp := by
    intro U V W f g
    simpa using congrArg CommRingCat.ofHom (localizedContinuousMap_map_comp X T s U V W f g)

/-- Sheafification of sectionwise localization on the small pro-etale site.
Source: Bhatt--Scholze, paragraph before Definition 6.8.6 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def localizedContinuousCoefficientSheaf (X : Scheme.{u})
    (T : Type (u + 1)) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (s : T) : Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  (CategoryTheory.presheafToSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj
    (localizedContinuousMapPresheaf X T s)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- Localization of the integral coefficient sheaf at the chosen uniformizer.
Source: Bhatt--Scholze, Lemma 6.8.2(2) (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def integralCoefficientLocalization (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Sheaf (ProEt.topology X) CommRingCat.{u + 1} := by
  letI := coefficientExtensionNormedField l E
  exact localizedContinuousCoefficientSheaf X
    (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
    (ULift.up (Padic.coefficientExtensionUniformizer l E))

/-- The continuous-function sheaf for a finite quotient, with its discrete topology.
Source: Bhatt--Scholze, Lemma 4.2.12, discrete-target clause
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def finiteContinuousCoefficientSheaf (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    Sheaf (ProEt.topology X) CommRingCat.{u + 1} := by
  letI : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
  letI : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
  exact continuousCoefficientSheaf X (finiteCoefficientRing l E n)

/-- Evaluation in the continuous-function presentation; `id` only exposes the carrier.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
def continuousCoefficientValue (X : Scheme.{u}) (T : Type (u + 1))
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] (U : X.ProEtᵒᵖ)
    (s : (continuousCoefficientSheaf X T).obj.obj U) (x : U.unop.left) : T :=
  (@id C(U.unop.left, T) s) x

/-- Evaluation of an integral continuous coefficient section in the valuation ring.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def integralCoefficientValue (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (U : X.ProEtᵒᵖ)
    (s : (integralCoefficientSheaf l X E).obj.obj U) (x : U.unop.left) :
    Padic.coefficientExtensionIntegers l E := by
  letI := coefficientExtensionNormedField l E
  exact (continuousCoefficientValue X
    (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) U s x).down

/-- Evaluation of a rational continuous coefficient section in the coefficient field.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def rationalCoefficientValue (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (U : X.ProEtᵒᵖ)
    (s : (rationalCoefficientSheaf l X E).obj.obj U) (x : U.unop.left) : E := by
  letI := coefficientExtensionNormedField l E
  exact (continuousCoefficientValue X (ULift.{u + 1, u} E) U s x).down

/-- Evaluation of a discrete finite quotient section, in the site's coefficient universe.
Source: Bhatt--Scholze, Lemma 4.2.12
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def finiteContinuousCoefficientValue (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (n : ℕ) (U : X.ProEtᵒᵖ)
    (s : (finiteContinuousCoefficientSheaf l X E n).obj.obj U) (x : U.unop.left) :
    finiteCoefficientRing l E n := by
  letI : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
  letI : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
  exact continuousCoefficientValue X (finiteCoefficientRing l E n) U s x

/-- The normalization that specifies pullback of continuous functions uniquely, using
its adjunct on each test object. The variable factor of base change is first.
Source: Bhatt--Scholze, Lemma 6.5.8(1), paragraph before Definition 6.8.6
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
def continuousCoefficientRestrictionNormalized (T : Type (u + 1))
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    {Z X : Scheme.{u}} (h : Z ⟶ X)
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (continuousCoefficientSheaf X T) ⟶ continuousCoefficientSheaf Z T) : Prop :=
  ∀ (U : X.ProEt) (s : C(U.left, T))
    (x : ((proEtaleBaseChange h).obj U).left),
    continuousCoefficientValue Z T (Opposite.op ((proEtaleBaseChange h).obj U))
      ((((proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _) c).hom.app
        (Opposite.op U) s) x = s ((CategoryTheory.Limits.pullback.fst U.hom h) x)

/-- Pullback normalization for the integral coefficient ring in its valuation topology.
Source: Bhatt--Scholze, Lemma 6.5.8(1)
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
def integralCoefficientRestrictionNormalized (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Z X : Scheme.{u}} (h : Z ⟶ X)
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (integralCoefficientSheaf l X E) ⟶ integralCoefficientSheaf l Z E) : Prop := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientRestrictionNormalized
    (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) h c

/-- Pullback normalization for the rational coefficient ring in its valuation topology.
Source: Bhatt--Scholze, paragraph before Definition 6.8.6
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
def rationalCoefficientRestrictionNormalized (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Z X : Scheme.{u}} (h : Z ⟶ X)
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l X E) ⟶ rationalCoefficientSheaf l Z E) : Prop := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientRestrictionNormalized (ULift.{u + 1, u} E) h c

/-- The sectionwise normalization of the coefficient inclusion `A → E`.
Source: Bhatt--Scholze, Definition 6.8.1 and Lemma 6.8.2(2)
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
def integralRationalCoefficientNormalized (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (a : integralCoefficientSheaf l X E ⟶ rationalCoefficientSheaf l X E) :
    Prop :=
  ∀ (U : X.ProEt) (s : (integralCoefficientSheaf l X E).obj.obj (Opposite.op U))
    (x : U.left), rationalCoefficientValue l E X (Opposite.op U)
      (a.hom.app (Opposite.op U) s) x =
        (integralCoefficientValue l E X (Opposite.op U) s x).val

/-- Normalization of the localization comparison on integral numerators.
A ring map from a localization is determined by these values, so this specifies the
canonical fraction map, including every power of the uniformizer in the denominator.
Source: Bhatt--Scholze, Lemma 6.8.2(2)
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
def integralCoefficientLocalizationNormalized (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u})
    (b : integralCoefficientLocalization l X E ⟶ rationalCoefficientSheaf l X E) : Prop := by
  letI := coefficientExtensionNormedField l E
  exact ∀ (U : X.ProEtᵒᵖ)
    (s : C(U.unop.left, ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)))
    (x : U.unop.left),
    rationalCoefficientValue l E X U (b.hom.app U ((CategoryTheory.toSheafify (ProEt.topology X)
      (localizedContinuousMapPresheaf X
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
        (ULift.up (Padic.coefficientExtensionUniformizer l E)))).app U
          (algebraMap _ (Localization.Away (ContinuousMap.const U.unop.left
            (ULift.up (Padic.coefficientExtensionUniformizer l E)))) s))) x =
      (s x).down.val
```

## New

The following complete prelude is in ContinuousCoefficientBasic. The original module publicly
imports it and retains the main theorem with its exact signature and docstring.

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Topology.ContinuousMap.Algebra
public import Sheaf.NumberTheory.Padics.CoefficientExtension
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-!
# Continuous coefficient sheaves and immersion restriction

Source: Bhatt--Scholze, Lemmas 4.2.12 and 6.5.8(1), Definition 6.8.1,
Lemma 6.8.2 and the paragraph preceding Definition 6.8.6
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry Scheme

namespace AlgebraicGeometry.Scheme

/-- Continuous-function presheaf of commutative rings on schemes.

Source: Bhatt--Scholze, Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def continuousMapPresheafCommRing (T : Type v) [TopologicalSpace T]
    [CommRing T] [IsTopologicalRing T] : Scheme.{u}ᵒᵖ ⥤ CommRingCat.{max v u} where
  obj U := CommRingCat.of C(U.unop, T)
  map {U V} f := CommRingCat.ofHom {
    toFun := fun g => ContinuousMap.comp g f.unop.base.hom
    map_one' := by ext; rfl
    map_mul' := by intros; ext; rfl
    map_zero' := by ext; rfl
    map_add' := by intros; ext; rfl }

private theorem commRingForgetReflectsLimit {J : Type v} [Category J]
    (F : J ⥤ CommRingCat.{u}) (c : Limits.Cone F)
    (hc : Limits.IsLimit ((CategoryTheory.forget CommRingCat).mapCone c)) :
    Nonempty (Limits.IsLimit c) := by
  let ext (x y : c.pt) (h : ∀ j, c.π.app j x = c.π.app j y) : x = y := by
    apply (Limits.Types.isLimitEquivSections hc).injective
    exact Subtype.ext (funext h)
  let lift (s : Limits.Cone F) : s.pt ⟶ c.pt := CommRingCat.ofHom
    { toFun := hc.lift ((CategoryTheory.forget CommRingCat).mapCone s)
      map_one' := by
        apply ext
        intro j
        simpa using ConcreteCategory.congr_hom (hc.fac
          ((CategoryTheory.forget CommRingCat).mapCone s) j) (1 : s.pt)
      map_mul' := by
        intro x y
        apply ext
        intro j
        have hj (z : s.pt) : c.π.app j
            (hc.lift ((CategoryTheory.forget CommRingCat).mapCone s) z) = s.π.app j z :=
          ConcreteCategory.congr_hom (hc.fac
            ((CategoryTheory.forget CommRingCat).mapCone s) j) z
        simp only [map_mul]
        rw [hj, hj, hj, map_mul]
      map_zero' := by
        apply ext
        intro j
        simpa using ConcreteCategory.congr_hom (hc.fac
          ((CategoryTheory.forget CommRingCat).mapCone s) j) (0 : s.pt)
      map_add' := by
        intro x y
        apply ext
        intro j
        have hj (z : s.pt) : c.π.app j
            (hc.lift ((CategoryTheory.forget CommRingCat).mapCone s) z) = s.π.app j z :=
          ConcreteCategory.congr_hom (hc.fac
            ((CategoryTheory.forget CommRingCat).mapCone s) j) z
        simp only [map_add]
        rw [hj, hj, hj, map_add] }
  refine ⟨{ lift := lift, fac := ?_, uniq := ?_ }⟩
  · intro s j
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact ConcreteCategory.congr_hom (hc.fac ((CategoryTheory.forget CommRingCat).mapCone s) j) x
  · intro s m hm
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    apply ext
    intro j
    exact (congrArg (fun f : s.pt ⟶ _ ↦ f x) (hm j)).trans
      (ConcreteCategory.congr_hom (hc.fac ((CategoryTheory.forget CommRingCat).mapCone s) j) x).symm

/-- The continuous-function presheaf is a pro-etale sheaf.

Source: Bhatt--Scholze, Lemma 4.2.12 and Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction).
Proof: apply fpqc descent for continuous abelian functions and restrict to the weaker
pro-etale topology. The pointwise ring structure commutes with restriction; reflect
sheafhood through the ring forgetful functor. This is step 1 of the node. -/
theorem continuousMapPresheafCommRing_isSheaf (T : Type v)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    Presheaf.IsSheaf proetaleTopology (continuousMapPresheafCommRing T) := by
  have h : Presheaf.IsSheaf proetaleTopology
      (continuousMapPresheafCommRing T ⋙ CategoryTheory.forget _) :=
    Presheaf.IsSheaf.of_le proetaleTopology_le_fpqcTopology
      (isSheaf_fpqcTopology_continuousMapPresheaf T)
  rw [Presheaf.isSheaf_iff_isLimit] at h ⊢
  intro X S hS
  rcases h S hS with ⟨hc⟩
  exact commRingForgetReflectsLimit _ _ hc

/-- The continuous-function coefficient sheaf on the small pro-etale site.

Source: Bhatt--Scholze, Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def continuousCoefficientSheaf (X : Scheme.{u}) (T : Type v)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    Sheaf (ProEt.topology X) CommRingCat.{max v u} :=
  ((ProEt.forget X ⋙ Over.forget _).sheafPushforwardContinuous _ _ proetaleTopology).obj
    ⟨continuousMapPresheafCommRing T,
      continuousMapPresheafCommRing_isSheaf T⟩

/-- The coefficient extension field equipped with its spectral norm.

Source: Bhatt--Scholze, Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
@[instance_reducible]
noncomputable def coefficientExtensionNormedField (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] : NormedField E :=
  (Padic.coefficientExtensionAbsoluteValue l E).toNormedField

/-- Integral continuous coefficient sheaf `A_X`.

Source: Bhatt--Scholze, Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def integralCoefficientSheaf (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Sheaf (ProEt.topology X) CommRingCat.{u + 1} := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientSheaf X (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))

/-- Rational continuous coefficient sheaf `E_X`.

Source: Bhatt--Scholze, Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def rationalCoefficientSheaf (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Sheaf (ProEt.topology X) CommRingCat.{u + 1} := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientSheaf X (ULift.{u + 1, u} E)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- The finite quotient ring at positive level `n+1`, lifted to the pro-etale coefficient universe.
Source: Bhatt--Scholze, Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def finiteCoefficientRing (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))

/-- Quotient transition map for positive coefficient levels.
Source: Bhatt--Scholze, Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def finiteCoefficientRingMap (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {m n : ℕ} (h : n ≤ m) : finiteCoefficientRing l E m ⟶ finiteCoefficientRing l E n :=
  CommRingCat.ofHom <| RingHom.ulift <|
    Ideal.Quotient.factor (by
      simpa [Padic.coefficientExtensionIdeal] using
        (Ideal.pow_le_pow_right (I := Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
          Set (Padic.coefficientExtensionIntegers l E))) (Nat.succ_le_succ h)))

/-- The quotient maps satisfy the identity law after passing to constant sheaves.
Source: Bhatt--Scholze, Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction).
Proof: A quotient map induced by the identity acts identically on every representative;
quotient induction proves it is the identity ring map. Apply constantSheaf.map_id.
This is a construction law for node steps 2--4. -/
theorem finiteCoefficientTower_map_id (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕᵒᵖ) :
    (CategoryTheory.constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (finiteCoefficientRingMap l E (h := le_rfl)) =
      𝟙 ((CategoryTheory.constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj
        (finiteCoefficientRing l E n.unop)) := by
  have hmap : finiteCoefficientRingMap l E (h := le_rfl (a := n.unop)) =
      𝟙 (finiteCoefficientRing l E n.unop) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    rcases x with ⟨x⟩
    induction x using Quotient.inductionOn' with
    | h x => rfl
  rw [hmap, CategoryTheory.Functor.map_id]

/-- The quotient maps satisfy the composition law after passing to constant sheaves.
Source: Bhatt--Scholze, Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction).
Proof: Both quotient maps act identically on representatives of the valuation ring;
quotient induction proves their equality. Apply constantSheaf.map_comp.
This is a construction law for node steps 2--4. -/
theorem finiteCoefficientTower_map_comp (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (a b c : ℕᵒᵖ) (f : a ⟶ b) (g : b ⟶ c) :
    (CategoryTheory.constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (finiteCoefficientRingMap l E (f ≫ g).unop.le) =
      (CategoryTheory.constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (finiteCoefficientRingMap l E f.unop.le) ≫
      (CategoryTheory.constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (finiteCoefficientRingMap l E g.unop.le) := by
  rw [← CategoryTheory.Functor.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  rcases x with ⟨x⟩
  induction x using Quotient.inductionOn' with
  | h x => rfl

/-- The tower of finite constant coefficient sheaves.
Source: Bhatt--Scholze, Definition 6.8.1 and Lemma 6.8.2(1) (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def finiteCoefficientTower (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) CommRingCat.{u + 1} where
  obj n := (CategoryTheory.constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj
    (finiteCoefficientRing l E n.unop)
  map f := (CategoryTheory.constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
    (finiteCoefficientRingMap l E f.unop.le)
  map_id := by
    intro n
    exact finiteCoefficientTower_map_id l X E n
  map_comp := by
    intro a b c f g
    exact finiteCoefficientTower_map_comp l X E a b c f g

/-- The completed finite-level coefficient sheaf.
Source: Bhatt--Scholze, Lemma 6.8.2(1) (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def finiteCoefficientLimit (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  Limits.limit (finiteCoefficientTower l X E)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- Restriction of continuous functions as a ring homomorphism.
Source: Bhatt--Scholze, Definition 6.8.1 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def continuousMapRestrictionRingHom (T : Type (u + 1))
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    {U V : Scheme.{u}} (f : V ⟶ U) : C(U, T) →+* C(V, T) :=
  { toFun := fun g => ContinuousMap.comp g f.base.hom
    map_one' := by ext; rfl
    map_mul' := by intros; ext; rfl
    map_zero' := by ext; rfl
    map_add' := by intros; ext; rfl }

/-- Restriction followed by sectionwise localization.
Source: Bhatt--Scholze, paragraph before Definition 6.8.6 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def localizedContinuousMapRestriction (X : Scheme.{u})
    (T : Type (u + 1)) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (s : T) {U V : X.ProEtᵒᵖ} (f : U ⟶ V) :
    Localization.Away (ContinuousMap.const U.unop.left s) →+*
      Localization.Away (ContinuousMap.const V.unop.left s) := by
  have hs : (continuousMapRestrictionRingHom T f.unop.left)
      (ContinuousMap.const U.unop.left s) = ContinuousMap.const V.unop.left s := by
    ext x
    rfl
  letI : IsLocalization.Away
      ((continuousMapRestrictionRingHom T f.unop.left)
        (ContinuousMap.const U.unop.left s))
      (Localization.Away (ContinuousMap.const V.unop.left s)) := hs ▸ inferInstance
  exact IsLocalization.Away.map
    (S := Localization.Away (ContinuousMap.const U.unop.left s))
    (Q := Localization.Away (ContinuousMap.const V.unop.left s))
    (continuousMapRestrictionRingHom T f.unop.left)
    (ContinuousMap.const U.unop.left s)

/-- Restriction-localization maps satisfy the identity law.
Source: Bhatt--Scholze, paragraph before Definition 6.8.6 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction).
Proof: The two ring maps agree on every integral numerator by identity precomposition;
the universal property of Localization.Away makes the ring maps equal.
This is a construction law for node steps 2--4. -/
theorem localizedContinuousMap_map_id (X : Scheme.{u})
    (T : Type (u + 1)) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (s : T) (U : X.ProEtᵒᵖ) :
    localizedContinuousMapRestriction X T s (𝟙 U) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (ContinuousMap.const U.unop.left s))
  apply RingHom.ext
  intro x
  simp only [localizedContinuousMapRestriction, IsLocalization.Away.map,
    IsLocalization.map_eq, RingHom.comp_apply, RingHom.id_apply]
  rfl

/-- Restriction-localization maps satisfy the composition law.
Source: Bhatt--Scholze, paragraph before Definition 6.8.6 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction).
Proof: Successive and composite precomposition agree on every numerator. The universal
property of Localization.Away gives equality on fractions, hence on the ring maps.
This is a construction law for node steps 2--4. -/
theorem localizedContinuousMap_map_comp (X : Scheme.{u})
    (T : Type (u + 1)) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (s : T) (U V W : X.ProEtᵒᵖ) (f : U ⟶ V) (g : V ⟶ W) :
    localizedContinuousMapRestriction X T s (f ≫ g) =
      RingHom.comp (localizedContinuousMapRestriction X T s g)
        (localizedContinuousMapRestriction X T s f) := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (ContinuousMap.const U.unop.left s))
  apply RingHom.ext
  intro x
  simp only [RingHom.comp_apply, localizedContinuousMapRestriction,
    IsLocalization.Away.map, IsLocalization.map_eq]
  rfl

/-- Sectionwise localization of the continuous-function presheaf on a small pro-etale site.
Source: Bhatt--Scholze, paragraph before Definition 6.8.6 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def localizedContinuousMapPresheaf (X : Scheme.{u})
    (T : Type (u + 1)) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (s : T) : X.ProEtᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj U := CommRingCat.of (Localization.Away
    (ContinuousMap.const U.unop.left s))
  map {U V} f := CommRingCat.ofHom (localizedContinuousMapRestriction X T s f)
  map_id := by
    intro U
    simpa using congrArg CommRingCat.ofHom (localizedContinuousMap_map_id X T s U)
  map_comp := by
    intro U V W f g
    simpa using congrArg CommRingCat.ofHom (localizedContinuousMap_map_comp X T s U V W f g)

/-- Sheafification of sectionwise localization on the small pro-etale site.
Source: Bhatt--Scholze, paragraph before Definition 6.8.6 (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def localizedContinuousCoefficientSheaf (X : Scheme.{u})
    (T : Type (u + 1)) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (s : T) : Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  (CategoryTheory.presheafToSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj
    (localizedContinuousMapPresheaf X T s)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- Localization of the integral coefficient sheaf at the chosen uniformizer.
Source: Bhatt--Scholze, Lemma 6.8.2(2) (blueprint:
lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def integralCoefficientLocalization (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Sheaf (ProEt.topology X) CommRingCat.{u + 1} := by
  letI := coefficientExtensionNormedField l E
  exact localizedContinuousCoefficientSheaf X
    (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
    (ULift.up (Padic.coefficientExtensionUniformizer l E))

/-- The continuous-function sheaf for a finite quotient, with its discrete topology.
Source: Bhatt--Scholze, Lemma 4.2.12, discrete-target clause
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def finiteContinuousCoefficientSheaf (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    Sheaf (ProEt.topology X) CommRingCat.{u + 1} := by
  letI : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
  letI : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
  exact continuousCoefficientSheaf X (finiteCoefficientRing l E n)

/-- Evaluation in the continuous-function presentation; `id` only exposes the carrier.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
def continuousCoefficientValue (X : Scheme.{u}) (T : Type (u + 1))
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] (U : X.ProEtᵒᵖ)
    (s : (continuousCoefficientSheaf X T).obj.obj U) (x : U.unop.left) : T :=
  (@id C(U.unop.left, T) s) x

/-- Evaluation of an integral continuous coefficient section in the valuation ring.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def integralCoefficientValue (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (U : X.ProEtᵒᵖ)
    (s : (integralCoefficientSheaf l X E).obj.obj U) (x : U.unop.left) :
    Padic.coefficientExtensionIntegers l E := by
  letI := coefficientExtensionNormedField l E
  exact (continuousCoefficientValue X
    (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) U s x).down

/-- Evaluation of a rational continuous coefficient section in the coefficient field.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def rationalCoefficientValue (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (U : X.ProEtᵒᵖ)
    (s : (rationalCoefficientSheaf l X E).obj.obj U) (x : U.unop.left) : E := by
  letI := coefficientExtensionNormedField l E
  exact (continuousCoefficientValue X (ULift.{u + 1, u} E) U s x).down

/-- Evaluation of a discrete finite quotient section, in the site's coefficient universe.
Source: Bhatt--Scholze, Lemma 4.2.12
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
noncomputable def finiteContinuousCoefficientValue (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (n : ℕ) (U : X.ProEtᵒᵖ)
    (s : (finiteContinuousCoefficientSheaf l X E n).obj.obj U) (x : U.unop.left) :
    finiteCoefficientRing l E n := by
  letI : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
  letI : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
  exact continuousCoefficientValue X (finiteCoefficientRing l E n) U s x

/-- The normalization that specifies pullback of continuous functions uniquely, using
its adjunct on each test object. The variable factor of base change is first.
Source: Bhatt--Scholze, Lemma 6.5.8(1), paragraph before Definition 6.8.6
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
def continuousCoefficientRestrictionNormalized (T : Type (u + 1))
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    {Z X : Scheme.{u}} (h : Z ⟶ X)
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (continuousCoefficientSheaf X T) ⟶ continuousCoefficientSheaf Z T) : Prop :=
  ∀ (U : X.ProEt) (s : C(U.left, T))
    (x : ((proEtaleBaseChange h).obj U).left),
    continuousCoefficientValue Z T (Opposite.op ((proEtaleBaseChange h).obj U))
      ((((proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _) c).hom.app
        (Opposite.op U) s) x = s ((CategoryTheory.Limits.pullback.fst U.hom h) x)

/-- Pullback normalization for the integral coefficient ring in its valuation topology.
Source: Bhatt--Scholze, Lemma 6.5.8(1)
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
def integralCoefficientRestrictionNormalized (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Z X : Scheme.{u}} (h : Z ⟶ X)
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (integralCoefficientSheaf l X E) ⟶ integralCoefficientSheaf l Z E) : Prop := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientRestrictionNormalized
    (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) h c

/-- Pullback normalization for the rational coefficient ring in its valuation topology.
Source: Bhatt--Scholze, paragraph before Definition 6.8.6
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
def rationalCoefficientRestrictionNormalized (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Z X : Scheme.{u}} (h : Z ⟶ X)
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l X E) ⟶ rationalCoefficientSheaf l Z E) : Prop := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientRestrictionNormalized (ULift.{u + 1, u} E) h c

/-- The sectionwise normalization of the coefficient inclusion `A → E`.
Source: Bhatt--Scholze, Definition 6.8.1 and Lemma 6.8.2(2)
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
def integralRationalCoefficientNormalized (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (a : integralCoefficientSheaf l X E ⟶ rationalCoefficientSheaf l X E) :
    Prop :=
  ∀ (U : X.ProEt) (s : (integralCoefficientSheaf l X E).obj.obj (Opposite.op U))
    (x : U.left), rationalCoefficientValue l E X (Opposite.op U)
      (a.hom.app (Opposite.op U) s) x =
        (integralCoefficientValue l E X (Opposite.op U) s x).val

/-- Normalization of the localization comparison on integral numerators.
A ring map from a localization is determined by these values, so this specifies the
canonical fraction map, including every power of the uniformizer in the denominator.
Source: Bhatt--Scholze, Lemma 6.8.2(2)
(blueprint: lem-weil-pbc-continuous-coefficients-immersion-restriction). -/
def integralCoefficientLocalizationNormalized (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u})
    (b : integralCoefficientLocalization l X E ⟶ rationalCoefficientSheaf l X E) : Prop := by
  letI := coefficientExtensionNormedField l E
  exact ∀ (U : X.ProEtᵒᵖ)
    (s : C(U.unop.left, ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)))
    (x : U.unop.left),
    rationalCoefficientValue l E X U (b.hom.app U ((CategoryTheory.toSheafify (ProEt.topology X)
      (localizedContinuousMapPresheaf X
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
        (ULift.up (Padic.coefficientExtensionUniformizer l E)))).app U
          (algebraMap _ (Localization.Away (ContinuousMap.const U.unop.left
            (ULift.up (Padic.coefficientExtensionUniformizer l E)))) s))) x =
      (s x).down.val

end AlgebraicGeometry.Scheme
```

All new comparison declarations are proved. Their separate modules permit importing the
constructions without a cycle; this extraction does not divide an expensive proof.

## Users

The table records the transitive importers and textual users of the moved declarations,
including the six Sheaf.Paper consumers identified in the return of c04f1e5123.
The moved definitions remain publicly available through the same import, with identical
signatures and bodies. Each consumer retains the same objects and normalization predicates,
so no consumer needs adaptation and target statements retain their meaning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction | J3 | Public reexport of unchanged definitions; complete combination proof. |
| Sheaf.AlgebraicGeometry.ContinuousCoefficientBasic | new in this delivery | Existing definitions and construction laws moved verbatim. |
| Sheaf.AlgebraicGeometry.ContinuousCoefficientPullback | new in this delivery | Constructed maps with proved normalization, naturality and composition. |
| Sheaf.AlgebraicGeometry.ContinuousCoefficientCompletion | new in this delivery | Proved normalized completion comparison. |
| Sheaf.AlgebraicGeometry.ContinuousCoefficientLocalization | new in this delivery | Proved normalized localization comparison. |
| Sheaf.AlgebraicGeometry.ContinuousCoefficientPullbackIso | new in this delivery | Proved canonical integral and rational invertibility. |

| Comparator.Weil.Solution | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Algebra.Homology.DerivedTensorTruncationWindow | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Algebra.Homology.SitePerfectTorWindow | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.CartierReductionSiteComparison | Y6 | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ClosedSupportStratumHom | D3 | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentExtVanishing | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactSupportSiteComparisonOpen | X3 | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ComparisonTorInterval | H5 | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | E3 | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | X2 | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | D4 | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor | A9 | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleProEtaleExceptionalTransport | T7 | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ExtSupportCohomologyVanishing | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoefficientEtaleProjectionFormula | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula | H1 | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleProEtaleAdjunction | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators | G3 | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleCompact | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleGeneration | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalPlaneAdjunctionLattice | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.RankOneFiniteGeometricImageCurve | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.GeoCartierCycleClass | T8 | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.GeoP1Cohomology | T9 | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | H9 | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.KunnethSupported | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.MarkedNodalDualizingDegrees | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.NodalNormalizationAdjunction | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenComparisonTensorNormalization | J6 | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenImmersionHigherDirectImages | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenProjectionSiteTransport | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleTorLocalGlobal | U7 | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | W8 | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperOpenSiteTransport | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | X7 | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeAdjointOpenOrigin | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.SfFullcdEtaleOrigin | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.SfFullcdUsedClass | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.SheafExtCoherent | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.StableModificationStabilityLocus | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportLongExact | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportQuotientFlat | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportQuotientProduct | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.CategoryTheory.SiteTorIntervalRestriction | M7 | Identical reexported declarations; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.AdicClosedConstructible | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.AdicTorFlatCohomology | S6 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.AffineLineInvariance | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.AffineLineOrdinaryInvariance | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedSums | F5 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ArbitraryFieldAdjunctionScalars | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | K2 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.BoundedConstructibleHomFiniteness | H5 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.BoundedSiteAdjunctionTranspose | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | E1 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CanonicalOriginCompactSupportComposition | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CanonicalWeilFundamentalRepresentation | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CartesianCoefficientTwists | Q4 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CartesianCoefficients | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | M1 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ClosedSupportConstructible | N4 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentHom | E4 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentLisse | F1 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CoefficientHeart | X8 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CoefficientHeartClosure | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CoefficientHeartCommonStratification | F2 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CoefficientHeartFiltration | P4 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CoefficientHeartGeneration | P7 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CoefficientHeartSmall | F3 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CoefficientHeartTriangulated | Y5 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CoefficientTwistsDetailed | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CompactFiberStalk | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CompactSupportDirectImageTriangulated | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CompactSupportReductionTower | F8 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CompactSupportSiteCoherence | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | F4 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | T9 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ComparisonPullbackExact | K3 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CompositeIntegrationCounit | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ConcentratedComplexShift | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CondensedERealization | Y9 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CondensedTateRealization | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ConstantCoefficientScalarNormalization | Z5 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ConstantWeilStructureStageIndependence | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | U7 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ConstructibleCompactnessBounded | R4 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | Z7 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ConstructibleExtContinuity | U8 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ConstructibleFlatCohomologyTorBound | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | P8 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | R2 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ConstructiblePullbackTExact | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.CurveWeilMiddleExtension | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.DegreeZeroDerivedMapGluing | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.DenseOpenPiOneSurjective | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | T2 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.DetIndHeartIISums | C5 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | G3 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.DiagonalTowerSystem | H4 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.DirectImageChangeRingTranspose | J2 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.DirectImageCtfOpenTor | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.DlLocallyConstructibleAdicHeart | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | S1 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.EtaleCompactScalarCoherence | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | F8 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | N1 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.EtaleLocallyClosedShriek | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | V5 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y8 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.EtaleSectionDeformationComparison | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.EtaleWeilFundamentalRepresentation | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.EtaleWeilSheafEquivalence | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.EvenTensorPositivity | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ExceptionalCoefficientComparison | S4 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | U1 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ExplicitExceptionalPreservation | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FieldStageOrdinaryRealization | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FieldTorAmplitude | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FilteredCoefficientTensorBounds | Q5 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | U2 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | G7 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDirectImage | G8 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteCoefficientPoint | A3 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteCoefficientReductionFlatModel | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportConstructibility | G9 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteExtensionCompactSupportBaseChange | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteExtensionReductionConeBound | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteFieldExceptionalPreservation | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteFieldInternalHomFiniteness | U3 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteForwardProductSymmetry | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteFreeHomComparison | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteProperLocalizing | V9 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteReductionConstructibility | V2 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteRingSectionDeformation | V3 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | A4 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | W2 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteTateSiteDescent | V9 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteTorInternalHomAnyField | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteWindow | W5 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | C1 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | C7 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FormalClosedSupport | Q9 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FormalClosedSupportII | M2 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | W6 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FourierTraceFunctions | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionMap | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FrobeniusGeometricExchange | A2 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FrobeniusSquareExchange | J3 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IndConstructibleExtensions | K4 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IndConstructibleFilteredColimits | M1 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IndHeartCanonicalPresentation | W8 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IndHeartFullFaithfulness | M2 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IndHeartIIVanishing | E9 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IndHeartKernelsCokernels | M3 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | W7 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | C2 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | J9 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralExtensionByZero | A3 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | C3 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | H2 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralModelSurjectiveClosedReflection | S3 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralModels | D4 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralModelsOperations | N1 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerRealization | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | B4 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | W9 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralTensorShriek | F2 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralTwistBaseChange | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntegralTwistScalarCoherence | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | S4 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.InternalAdjunctionPairingChange | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntrinsicCoefficientTwists | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted | C3 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.KummerAdditivity | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.LevelwiseAdicTruncations | S9 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.LisseEConstructibleIntegralLattice | H8 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.LisseIntegralCompletedRealization | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTrace | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.LocalWeilModelTraceIndependence | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | H9 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | J5 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | D7 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.MixedReductionUnit | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.MixedWeightsStability | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.NearbyCycleSheafFiniteness | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.OpenExtensionFiniteTor | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.OpenImmersionLocalizing | X5 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PbcCoefficientTwists | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PbcCohomologySheaves | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PbcQbarStandardCohomology | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PbcSupportCondition | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PlurinodalProperHypercover | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensor | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorBasic | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorFiniteModels | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorModels | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorQbar | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorRational | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorScalar | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PointFibreEquivalence | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PointRealizationCoefficientComparison | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PointSectionsReconstruction | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PointSectionsScalarExtension | P4 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PointSectionsTensorShift | Q1 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ProEtaleTateTwists | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | P2 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ProperHeartBound | K5 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | G2 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ProperHeartBoundTorsion | J4 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | Q3 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | K6 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ProperOpenCoefficientMate | X5 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | U2 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | F8 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PsiGoodOrientedCohomologyStrata | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PurTwistSheafLocallyFree | K7 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PurityAffineChartBounds | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PurityComparisonUnitInjectiveModel | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PurityConventions | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PurityCoprojection | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PurityDivisorClass | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PurityDncComparisons | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PurityFiniteExceptionalComposition | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PurityFiniteKummerLevel | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PurityFrameClass | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PurityFrameIndependence | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PurityFramePrincipalBoundary | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PurityGeneralAdmissibility | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PurityRankOneLocalCalculation | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PurityRelativeKummer | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.QbarAffineSupportBound | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.QbarCompactSupportBaseChange | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.QbarDerivedDirectImage | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.QbarOrdinaryAdjunction | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.QcqsCompactSupportRealization | D3 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | C1 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.RationalCompactSupportCoefficientCoherence | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | K8 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | R9 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.RealBoundaryPathIndependence | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.RealSheafSections | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.RefinementCoefficientMate | X6 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.RelativeSupportBottomDescent | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.RestrictionLocal | R3 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SfCommonStageDirectImage | E1 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SfCommonStageWeilCohomology | V2 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | K9 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SfPreservationClass | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SfProEtaleProjectionFormula | X7 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SiteComparisonEdgeSection | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SmoothExceptionalBaseChangeStatement | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SmoothExceptionalPreservation | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SmoothMateCounitCancellation | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | S6 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.StandingExceptionalComposition | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.StratifiedLatticeRank | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.StratumScalarExtension | W2 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SupportedAffineLineHomotopy | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SupportedCohomologyHom | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SupportedCup | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SupportedCupFunctoriality | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SupportedHomAdjunctionTranspose | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SupportedHomPullback | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.SystemOperationExchangeRealization | K1 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.TateTwistLocallyFree | S7 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.TensorTraceTranspose | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.TraceBaseChangeFirst | E1 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | E4 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.TraceExceptionalAdmissibility | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.TraceTransposeBaseChange | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.TwConventions | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.TwistPreservesFiniteness | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | K3 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.UnboundedLocalizingPullback | Y7 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | X9 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | K4 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | M4 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.VectorPurityFiniteReduction | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.VectorPurityScalarSingle | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.WeilCompactSupportCohomology | D8 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.WeilComplexTraceFunction | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.WeilFourierTransform | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.WeilIndSheafCategory | D9 | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | C3 | Identical reexported declarations; no adaptation. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SecSmoothPurity.DirectImageScalarExchange | E5 | Identical reexported declarations; no adaptation. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | U9 | Identical reexported declarations; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SecSmoothPurity.OpenScalarExchange | S1 | Identical reexported declarations; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | Identical reexported declarations; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | F3 | Identical reexported declarations; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | G1 | Identical reexported declarations; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SecSmoothPurity.WeilTwistRationalization | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | M1 | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.BrownHypothesesSmall | Z9 | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.CompactCoefficientComposition | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.ComparisonOpenTensorCoherence | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.ConstructibleTensorCompletion | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | H6 | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.EtaleInternalHomDevissage | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.FieldTensor | N1 | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.FiniteCompactProetale | A2 | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.FiniteCoverCTFLocality | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.FlatModel | A3 | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.FlatModelGeneration | S3 | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | E3 | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.FrobeniusPointTransport | E7 | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.FrobeniusPointTransportNatural | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | M7 | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | N4 | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | T2 | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralModelsGenerators | T3 | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | U3 | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | G9 | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | T4 | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | F4 | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | B4 | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | U1 | Identical reexported declarations; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Targets.VectorBundlePurity | F6 | Identical reexported declarations; no adaptation. |
| Sheaf.TraceFormula.BoundedConstructibleTransport | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.TraceFormula.PointTransportComposition | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.TraceFormula.StableCurveDiagramNoetherianModel | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.TraceFormula.StableModificationConstructibility | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.TraceFormula.StableModificationSpreading | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.TraceFormula.TemkinStableModification | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.TraceFormula.TwoTermPerfectDeterminant | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.TraceFormula.ValuationMarkingSemistableSeparation | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.TraceFormula.ValuationSemistableDominatesStable | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.WeilSheaf.CohomologyGeometricEquivalence | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Identical reexported declarations; no adaptation. |
| TargetsCheck | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.AdditiveCharacters | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocalMonodromy | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocalMonodromyFrobenius | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TameInertia | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Defs | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DenseOpen | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.Weights | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Boundary | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryInertia | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalk | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightExterior | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeights | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationData | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationDual | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationSections | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationStalk | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPath | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobenius | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobeniusElement | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathGeometric | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.Statement | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierDual | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierFrobenius | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierPurity | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.BoundaryStalk | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.Cohomology | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyExact | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyShift | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.ComplexWeights | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.ConstantTwistCohomology | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.Defs | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.DenseOpen | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.DirectImageRestriction | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.DirectImageStalk | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.ExtensionByZero | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.FiniteEtaleLisse | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.Fourier | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Defs | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisse | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.UpperStar | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTateTwist | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTateTwist.Transform | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTraceAux | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.GeometricCoinvariants | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.GeometricallyConstant | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.HomologyShift | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.Localization | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriek | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStar | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarComp | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarId | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarPairing | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarTensorPow | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.MiddleExtension | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.OpenImmersion | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.OpenImmersionRestriction | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.Operations | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.ProperCohomology | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.Realizable | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.StalkConstantTwist | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.StalkExtensionByZero | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.StalkInternalHom | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.StalkOpenImmersion | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.StalkTateTwist | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.StalkTensor | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.TateTwist | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.TateTwistCohomology | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.Tensor | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.TensorObjPairing | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.TensorPower | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.TraceFunctionCongr | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.TraceFunctionOps | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.TraceFunctionTensor | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.TraceSeries | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.WeilSheaf.UpperStarPointwise | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Identical reexported declarations; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Identical reexported declarations; no adaptation. |

| Sheaf.Paper.CompactSupportCondensedRealization | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unclaimed | Identical reexported declarations; no adaptation. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | Identical reexported declarations; no adaptation. |

| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Uses `rationalCoefficientSheaf`; definitions and signatures are reexported verbatim, so no adaptation or statement change. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Uses `rationalCoefficientSheaf`; definitions and signatures are reexported verbatim, so no adaptation or statement change. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Uses `rationalCoefficientSheaf`, `rationalCoefficientValue`, `rationalCoefficientRestrictionNormalized`; definitions and signatures are reexported verbatim, so no adaptation or statement change. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Uses `rationalCoefficientSheaf`; definitions and signatures are reexported verbatim, so no adaptation or statement change. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Uses `rationalCoefficientSheaf`; definitions and signatures are reexported verbatim, so no adaptation or statement change. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Uses `rationalCoefficientSheaf`; definitions and signatures are reexported verbatim, so no adaptation or statement change. |

| Sheaf.AlgebraicGeometry.FormalPuncturedSections | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.LogSmoothTraitPunctualPurity | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.MonomialBoundaryPurityCriterion | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.MonomialTraitPunctualPurity | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.PrimeFieldPunctualPurity | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.PunctualPurityTraitTest | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.PunctualStrictCompletionTest | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.PuncturedPerverseHighComparison | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.PuncturedSupportCohomologicalBound | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.SmoothPunctualPurityAscent | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.AlgebraicGeometry.StrictLocalEtaleDimensionBounds | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.AdicExceptionalBase | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.AdicExceptionalOperations | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.AdicExceptionalProjectionData | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.CompactSupportReductionTowerConstruction | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.CompletionSupportedConstantComparison | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.FiniteExceptionalSystemAdjunction | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.NoetherianPrimePowerSmoothDuality | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.PuncturedDerivedCompletionSections | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.PuritySourceTransports | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.RegularImmersionCancellation | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.RegularImmersionClassData | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.RegularImmersionExteriorClass | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.SystemClopenTensorCompatibility | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.TowerClassChern | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.TowerClassFinite | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.TowerClassProjective | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.TowerClassPullback | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.TowerClassReduction | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.TowerClassSystems | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.TowerClassTwisting | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.WfTensorCompletionFrobenius | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.Paper.ZlOpenDiagramComparisonTransport | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.RingTheory.CompleteLocalConnectednessBound | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.RingTheory.NormalPuncturedHypersurfaceConnected | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ArtinSchreierDual | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Constituent | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DirectImageUnit | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.GeometricSMul | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LaurentPoints | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LinearCharacters | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Punctual | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualSupport | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RamifiedAtInfinity | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryGenericRep | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryNeighbourhoodConstruction | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryNeighbourhoodExistence | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LisseWeilSheafTensor | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentationTensor | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSections | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationFunctor | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationTensor | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.FieldStagePointers | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyCoverEquivalence | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExists | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExtension | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyLift | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyPullback | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.TwistedSection | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierFunctions | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierInertia | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierIsotypic | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierMul | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierMulGeometric | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierNeg | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierPlane | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierPullback | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrivialization | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.BoundaryStalkFrobenius | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.BoundaryStalkGaloisInvariants | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.BoundaryStalkSpecialization | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.BoundaryStrictHenselization | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.CohomologyDegreeZero | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.CohomologyGeometricConjugacy | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.CohomologyGeometricEquivalence | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.CohomologySequence | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.CohomologyZero | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.ConstantTwistWeight | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.DerivedHom | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.DirectImageStalkMap | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.FiniteLeray | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.FiniteLowerStar | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.FinitePointCohomology | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.GlobalSectionsUpperStar | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.IhomCurry | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.IhomLisse.CompWeil | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.IhomLisse.UpperStar | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.IhomLisse.UpperStarDual | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.Isotypic | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.IsotypicPullback | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.LSeries | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.LisseExtension | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.LowerStarTriangulated | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.ProperBaseChange | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.ShiftedSheaf | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.SplitTorsor | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.StalkRationalPoint | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.StalkStrictlyHenselian | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.StalkTensorTrace | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.TorsorPairing | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunctionWeil | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed in this checkout | Unchanged public reexport; no statement change or adaptation. |

## Status

landed 20261019T192754-L-1866283 2026-10-19 (merge of deliver/J3/Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction)
