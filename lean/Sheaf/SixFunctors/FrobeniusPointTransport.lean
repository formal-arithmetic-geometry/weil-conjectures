/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison
public import Sheaf.Paper.IsomorphismDerivedPullback
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.CharP.Invertible
import Sheaf.Paper.IntegralPullbackReductionCounit

/-!
# Point transport along geometric Frobenius

Source: Deligne, Weil II (1.1.7), pp. 150--151; the explicit restriction,
comma-coprojection and sheafification construction in the blueprint
(blueprint: def-weil-frobenius-point-transport).

The canonical sectionwise model of inverse image along an isomorphism identifies
its comma coprojection followed by sheafification with the identity on sections.
Thus sigma is the restriction along g_s in that model. The finite comparison is
the recorded tensor-unit map; the integral comparison is the recorded Roos lift,
not tensor extension by the completed coefficient sheaf. Rational transport is
scalar extension of the integral arrow. The algebraic-closure arrow is represented
at the object's own coefficient stage. No naturality or invertibility is asserted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

/-- Spec of the geometric field Frobenius, with its prescribed inverse.
Source: Deligne, Weil II (1.1.7) (blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointIso (D : FiniteFieldDatum.{u}) : Spec (.of D.k) ≅ Spec (.of D.k) :=
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  Scheme.Spec.mapIso
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k).toRingEquiv.toCommRingCatIso.op

/-- The arrow (s,g_s) to (s,id) of the small pro-etale site.
Source: blueprint restriction formula (blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointRestriction (D : FiniteFieldDatum.{u}) :
    (proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj
        (ProEt.mk (𝟙 (Spec (.of D.k)))) ⟶ ProEt.mk (𝟙 (Spec (.of D.k))) :=
  (ProEt.forget (Spec (.of D.k))).preimage (Over.homMk (frobeniusPointIso D).hom)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The excluded characteristic makes l a unit in every stalk of s.
Source: finite-field datum and l ≠ p (blueprint: def-weil-frobenius-point-transport).
Proof: Nat.card k₀ = p^a with p prime and a positive implies characteristic p.
The algebraic closure and its local rings have the same characteristic. A prime l
unequal to p has nonzero image there, so is a unit in the field stalk. -/
theorem frobeniusPointPrimeUnit (D : FiniteFieldDatum.{u}) (l : ℕ)
    [Fact l.Prime] (_hl : l ≠ D.p) :
    ∀ x : Spec (.of D.k), IsUnit (l : (Spec (.of D.k)).presheaf.stalk x) := by
  intro x
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  have hc : Fintype.card D.k₀ = D.p ^ D.a := by
    simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow hc
  have hu : IsUnit (l : D.k₀) := (CharP.isUnit_natCast_iff D.prime).2 (by
    intro hdiv
    exact _hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 hdiv).symm)
  have hk : IsUnit (l : D.k) := by
    simpa only [map_natCast] using hu.map (algebraMap D.k₀ D.k)
  have h := hk.map
    (StructureSheaf.toStalk (CommRingCat.of D.k) x).hom
  simpa only [map_natCast] using h

/-- The same excluded characteristic makes l a unit in the residue fields.
Source: finite-field datum (blueprint: def-weil-frobenius-point-transport).
Proof: the unique point has residue field canonically k, of characteristic p.
The image of l is nonzero because l and p are distinct primes, hence invertible. -/
theorem frobeniusPointPrimeResidueUnit (D : FiniteFieldDatum.{u}) (l : ℕ)
    [Fact l.Prime] (_hl : l ≠ D.p) :
    ∀ x : Spec (.of D.k), IsUnit (l : (Spec (.of D.k)).residueField x) := by
  intro x
  simpa only [map_natCast] using
    (frobeniusPointPrimeUnit D l _hl x).map ((Spec (.of D.k)).residue x).hom

/-- The canonical inverse of the residue-field unit; no extra hypothesis on s.
Source: finite-field datum (blueprint: def-weil-frobenius-point-transport). -/
@[instance_reducible]
def frobeniusPointPrimeInvertible (x : Spec (.of D.k)) :
    Invertible (l : (Spec (.of D.k)).residueField x) :=
  (frobeniusPointPrimeResidueUnit D l hl x).invertible

private theorem sectionwiseSigma_existsUnique
    (C : Type (u + 1)) [Category.{u} C] (J : GrothendieckTopology C)
    (F : C ⥤ C) [F.IsContinuous J J] (U : C) (r : F.obj U ⟶ U)
    (R : Sheaf J RingCat.{u + 1})
    (c : (F.sheafPushforwardContinuous RingCat.{u + 1} J J).obj R ⟶ R) [IsIso c]
    [(SheafOfModules.pushforward.{u + 1} (F := F) (inv c)).Additive]
    (B : Type (u + 1)) [Ring B]
    (a : B →+* R.obj.obj (op U))
    (ha : ∀ b, R.obj.map r.op (a b) =
      (inv c).hom.app (op U) (a b))
    (K : CochainComplex (SheafOfModules.{u + 1} R) ℤ) :
    let S := SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj (op U) ⋙
      ModuleCat.restrictScalars (R := B) a
    ∃! f : (S.mapHomologicalComplex (.up ℤ)).obj K ⟶
        (S.mapHomologicalComplex (.up ℤ)).obj
          (((SheafOfModules.pushforward.{u + 1} (F := F) (inv c)).mapHomologicalComplex
            (.up ℤ)).obj K),
      ∀ i : ℤ, HEq (fun x ↦ f.f i x)
        (fun x ↦ (K.X i).val.map r.op x) := by
  dsimp only
  let S := SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj (op U) ⋙
      ModuleCat.restrictScalars (R := B) a
  let f : (S.mapHomologicalComplex (.up ℤ)).obj K ⟶
      (S.mapHomologicalComplex (.up ℤ)).obj
        (((SheafOfModules.pushforward.{u + 1} (F := F) (inv c)).mapHomologicalComplex
          (.up ℤ)).obj K) :=
    { f i := by
        let M := S.obj (K.X i)
        let N := S.obj ((SheafOfModules.pushforward.{u + 1} (F := F) (inv c)).obj (K.X i))
        exact @ModuleCat.ofHom B _ M N M.isAddCommGroup M.isModule
          N.isAddCommGroup N.isModule
          { toFun := (K.X i).val.map r.op
            map_add' := fun x y ↦ map_add ((K.X i).val.map
              r.op).hom x y
            map_smul' := fun b x ↦ by
              change (K.X i).val.map r.op
                  (a b • (show (K.X i).val.obj
                    (op U) from x)) =
                (inv c).hom.app (op U) (a b) •
                  (show (K.X i).val.obj
                    (op (F.obj U)) from
                    (K.X i).val.map r.op x)
              exact ((K.X i).val.map_smul _ _ _).trans
                (congrArg (fun z ↦ z • (show (K.X i).val.obj
                  (op (F.obj U)) from
                    (K.X i).val.map r.op x)) (ha b)) }
      comm' i j _ := by
        ext x
        exact PresheafOfModules.naturality_apply (K.d i j).val r.op x }
  refine ⟨f, fun _ ↦ HEq.rfl, ?_⟩
  intro h hh
  apply HomologicalComplex.Hom.ext
  funext i
  ext x
  exact congrFun (eq_of_heq (hh i)) x

private theorem finiteScalarRestriction (A : Type u) [CommRing A]
    (a : ULift.{u + 1, u} A) :
    let R := (sheafCompose (ProEt.topology (Spec (.of D.k)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf (ProEt.topology (Spec (.of D.k))) CommRingCat.{u + 1}).obj
          (CommRingCat.of (ULift.{u + 1, u} A)))
    R.obj.map (frobeniusPointRestriction D).op (pointConstantSectionMap D.k A a) =
      (inv (isoSectionwiseConstantMap.{u, u} (frobeniusPointIso D).hom
        (CommRingCat.of (ULift.{u + 1, u} A)))).hom.app
          (op (ProEt.mk (𝟙 (Spec (.of D.k))))) (pointConstantSectionMap D.k A a) := by
  dsimp only
  let U := ProEt.mk (𝟙 (Spec (.of D.k)))
  let c := isoSectionwiseConstantMap.{u, u} (frobeniusPointIso D).hom
    (CommRingCat.of (ULift.{u + 1, u} A))
  have hn := ConcreteCategory.congr_hom
    ((toSheafify (ProEt.topology (Spec (.of D.k)))
      ((Functor.const (Spec (.of D.k)).ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1, u} A)))).naturality
          (frobeniusPointRestriction D).op) a
  have hc := (isoSectionwiseConstantMap_existsUnique.{u, u} (frobeniusPointIso D).hom
    (CommRingCat.of (ULift.{u + 1, u} A))).exists.choose_spec U a
  let x := (toSheafify (ProEt.topology (Spec (.of D.k)))
    ((Functor.const (Spec (.of D.k)).ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1, u} A)))).app
        (op ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj U)) a
  have hi := congrArg (fun f ↦ f.hom.app (op U) x) (IsIso.hom_inv_id c)
  change (inv c).hom.app (op U) (c.hom.app (op U) x) = x at hi
  calc
    _ = x := hn.symm
    _ = (inv c).hom.app (op U) (c.hom.app (op U) x) := hi.symm
    _ = _ := congrArg ((inv c).hom.app (op U)) hc

/-- The finite sigma chain map is uniquely fixed on every term and section.
Source: blueprint finite/integral paragraph (blueprint: def-weil-frobenius-point-transport).
Proof: use restriction along g_s and then the distinguished comma coprojection
and the sheafification unit. In the recorded sectionwise inverse-image model the
latter two maps identify the section with itself. Restrictions commute with d.
The constant coefficient comparison fixes every constant section, so restriction
is linear for the transported c inverse action. Equality on all sections proves
uniqueness of the chain map. Heterogeneous equality of the underlying functions
is equivalent to that pointwise condition, with definitionally equal section carriers.
It avoids repeated normalization of the composite functors in the specification.
No naturality in derived morphisms is used. -/
theorem frobeniusPointFiniteSigma_existsUnique (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    ∃! f : ((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
      (.up ℤ)).obj K ⟶
        ((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
      (.up ℤ)).obj
          (((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapHomologicalComplex
               (.up ℤ)).obj K),
      ∀ i : ℤ, HEq (fun x ↦ f.f i x)
        (fun x ↦ (K.X i).val.map (frobeniusPointRestriction D).op x) := by
  let : (SheafOfModules.pushforward (F :=
      proEtaleIsoPostcompose (frobeniusPointIso D).hom)
      (inv (inverseImageFiniteCoefficientMap l E (frobeniusPointIso D).hom n))).Additive :=
    isoSectionwiseModuleInverseImage_additive.{u, u} (frobeniusPointIso D).hom
      (inverseImageFiniteCoefficientMap l E (frobeniusPointIso D).hom n)
  exact sectionwiseSigma_existsUnique _ _
    (proEtaleIsoPostcompose (frobeniusPointIso D).hom) _ (frobeniusPointRestriction D) _
    (inverseImageFiniteCoefficientMap l E (frobeniusPointIso D).hom n) _
    (pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E (n + 1)))
    (finiteScalarRestriction D _) K

/-- Sigma is the specified chain map res, ins, sheafification, in its sectionwise model.
Source: blueprint displayed sigma (blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointFiniteSigma (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    ((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
      (.up ℤ)).obj K ⟶
        ((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
      (.up ℤ)).obj
          (((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapHomologicalComplex
               (.up ℤ)).obj K) :=
  Classical.choose (frobeniusPointFiniteSigma_existsUnique D l E n K)

private abbrev integralScalarSection
    (U : (Spec (.of D.k)).ProEtᵒᵖ)
    (a : ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) :=
  (integralConstantToCompletion l E (Spec (.of D.k))).hom.app U
    ((toSheafify (ProEt.topology (Spec (.of D.k)))
      ((Functor.const (Spec (.of D.k)).ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))))).app U a)

private theorem integralScalarProjection (n : ℕ)
    (U : (Spec (.of D.k)).ProEtᵒᵖ)
    (a : ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) :
    (limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op n)).hom.app U
        (integralScalarSection D l E U a) =
      (toSheafify (ProEt.topology (Spec (.of D.k)))
        ((Functor.const (Spec (.of D.k)).ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1, u}
            (Padic.coefficientExtensionRing l E (n + 1)))))).app U
              (ULift.up
                (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a.down)) := by
  let q : CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) ⟶
      CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) :=
    CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
        ULift.ringEquiv.toRingHom))
  have hp := congrArg (fun f ↦ f.hom.app U
    ((toSheafify (ProEt.topology (Spec (.of D.k)))
      ((Functor.const (Spec (.of D.k)).ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1, u}
          (Padic.coefficientExtensionIntegers l E))))).app U a))
    (limit.lift_π (integralConstantCoefficientCone l E (Spec (.of D.k))) (op n))
  have hq := congrArg (fun f ↦ f.app U a)
    (toSheafify_naturality (ProEt.topology (Spec (.of D.k)))
      ((Functor.const (Spec (.of D.k)).ProEtᵒᵖ).map q))
  exact hp.trans hq.symm

private theorem integralScalarRestriction
    (a : ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) :
    (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k))).obj.map
        (frobeniusPointRestriction D).op (pointIntegralSectionMap l E D.k a) =
      (inv (inverseImageCompletedCoefficientMap l E (frobeniusPointIso D).hom)).hom.app
        (op (ProEt.mk (𝟙 (Spec (.of D.k))))) (pointIntegralSectionMap l E D.k a) := by
  let U := op (ProEt.mk (𝟙 (Spec (.of D.k))))
  let V := op ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj U.unop)
  let R := completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k))
  let T := integralCoefficientSheafSystem l E (Spec (.of D.k))
  let c := inverseImageCompletedCoefficientMap l E (frobeniusPointIso D).hom
  let x := R.obj.map (frobeniusPointRestriction D).op (pointIntegralSectionMap l E D.k a)
  have hc : c.hom.app U x = pointIntegralSectionMap l E D.k a := by
    let ev := sheafToPresheaf (ProEt.topology (Spec (.of D.k))) RingCat.{u + 1} ⋙
      (evaluation (Spec (.of D.k)).ProEtᵒᵖ RingCat.{u + 1}).obj U
    apply Concrete.isLimit_ext (T ⋙ ev) (isLimitOfPreserves ev (limit.isLimit T))
    intro j
    obtain ⟨n⟩ := j
    have hp := congrArg (fun f ↦ f.hom.app U x)
      (limit.lift_π
        (show Cone T from
          { pt := (isoSectionwiseInverseImage (frobeniusPointIso D).hom RingCat.{u + 1}).obj R
            π := { app j := inverseImageCompletedCoefficientComponent l E
                      (frobeniusPointIso D).hom j.unop
                   naturality _ _ f := (Category.id_comp _).trans
                     (inverseImageCompletedCoefficientComponent_naturality l E
                       (frobeniusPointIso D).hom f).symm } }) (op n))
    have hr := ConcreteCategory.congr_hom
      ((limit.π T (op n)).hom.naturality (frobeniusPointRestriction D).op)
      (pointIntegralSectionMap l E D.k a)
    have hpu := integralScalarProjection D l E n U a
    have hnorm := (isoSectionwiseConstantMap_existsUnique.{u, u}
      (frobeniusPointIso D).hom
      (CommRingCat.of (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))))).exists.choose_spec U.unop
        (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a.down))
    change (limit.π T (op n)).hom.app U (c.hom.app U x) =
      (limit.π T (op n)).hom.app U (pointIntegralSectionMap l E D.k a)
    change (limit.π T (op n)).hom.app U (c.hom.app U x) =
      (inverseImageFiniteCoefficientMap l E (frobeniusPointIso D).hom n).hom.app U
        ((limit.π T (op n)).hom.app V x) at hp
    rw [hp, show (limit.π T (op n)).hom.app V x = _ from hr]
    change _ = (limit.π T (op n)).hom.app U (integralScalarSection D l E U a)
    change (inverseImageFiniteCoefficientMap l E (frobeniusPointIso D).hom n).hom.app U
      ((integralCoefficientSheaf l E (Spec (.of D.k)) n).obj.map
        (frobeniusPointRestriction D).op
        ((limit.π T (op n)).hom.app U (integralScalarSection D l E U a))) = _
    rw [hpu]
    have hn := ConcreteCategory.congr_hom
      ((toSheafify (ProEt.topology (Spec (.of D.k)))
        ((Functor.const (Spec (.of D.k)).ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1, u}
            (Padic.coefficientExtensionRing l E (n + 1)))))).naturality
              (frobeniusPointRestriction D).op)
      (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a.down))
    exact (congrArg
      ((inverseImageFiniteCoefficientMap l E (frobeniusPointIso D).hom n).hom.app U)
      hn.symm).trans hnorm
  have hi := congrArg (fun f ↦ f.hom.app U x) (IsIso.hom_inv_id c)
  change (inv c).hom.app U (c.hom.app U x) = x at hi
  exact hi.symm.trans (congrArg ((inv c).hom.app U) hc)

/-- The integral sigma chain map is fixed on every term and section, with completed action.
Source: blueprint integral paragraph (blueprint: def-weil-frobenius-point-transport).
Proof: use the same restriction and comma generator as at finite level. The limit
coefficient comparison is compatible with every quotient projection. Constant
integral sections are the compatible constant reductions, hence it fixes them.
Restriction is therefore O_E-linear for the completed action. Restrictions commute
with differentials, and equality on all term sections gives uniqueness. The
heterogeneous function equality records precisely that pointwise section condition. -/
theorem frobeniusPointIntegralSigma_existsUnique
    (K : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    ∃! f : ((pointIntegralSections l E D.k).mapHomologicalComplex
      (.up ℤ)).obj K ⟶
        ((pointIntegralSections l E D.k).mapHomologicalComplex
      (.up ℤ)).obj
          (((inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapHomologicalComplex
               (.up ℤ)).obj K),
      ∀ i : ℤ, HEq (fun x ↦ f.f i x)
        (fun x ↦ (K.X i).val.map (frobeniusPointRestriction D).op x) := by
  let : (SheafOfModules.pushforward (F :=
      proEtaleIsoPostcompose (frobeniusPointIso D).hom)
      (inv (inverseImageCompletedCoefficientMap l E (frobeniusPointIso D).hom))).Additive :=
    isoSectionwiseModuleInverseImage_additive.{u, u} (frobeniusPointIso D).hom
      (inverseImageCompletedCoefficientMap l E (frobeniusPointIso D).hom)
  exact sectionwiseSigma_existsUnique _ _
    (proEtaleIsoPostcompose (frobeniusPointIso D).hom) _ (frobeniusPointRestriction D) _
    (inverseImageCompletedCoefficientMap l E (frobeniusPointIso D).hom) _
    (pointIntegralSectionMap l E D.k) (integralScalarRestriction D l E) K

/-- Integral sigma, with its completed coefficient action fixed by all quotient maps.
Source: blueprint displayed sigma (blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointIntegralSigma
    (K : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    ((pointIntegralSections l E D.k).mapHomologicalComplex
      (.up ℤ)).obj K ⟶
        ((pointIntegralSections l E D.k).mapHomologicalComplex
      (.up ℤ)).obj
          (((inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapHomologicalComplex
               (.up ℤ)).obj K) :=
  Classical.choose (frobeniusPointIntegralSigma_existsUnique D l E K)

private theorem adjunctionComparison_exists
    {A B C : Type*} [Category A] [Category B] [Category C]
    (H F : A ⥤ B) (L : B ⥤ C) (R : C ⥤ B) (adj : L ⊣ R)
    (T : A ⥤ C) (e : F ≅ T ⋙ R) (β : H ⋙ L ⟶ T)
    (I : Type*) (P : I → A) (a : ∀ i, H.obj (P i) ⟶ F.obj (P i))
    (ha : ∀ i, L.map (a i ≫ e.hom.app (P i)) ≫ adj.counit.app (T.obj (P i)) =
      β.app (P i)) :
    ∃ κ : H ⟶ F, ∀ i, κ.app (P i) = a i := by
  let κ' : H ⟶ T ⋙ R :=
    Functor.whiskerLeft H adj.unit ≫ Functor.whiskerRight β R
  let κ : H ⟶ F := κ' ≫ e.inv
  have hc (N : A) : L.map (κ'.app N) ≫ adj.counit.app (T.obj N) = β.app N := by
    have h := (adj.homEquiv (H.obj N) (T.obj N)).symm_apply_apply (β.app N)
    simpa only [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit,
      κ', NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] using h
  refine ⟨κ, ?_⟩
  intro i
  apply (cancel_mono (e.hom.app (P i))).1
  apply (adj.homEquiv _ _).symm.injective
  change L.map (κ.app _ ≫ e.hom.app _) ≫ _ = L.map (_ ≫ e.hom.app _) ≫ _
  have hleft : κ.app (P i) ≫ e.hom.app (P i) = κ'.app (P i) := by
    simp only [κ, NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  calc
    _ = β.app (P i) :=
      (congrArg (fun f ↦ L.map f ≫ adj.counit.app (T.obj (P i))) hleft).trans (hc _)
    _ = _ := (ha i).symm

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem integralKappaNatural_exists
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    ∃ κ : inverseImageIntegralDerived l E g ⟶
        integralDerivedPullback l E g,
      ∀ (K : CochainComplex (integralTowerModules l E Y) ℤ)
        (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (q : P.obj ⟶ K) [QuasiIso q],
        κ.app (DerivedCategory.Q.obj K) =
          inverseImagePullbackComparison l E g
            hX hY K P q := by
  let H := inverseImageIntegralDerived l E g
  let F := integralDerivedPullback l E g
  obtain ⟨R, _⟩ := integralPullbackComparisonRealization l E E (AlgHom.id ℚ_[l] E)
  let S := (R.coefficient E).system Y
  let B := integralComparisonDerivedSequencePullback l E g
  let U := coefficientSequenceDerivedRestriction l E X
  let Δ := integralComparisonConstantTower l E X
  let ΔY := integralComparisonConstantTower l E Y
  let Ht := integralDerivedTowerInverseImage l E g
  let UY := coefficientSequenceDerivedRestriction l E Y
  let d : ΔY ⟶ S.reduction ⋙ UY :=
    Functor.whiskerRight S.adjunction.unit ΔY ≫
      Functor.whiskerLeft (S.reduction ⋙ UY) (integralComparisonTowerCounit l E Y)
  let β : H ⋙ Δ ⟶ S.reduction ⋙ B ⋙ U :=
    (integralTowerInverseImageDiagonal l E g).hom ≫
      Functor.whiskerRight d Ht ≫
      Functor.whiskerLeft S.reduction (integralDerivedTowerInverseImageUnit l E g).hom
  let T := S.reduction ⋙ B ⋙ U
  let adj := integralComparisonConstantAdjunction l E X
  let e := (R.coefficient E).pullback g |>.realization
  let a (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :=
    (inverseImageIntegralModules l E g).mapDerivedCategoryFactors.hom.app P.obj ≫
      DerivedCategory.Q.map (inverseImageRoosComparisonComplex l E g P.obj) ≫
      (integralDerivedPullbackComparison l E g).inv.app P
  have ha (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
      Δ.map (a P ≫ e.hom.app (DerivedCategory.Q.obj P.obj)) ≫
        adj.counit.app (T.obj (DerivedCategory.Q.obj P.obj)) =
          β.app (DerivedCategory.Q.obj P.obj) := by
    simpa only [a, β, d, T, H, B, U, UY, Δ, ΔY, Ht, e, adj,
      inverseImageIntegralDerived, integralComparisonTowerCounit,
      Functor.comp_obj, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      NatTrans.comp_app, Category.assoc] using
      integralPullbackKFlatReductionCounit l E g S ((R.coefficient E).roos X)
        ((R.coefficient E).pullback g) P
  obtain ⟨κ, hP⟩ := adjunctionComparison_exists H F Δ
    (coefficientConstantTowerLimit l E X) adj T e β
    (integralOperationsGoodComplex l E Y).FullSubcategory
    (fun P ↦ DerivedCategory.Q.obj P.obj) a ha
  refine ⟨κ, ?_⟩
  intro K P q hq
  have hn := κ.naturality (DerivedCategory.Q.map q)
  apply (cancel_epi (H.map (DerivedCategory.Q.map q))).1
  rw [hn, hP]
  unfold inverseImagePullbackComparison
  erw [← Category.assoc (H.map (DerivedCategory.Q.map q)),
    (inverseImageIntegralModules l E g).mapDerivedCategoryFactors.hom.naturality q]
  simp only [a, H, F, Functor.comp_map, Category.assoc, IsIso.hom_inv_id_assoc]

private theorem sectionwiseSigma_naturality
    (C : Type (u + 1)) [Category.{u} C] (J : GrothendieckTopology C)
    (F : C ⥤ C) [F.IsContinuous J J] (U : C) (r : F.obj U ⟶ U)
    (R : Sheaf J RingCat.{u + 1})
    (c : (F.sheafPushforwardContinuous RingCat.{u + 1} J J).obj R ⟶ R) [IsIso c]
    [(SheafOfModules.pushforward.{u + 1} (F := F) (inv c)).Additive]
    (B : Type (u + 1)) [Ring B]
    (a : B →+* R.obj.obj (op U))
    (K L : CochainComplex (SheafOfModules.{u + 1} R) ℤ)
    (f : K ⟶ L) :
    let G := SheafOfModules.pushforward.{u + 1} (F := F) (inv c)
    let S := SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj (op U) ⋙
      ModuleCat.restrictScalars (R := B) a
    ∀ (sK : (S.mapHomologicalComplex (.up ℤ)).obj K ⟶
        (S.mapHomologicalComplex (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj K))
      (sL : (S.mapHomologicalComplex (.up ℤ)).obj L ⟶
        (S.mapHomologicalComplex (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj L)),
      (∀ i : ℤ, HEq (fun x ↦ sK.f i x) (fun x ↦ (K.X i).val.map r.op x)) →
      (∀ i : ℤ, HEq (fun x ↦ sL.f i x) (fun x ↦ (L.X i).val.map r.op x)) →
      (S.mapHomologicalComplex (.up ℤ)).map f ≫ sL =
        sK ≫ (S.mapHomologicalComplex (.up ℤ)).map
          ((G.mapHomologicalComplex (.up ℤ)).map f) := by
  intro G S sK sL hK hL
  apply HomologicalComplex.Hom.ext
  funext i
  ext x
  change sL.f i ((f.f i).val.app (op U) x) =
    (f.f i).val.app (op (F.obj U)) (sK.f i x)
  rw [congrFun (eq_of_heq (hL i)) _, congrFun (eq_of_heq (hK i)) _]
  exact (PresheafOfModules.naturality_apply (f.f i).val r.op x).symm

private theorem derivedSectionsNatTrans_exists
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (S : B ⥤ C) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (T : A ⥤ C) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (η : T.mapHomologicalComplex (.up ℤ) ⟶
      G.mapHomologicalComplex (.up ℤ) ⋙ S.mapHomologicalComplex (.up ℤ)) :
    ∃ σ : T.mapDerivedCategory ⟶ G.mapDerivedCategory ⋙ S.mapDerivedCategory,
      ∀ K, σ.app (DerivedCategory.Q.obj K) =
        T.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map (η.app K) ≫
          S.mapDerivedCategoryFactors.inv.app
            ((G.mapHomologicalComplex (.up ℤ)).obj K) ≫
          S.mapDerivedCategory.map (G.mapDerivedCategoryFactors.inv.app K) := by
  let α : DerivedCategory.Q ⋙ T.mapDerivedCategory ⟶
      DerivedCategory.Q ⋙ G.mapDerivedCategory ⋙ S.mapDerivedCategory :=
    T.mapDerivedCategoryFactors.hom ≫
      Functor.whiskerRight η DerivedCategory.Q ≫
      Functor.whiskerLeft (G.mapHomologicalComplex (.up ℤ)) S.mapDerivedCategoryFactors.inv ≫
      Functor.whiskerRight G.mapDerivedCategoryFactors.inv S.mapDerivedCategory
  let ff := Localization.fullyFaithfulWhiskeringLeft
    (DerivedCategory.Q (C := A)) (HomologicalComplex.quasiIso _ _) (DerivedCategory C)
  refine ⟨ff.preimage α, ?_⟩
  intro K
  exact congrArg (fun t ↦ t.app K) (ff.map_preimage α)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem integralSigmaDerived_exists :
    ∃ σ : pointFibreIntegralAmbient D l E ⟶
        inverseImageIntegralDerived l E (frobeniusPointIso D).hom ⋙
          pointFibreIntegralAmbient D l E,
      ∀ K, σ.app (DerivedCategory.Q.obj K) =
        (pointIntegralSections l E D.k).mapDerivedCategoryFactors.hom.app K ≫
          DerivedCategory.Q.map (frobeniusPointIntegralSigma D l E K) ≫
          (pointIntegralSections l E D.k).mapDerivedCategoryFactors.inv.app
            (((inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapHomologicalComplex
              (.up ℤ)).obj K) ≫
          (pointFibreIntegralAmbient D l E).map
            ((inverseImageIntegralModules l E
              (frobeniusPointIso D).hom).mapDerivedCategoryFactors.inv.app K) := by
  let S := pointIntegralSections l E D.k
  let G := inverseImageIntegralModules l E (frobeniusPointIso D).hom
  let η : S.mapHomologicalComplex (.up ℤ) ⟶
      G.mapHomologicalComplex (.up ℤ) ⋙ S.mapHomologicalComplex (.up ℤ) :=
    { app K := frobeniusPointIntegralSigma D l E K
      naturality K L f := by
        let R := (sheafCompose (ProEt.topology (Spec (.of D.k)))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)))
        let c : (isoSectionwiseInverseImage (frobeniusPointIso D).hom RingCat.{u + 1}).obj
            R ⟶ R := inverseImageCompletedCoefficientMap l E (frobeniusPointIso D).hom
        let : IsIso c := inferInstanceAs
          (IsIso (inverseImageCompletedCoefficientMap l E (frobeniusPointIso D).hom))
        let : (SheafOfModules.pushforward (F :=
            proEtaleIsoPostcompose (frobeniusPointIso D).hom) (inv c)).Additive :=
          isoSectionwiseModuleInverseImage_additive.{u, u} (frobeniusPointIso D).hom c
        exact sectionwiseSigma_naturality (Spec (.of D.k)).ProEt
          (ProEt.topology (Spec (.of D.k))) (proEtaleIsoPostcompose (frobeniusPointIso D).hom)
          (ProEt.mk (𝟙 (Spec (.of D.k)))) (frobeniusPointRestriction D) R c
          (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
          (pointIntegralSectionMap l E D.k) K L f _ _
          (Classical.choose_spec (frobeniusPointIntegralSigma_existsUnique D l E K)).1
          (Classical.choose_spec (frobeniusPointIntegralSigma_existsUnique D l E L)).1 }
  exact derivedSectionsNatTrans_exists S S G η

/-- The finite arrow Gamma(kappa) after sigma, including localization's comparisons.
Source: blueprint finite formula (blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointTransportFiniteComplex (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K) ⟶
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj
          ((finiteDerivedPullback l E n (frobeniusPointIso D).hom).obj
            (DerivedCategory.Q.obj K)) :=
  (pointFiniteSections D.k
    (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategoryFactors.hom.app
      K ≫
    DerivedCategory.Q.map (frobeniusPointFiniteSigma D l E n K) ≫
    (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategoryFactors.inv.app
      (((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapHomologicalComplex
        (.up ℤ)).obj K) ≫
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
        ((inverseImageFiniteModules l E
          (frobeniusPointIso D).hom n).mapDerivedCategoryFactors.inv.app K ≫
          inverseImagePullbackComparisonFiniteIntrinsic l (frobeniusPointIso D).hom E
            (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl) n K)

/-- The integral arrow uses the recorded resolution and map into the strict derived limit.
Source: blueprint integral formula (blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointTransportIntegralComplex
    (K : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (q : P.obj ⟶ K) [QuasiIso q] :
    (pointFibreIntegralAmbient D l E).obj (DerivedCategory.Q.obj K) ⟶
      (pointFibreIntegralAmbient D l E).obj
        ((integralDerivedPullback l E (frobeniusPointIso D).hom).obj
          (DerivedCategory.Q.obj K)) :=
  (pointIntegralSections l E D.k).mapDerivedCategoryFactors.hom.app K ≫
    DerivedCategory.Q.map (frobeniusPointIntegralSigma D l E K) ≫
    (pointIntegralSections l E D.k).mapDerivedCategoryFactors.inv.app
      (((inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapHomologicalComplex
        (.up ℤ)).obj K) ≫
    (pointFibreIntegralAmbient D l E).map
      ((inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapDerivedCategoryFactors.inv.app
          K ≫
        inverseImagePullbackComparison l E (frobeniusPointIso D).hom
          (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl) K P q)

/-- Finite transport on any derived object, using the localization's chosen representative.
Source: blueprint finite formula (blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointTransportFinite (n : ℕ)
    (N : proEtaleDerivedCategory (Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (n + 1))) :
    (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj N ⟶
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj
        ((finiteDerivedPullback l E n (frobeniusPointIso D).hom).obj N) :=
  (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
      (DerivedCategory.Q.objObjPreimageIso N).inv ≫
    frobeniusPointTransportFiniteComplex D l hl E n (DerivedCategory.Q.objPreimage N) ≫
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
      ((finiteDerivedPullback l E n (frobeniusPointIso D).hom).map
        (DerivedCategory.Q.objObjPreimageIso N).hom)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
/-- The integral arrow is uniquely specified by the explicit formula on resolutions.
This is well-definedness of the component, not naturality of a family of components.
Source: blueprint integral formula and its fixed-resolution convention
(blueprint: def-weil-frobenius-point-transport).
Proof: constant-coefficient restriction is a natural map of section complexes.
Descend it through the universal property of localization at quasi-isomorphisms.
For the integral comparison, use its recorded reduction-counit identity on good
complexes. The diagonal/derived-limit adjunction transposes the natural tower
counit to a natural comparison; injectivity of the adjunction correspondence
identifies its value on each good complex with the recorded Roos comparison.
Naturality along a resolution quasi-isomorphism gives the prescribed formula for
any resolution. Compose the descended restriction with this comparison and
conjugate along the representing isomorphism. Naturality proves that every
representative gives this same component. A flat-term K-flat resolution of one
representative exists and its formula forces uniqueness. No invertibility of
kappa on arbitrary objects is used. -/
theorem frobeniusPointTransportIntegral_existsUnique
    (N : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))) :
    ∃! f : (pointFibreIntegralAmbient D l E).obj N ⟶
        (pointFibreIntegralAmbient D l E).obj
          ((integralDerivedPullback l E (frobeniusPointIso D).hom).obj N),
      ∀ (K : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
        (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
        (q : P.obj ⟶ K) [QuasiIso q] (e : DerivedCategory.Q.obj K ≅ N),
        f = (pointFibreIntegralAmbient D l E).map e.inv ≫
          frobeniusPointTransportIntegralComplex D l hl E K P q ≫
          (pointFibreIntegralAmbient D l E).map
            ((integralDerivedPullback l E (frobeniusPointIso D).hom).map e.hom) := by
  obtain ⟨κ, hκ⟩ := integralKappaNatural_exists l E (frobeniusPointIso D).hom
    (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl)
  obtain ⟨σ, hσ⟩ := integralSigmaDerived_exists D l E
  let S := pointFibreIntegralAmbient D l E
  let F := integralDerivedPullback l E (frobeniusPointIso D).hom
  let τ : S ⟶ F ⋙ S := σ ≫ Functor.whiskerRight κ S
  have hτ (K : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
      (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (q : P.obj ⟶ K) [QuasiIso q] :
      τ.app (DerivedCategory.Q.obj K) =
        frobeniusPointTransportIntegralComplex D l hl E K P q := by
    change σ.app (DerivedCategory.Q.obj K) ≫ S.map (κ.app (DerivedCategory.Q.obj K)) = _
    rw [hσ, hκ K P q]
    simp only [frobeniusPointTransportIntegralComplex, Functor.map_comp,
      Category.assoc, S]
  have hformula (K : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
      (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (q : P.obj ⟶ K) [QuasiIso q] (e : DerivedCategory.Q.obj K ≅ N) :
      τ.app N = S.map e.inv ≫ frobeniusPointTransportIntegralComplex D l hl E K P q ≫
        S.map (F.map e.hom) := by
    calc
      _ = S.map e.inv ≫ S.map e.hom ≫ τ.app N := by
        rw [← Category.assoc, ← S.map_comp, e.inv_hom_id, S.map_id, Category.id_comp]
      _ = S.map e.inv ≫ τ.app (DerivedCategory.Q.obj K) ≫ S.map (F.map e.hom) := by
        rw [τ.naturality e.hom]
        rfl
      _ = _ := by rw [hτ K P q]
  refine ⟨τ.app N, hformula, ?_⟩
  intro f hf
  let K := DerivedCategory.Q.objPreimage N
  let e : DerivedCategory.Q.obj K ≅ N := DerivedCategory.Q.objObjPreimageIso N
  obtain ⟨P, q, hP, hflat, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) K
  let : QuasiIso q := hq
  let P' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory :=
    ⟨P, hP, fun i ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso _ (P.X i)).symm (hflat i)⟩
  exact (hf K P' q e).trans (hformula K P' q e).symm

/-- Integral point transport, fixed uniquely by its restriction and Roos-resolution formula.
Source: blueprint integral formula (blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointTransportIntegral
    (N : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))) :
    (pointFibreIntegralAmbient D l E).obj N ⟶
      (pointFibreIntegralAmbient D l E).obj
        ((integralDerivedPullback l E (frobeniusPointIso D).hom).obj N) :=
  Classical.choose (frobeniusPointTransportIntegral_existsUnique D l hl E N)

/-- The actual constructible integral pullback, with l-invertibility derived from l ≠ p.
Source: blueprint constructible-pullback paragraph
(blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointIntegralPullback :
    sfIntegralConstructibleCategory l E (Spec (.of D.k)) ⥤
      sfIntegralConstructibleCategory l E (Spec (.of D.k)) :=
  letI := frobeniusPointPrimeInvertible D l hl
  constructibleIntegralPullback l E (frobeniusPointIso D).hom

/-- Restrict the recorded finite pullback to constructible objects, using its recorded
isomorphism-preservation theorem.
Source: blueprint constructible-pullback paragraph
(blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointFinitePullback (n : ℕ) :
    (intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))).FullSubcategory ⥤
      (intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))).FullSubcategory :=
  letI := frobeniusPointPrimeInvertible D l hl
  (intrinsicFiniteTorsionConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))).lift
    ((intrinsicFiniteTorsionConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))).ι ⋙
        finiteDerivedPullback l E n (frobeniusPointIso D).hom)
    (fun K ↦ ((isomorphismFiniteDerivedPullback_termwise l E
      (frobeniusPointIso D).hom n).choose K.obj K.property).1)

/-- The finite component in the actual point-fibre target category.
Source: blueprint finite point-transport formula
(blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointTransportFiniteConstructible (n : ℕ)
    (N : (intrinsicFiniteTorsionConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))).FullSubcategory) :
    (pointFiniteFibre D l hl E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))).obj N ⟶
      (pointFiniteFibre D l hl E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))).obj
        ((frobeniusPointFinitePullback D l hl E n).obj N) :=
  ObjectProperty.homMk (frobeniusPointTransportFinite D l hl E n N.obj)

/-- The integral component in the actual finitely generated complete point-fibre category.
Source: blueprint integral point-transport formula
(blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointTransportIntegralConstructible
    (N : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    (pointIntegralFibre D l hl E).obj N ⟶
      (pointIntegralFibre D l hl E).obj ((frobeniusPointIntegralPullback D l hl E).obj N) :=
  ObjectProperty.homMk (frobeniusPointTransportIntegral D l hl E N.obj)

/-- The rational pullback object is the same integral pullback object in raw rationalization.
Source: blueprint rational paragraph (blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointRationalPullbackObj
    (N : sfRationalConstructibleCategory l E (Spec (.of D.k))) :
    sfRationalConstructibleCategory l E (Spec (.of D.k)) :=
  ⟨(frobeniusPointIntegralPullback D l hl E).obj N.obj⟩

/-- Rational transport is exactly tensor with E of the integral arrow. The only additional
arrows are the recorded coefficient-size descent and rational-object identifications.
Source: blueprint rational formula (blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointTransportRational
    (N : sfRationalConstructibleCategory l E (Spec (.of D.k))) :
    (pointRationalFibre D l hl E).obj N ⟶
      (pointRationalFibre D l hl E).obj (frobeniusPointRationalPullbackObj D l hl E N) :=
  let f : pointFibreRationalLarge D l hl E N.obj ⟶
      pointFibreRationalLarge D l hl E
        ((frobeniusPointIntegralPullback D l hl E).obj N.obj) :=
    ObjectProperty.homMk
      ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointIntegralToField l E)).mapDerivedCategory.map
          (frobeniusPointTransportIntegral D l hl E N.obj.obj))
  (pointRationalFibreObjIso D l hl E N).hom ≫
    (pointFibreSizeDescent E).map f ≫
    (pointRationalFibreObjIso D l hl E (frobeniusPointRationalPullbackObj D l hl E N)).inv

variable (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The algebraic-closure pullback object retains the actual coefficient stage.
Source: blueprint algebraic-closure paragraph
(blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointQbarPullbackObj
    (N : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :
    generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)) :=
  ⟨N.stage, frobeniusPointRationalPullbackObj D l hl
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N.stage) N.obj⟩

/-- The point transport at Qbar is represented at precisely the object's own stage E'.
The Shrink algebra equivalence is the recorded coefficient-model identification.
Source: blueprint algebraic-closure formula
(blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointTransportQbar
    (N : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :
    pointQbarFibreObj D l hl Ω N ⟶
      pointQbarFibreObj D l hl Ω (frobeniusPointQbarPullbackObj D l hl Ω N) :=
  (DerivedCategory.pointFdQbarStage l Ω N.stage).map
    ((DerivedCategory.pointFdScalarExtension (Shrink.algEquiv ℚ_[l] N.stage.val :
        AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N.stage ≃ₐ[ℚ_[l]]
          N.stage.val).toRingHom).map
      (frobeniusPointTransportRational D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N.stage) N.obj))

end WeilConjectures
