module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.SixFunctors.FrobeniusPointTransportNatural
public import Sheaf.Paper.FrobeniusCoefficientTwistsCanonical
public import Sheaf.Paper.PointFibreEquivalence
public import Sheaf.SixFunctors.FrobeniusCohomologyTransport
public import Sheaf.Paper.CompletedPullbackTensorComparison
public import Sheaf.Paper.FieldWeilShriekShiftData
public import Sheaf.Paper.ConstantGeometricStalkUnit
public import Sheaf.Paper.PointTateFiberCoefficientComparisons
public import Sheaf.Paper.PointFibreDerivedTensor
public import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.PointWeilPairingCoordinates
import Sheaf.Paper.PointWeilTransportUnitShift
import Sheaf.Paper.PointWeilTensorRepresentatives

/-! # Canonical point realization of Weil pairings

Source: literature/blueprint/latest/blueprint/sec-poincare-duality/
`sk-thm-frobenius/prop-weil-operations.proof.md`, final smooth-pairing clause,
retained rational proof Step 10 (blueprint: lem-pod-point-weil-pairing-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] AlgebraicGeometry.Scheme.residueLisseAlgebraHasDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PointWeilPairing
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem realize_postcomp (N M : C D l E) (a : N ⟶ M)
    (r : ℤ) (x : U D l hl E ⟶ N⟦r⟧) :
    realize D l hl E M r (x ≫ a⟦r⟧') =
      (DerivedCategory.homologyFunctor.{u} (ModuleCat.{u} E) r).map
        ((F D l hl E).map a) (realize D l hl E N r x) := by
  let q := Functor.commShiftIso (F D l hl E) (self := fShift D l hl E) r
  have hx : (unit D l hl E).inv ≫ (F D l hl E).map (x ≫ a⟦r⟧') ≫
      q.hom.app M =
      ((unit D l hl E).inv ≫ (F D l hl E).map x ≫ q.hom.app N) ≫
        ((F D l hl E).map a)⟦r⟧' := by
    simp only [Functor.map_comp, Category.assoc]
    rw [Functor.commShiftIso_hom_naturality]
  have h := (((DerivedCategory.homologyFunctor.{u} (ModuleCat.{u} E) 0).shiftIso
    r 0 r (add_zero r)).hom.naturality ((F D l hl E).map a))
  change (DerivedCategory.homologyFunctor.{u} (ModuleCat.{u} E) 0).map
      (((F D l hl E).map a)⟦r⟧') ≫
      (((DerivedCategory.homologyFunctor.{u} (ModuleCat.{u} E) 0).shiftIso
        r 0 r (add_zero r)).hom.app ((F D l hl E).obj M)) =
    (((DerivedCategory.homologyFunctor.{u} (ModuleCat.{u} E) 0).shiftIso
      r 0 r (add_zero r)).hom.app ((F D l hl E).obj N)) ≫
      (DerivedCategory.homologyFunctor.{u} (ModuleCat.{u} E) r).map
        ((F D l hl E).map a) at h
  dsimp only [realize]
  rw [hx, DerivedCategory.homSingleToHomology_comp, Category.assoc, h]
  rfl

/-- Canonical point transport realizes shifted Weil pairings on cohomology.
Source: blueprint final smooth-pairing clause, retained rational proof Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization).
Proof: identify the point unit with E in degree zero by constant sections and
rationalization. Field cohomology splitting and full faithfulness give realization.
Restriction and the inverse-image coprojection preserve 1; the normalized coefficient
comparison and its inverse cancel. Naturality gives transportRep and frobeniusRep.
On total tensors the two-shift comparison has sign (-1)^(j*p); the Roos shift has
second cone coordinate (-1)^r. These commute with canonical pullback comparison.
Unitality combines the two inverse coefficient maps into one. Tensor the two
Frobenius representatives, move theta through the signed shift, and apply the Weil
equation of B. The result is c inverse, then P of the pairing, then c. Every unit
endomorphism is a unique E scalar, and rational pullback is E-linear, so this
conjugation fixes it. All steps hold for zero objects and every integer shift;
no integral lattice for either rational Weil arrow is used.
-/
theorem point_weil_pairing_realization :
    frobenius D l hl E (U D l hl E) (c D l hl E) = 𝟙 _ ∧
    (∀ (N : C D l E) (r : ℤ) (x : U D l hl E ⟶ N⟦r⟧),
      realize D l hl E ((P D l hl E).obj N) r (transportRep D l hl E N r x) =
        (DerivedCategory.homologyFunctor.{u} (ModuleCat.{u} E) r).map
          (iota D l hl E N) (realize D l hl E N r x)) ∧
    (∀ (N : C D l E) (theta : (P D l hl E).obj N ≅ N) (r : ℤ)
      (x : U D l hl E ⟶ N⟦r⟧),
      realize D l hl E N r (frobeniusRep D l hl E N theta r x) =
        (DerivedCategory.homologyFunctor.{u} (ModuleCat.{u} E) r).map
          (frobenius D l hl E N theta) (realize D l hl E N r x)) ∧
    ((c D l hl E).inv ≫ (P D l hl E).map (j D l hl E) ≫
        (mu D l hl E (U D l hl E) (U D l hl E)).hom =
      j D l hl E ≫ (T D l hl E).map
        (Prod.mkHom (c D l hl E).inv (c D l hl E).inv)) ∧
    (∀ (A D₁ : C D l E) (thetaA : (P D l hl E).obj A ≅ A)
      (thetaD : (P D l hl E).obj D₁ ≅ D₁) (n : ℤ)
      (B : (T D l hl E).obj (A, D₁⟦n⟧) ⟶ U D l hl E),
      (mu D l hl E A (D₁⟦n⟧)).hom ≫
          (T D l hl E).map
            (Prod.mkHom thetaA.hom (shiftedTheta D l hl E D₁ thetaD n).hom) ≫ B =
        (P D l hl E).map B ≫ (c D l hl E).hom →
      (∀ (i : ℤ) (x : U D l hl E ⟶ A⟦i⟧) (y : U D l hl E ⟶ D₁⟦n - i⟧),
        pairingEnd D l hl E A D₁ n i B
            (frobeniusRep D l hl E A thetaA i x)
            (frobeniusRep D l hl E D₁ thetaD (n - i) y) =
          (c D l hl E).inv ≫ (P D l hl E).map
            (pairingEnd D l hl E A D₁ n i B x y) ≫ (c D l hl E).hom) ∧
      (∀ (i : ℤ)
        (x : (DerivedCategory.homologyFunctor.{u} (ModuleCat.{u} E) i).obj
          ((F D l hl E).obj A))
        (y : (DerivedCategory.homologyFunctor.{u} (ModuleCat.{u} E) (n - i)).obj
          ((F D l hl E).obj D₁)),
        pairing D l hl E A D₁ n i B
            ((DerivedCategory.homologyFunctor.{u} (ModuleCat.{u} E) i).map
              (frobenius D l hl E A thetaA) x)
            ((DerivedCategory.homologyFunctor.{u} (ModuleCat.{u} E) (n - i)).map
              (frobenius D l hl E D₁ thetaD) y) =
          pairing D l hl E A D₁ n i B x y)) := by
  obtain ⟨hu, ht, hc⟩ := point_weil_transport_unit_shift D l hl E
  obtain ⟨hj, hv⟩ := point_weil_tensor_representatives D l hl E
  have hf (N : C D l E) (theta : (P D l hl E).obj N ≅ N) (r : ℤ)
      (x : U D l hl E ⟶ N⟦r⟧) :
      realize D l hl E N r (frobeniusRep D l hl E N theta r x) =
        (DerivedCategory.homologyFunctor.{u} (ModuleCat.{u} E) r).map
          (frobenius D l hl E N theta) (realize D l hl E N r x) := by
    rw [frobeniusRep, realize_postcomp, ht]
    simp only [frobenius, Functor.map_comp, ModuleCat.comp_apply]
  refine ⟨hu, ht, hf, hj, ?_⟩
  intro A D₁ thetaA thetaD n B hB
  have hp (i : ℤ) (x : U D l hl E ⟶ A⟦i⟧)
      (y : U D l hl E ⟶ D₁⟦n - i⟧) :
      pairingEnd D l hl E A D₁ n i B
          (frobeniusRep D l hl E A thetaA i x)
          (frobeniusRep D l hl E D₁ thetaD (n - i) y) =
        (c D l hl E).inv ≫ (P D l hl E).map
          (pairingEnd D l hl E A D₁ n i B x y) ≫ (c D l hl E).hom := by
    have he (x' : U D l hl E ⟶ A⟦i⟧) (y' : U D l hl E ⟶ D₁⟦n - i⟧) :
        pairingEnd D l hl E A D₁ n i B x' y' =
          pairingVector D l hl E A D₁ n i x' y' ≫ B := by
      simp only [pairingEnd, pairingVector, Category.assoc]
    simp only [he]
    rw [hv]
    simp only [Category.assoc]
    rw [hB, Functor.map_comp]
    simp only [Category.assoc]
  refine ⟨hp, ?_⟩
  intro i x y
  let x₀ := (realization D l hl E A i).symm x
  let y₀ := (realization D l hl E D₁ (n - i)).symm y
  have hx : (realization D l hl E A i).symm
      ((DerivedCategory.homologyFunctor.{u} (ModuleCat.{u} E) i).map
        (frobenius D l hl E A thetaA) x) =
      frobeniusRep D l hl E A thetaA i x₀ := by
    have h₀ : realize D l hl E A i x₀ = x :=
      (realization D l hl E A i).apply_symm_apply x
    apply (realization D l hl E A i).injective
    rw [Equiv.apply_symm_apply]
    change _ = realize D l hl E A i (frobeniusRep D l hl E A thetaA i x₀)
    simpa only [h₀] using (hf A thetaA i x₀).symm
  have hy : (realization D l hl E D₁ (n - i)).symm
      ((DerivedCategory.homologyFunctor.{u} (ModuleCat.{u} E) (n - i)).map
        (frobenius D l hl E D₁ thetaD) y) =
      frobeniusRep D l hl E D₁ thetaD (n - i) y₀ := by
    have h₀ : realize D l hl E D₁ (n - i) y₀ = y :=
      (realization D l hl E D₁ (n - i)).apply_symm_apply y
    apply (realization D l hl E D₁ (n - i)).injective
    rw [Equiv.apply_symm_apply]
    change _ = realize D l hl E D₁ (n - i)
      (frobeniusRep D l hl E D₁ thetaD (n - i) y₀)
    simpa only [h₀] using (hf D₁ thetaD (n - i) y₀).symm
  dsimp only [pairing]
  rw [hx, hy, hp, hc]


section SchemeActions
open FrobeniusExchange
variable (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom]
  [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
  (R : SupportModel (D.geometricFiber Y₀).hom (galois D Y₀) (frobeniusPointIso D).hom)

/-- The retained rational support operation: direct image or the chosen compact recipe.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
def operation : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left ⥤
    C D l E :=
  letI := sfWeilPrimeInvertible D l hl Y₀
  letI := frobeniusPointPrimeInvertible D l hl
  letI : IsIso (galois D Y₀) := inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (D.geometricFiber Y₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber Y₀).hom⟩
  letI : (D.geometricFiber Y₀).hom.IsOver (Spec (.of D.k)) := ⟨Category.comp_id _⟩
  letI : IsSeparated (D.geometricFiber Y₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  modelRationalFunctor l D.k (zlClosurePrimeUnit D l hl)
    (D.geometricFiber Y₀).hom (galois D Y₀) (frobeniusPointIso D).hom R E

/-- The actual rational exchange map for the retained structure square and support model.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
def exchange
    (K : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :
    (P D l hl E).obj ((operation D l hl E Y₀ R).obj K) ⟶
      (operation D l hl E Y₀ R).obj
        ((@rationalDerivedPullback l _ E _ _ _ _ _ (galois D Y₀)
          (sfWeilPrimeInvertible D l hl Y₀) (sfWeilPrimeInvertible D l hl Y₀)).obj K) :=
  letI := sfWeilPrimeInvertible D l hl Y₀
  letI := frobeniusPointPrimeInvertible D l hl
  letI : IsIso (galois D Y₀) := inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (D.geometricFiber Y₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber Y₀).hom⟩
  letI : (D.geometricFiber Y₀).hom.IsOver (Spec (.of D.k)) := ⟨Category.comp_id _⟩
  letI : IsSeparated (D.geometricFiber Y₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  by
    simpa only [P, operation, modelRationalSource, modelRationalTarget, Functor.comp_obj] using
      (modelRationalExchange l D.k (zlClosurePrimeUnit D l hl)
        (D.geometricFiber Y₀).hom (galois D Y₀) (frobeniusPointIso D).hom R E).app K

/-- The structure-square Frobenius exchange is invertible for either support recipe.
Proof: geometric Frobenius is an automorphism and its structure square is
cartesian. The ordinary base-change mate is invertible after this relabelling.
For compact support apply the same relabelling to the retained open/proper
compactification. Whole-system exchange and rational localization preserve the
inverse. Thus the two constructors of SupportModel give invertible exchange.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
theorem exchange_isIso
    (K : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :
    IsIso (exchange D l hl E Y₀ R K) := by
  sorry

/-- The induced Weil datum: exchange followed by the support operation on theta.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
def operationTheta
    (K : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left)
    (theta : (@rationalDerivedPullback l _ E _ _ _ _ _ (galois D Y₀)
      (sfWeilPrimeInvertible D l hl Y₀) (sfWeilPrimeInvertible D l hl Y₀)).obj K ≅ K) :=
  letI := exchange_isIso D l hl E Y₀ R K
  asIso (exchange D l hl E Y₀ R K) ≪≫ (operation D l hl E Y₀ R).mapIso theta

/-- The scheme clause, with compact and ordinary support kept as the two
constructors of SupportModel. In particular apply this to the compact model for K
and to the direct model for L; no properness or comparison of support conventions occurs.
Source: blueprint final smooth-pairing clause, retained rational proof Step 7
(blueprint: lem-pod-point-weil-pairing-realization).
Proof: expand operationTheta and the definition of Frobenius. Functoriality factors
F(exchange followed by operation(theta)) into F(exchange) followed by F(operation(theta)).
The preceding iota followed by F(exchange) is exactly frobeniusTransportRational,
including its rational-pullback object identification. This is a derived equality,
so applying every cohomology functor gives precisely the two specified actions.
-/
theorem compact_ordinary_specialization
    (K : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left)
    (theta : (@rationalDerivedPullback l _ E _ _ _ _ _ (galois D Y₀)
      (sfWeilPrimeInvertible D l hl Y₀) (sfWeilPrimeInvertible D l hl Y₀)).obj K ≅ K) :
    frobenius D l hl E ((operation D l hl E Y₀ R).obj K)
        (operationTheta D l hl E Y₀ R K theta) =
      (DerivedCategory.pointFiniteDimensional E).ι.map
          (frobeniusTransportRational D l hl E Y₀ R K) ≫
        (F D l hl E).map ((operation D l hl E Y₀ R).map theta.hom) := by
  dsimp only [frobenius, operationTheta, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  rw [Functor.map_comp, ← Category.assoc]
  congr 1
  dsimp only [iota, frobeniusTransportRational, F, Functor.comp_map]
  rw [Functor.map_comp, Functor.map_comp, Category.assoc]
  rfl

end SchemeActions

end WeilConjectures.PointWeilPairing
