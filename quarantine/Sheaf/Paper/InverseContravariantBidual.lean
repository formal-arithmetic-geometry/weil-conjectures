/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.SitePerfectComplex
public import Sheaf.Paper.FrobeniusCoefficientTwistsCanonical
public import Sheaf.Paper.DerivedAutomorphismHomEvaluation

import Sheaf.Paper.AdmissibleHomSubstitution
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

import Sheaf.Paper.CompletedTensorHomTranspose
import Sheaf.Paper.RationalTensorSymmetry
import Sheaf.Paper.DerivedPullbackTensorIso

/-! # Coefficient biduality for inverse contravariant rational Weil data

Source: current Weil blueprint, sec-poincare-duality/sk-thm-frobenius,
prop-weil-operations.proof, final duality/pairing paragraph; sec-six-functors,
cor-coef-verdier-weil-equivariance.proof, paragraph 2.
(blueprint: lem-pod-inverse-contravariant-bidual).

The dual structures use the actual evaluation-defined pullback comparison and
contravariant inverse. The bidual map retains the canonical signed symmetry.
The two domain lemmas supply proofs for the existing partial internal-Hom API.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem partialUntranspose
    {C : Type*} [Category* C] [Preadditive C]
    {T : C × C ⥤ C} {J : ObjectProperty (Cᵒᵖ × C)}
    {H : J.FullSubcategory ⥤ C} (S : PodPartialClosed T J H)
    (L : C) (P : J.FullSubcategory) (f : L ⟶ H.obj P) :
    (S.transpose L P).symm f = T.map (Prod.mkHom f (𝟙 _)) ≫ S.evaluation P := by
  apply (S.transpose L P).injective
  rw [AddEquiv.apply_symm_apply, S.parameter_naturality]
  simp only [PodPartialClosed.evaluation, AddEquiv.apply_symm_apply, Category.comp_id]

private theorem partialUntransposeNaturality
    {C : Type*} [Category* C] [Preadditive C]
    {T : C × C ⥤ C} {J : ObjectProperty (Cᵒᵖ × C)}
    {H : J.FullSubcategory ⥤ C} (S : PodPartialClosed T J H)
    (beta : ∀ A B : C, T.obj (A, B) ≅ T.obj (B, A))
    (hn : ∀ (A B A' B' : C) (f : A ⟶ A') (g : B ⟶ B'),
      (beta A B).hom ≫ T.map (Prod.mkHom g f) =
        T.map (Prod.mkHom f g) ≫ (beta A' B').hom)
    (tau : ∀ L P, (L ⟶ H.obj P) ≃+ (T.obj (P.obj.1.unop, L) ⟶ P.obj.2))
    (ht : CoefficientTransposeLaws S beta (fun L P f ↦ tau L P f))
    (L L' : C) (P P' : J.FullSubcategory) (f : L' ⟶ L)
    (g : P ⟶ P') (phi : L ⟶ H.obj P) :
    (S.transpose L' P').symm (f ≫ phi ≫ H.map g) =
      T.map (Prod.mkHom f g.hom.1.unop) ≫
        (S.transpose L P).symm phi ≫ g.hom.2 := by
  apply (cancel_epi (beta P'.obj.1.unop L').hom).mp
  calc
    _ = tau L' P' (f ≫ phi ≫ H.map g) := (ht.symmetry _ _ _).symm
    _ = _ := ht.naturality L L' P P' f g phi
    _ = _ := by
      rw [ht.symmetry]
      simpa only [Category.assoc] using congrArg
        (fun k ↦ k ≫ (S.transpose L P).symm phi ≫ g.hom.2)
        (hn P'.obj.1.unop L' P.obj.1.unop L g.hom.1.unop f).symm

private theorem partialDualEvaluation
    {C : Type*} [Category* C] [Preadditive C]
    {T : C × C ⥤ C} {J : ObjectProperty (Cᵒᵖ × C)}
    {H : J.FullSubcategory ⥤ C} (S : PodPartialClosed T J H)
    (hs : ∀ (L L' : C) (P P' : J.FullSubcategory) (f : L' ⟶ L)
      (g : P ⟶ P') (phi : L ⟶ H.obj P),
      (S.transpose L' P').symm (f ≫ phi ≫ H.map g) =
        T.map (Prod.mkHom f g.hom.1.unop) ≫
          (S.transpose L P).symm phi ≫ g.hom.2)
    (F : C ⥤ C) (h : ∀ P : J.FullSubcategory, J ((F.op.prod F).obj P.obj))
    (mu : ∀ A B, F.obj (T.obj (A, B)) ≅ T.obj (F.obj A, F.obj B))
    (P : J.FullSubcategory) (a : F.obj P.obj.1.unop ≅ P.obj.1.unop)
    (c : F.obj P.obj.2 ≅ P.obj.2) :
    T.map (Prod.mkHom
      (podPartialHomComparison S S F h mu P ≫
        H.map (ObjectProperty.homMk (Prod.mkHom a.inv.op c.hom))) a.hom) ≫
      S.evaluation P = (mu _ _).inv ≫ F.map (S.evaluation P) ≫ c.hom := by
  let R := (podPairPullback F J J h).obj P
  let r : R ⟶ P := ObjectProperty.homMk (Prod.mkHom a.inv.op c.hom)
  let k := podPartialHomComparison S S F h mu P
  have he : (S.transpose _ P).symm (k ≫ H.map r) =
      T.map (Prod.mkHom k a.inv) ≫ S.evaluation R ≫ c.hom := by
    simpa only [Category.id_comp, PodPartialClosed.evaluation, r,
      ObjectProperty.homMk, Prod.mkHom, Quiver.Hom.unop_op] using
      hs (H.obj R) (F.obj (H.obj P)) R P k r (𝟙 _)
  rw [partialUntranspose] at he
  change T.map (Prod.mkHom (k ≫ H.map r) a.hom) ≫ S.evaluation P = _
  calc
    _ = T.map (Prod.mkHom (𝟙 _) a.hom) ≫
        (T.map (Prod.mkHom (k ≫ H.map r) (𝟙 _)) ≫ S.evaluation P) := by
      simp only [← Functor.map_comp_assoc, CategoryTheory.prod_comp,
        Category.id_comp, Category.comp_id]
    _ = T.map (Prod.mkHom (𝟙 _) a.hom) ≫
        (T.map (Prod.mkHom k a.inv) ≫ S.evaluation R ≫ c.hom) := by rw [he]
    _ = T.map (Prod.mkHom k (𝟙 _)) ≫ S.evaluation R ≫ c.hom := by
      simp only [← Functor.map_comp_assoc, CategoryTheory.prod_comp,
        Category.id_comp, Iso.hom_inv_id]
      rfl
    _ = (S.transpose _ R).symm k ≫ c.hom := by
      rw [partialUntranspose]
      exact (Category.assoc _ _ _).symm
    _ = _ := by
      dsimp only [k, podPartialHomComparison]
      change ((S.transpose _ R).symm (S.transpose _ R _) ≫ _) = _
      rw [AddEquiv.symm_apply_apply, Category.assoc]

private theorem partialBidualEquivariance
    {C : Type*} [Category* C] [Preadditive C]
    {T : C × C ⥤ C} {J : ObjectProperty (Cᵒᵖ × C)}
    {H : J.FullSubcategory ⥤ C} (S : PodPartialClosed T J H)
    (F : C ⥤ C) (mu : T ⋙ F ≅ F.prod F ⋙ T)
    (beta : ∀ A B : C, T.obj (A, B) ≅ T.obj (B, A))
    (hn : ∀ (A B A' B' : C) (f : A ⟶ A') (g : B ⟶ B'),
      (beta A B).hom ≫ T.map (Prod.mkHom g f) =
        T.map (Prod.mkHom f g) ≫ (beta A' B').hom)
    (hb : ∀ A B, F.map (beta A B).hom ≫ (mu.app (B, A)).hom =
      (mu.app (A, B)).hom ≫ (beta (F.obj A) (F.obj B)).hom)
    (A : C) (Q : J.FullSubcategory)
    (a : F.obj A ≅ A) (b : F.obj Q.obj.1.unop ≅ Q.obj.1.unop)
    (c : F.obj Q.obj.2 ≅ Q.obj.2) (d : F.obj (H.obj Q) ≅ H.obj Q)
    (e : T.obj (Q.obj.1.unop, A) ⟶ Q.obj.2)
    (he : T.map (Prod.mkHom b.hom a.hom) ≫ e =
      (mu.app (Q.obj.1.unop, A)).inv ≫ F.map e ≫ c.hom)
    (hd : T.map (Prod.mkHom d.hom b.hom) ≫ S.evaluation Q =
      (mu.app (H.obj Q, Q.obj.1.unop)).inv ≫ F.map (S.evaluation Q) ≫ c.hom) :
    a.hom ≫ S.transpose A Q ((beta A Q.obj.1.unop).hom ≫ e) =
      F.map (S.transpose A Q ((beta A Q.obj.1.unop).hom ≫ e)) ≫ d.hom := by
  let j := S.transpose A Q ((beta A Q.obj.1.unop).hom ≫ e)
  have hj : T.map (Prod.mkHom j (𝟙 _)) ≫ S.evaluation Q =
      (beta A Q.obj.1.unop).hom ≫ e := by
    rw [← partialUntranspose]
    exact AddEquiv.symm_apply_apply _ _
  have hswap : (beta (F.obj A) (F.obj Q.obj.1.unop)).hom ≫
        (mu.app (Q.obj.1.unop, A)).inv =
      (mu.app (A, Q.obj.1.unop)).inv ≫ F.map (beta A Q.obj.1.unop).hom := by
    apply (cancel_epi (mu.app (A, Q.obj.1.unop)).hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← hb]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hleft : T.map (Prod.mkHom (a.hom ≫ j) b.hom) ≫ S.evaluation Q =
      (mu.app (A, Q.obj.1.unop)).inv ≫
        F.map ((beta A Q.obj.1.unop).hom ≫ e) ≫ c.hom := by
    calc
      _ = T.map (Prod.mkHom a.hom b.hom) ≫
          (T.map (Prod.mkHom j (𝟙 _)) ≫ S.evaluation Q) := by
        simp only [← Functor.map_comp_assoc, CategoryTheory.prod_comp, Category.comp_id]
      _ = T.map (Prod.mkHom a.hom b.hom) ≫ (beta A Q.obj.1.unop).hom ≫ e := by
        rw [hj]
      _ = (beta (F.obj A) (F.obj Q.obj.1.unop)).hom ≫
          T.map (Prod.mkHom b.hom a.hom) ≫ e := by
        rw [← Category.assoc, ← hn]
        simp only [Category.assoc]
      _ = _ := by rw [he, ← Category.assoc, hswap]; simp only [Category.assoc, F.map_comp]
  have hright : T.map (Prod.mkHom (F.map j ≫ d.hom) b.hom) ≫ S.evaluation Q =
      (mu.app (A, Q.obj.1.unop)).inv ≫
        F.map ((beta A Q.obj.1.unop).hom ≫ e) ≫ c.hom := by
    calc
      _ = T.map (Prod.mkHom (F.map j) (𝟙 _)) ≫
          (T.map (Prod.mkHom d.hom b.hom) ≫ S.evaluation Q) := by
        simp only [← Functor.map_comp_assoc, CategoryTheory.prod_comp, Category.id_comp]
      _ = T.map (Prod.mkHom (F.map j) (𝟙 _)) ≫
          (mu.app (H.obj Q, Q.obj.1.unop)).inv ≫
            F.map (S.evaluation Q) ≫ c.hom := by rw [hd]
      _ = (mu.app (A, Q.obj.1.unop)).inv ≫
          F.map (T.map (Prod.mkHom j (𝟙 _))) ≫ F.map (S.evaluation Q) ≫ c.hom := by
        have h := mu.inv.naturality (Prod.mkHom j (𝟙 Q.obj.1.unop))
        simpa only [Functor.comp_map, Functor.prod_map, F.map_id, Iso.app_inv, Category.assoc] using
          congrArg (fun k ↦ k ≫ F.map (S.evaluation Q) ≫ c.hom) h
      _ = _ := by rw [← F.map_comp_assoc, hj]
  apply (S.transpose (F.obj A) Q).symm.injective
  rw [partialUntranspose, partialUntranspose]
  apply (cancel_epi (T.mapIso (Iso.refl (F.obj A) |>.prod b)).hom).mp
  change T.map (Prod.mkHom (𝟙 _) b.hom) ≫ _ = _
  simpa only [← Functor.map_comp_assoc, CategoryTheory.prod_comp,
    Category.id_comp, Category.comp_id, Functor.mapIso_hom, Iso.prod_hom,
    Iso.refl_hom] using hleft.trans hright.symm

/-- Inverse contravariance on a permitted pair: first the evaluation-defined
comparison, then internal Hom applied to theta inverse and the coefficient datum.
Its inverse uses the inverses of these specified maps, with no choice of an arrow.
Source: current blueprint, cor-coef-verdier-weil-equivariance.proof, paragraph 2
(blueprint: lem-pod-inverse-contravariant-bidual). -/
def podInverseContravariantDatum
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    (g : X ⟶ X) [IsIso g]
    (Q : (constructibleRationalHomPairs l E X).FullSubcategory)
    (theta : (rationalDerivedPullback l E g).obj Q.obj.1.unop ≅ Q.obj.1.unop)
    (c : (rationalDerivedPullback l E g).obj Q.obj.2 ≅ Q.obj.2) :
    (rationalDerivedPullback l E g).obj ((rationalDerivedInternalHom l E X).obj Q) ≅
      (rationalDerivedInternalHom l E X).obj Q :=
  @asIso _ _ _ _ (podRationalHomComparison l E g Q)
      ((podRationalHomComparison_laws l E g).1.isIso Q) ≪≫
    (rationalDerivedInternalHom l E X).mapIso
      (ObjectProperty.isoMk _ (theta.symm.op.prod c))

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

include hl in
private theorem coefficientPairPermitted
    (M N : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) :
    constructibleRationalHomPairs l E (D.geometricFiber X₀).left (op M, N) := by
  let C : D.CoefficientDatum :=
    { l := l, different := hl, Qbar := AlgebraicClosure E }
  let X : SixFunctorSpace D := ⟨D.geometricFiber X₀, by
    change LocallyOfFiniteType (pullback.snd X₀.hom _) ∧
      QuasiCompact (pullback.snd X₀.hom _)
    exact ⟨inferInstance, inferInstance⟩⟩
  let : IsSeparated X.obj.hom := by
    change IsSeparated (pullback.snd X₀.hom _)
    infer_instance
  exact AdmissibleHomSubstitution.rationalPairPermitted D C E X M N

/-- The perfect coefficient-dual pair belongs to the existing Hom domain.
Source: node proof Step 1, perfect-dual stability at zero twist and shift
(blueprint: lem-pod-inverse-contravariant-bidual).
Proof: use the perfect coefficient domain of
lem-sf-perfect-dual-pair-and-tate-stability with the coefficient line at twist zero.
Its normalized coefficient dual is constructible and is the recorded internal Hom.
This is a domain proof only; it does not choose the dual object or its evaluation. -/
theorem podCoefficientDual_permitted
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left)
    (hK : IsSfRationalCoefficientSitePerfect l E (D.geometricFiber X₀).left K) :
    constructibleRationalHomPairs l E (D.geometricFiber X₀).left
      (op K, (FrobeniusCoefficientTwists.rationalWeilLine D l hl X₀ E 0).carrier) := by
  have _ := hK
  exact coefficientPairPermitted D l hl X₀ E _ _

/-- The actual permitted pair (K,E_X), with the canonical coefficient object.
Source: node proof Step 1 (blueprint: lem-pod-inverse-contravariant-bidual). -/
def podCoefficientDualPair
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left)
    (hK : IsSfRationalCoefficientSitePerfect l E (D.geometricFiber X₀).left K) :
    (constructibleRationalHomPairs l E (D.geometricFiber X₀).left).FullSubcategory :=
  ⟨(op K, (FrobeniusCoefficientTwists.rationalWeilLine D l hl X₀ E 0).carrier),
    podCoefficientDual_permitted D l hl X₀ E K hK⟩

/-- Coefficient dual means the existing rational internal Hom into E_X.
Source: node statement (blueprint: lem-pod-inverse-contravariant-bidual). -/
def podCoefficientDual
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left)
    (hK : IsSfRationalCoefficientSitePerfect l E (D.geometricFiber X₀).left K) :
    sfRationalConstructibleCategory l E (D.geometricFiber X₀).left :=
  (rationalDerivedInternalHom l E (D.geometricFiber X₀).left).obj
    (podCoefficientDualPair D l hl X₀ E K hK)

/-- The second coefficient-dual pair is also permitted.
Source: node proof Step 1, perfect-dual stability
(blueprint: lem-pod-inverse-contravariant-bidual).
Proof: perfect-dual stability keeps K dual site-perfect. Apply the same coefficient
Hom-domain assertion to this dual and the zero-twist coefficient line. Its internal
Hom is therefore the constructible second dual. No inverse or Frobenius datum is
used for this domain assertion. -/
theorem podCoefficientBidual_permitted
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left)
    (hK : IsSfRationalCoefficientSitePerfect l E (D.geometricFiber X₀).left K) :
    constructibleRationalHomPairs l E (D.geometricFiber X₀).left
      (op (podCoefficientDual D l hl X₀ E K hK),
        (FrobeniusCoefficientTwists.rationalWeilLine D l hl X₀ E 0).carrier) := by
  have _ := hK
  exact coefficientPairPermitted D l hl X₀ E _ _

/-- The actual pair (K dual,E_X) on which the second dual is evaluated.
Source: node statement (blueprint: lem-pod-inverse-contravariant-bidual). -/
def podCoefficientBidualPair
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left)
    (hK : IsSfRationalCoefficientSitePerfect l E (D.geometricFiber X₀).left K) :
    (constructibleRationalHomPairs l E (D.geometricFiber X₀).left).FullSubcategory :=
  ⟨(op (podCoefficientDual D l hl X₀ E K hK),
    (FrobeniusCoefficientTwists.rationalWeilLine D l hl X₀ E 0).carrier),
      podCoefficientBidual_permitted D l hl X₀ E K hK⟩

/-- The first inverse contravariant Weil isomorphism, for arbitrary rational theta.
Source: node displayed formula for theta of K dual
(blueprint: lem-pod-inverse-contravariant-bidual). -/
def podCoefficientDualStructure (K : sfWeilComplex D l hl X₀ E)
    (hK : IsSfRationalCoefficientSitePerfect l E (D.geometricFiber X₀).left K.carrier) :
    (sfWeilFrobeniusPullback D l hl X₀ E).obj
        (podCoefficientDual D l hl X₀ E K.carrier hK) ≅
      podCoefficientDual D l hl X₀ E K.carrier hK :=
  @podInverseContravariantDatum l _ E _ _ _ (D.geometricFiber X₀).left
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x) (D.geometricFrobenius X₀).hom _
    (podCoefficientDualPair D l hl X₀ E K.carrier hK) K.str
    (FrobeniusCoefficientTwists.rationalWeilLine D l hl X₀ E 0).str

/-- The second structure is obtained by exactly the same inverse contravariant formula.
Source: node displayed formula for theta of K double dual
(blueprint: lem-pod-inverse-contravariant-bidual). -/
def podCoefficientBidualStructure (K : sfWeilComplex D l hl X₀ E)
    (hK : IsSfRationalCoefficientSitePerfect l E (D.geometricFiber X₀).left K.carrier) :
    (sfWeilFrobeniusPullback D l hl X₀ E).obj
        ((rationalDerivedInternalHom l E (D.geometricFiber X₀).left).obj
          (podCoefficientBidualPair D l hl X₀ E K.carrier hK)) ≅
      (rationalDerivedInternalHom l E (D.geometricFiber X₀).left).obj
        (podCoefficientBidualPair D l hl X₀ E K.carrier hK) :=
  @podInverseContravariantDatum l _ E _ _ _ (D.geometricFiber X₀).left
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x) (D.geometricFrobenius X₀).hom _
    (podCoefficientBidualPair D l hl X₀ E K.carrier hK)
    (podCoefficientDualStructure D l hl X₀ E K hK)
    (FrobeniusCoefficientTwists.rationalWeilLine D l hl X₀ E 0).str

/-- The canonical coefficient bidual map is the actual evaluation transpose.
The Hom-first counit S.evaluation is ev_K after the signed symmetry, so the
additional braiding below converts it into the Hom-first transpose convention.
Source: node displayed definition of delta_K
(blueprint: lem-pod-inverse-contravariant-bidual). -/
def podCoefficientBidualMap
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left)
    (hK : IsSfRationalCoefficientSitePerfect l E (D.geometricFiber X₀).left K) :
    K ⟶ (rationalDerivedInternalHom l E (D.geometricFiber X₀).left).obj
      (podCoefficientBidualPair D l hl X₀ E K hK) :=
  (@podRationalClosed l _ E _ _ _ (D.geometricFiber X₀).left
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)).transpose K
      (podCoefficientBidualPair D l hl X₀ E K hK)
      ((@pullbackTensorRationalBraiding l _ E _ _ _ (D.geometricFiber X₀).left
        (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x) K
        (podCoefficientDual D l hl X₀ E K hK)).hom ≫
        (@podRationalClosed l _ E _ _ _ (D.geometricFiber X₀).left
          (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)).evaluation
            (podCoefficientDualPair D l hl X₀ E K hK))

attribute [local irreducible] rationalDerivedTensor rationalDerivedInternalHom
  rationalDerivedPullback pullbackTensorRationalBraiding canonicalRationalPullbackTensor
  podRationalClosed Scheme.residueField

set_option maxHeartbeats 800000 in
-- The coefficient and geometric-base-change instances need extra elaboration heartbeats.
/-- Coefficient biduality is a Weil arrow for arbitrary rational inverse
contravariant structures, without any stable integral lattice.
Source: current blueprint prop-weil-operations.proof, final duality/pairing paragraph;
cor-coef-verdier-weil-equivariance.proof, paragraph 2
(blueprint: lem-pod-inverse-contravariant-bidual).

Proof: (1) Perfect-dual stability permits both coefficient Hom pairs. The
comparison is invertible by lem-pod-derived-automorphism-hom-evaluation; Hom
functoriality makes both displayed inverse contravariant structures isomorphisms.
(2) Rational transpose naturality cancels theta inverse against theta, giving
for each dual evaluation e_M(theta_M tensor theta_dual) = c P(e_M) mu inverse.
(3) Put b = ev_K sigma and delta = its transpose. By the transpose identity,
evaluation at the first dual composed with 1 tensor delta equals b. Injectivity
reduces the claimed equation to two uncurried maps; precompose with the
invertible theta_dual tensor 1.
(4) The first composite equals c P(b) mu inverse by symmetry naturality and
compatibility of pullback tensor with the signed symmetry.
(5) The second equals the same map by the other evaluation identity and tensor
comparison naturality in the actual rational arrow delta.
(6) Cancel theta_dual tensor 1 and use transpose injectivity. On a point theta=l
has dual l inverse and second dual l; at zero both arrows are zero. All steps
use arbitrary rational arrows, as in lem-coef-completed-tensor-hom-transpose. -/
theorem podInverseContravariantBidual
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (ι : E →ₐ[Padic l] Ω) (K : sfWeilComplex D l hl X₀ E)
    (hK : IsSfRationalCoefficientSitePerfect l E (D.geometricFiber X₀).left K.carrier) :
    K.str.hom ≫ podCoefficientBidualMap D l hl X₀ E K.carrier hK =
      (sfWeilFrobeniusPullback D l hl X₀ E).map
        (podCoefficientBidualMap D l hl X₀ E K.carrier hK) ≫
          (podCoefficientBidualStructure D l hl X₀ E K hK).hom := by
  have _ := ι
  let : ∀ x : (D.geometricFiber X₀).left,
      Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
    fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  let : (D.geometricFiber X₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber X₀).hom⟩
  let : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) := by
    change LocallyOfFiniteType (pullback.snd X₀.hom _)
    infer_instance
  let : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) := by
    change QuasiCompact (pullback.snd X₀.hom _)
    infer_instance
  let : IsSeparated ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) := by
    change IsSeparated (pullback.snd X₀.hom _)
    infer_instance
  let C : D.CoefficientDatum :=
    { l := l, different := hl, Qbar := AlgebraicClosure E }
  let S := podRationalClosed l E (D.geometricFiber X₀).left
  let T := rationalDerivedTensor l E (D.geometricFiber X₀).left
  let H := rationalDerivedInternalHom l E (D.geometricFiber X₀).left
  let F := rationalDerivedPullback l E (D.geometricFrobenius X₀).hom
  let beta := pullbackTensorRationalBraiding l E (D.geometricFiber X₀).left
  have hn : ∀ (A B A' B' : sfRationalConstructibleCategory l E
      (D.geometricFiber X₀).left) (f : A ⟶ A') (g : B ⟶ B'),
      (beta A B).hom ≫ T.map (Prod.mkHom g f) =
        T.map (Prod.mkHom f g) ≫ (beta A' B').hom := by
    intro A B A' B' f g
    exact (rationalTensorSymmetry_laws D l hl (D.geometricFiber X₀).left E).1
      B' A' B A g f
  obtain ⟨tau, ht, _⟩ := (completedTensorHomTranspose D C E
    (D.geometricFiber X₀).left).2
  have hs := partialUntransposeNaturality S beta hn tau ht
  obtain ⟨mu, hmu⟩ := (derivedPullbackTensorIso l E
    (D.geometricFrobenius X₀).hom 0 Ω).2.2.2.2.2.2.1
  let P := podCoefficientDualPair D l hl X₀ E K.carrier hK
  let Q := podCoefficientBidualPair D l hl X₀ E K.carrier hK
  let c := (FrobeniusCoefficientTwists.rationalWeilLine D l hl X₀ E 0).str
  have ev
      (R : (constructibleRationalHomPairs l E (D.geometricFiber X₀).left).FullSubcategory)
      (a : F.obj R.obj.1.unop ≅ R.obj.1.unop)
      (c : F.obj R.obj.2 ≅ R.obj.2) :
      T.map (Prod.mkHom (podInverseContravariantDatum l E
        (D.geometricFiber X₀).left (D.geometricFrobenius X₀).hom R a c).hom a.hom) ≫
        S.evaluation R = (mu.app (H.obj R, R.obj.1.unop)).inv ≫
          F.map (S.evaluation R) ≫ c.hom := by
    simpa only [hmu, S, T, H, F, podRationalHomComparison,
      podInverseContravariantDatum, Iso.trans_hom, asIso_hom,
      Functor.mapIso_hom, ObjectProperty.isoMk_hom, Iso.symm_hom, Iso.op_hom,
      Iso.prod_hom] using
      partialDualEvaluation S hs F (podRationalPairs_pullback l E
        (D.geometricFrobenius X₀).hom) (canonicalRationalPullbackTensor l E
        (D.geometricFrobenius X₀).hom) R a c
  have hb : ∀ A B, F.map (beta A B).hom ≫ (mu.app (B, A)).hom =
      (mu.app (A, B)).hom ≫ (beta (F.obj A) (F.obj B)).hom := by
    intro A B
    simpa only [hmu] using canonicalRationalPullbackTensor_braiding_spec l E
      (D.geometricFrobenius X₀).hom A B
  exact partialBidualEquivariance S F mu beta hn hb K.carrier Q K.str
    (podCoefficientDualStructure D l hl X₀ E K hK) c
    (podCoefficientBidualStructure D l hl X₀ E K hK) (S.evaluation P)
    (ev P K.str c) (ev Q (podCoefficientDualStructure D l hl X₀ E K hK) c)

end WeilConjectures
