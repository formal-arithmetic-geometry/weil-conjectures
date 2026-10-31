/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GaloisAdicDataFromFinite
import WeilConjectures.AlgebraicGeometry.GaloisAdicRationalProperties
import WeilConjectures.AlgebraicGeometry.GaloisAdicAlgebraicScalar
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Tensor and unit comparisons for algebraic l-adic sheaves -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open scoped TensorProduct MonoidalCategory

namespace AlgebraicGeometry.Scheme

private def scalarRep
    (E L : Type (u + 1)) [Field E] [Field L] [Algebra E L]
    {G : Type u} [Group G] (X : Rep.{u + 1} E G) : Rep.{u + 1} L G :=
  Rep.of ((Module.End.baseChangeHom E L X.V).toMonoidHom.comp X.ρ)

private def scalarMapIso
    (E L : Type (u + 1)) [Field E] [Field L] [Algebra E L]
    {G : Type u} [Group G] {X Y : Rep.{u + 1} E G} (r : X ≅ Y) :
    scalarRep E L X ≅ scalarRep E L Y := by
  let e := ((forget₂ (Rep.{u + 1} E G) (ModuleCat E)).mapIso r).toLinearEquiv
  exact Rep.mkIso
    { toLinearEquiv := e.baseChange E L _ _
      isIntertwining' := fun g ↦ by
        apply TensorProduct.AlgebraTensorModule.ext
        intro a x
        change TensorProduct.tmul E a (r.hom.hom (X.ρ g x)) =
          TensorProduct.tmul E a (Y.ρ g (r.hom.hom x))
        rw [Rep.hom_comm_apply r.hom] }

private def scalarTowerIso
    (E L Q : Type (u + 1)) [Field E] [Field L] [Field Q]
    [Algebra E L] [Algebra E Q] [Algebra L Q] [IsScalarTower E L Q]
    {G : Type u} [Group G] (X : Rep.{u + 1} E G) :
    scalarRep L Q (scalarRep E L X) ≅ scalarRep E Q X := by
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange E L Q Q X.V
  exact Rep.mkIso
    { toLinearEquiv := e
      isIntertwining' := fun g ↦ by
        apply TensorProduct.AlgebraTensorModule.ext
        intro a v
        induction v using TensorProduct.induction_on with
        | zero => simp only [TensorProduct.tmul_zero, map_zero]
        | add x z hx hz => simp only [TensorProduct.tmul_add, map_add, hx, hz]
        | tmul b x =>
          change e (a ⊗ₜ[L] (b ⊗ₜ[E] X.ρ g x)) =
            (LinearMap.baseChange Q (X.ρ g)) (e (a ⊗ₜ[L] (b ⊗ₜ[E] x)))
          simp only [e, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
            LinearMap.baseChange_tmul] }

private noncomputable def scalarTensorIso
    (E Q : Type (u + 1)) [Field E] [Field Q] [Algebra E Q]
    {G : Type u} [Group G] (X Y : Rep.{u + 1} E G) :
    scalarRep E Q X ⊗ scalarRep E Q Y ≅ scalarRep E Q (X ⊗ Y) := by
  let e := (TensorProduct.AlgebraTensorModule.distribBaseChange E Q X.V Y.V).symm
  exact Rep.mkIso
    { toLinearEquiv := e
      isIntertwining' := fun g ↦ by
        apply TensorProduct.AlgebraTensorModule.ext
        intro v w
        induction v using TensorProduct.induction_on generalizing w with
        | zero => simp only [map_zero, TensorProduct.zero_tmul]
        | add x z hx hz => simp only [map_add, TensorProduct.add_tmul, hx, hz]
        | tmul a x =>
          induction w using TensorProduct.induction_on with
          | zero => simp only [map_zero, TensorProduct.tmul_zero]
          | add y z hy hz => simp only [map_add, TensorProduct.tmul_add, hy, hz]
          | tmul b y =>
            change e ((a ⊗ₜ[E] X.ρ g x) ⊗ₜ[Q] (b ⊗ₜ[E] Y.ρ g y)) =
              (LinearMap.baseChange Q ((X.ρ.tprod Y.ρ) g))
                (e ((a ⊗ₜ[E] x) ⊗ₜ[Q] (b ⊗ₜ[E] y)))
            simp only [e, TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul,
              LinearMap.baseChange_tmul, Representation.tprod_apply, TensorProduct.map_tmul] }


set_option maxHeartbeats 8000000 in
-- The construction witness has large dependent fibre types.
private theorem algebraicUnit_from_rational
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q)
    (hcanon : GaloisAdicCanonicalConstruction y G c l Q d) :
    galoisAlgebraicUnit y G c l Q d := by
  obtain ⟨_, _, _, _, _, _, _, hRU⟩ :=
    galois_adic_rational_properties y G c l Q d hcanon
  let E := Padic.finiteCoefficientBase l Q
  let F := lisseRationalUnit l E.val Y
  let X := ((d.eR E).functor.obj F).obj
  let Z := (d.eA.functor.obj (lisseAlgebraicUnit l Y Q)).obj
  obtain ⟨η, hη, _⟩ := GaloisAdicCanonicalConstruction.colimit
    (y := y) (G := G) (c := c) (l := l) (Q := Q) (d := d) hcanon E F
  obtain ⟨r⟩ := hRU E
  let θ := ((forget₂ (Rep.{u + 1} E.val G) (ModuleCat E.val)).mapIso r).toLinearEquiv
  have hX (g : G) (x : X.V) : X.ρ g x = x := by
    apply θ.injective
    exact Rep.hom_comm_apply r.hom g x
  have hZ (g : G) (z : Z.V) : Z.ρ g z = z := by
    obtain ⟨t, rfl⟩ := η.surjective z
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x z hx hz => simp only [map_add, hx, hz]
    | tmul a x =>
      exact (hη g a x).symm.trans
        (congrArg (fun v ↦ η (TensorProduct.tmul _ a v)) (hX g x))
  let e : Z.V ≃ₗ[Q] Q := η.symm.trans
    ((θ.baseChange E.val Q _ _).trans (TensorProduct.AlgebraTensorModule.rid E.val Q Q))
  exact ⟨Rep.mkIso
    { toLinearEquiv := e
      isIntertwining' := fun g ↦ LinearMap.ext (fun z ↦ by
        change e (Z.ρ g z) = e z
        rw [hZ]) }⟩

private theorem algebraicOfPairModel_eq
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (F : LisseAlgebraicSheaf l Y Q) :
    lisseAlgebraicOfModel l Y Q (lisseAlgebraicPair l Y Q F).base
      (lisseCoefficientPairModel l Y Q (lisseAlgebraicPair l Y Q F)) = F := by
  let P := lisseAlgebraicPair l Y Q F
  have cancel (C D : Cat.{u + 1, u + 2}) (h : C = D) (X : C) :
      (eqToHom h.symm).toFunctor.obj ((eqToHom h).toFunctor.obj X) = X := by
    cases h
    rfl
  change (lisseCoefficientCocartesian l Y Q).Q.obj
    { base := P.base
      fiber := (eqToHom ((lisseCoefficientDiagramData l Y Q).obj_eq P.base).symm).toFunctor.obj
        ((eqToHom ((lisseCoefficientDiagramData l Y Q).obj_eq P.base)).toFunctor.obj
          P.fiber) } = F
  rw [cancel]
  rcases F with ⟨⟨X⟩⟩
  rfl

set_option maxHeartbeats 8000000 in
-- The colimit witness contains dependent scalar-extension fibre objects.
private theorem modelRepIso
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q)
    (hcanon : GaloisAdicCanonicalConstruction y G c l Q d)
    (E : Padic.FiniteCoefficientFields l Q) (F : LisseRationalSheaf l E.val Y) :
    Nonempty (scalarRep E.val Q ((d.eR E).functor.obj F).obj ≅
      (d.eA.functor.obj (lisseAlgebraicOfModel l Y Q E F)).obj) := by
  obtain ⟨η, hη, _⟩ := GaloisAdicCanonicalConstruction.colimit
    (y := y) (G := G) (c := c) (l := l) (Q := Q) (d := d) hcanon E F
  exact ⟨Rep.mkIso
    { toLinearEquiv := η
      isIntertwining' := fun g ↦ by
        apply TensorProduct.AlgebraTensorModule.ext
        intro a x
        exact hη g a x }⟩

private theorem coefficientRepIso
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q)
    (hs : galoisRationalScalarExtension y G c l Q d)
    (E L : Padic.FiniteCoefficientFields l Q) (h : E ≤ L) [Algebra E.val L.val]
    (ha : algebraMap E.val L.val = (IntermediateField.inclusion h).toRingHom)
    (F : LisseRationalSheaf l E.val Y) :
    Nonempty (scalarRep E.val L.val ((d.eR E).functor.obj F).obj ≅
      ((d.eR L).functor.obj ((lisseRationalScalarExtension l E.val Y L.val
        (IntermediateField.inclusion h)).obj F)).obj) := by
  obtain ⟨e, he, _⟩ := hs E L h ha
  exact ⟨Rep.mkIso
    { toLinearEquiv := e F
      isIntertwining' := fun g ↦ LinearMap.ext (fun z ↦ he F g z) }⟩

set_option maxHeartbeats 8000000 in
-- Coefficient models and their tensor objects carry large dependent category transports.
private theorem algebraicTensor_from_models
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q)
    (hcanon : GaloisAdicCanonicalConstruction y G c l Q d) :
    galoisAlgebraicTensor y G c l Q d := by
  obtain ⟨_, _, _, _, _, _, hRT, _⟩ :=
    galois_adic_rational_properties y G c l Q d hcanon
  obtain ⟨_, hRS⟩ := galois_adic_algebraic_scalar y G c l Q d hcanon
  intro F H
  let T := d.eA.functor ⋙ ObjectProperty.ι _
  let P := lisseAlgebraicPair l Y Q F
  let P' := lisseAlgebraicPair l Y Q H
  let E := P.base
  let L := P'.base
  let N := Padic.finiteCoefficientCompositum l Q E L
  have hE : E ≤ N := show E.val ≤ N.val from le_sup_left
  have hL : L ≤ N := show L.val ≤ N.val from le_sup_right
  let : Algebra E.val N.val := (IntermediateField.inclusion hE).toAlgebra
  let : Algebra L.val N.val := (IntermediateField.inclusion hL).toAlgebra
  let : IsScalarTower E.val N.val Q := IsScalarTower.of_algebraMap_eq' (by ext x; rfl)
  let : IsScalarTower L.val N.val Q := IsScalarTower.of_algebraMap_eq' (by ext x; rfl)
  let F₀ := lisseCoefficientPairModel l Y Q P
  let H₀ := lisseCoefficientPairModel l Y Q P'
  let F' := (lisseRationalScalarExtension l E.val Y N.val
    (IntermediateField.inclusion hE)).obj F₀
  let H' := (lisseRationalScalarExtension l L.val Y N.val
    (IntermediateField.inclusion hL)).obj H₀
  let X := ((d.eR E).functor.obj F₀).obj
  let Y' := ((d.eR L).functor.obj H₀).obj
  obtain ⟨ηF⟩ := modelRepIso y G c l Q d hcanon E F₀
  obtain ⟨ηH⟩ := modelRepIso y G c l Q d hcanon L H₀
  obtain ⟨rF⟩ := coefficientRepIso y G c l Q d hRS E N hE rfl F₀
  obtain ⟨rH⟩ := coefficientRepIso y G c l Q d hRS L N hL rfl H₀
  let uF : T.obj F ≅ scalarRep N.val Q ((d.eR N).functor.obj F').obj :=
    T.mapIso (eqToIso (algebraicOfPairModel_eq l Y Q F).symm) ≪≫ ηF.symm ≪≫
      (scalarTowerIso E.val N.val Q X).symm ≪≫ scalarMapIso N.val Q rF
  let uH : T.obj H ≅ scalarRep N.val Q ((d.eR N).functor.obj H').obj :=
    T.mapIso (eqToIso (algebraicOfPairModel_eq l Y Q H).symm) ≪≫ ηH.symm ≪≫
      (scalarTowerIso L.val N.val Q Y').symm ≪≫ scalarMapIso N.val Q rH
  obtain ⟨e, he⟩ := hRT N F' H'
  let r : ((d.eR N).functor.obj F').obj ⊗ ((d.eR N).functor.obj H').obj ≅
      ((d.eR N).functor.obj (lisseRationalTensor l N.val Y F' H')).obj :=
    Rep.mkIso { toLinearEquiv := e
                isIntertwining' := fun g ↦ LinearMap.ext (fun z ↦ he g z) }
  obtain ⟨ηT⟩ := modelRepIso y G c l Q d hcanon N (lisseRationalTensor l N.val Y F' H')
  let rA : T.obj F ⊗ T.obj H ≅ T.obj (lisseAlgebraicTensor l Y Q F H) :=
    (uF ⊗ᵢ uH) ≪≫ scalarTensorIso N.val Q _ _ ≪≫ scalarMapIso N.val Q r ≪≫ ηT
  refine ⟨((forget₂ (Rep.{u + 1} Q G) (ModuleCat Q)).mapIso rA).toLinearEquiv, ?_⟩
  intro g z
  exact Rep.hom_comm_apply rA.hom g z

/-- Equivariant tensor and unit comparisons at algebraic coefficients.
Source: Deligne, Weil II (1.1.1), (1.1.6), and Stanford Weil II seminar L19,
Proposition 1.1.9. (blueprint: new-c5-galois-adic-algebraic-monoidal).

Proof: use the stated rational tensor and unit properties. The rational scalar
comparison identifies extension of a coefficient representation with the representation
of the scalar-extended sheaf. For each algebraic object, its displayed coefficient pair
recovers the object after transporting the fibre to its rational-model category and back.
Extend the two displayed models to their compositum. The normalized colimit witnesses,
tensor cancellation for the field towers, and distributivity of scalar extension over
tensor products identify the algebraic tensor representation with scalar extension of
the rational tensor representation at that compositum. The standard linear equivalences
are equivariant on tensor generators, hence everywhere by additivity. Compose with the
rational tensor comparison to obtain the required algebraic one. For the unit, the
rational unit action at the base field is trivial. The normalized colimit comparison
makes the algebraic unit action trivial too. Compose with base change of the rational
unit isomorphism and the tensor right-unitor. The parent supplies monoidal coherence
by full faithfulness. -/
theorem galois_adic_algebraic_tensor_unit
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q)
    (hcanon : GaloisAdicCanonicalConstruction y G c l Q d) :
    galoisAlgebraicTensor y G c l Q d ∧
    galoisAlgebraicUnit y G c l Q d := by
  exact ⟨algebraicTensor_from_models y G c l Q d hcanon,
    algebraicUnit_from_rational y G c l Q d hcanon⟩

end AlgebraicGeometry.Scheme
