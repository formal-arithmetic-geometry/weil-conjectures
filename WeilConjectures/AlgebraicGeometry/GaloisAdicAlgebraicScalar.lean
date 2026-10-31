/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GaloisAdicDataFromFinite
import WeilConjectures.AlgebraicGeometry.FibreFunctorLinearTransport
import WeilConjectures.AlgebraicGeometry.IntegralFibrePathConstruction
import WeilConjectures.AlgebraicGeometry.IntegralFibreScalarComparison
import WeilConjectures.AlgebraicGeometry.RationalFibrePathScalarSquare
import WeilConjectures.AlgebraicGeometry.LisseRationalScalarFiberMaps

/-! # Coefficient extension for normalized adic correspondences -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme

private theorem normalizedStalkEquiv_eq
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (κ : (((pointSmallEtale y).ulift.{u + 1}.sheafFiber
      (A := ModuleCat.{u + 1} R)).obj F) ≃
      (((pointSmallEtale y).sheafFiber (A := Type (u + 1))).obj
        (galoisUnderlyingSetSheaf R F)))
    (hκ : ∀ (U : Y.Etale) (x : (pointSmallEtale y).fiber.obj U)
      (z : F.obj.obj (op U)),
      κ ((pointSmallEtale y).ulift.{u + 1}.toPresheafFiber U ⟨x⟩ F.obj z) =
        (pointSmallEtale y).toPresheafFiber U x (galoisUnderlyingSetSheaf R F).obj z) :
    κ = pathUnderlyingStalk y R F := by
  ext z
  obtain ⟨U, ⟨ξ⟩, s, rfl⟩ :=
    (pointSmallEtale y).ulift.{u + 1}.toPresheafFiber_jointly_surjective (P := F.obj) z
  rw [hκ]
  exact (pathUnderlyingStalk_germ y R F U ξ s).symm

set_option maxHeartbeats 8000000 in
-- Normalized projections involve large dependent module types.
private theorem normalizedIntegralAction
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
    (E : Padic.FiniteCoefficientFields l Q) (F : LisseIntegralSheaf l E.val Y)
    (g : G) (z : ((d.eI E).functor.obj F).obj.V) (n : ℕ)
    (h : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf
      (Padic.coefficientExtensionIntegers l E.val) (F.obj.obj (op n)))) :
    pathUnderlyingStalk y (Padic.coefficientExtensionIntegers l E.val)
      (F.obj.obj (op n))
      (limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op n)
        ((d.τI E).hom.app F (((d.eI E).functor.obj F).obj.ρ g z))) =
    (c.γ g).hom.app (galoisUnderlyingFLC (Padic.coefficientExtensionIntegers l E.val)
      (F.obj.obj (op n)) h)
      (pathUnderlyingStalk y (Padic.coefficientExtensionIntegers l E.val)
        (F.obj.obj (op n))
        (limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op n)
          ((d.τI E).hom.app F z))) := by
  have hi := GaloisAdicCanonicalConstruction.inverseLimit
    (y := y) (G := G) (c := c) (l := l) (Q := Q) (d := d) hcanon E F
  -- Destructure one existential at a time: a nested pattern costs about a minute here.
  obtain ⟨V, hi⟩ := hi
  obtain ⟨α, hi⟩ := hi
  obtain ⟨C, hi⟩ := hi
  obtain ⟨e, hi⟩ := hi
  obtain ⟨-, hn, hl⟩ := hi
  have hl' := hl n
  obtain ⟨h₀, hl'⟩ := hl'
  obtain ⟨κ, hκ, ha⟩ := hl'
  have hk := normalizedStalkEquiv_eq y _ (F.obj.obj (op n)) κ hκ
  have hz (w : ((d.eI E).functor.obj F).obj.V) :
      (α.hom.app (op n)) ((C.π.app (op n)).hom (e.inv.hom w)) =
        limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op n)
          ((d.τI E).hom.app F w) :=
    ConcreteCategory.congr_hom (hn n) w
  let P := pathUnderlyingStalk y (Padic.coefficientExtensionIntegers l E.val)
    (F.obj.obj (op n))
  let π := (C.π.app (op n)).hom
  have hv : π (e.inv.hom (((d.eI E).functor.obj F).obj.ρ g z)) =
      (V.obj (op n)).ρ g (π (e.inv.hom z)) :=
    (congrArg π (Rep.hom_comm_apply e.inv g z)).trans
      (Rep.hom_comm_apply (C.π.app (op n)) g (e.inv.hom z))
  exact (congrArg P (hz _).symm).trans
    ((Equiv.congr_fun hk _).symm.trans
      ((congrArg (fun w ↦ κ (α.hom.app (op n) w)) hv).trans
        ((ha g (π (e.inv.hom z))).trans
          (congrArg ((c.γ g).hom.app (galoisUnderlyingFLC
            (Padic.coefficientExtensionIntegers l E.val) (F.obj.obj (op n)) h))
            ((Equiv.congr_fun hk _).trans (congrArg P (hz z)))))))

set_option maxHeartbeats 8000000 in
-- Normalized comparisons involve large dependent fibre objects.
private theorem normalizedIntegralPath
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
    (i : IntegralFibrePathTransport l Y Q)
    (E : Padic.FiniteCoefficientFields l Q) (F : LisseIntegralSheaf l E.val Y)
    (g : G) (z : ((d.eI E).functor.obj F).obj.V) :
    (d.τI E).hom.app F (((d.eI E).functor.obj F).obj.ρ g z) =
      ((i.linear E).map y y (c.γ g)).hom.app F ((d.τI E).hom.app F z) := by
  apply Concrete.limit_ext (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber)
  intro j
  -- Name the evidence before destructuring it: `obtain` on the term itself costs about a minute.
  have hev := IntegralFibrePathTransport.evaluation
    (l := l) (Y := Y) (Q := Q) i y y (c.γ g) E F j.unop
  obtain ⟨h, hp⟩ := hev
  apply (pathUnderlyingStalk y (Padic.coefficientExtensionIntegers l E.val)
    (F.obj.obj j)).injective
  exact (normalizedIntegralAction y G c l Q d hcanon E F g z j.unop h).trans
    (hp ((d.τI E).hom.app F z)).symm

private def repNatIsoOfUnderlying
    {C : Type*} [Category C] {R : Type*} [Ring R] {G : Type*} [Monoid G]
    (F H : C ⥤ Rep.{u + 1} R G)
    (α : F ⋙ forget₂ (Rep.{u + 1} R G) (ModuleCat R) ≅
      H ⋙ forget₂ (Rep.{u + 1} R G) (ModuleCat R))
    (hα : ∀ (X : C) (g : G) (z : (F.obj X).V),
      α.hom.app X ((F.obj X).ρ g z) = (H.obj X).ρ g (α.hom.app X z)) : F ≅ H :=
  NatIso.ofComponents (fun X ↦ Rep.mkIso
    { toLinearEquiv := (α.app X).toLinearEquiv
      isIntertwining' := fun g ↦ LinearMap.ext (fun z ↦ hα X g z) }) (by
    intro X Z f
    apply (forget₂ (Rep.{u + 1} R G) (ModuleCat R)).map_injective
    exact α.hom.naturality f)

set_option maxHeartbeats 8000000 in
-- Transporting the scalar natural isomorphism unfolds dependent coefficient categories.
private theorem normalizedIntegralScalar
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
    (i : IntegralFibrePathTransport l Y Q) :
    galoisIntegralScalarExtension y G c l Q d := by
  intro E L h
  let J := lisseIntegralScalarExtension l E.val Y L.val (IntermediateField.inclusion h)
  let R := Padic.coefficientExtensionIntegers l E.val
  let S := Padic.coefficientExtensionIntegers l L.val
  let Φ := ModuleCat.ringExtendScalars.{u + 1, u + 1}
    (lisseIntegerInclusion l E.val L.val (IntermediateField.inclusion h))
  let A := J ⋙ (d.eI L).functor ⋙ ObjectProperty.ι _
  let B := (d.eI E).functor ⋙ ObjectProperty.ι _ ⋙ (Rep.repIsoAction R G).functor ⋙
    Φ.mapAction G ⋙ (Rep.repIsoAction S G).inverse
  let η := integralFibreScalarIso l Y y E.val L.val (IntermediateField.inclusion h)
  let α : B ⋙ forget₂ (Rep.{u + 1} S G) (ModuleCat S) ≅
      A ⋙ forget₂ (Rep.{u + 1} S G) (ModuleCat S) :=
    Functor.isoWhiskerRight (d.τI E) Φ ≪≫ η ≪≫
      Functor.isoWhiskerLeft J (d.τI L).symm
  refine ⟨(repNatIsoOfUnderlying B A α ?_).symm⟩
  intro F g z
  let X := ((d.eI E).functor.obj F).obj
  let Z := ((d.eI L).functor.obj (J.obj F)).obj
  let τE := (d.τI E).app F
  let τL := (d.τI L).app (J.obj F)
  let pE := ((i.linear E).map y y (c.γ g)).hom.app F
  let pL := ((i.linear L).map y y (c.γ g)).hom.app (J.obj F)
  have hE : ModuleCat.ofHom (X.ρ g) ≫ τE.hom = τE.hom ≫ pE := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact normalizedIntegralPath y G c l Q d hcanon i E F g x
  have hE' := congrArg (fun f ↦ Φ.map f) hE
  rw [Functor.map_comp, Functor.map_comp] at hE'
  have hx := ConcreteCategory.congr_hom hE' z
  have hp := ConcreteCategory.congr_hom
    (integralFibreScalarIso_path l Y Q i y y (c.γ g) E L h F)
    (Φ.map τE.hom z)
  have hτ (w) : τL.hom (τL.inv w) = w :=
    ConcreteCategory.congr_hom τL.inv_hom_id w
  apply τL.toLinearEquiv.injective
  change τL.hom (τL.inv (η.hom.app F (Φ.map τE.hom
      (Φ.map (ModuleCat.ofHom (X.ρ g)) z)))) =
    τL.hom (Z.ρ g (τL.inv (η.hom.app F (Φ.map τE.hom z))))
  have hL : τL.hom (Z.ρ g (τL.inv (η.hom.app F (Φ.map τE.hom z)))) =
      pL (η.hom.app F (Φ.map τE.hom z)) :=
    (normalizedIntegralPath y G c l Q d hcanon i L (J.obj F) g _).trans
      (congrArg pL (hτ _))
  exact (hτ _).trans
    ((congrArg (η.hom.app F) hx).trans (hp.trans hL.symm))

private theorem moduleCast_cancel {R : Type*} [Ring R]
    {M N : ModuleCat.{u + 1} R} (h : M = N) (z : M) :
    eqToHom h.symm (eqToHom h z) = z := by
  cases h
  rfl

set_option maxHeartbeats 8000000 in
-- Normalized comparisons involve large dependent fibre objects.
private theorem normalizedRationalPath
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
    (i : IntegralFibrePathTransport l Y Q)
    (E : Padic.FiniteCoefficientFields l Q) (F : LisseRationalSheaf l E.val Y)
    (g : G) (z : ((d.eR E).functor.obj F).obj.V) :
    (d.τR E).hom.app F (((d.eR E).functor.obj F).obj.ρ g z) =
      ((rationalFibrePathFamily l E.val Y (i.linear E)).map y y (c.γ g)).hom.app F
        ((d.τR E).hom.app F z) := by
  have hloc := GaloisAdicCanonicalConstruction.localization
    (y := y) (G := G) (c := c) (l := l) (Q := Q) (d := d) hcanon E F
  obtain ⟨η, ha, hn⟩ := hloc
  let b := lisseRationalFiberFunctor_obj l E.val Y y F
  let p := ((rationalFibrePathFamily l E.val Y (i.linear E)).map y y (c.γ g)).hom.app F
  have hn' (a : E.val) (x : ((d.eI E).functor.obj F.integral).obj.V) :
      (d.τR E).hom.app F (η (TensorProduct.tmul _ a x)) =
        eqToHom b.symm (TensorProduct.tmul _ a ((d.τI E).hom.app F.integral x)) :=
    (moduleCast_cancel b _).symm.trans
      (congrArg (fun w ↦ eqToHom b.symm w) (hn a x))
  obtain ⟨t, rfl⟩ := η.surjective z
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x z hx hz => simp only [map_add, hx, hz]
  | tmul a x =>
    calc
      _ = (d.τR E).hom.app F
          (η (TensorProduct.tmul _ a (((d.eI E).functor.obj F.integral).obj.ρ g x))) :=
        congrArg (fun w ↦ (d.τR E).hom.app F w) (ha g a x).symm
      _ = eqToHom b.symm (TensorProduct.tmul _ a
          ((d.τI E).hom.app F.integral
            (((d.eI E).functor.obj F.integral).obj.ρ g x))) := hn' a _
      _ = eqToHom b.symm (TensorProduct.tmul _ a
          (((i.linear E).map y y (c.γ g)).hom.app F.integral
            ((d.τI E).hom.app F.integral x))) := by
        rw [normalizedIntegralPath y G c l Q d hcanon i E F.integral g x]
      _ = p (eqToHom b.symm
          (TensorProduct.tmul _ a ((d.τI E).hom.app F.integral x))) :=
        (rationalFibrePathFamily_apply l E.val Y (i.linear E) y y (c.γ g) F a
          ((d.τI E).hom.app F.integral x)).symm
      _ = p ((d.τR E).hom.app F (η (TensorProduct.tmul _ a x))) :=
        congrArg p (hn' a x).symm

set_option maxHeartbeats 8000000 in
-- The scalar natural isomorphism has dependent coefficient-category objects.
private theorem normalizedRationalScalar
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
    (i : IntegralFibrePathTransport l Y Q) :
    galoisRationalScalarExtension y G c l Q d := by
  intro E L h aEL ha
  let J := lisseRationalScalarExtension l E.val Y L.val (IntermediateField.inclusion h)
  let Φ := ModuleCat.extendScalars (algebraMap E.val L.val)
  let U := (d.eR E).functor ⋙ ObjectProperty.ι _ ⋙
    forget₂ (Rep.{u + 1} E.val G) (ModuleCat E.val)
  let V := J ⋙ (d.eR L).functor ⋙ ObjectProperty.ι _ ⋙
    forget₂ (Rep.{u + 1} L.val G) (ModuleCat L.val)
  let η := rationalFibreScalarIso l Y y E.val L.val (IntermediateField.inclusion h) ha
  let α : U ⋙ Φ ≅ V :=
    Functor.isoWhiskerRight (d.τR E) Φ ≪≫ η ≪≫
      Functor.isoWhiskerLeft J (d.τR L).symm
  let κ : U ⋙ algebraTensorFunctor (R := E.val) (A := L.val) ≅ V :=
    (Functor.isoWhiskerLeft U
      (tensorAlgebraNatIso (R := E.val) (A := L.val))).symm ≪≫ α
  refine ⟨fun F ↦ (κ.app F).toLinearEquiv, ?_, ?_⟩
  · intro F g z
    let X := ((d.eR E).functor.obj F).obj
    let Z := ((d.eR L).functor.obj (J.obj F)).obj
    let τE := (d.τR E).app F
    let τL := (d.τR L).app (J.obj F)
    let pE := ((rationalFibrePathFamily l E.val Y (i.linear E)).map y y (c.γ g)).hom.app F
    let pL := ((rationalFibrePathFamily l L.val Y (i.linear L)).map y y (c.γ g)).hom.app
      (J.obj F)
    let q := (tensorAlgebraIso (ModuleCat.of E.val X.V)).inv z
    have hE : ModuleCat.ofHom (X.ρ g) ≫ τE.hom = τE.hom ≫ pE := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact normalizedRationalPath y G c l Q d hcanon i E F g x
    have hE' := congrArg (fun f ↦ Φ.map f) hE
    rw [Functor.map_comp, Functor.map_comp] at hE'
    have hx := ConcreteCategory.congr_hom hE' q
    have hp := ConcreteCategory.congr_hom
      (rationalFibreScalarIso_path l Y Q i y y (c.γ g) E L h ha F)
      (Φ.map τE.hom q)
    have hτ (w) : τL.hom (τL.inv w) = w :=
      ConcreteCategory.congr_hom τL.inv_hom_id w
    have hq : (tensorAlgebraIso (ModuleCat.of E.val X.V)).inv
        (galoisScalarAction E.val L.val X g z) = Φ.map (ModuleCat.ofHom (X.ρ g)) q :=
      ConcreteCategory.congr_hom
        ((tensorAlgebraNatIso (R := E.val) (A := L.val)).inv.naturality
          (ModuleCat.ofHom (X.ρ g))) z
    apply τL.toLinearEquiv.injective
    change τL.hom (τL.inv (η.hom.app F (Φ.map τE.hom
        ((tensorAlgebraIso (ModuleCat.of E.val X.V)).inv
          (galoisScalarAction E.val L.val X g z))))) =
      τL.hom (Z.ρ g (τL.inv (η.hom.app F (Φ.map τE.hom q))))
    have hL : τL.hom (Z.ρ g (τL.inv (η.hom.app F (Φ.map τE.hom q)))) =
        pL (η.hom.app F (Φ.map τE.hom q)) :=
      (normalizedRationalPath y G c l Q d hcanon i L (J.obj F) g _).trans
        (congrArg pL (hτ _))
    exact (hτ _).trans
      ((congrArg (η.hom.app F)
        ((congrArg (Φ.map τE.hom) hq).trans hx)).trans (hp.trans hL.symm))
  · intro F H f z
    exact ConcreteCategory.congr_hom (κ.hom.naturality f) z

/-- Integral and rational coefficient extension respects the normalized actions.
Source: Deligne, Weil II (1.1.1), (1.1.6), and Stanford Weil II seminar L19,
Proposition 1.1.9. (blueprint: new-c5-galois-adic-algebraic-scalar).

Proof: for E contained in L, use the canonical integral fibre scalar isomorphism.
At a quotient level its pure scalar germ is the germ of the balanced scalar tensor.
Naturality of c.γ for the underlying finite locally constant sheaves makes this map
commute with the finite actions. The germ normalizations in hcanon.inverseLimit
identify those actions with the projections of the integral representations. Equality
of all projections gives equivariance of the integral fibre scalar isomorphism.
Transport it through τI, and lift the resulting natural module isomorphism to Rep;
this gives the stated natural isomorphism of integral representation functors.
For rational coefficients, rationalize this same comparison and use the normalized
localization equivalences. On a tensor a tensor (b tensor z), balancing multiplies the
two coefficients; hence the resulting L-linear equivalence intertwines the actions.
Naturality follows on these generators from naturality of the integral comparison
and τI and τR, then on all tensors by additivity. The formula is compatible with the
specified E-algebra structure on L because its algebra map is the coefficient
inclusion. This proves both rational equivariance and the required naturality square. -/
theorem galois_adic_algebraic_scalar
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
    galoisIntegralScalarExtension y G c l Q d ∧
    galoisRationalScalarExtension y G c l Q d := by
  obtain ⟨i⟩ := integral_fibre_path_transport_exists l Y Q
  exact ⟨normalizedIntegralScalar y G c l Q d hcanon i,
    normalizedRationalScalar y G c l Q d hcanon i⟩

end AlgebraicGeometry.Scheme
