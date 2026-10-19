/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleWeilTransport
public import Sheaf.Paper.RealSheavesSetup
public import Sheaf.Paper.CurveWeilMiddleExtension
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.ProEtale.Adic.DenseOpenUnit
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.RestrictionWeilGroup
import Sheaf.AlgebraicGeometry.NormalOpenLisseImage
import Sheaf.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.DenseOpenNormal
import WeilConjectures.ConstructibleSheaf.DenseOpenUnitNormal
import WeilConjectures.WeilSheaf.DenseOpen
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.Flat

/-!
# Dense open immersions and fundamental groups

Source: blueprint main-20261015, sec-purity-real-sheaves/sk-i-real-boundary,
lemma lem-wf-dense-open-pi1-surjective, clauses (1)--(5)
(blueprint: lem-wf-dense-open-pi1-surjective).

Normality is the stalkwise normal-domain condition, including at singular points.
The group models and every restriction map use the existing finite-etale fibre functor.
The Weil-group map is specified by its underlying pair, which determines it uniquely.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

attribute [local irreducible] AlgebraicGeometry.ProEtale.adicUpperStar

namespace AlgebraicGeometry

private theorem integrallyClosed_of_faithfullyFlat
    (A C : Type*) [CommRing A] [CommRing C] [Algebra A C]
    [Module.FaithfullyFlat A C] [IsDomain A] [IsDomain C] [IsIntegrallyClosed C] :
    IsIntegrallyClosed A := by
  let K := FractionRing A
  let L := FractionRing C
  let g : A →ₐ[A] L := Algebra.ofId A L
  have hg : Function.Injective g :=
    (IsFractionRing.injective C L).comp (FaithfulSMul.algebraMap_injective A C)
  let φ : K →ₐ[A] L := IsFractionRing.liftAlgHom (g := g) hg
  apply (isIntegrallyClosed_iff K).mpr
  intro x hx
  have hy : _root_.IsIntegral C (φ x) := (hx.map φ).tower_top
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hy
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hgb0 : g b ≠ 0 := by
    exact (map_ne_zero_iff g hg).mpr hb0
  have heq : algebraMap C L (algebraMap A C a) =
      algebraMap C L (algebraMap A C b * s) := by
    have hφ : φ (algebraMap A K a / algebraMap A K b) = g a / g b := by
      simp [φ, g]
    have he := (div_eq_iff hgb0).mp (hφ.symm.trans hs.symm)
    simpa [g, IsScalarTower.algebraMap_apply A C L, mul_comm] using he
  have heqC : algebraMap A C a = algebraMap A C b * s :=
    IsFractionRing.injective C L heq
  have ha : a ∈ Ideal.span ({b} : Set A) := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := C) (Ideal.span ({b} : Set A))]
    change algebraMap A C a ∈ Ideal.map (algebraMap A C) (Ideal.span ({b} : Set A))
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    exact ⟨s, heqC⟩
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp ha
  refine ⟨r, ?_⟩
  rw [hr, map_mul, mul_div_cancel_left₀]
  exact (map_ne_zero_iff (algebraMap A K) (IsFractionRing.injective A K)).mpr hb0

private theorem normal_stalks_of_flat_surjective {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] [Surjective f]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x)) (y : Y) :
    IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y) := by
  obtain ⟨x, rfl⟩ := f.surjective y
  let : IsDomain (X.presheaf.stalk x) := (hX x).1
  let : IsIntegrallyClosed (X.presheaf.stalk x) := (hX x).2
  algebraize [(f.stalkMap x).hom]
  have : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := Flat.stalkMap f x
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  let : IsDomain (Y.presheaf.stalk (f x)) := Function.Injective.isDomain _
    (FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (f x)) (X.presheaf.stalk x))
  exact ⟨inferInstance, integrallyClosed_of_faithfullyFlat
    (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)⟩

private theorem curve_regular_connected (D : RealSheaves.Setup.{u, v})
    (C : Scheme.{u}) [C.Over (Spec (.of D.k₀))] (hC : D.IsCurve C) :
    IsRegular C ∧ ConnectedSpace C := by
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have : Smooth (C ↘ Spec (.of D.k₀)) := hC.2.2.1
  have : GeometricallyConnected (C ↘ Spec (.of D.k₀)) :=
    (geometricallyConnected_iff_connectedSpace_of_isAlgClosed (Ω := D.k) C).2 hC.2.2.2.2.2.2
  exact ⟨IsRegular.of_smooth (C ↘ Spec (.of D.k₀)),
    GeometricallyConnected.connectedSpace_of_subsingleton (C ↘ Spec (.of D.k₀))⟩

private theorem curve_relativeDimension (D : RealSheaves.Setup.{u, v})
    (C : Scheme.{u}) [C.Over (Spec (.of D.k₀))] (hC : D.IsCurve C) :
    SmoothOfRelativeDimension 1 (C ↘ Spec (.of D.k₀)) := by
  have : Smooth (C ↘ Spec (.of D.k₀)) := hC.2.2.1
  have : LocallyOfFiniteType (C ↘ Spec (.of D.k₀)) := hC.2.2.2.1
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian
    (C ↘ Spec (.of D.k₀))
  obtain ⟨_, _⟩ := curve_regular_connected D C hC
  have : IrreducibleSpace C := IsRegular.irreducibleSpace C
  apply (smoothOfRelativeDimension_iff_topologicalKrullDim_eq _ 1).2
  have hdim := hC.2.2.2.2.2.1 Set.univ (by simp [irreducibleComponents_eq_singleton])
  exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ C).isHomeomorph).symm.trans hdim

private theorem mem_constantCoverWeilGroup_iff
    {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (g : Aut (Scheme.FiniteEtale.fiber s)) (n : Multiplicative ℤ) :
    (g, n) ∈ (Scheme.FiniteEtale.constantCoverAction p s
      (Aut (Scheme.FiniteEtale.fiber s))).weilGroup
        (Scheme.FiniteEtale.geometricFrobenius p s) ↔
      ∀ (A : Scheme.FiniteEtale.FiniteEtaleAlgebra k) (y : (Scheme.FiniteEtale.fiber s).obj
        (Scheme.FiniteEtale.constantCover p A)),
        g.hom.app _ y = (Scheme.FiniteEtale.geometricFrobenius p s A ^ n.toAdd) y := by
  rw [MonoidHom.mem_weilGroup, funext_iff]
  refine forall_congr' fun A ↦ ?_
  rw [Equiv.ext_iff]
  rfl

/-- The canonical fibre-automorphism map, with its group laws checked pointwise. -/
private def fiberAutBaseChangeHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    Aut (Scheme.FiniteEtale.fiber s) →* Aut (Scheme.FiniteEtale.fiber (s ≫ f)) where
  toFun := Scheme.FiniteEtale.fiberAutBaseChange f s
  map_one' := by
    ext P x
    change (Scheme.FiniteEtale.pullbackFiberIso f s).hom.app P
      ((Scheme.FiniteEtale.pullbackFiberIso f s).inv.app P x) = x
    exact ConcreteCategory.congr_hom
      ((Scheme.FiniteEtale.pullbackFiberIso f s).inv_hom_id_app P) x
  map_mul' g h := by
    ext P x
    let τ := Scheme.FiniteEtale.pullbackFiberIso f s
    change τ.hom.app P (g.hom.app _ (h.hom.app _ (τ.inv.app P x))) =
      τ.hom.app P (g.hom.app _ (τ.inv.app P (τ.hom.app P (h.hom.app _ (τ.inv.app P x)))))
    exact congrArg (fun z ↦ τ.hom.app P (g.hom.app _ z))
      (ConcreteCategory.congr_hom (τ.hom_inv_id_app P) _).symm

/-- Connected finite etale covers stay connected on a dense open of a connected normal
Noetherian scheme. Source: blueprint clause (1)
(blueprint: lem-wf-dense-open-pi1-surjective).
Proof: Step 0 uses rem-pc-regular-normal (2): the finitely many normal integral clopen
components of V reduce to one by connectedness and the geometric point. In Step (1a),
lem-fin-etale-normal-components makes a connected finite etale cover integral. Its image
is nonempty, open and closed, hence all of V. Its pullback to the nonempty open is a
nonempty open of an integral scheme and is therefore connected. -/
theorem Scheme.FiniteEtale.isConnected_pullback_of_normal_dense_open
    {U V : Scheme.{u}} [ConnectedSpace V] [IsNoetherian V]
    (hV : ∀ x : V, IsDomain (V.presheaf.stalk x) ∧
      IsIntegrallyClosed (V.presheaf.stalk x))
    (j : U ⟶ V) [IsOpenImmersion j] (hj : DenseRange j.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U)
    (P : V.FiniteEtale) (hP : IsConnected P) :
    IsConnected ((Scheme.FiniteEtale.pullback j).obj P) := by
  -- The source result only needs the nonemptiness supplied by the geometric point.
  have _ := hj
  have : Nonempty U := ⟨s (Classical.choice inferInstance)⟩
  have : IsConnected P := hP
  exact Scheme.FiniteEtale.isConnected_pullback_of_isIntegrallyClosed_stalk j hV P

/-- Surjectivity of the canonical map on fundamental groups at a geometric point of the open.
Source: blueprint clause (1) (blueprint: lem-wf-dense-open-pi1-surjective).
Proof: Step (1a) is the preceding connected-cover assertion. Step (1b) uses
thm-galois-fundamental, lem-fet-galois-category and lem-galois-transitive. The continuous
image is compact and closed. A proper image lies in a proper open subgroup by
lem-wf-profinite-closed-subgroup-intersection-open. By cor-galois-open-subgroups its coset
set is a connected cover whose restriction is disconnected, contradicting Step (1a). -/
theorem Scheme.FiniteEtale.fundamentalGroupMap_surjective_of_normal_dense_open
    {U V : Scheme.{u}} [ConnectedSpace V] [IsNoetherian V]
    (hV : ∀ x : V, IsDomain (V.presheaf.stalk x) ∧
      IsIntegrallyClosed (V.presheaf.stalk x))
    (j : U ⟶ V) [IsOpenImmersion j] (hj : DenseRange j.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U) :
    Function.Surjective (Scheme.FiniteEtale.fiberAutBaseChange j s) := by
  let : IrreducibleSpace V := irreducibleSpace_of_isDomain_stalk V (fun x ↦ (hV x).1)
  let : Nonempty U := ⟨s (Classical.choice inferInstance)⟩
  let : ConnectedSpace U := Scheme.FiniteEtale.connectedSpace_of_isOpenImmersion j
  let τ := Scheme.FiniteEtale.pullbackFiberIso j s
  let ρ : Aut (Scheme.FiniteEtale.fiber s) →*
      Aut (Scheme.FiniteEtale.fiber (s ≫ j)) :=
    (Aut.autMulEquivOfIso τ).toMonoidHom.comp
      (((Functor.whiskeringLeft _ _ _).obj (Scheme.FiniteEtale.pullback j)).mapAut _)
  let (P : V.FiniteEtale) : MulAction (Aut (Scheme.FiniteEtale.fiber s))
      ((Scheme.FiniteEtale.fiber (s ≫ j)).obj P) := MulAction.compHom _ ρ
  have hsmul (g : Aut (Scheme.FiniteEtale.fiber s)) (P : V.FiniteEtale)
      (x : (Scheme.FiniteEtale.fiber (s ≫ j)).obj P) :
      g • x = τ.hom.app P (g.hom.app _ (τ.inv.app P x)) := rfl
  have : IsNaturalSMul (Scheme.FiniteEtale.fiber (s ≫ j))
      (Aut (Scheme.FiniteEtale.fiber s)) :=
    ⟨fun g P Q f x ↦ IsNaturalSMul.naturality (ρ g) f x⟩
  have (P : V.FiniteEtale) : ContinuousSMul (Aut (Scheme.FiniteEtale.fiber s))
      ((Scheme.FiniteEtale.fiber (s ≫ j)).obj P) := by
    refine ⟨?_⟩
    simp only [hsmul]
    exact continuous_of_discreteTopology.comp
      (continuous_fst.smul (continuous_of_discreteTopology.comp continuous_snd))
  have hsurj := toAut_surjective_of_isPretransitive (Scheme.FiniteEtale.fiber (s ≫ j))
    (Aut (Scheme.FiniteEtale.fiber s)) (fun P _ ↦ ?_)
  · exact hsurj
  · have := Scheme.FiniteEtale.isConnected_pullback_of_normal_dense_open hV j hj s P
      inferInstance
    refine ⟨fun x y ↦ ?_⟩
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Aut (Scheme.FiniteEtale.fiber s))
      (show (Scheme.FiniteEtale.fiber s).obj ((Scheme.FiniteEtale.pullback j).obj P) from
        τ.inv.app P x)
      (show (Scheme.FiniteEtale.fiber s).obj ((Scheme.FiniteEtale.pullback j).obj P) from
        τ.inv.app P y)
    refine ⟨g, ?_⟩
    rw [hsmul]
    exact (congrArg (τ.hom.app P) hg).trans
      (ConcreteCategory.congr_hom (τ.inv_hom_id_app P) y)

/-- A surjective map with equivalent Weil-pair conditions surjects on the Weil groups. -/
private theorem weilGroup_lift_surjective
    {G H A B : Type*} [Group G] [Group H] [Group A] [Group B]
    (π : G →* A) (ψ : H →* B) (Φ : A) (Ψ : B) (r : G →* H)
    (hr : Function.Surjective r)
    (hmem : ∀ g n, (g, n) ∈ π.weilGroup Φ ↔ (r g, n) ∈ ψ.weilGroup Ψ) :
    ∃ ρ : π.weilGroup Φ →* ψ.weilGroup Ψ,
      (∀ w, (ρ w).val = (r w.val.1, w.val.2)) ∧
      (∀ w, ψ.weilGroupDeg Ψ (ρ w) = π.weilGroupDeg Φ w) ∧
      (∀ w ∈ (ψ.weilGroupDeg Ψ).ker,
        ∃ w' ∈ (π.weilGroupDeg Φ).ker, ρ w' = w) ∧ Function.Surjective ρ := by
  let ρ := ((r.prodMap (MonoidHom.id (Multiplicative ℤ))).comp
    (π.weilGroup Φ).subtype).codRestrict (ψ.weilGroup Ψ)
      (fun w ↦ (hmem w.val.1 w.val.2).1 w.property)
  have hρ : Function.Surjective ρ := by
    intro w
    obtain ⟨g, hg⟩ := hr w.val.1
    refine ⟨⟨(g, w.val.2), (hmem g w.val.2).2 ?_⟩, ?_⟩
    · simpa only [hg] using w.property
    · exact Subtype.ext (Prod.ext hg rfl)
  refine ⟨ρ, fun _ ↦ rfl, fun _ ↦ rfl, ?_, hρ⟩
  intro w hw
  obtain ⟨w', rfl⟩ := hρ w
  exact ⟨w', hw, rfl⟩

/-- The canonical map of Weil groups: its pair formula specifies the map induced by finite
etale pullback, its degree equality, its surjectivity on geometric kernels, and its
surjectivity on the whole Weil group. The fibre-product expressions below are exactly the
bodies of the recorded weilGroup and weilGroupDeg abbreviations; using them avoids
requiring geometric connectedness of the open as an extra hypothesis.
Source: blueprint clause (2) (blueprint: lem-wf-dense-open-pi1-surjective).
Proof: In Step (2), lem-sc-scheme-over-field-universally-open shows that the geometric
open is dense. Step (1) makes the geometric fundamental-group map surjective.
lem-weil-geometrically-connected-algebraic-closure checks geometric connectedness of both
schemes. Pullback preserves constant covers and geometric Frobenius, so the arithmetic
fundamental-group map induces (g,n) to (rho(g),n) on the fibre-product Weil groups of
def-wf-weil-group and def-wf-fundamental-representation. The exact sequence
lem-wf-weil-group-exact-sequence identifies the kernels with the geometric groups.
Given w of degree n, lift its degree in the source Weil group, then lift the quotient
of w by that image through the geometric surjection; their product lifts w. -/
theorem Scheme.FiniteEtale.weilGroup_dense_open_surjective
    {k₀ : Type u} [Field k₀] [Finite k₀]
    {U V : Scheme.{u}} (p : V ⟶ Spec (.of k₀)) (pU : U ⟶ Spec (.of k₀))
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    [ConnectedSpace p.geometricFiber]
    (hV : ∀ x : p.geometricFiber,
      IsDomain (p.geometricFiber.presheaf.stalk x) ∧
        IsIntegrallyClosed (p.geometricFiber.presheaf.stalk x))
    (j : U ⟶ V) [IsOpenImmersion j] (hj : DenseRange j.base) (hp : j ≫ p = pU)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ U) :
    ∃ ρ :
        (Scheme.FiniteEtale.constantCoverAction pU s (Aut (Scheme.FiniteEtale.fiber s))).weilGroup
          (Scheme.FiniteEtale.geometricFrobenius pU s) →*
        (Scheme.FiniteEtale.constantCoverAction p (s ≫ j)
          (Aut (Scheme.FiniteEtale.fiber (s ≫ j)))).weilGroup
            (Scheme.FiniteEtale.geometricFrobenius p (s ≫ j)),
      (∀ w, (ρ w).val = (Scheme.FiniteEtale.fiberAutBaseChange j s w.val.1, w.val.2)) ∧
      (∀ w,
        (Scheme.FiniteEtale.constantCoverAction p (s ≫ j)
          (Aut (Scheme.FiniteEtale.fiber (s ≫ j)))).weilGroupDeg
            (Scheme.FiniteEtale.geometricFrobenius p (s ≫ j)) (ρ w) =
        (Scheme.FiniteEtale.constantCoverAction pU s
          (Aut (Scheme.FiniteEtale.fiber s))).weilGroupDeg
            (Scheme.FiniteEtale.geometricFrobenius pU s) w) ∧
      (∀ w ∈
        ((Scheme.FiniteEtale.constantCoverAction p (s ≫ j)
          (Aut (Scheme.FiniteEtale.fiber (s ≫ j)))).weilGroupDeg
            (Scheme.FiniteEtale.geometricFrobenius p (s ≫ j))).ker,
        ∃ w' ∈
          ((Scheme.FiniteEtale.constantCoverAction pU s
            (Aut (Scheme.FiniteEtale.fiber s))).weilGroupDeg
              (Scheme.FiniteEtale.geometricFrobenius pU s)).ker,
          ρ w' = w) ∧
      Function.Surjective ρ := by
  let q := p.geometricFiberProj
  have : Surjective (Scheme.specAlgebraicClosure k₀).hom :=
    ⟨fun x ↦ ⟨(⟨⊥, inferInstance⟩ : PrimeSpectrum (AlgebraicClosure k₀)), Subsingleton.elim _ _⟩⟩
  have : Surjective q := inferInstanceAs
    (Surjective (pullback.fst p (Scheme.specAlgebraicClosure k₀).hom))
  have : Flat q := inferInstanceAs
    (Flat (pullback.fst p (Scheme.specAlgebraicClosure k₀).hom))
  have hnormal := normal_stalks_of_flat_surjective q hV
  have : ConnectedSpace V := q.surjective.connectedSpace q.continuous
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian V := ⟨⟩
  have : IrreducibleSpace V := irreducibleSpace_of_isDomain_stalk V (fun x ↦ (hnormal x).1)
  have : Nonempty U := ⟨s (Classical.choice inferInstance)⟩
  have : ConnectedSpace U := Scheme.FiniteEtale.connectedSpace_of_isOpenImmersion j
  let r : Aut (Scheme.FiniteEtale.fiber s) →*
      Aut (Scheme.FiniteEtale.fiber (s ≫ j)) :=
    fiberAutBaseChangeHom j s
  have hr : Function.Surjective r :=
    Scheme.FiniteEtale.fundamentalGroupMap_surjective_of_normal_dense_open hnormal j hj s
  have hmem (g : Aut (Scheme.FiniteEtale.fiber s)) (n : Multiplicative ℤ) :
      (g, n) ∈ (Scheme.FiniteEtale.constantCoverAction pU s
        (Aut (Scheme.FiniteEtale.fiber s))).weilGroup
          (Scheme.FiniteEtale.geometricFrobenius pU s) ↔
      (r g, n) ∈ (Scheme.FiniteEtale.constantCoverAction p (s ≫ j)
        (Aut (Scheme.FiniteEtale.fiber (s ≫ j)))).weilGroup
          (Scheme.FiniteEtale.geometricFrobenius p (s ≫ j)) := by
    rw [mem_constantCoverWeilGroup_iff, mem_constantCoverWeilGroup_iff]
    have hact (A : FiniteEtaleAlgebra k₀)
        (y : (Scheme.FiniteEtale.fiber s).obj (Scheme.FiniteEtale.constantCover pU A)) :
        (r g).hom.app _ (Scheme.FiniteEtale.constantCoverFiberMap j hp s A y) =
          Scheme.FiniteEtale.constantCoverFiberMap j hp s A (g.hom.app _ y) := by
      let τ := Scheme.FiniteEtale.pullbackFiberIso j s
      let φ := Scheme.FiniteEtale.constantCoverToPullback j hp A
      have ht := Scheme.FiniteEtale.pullbackFiberIso_constantCoverToPullback j hp s A y
      have hi : τ.inv.app _ (τ.hom.app _ ((Scheme.FiniteEtale.fiber s).map φ y)) =
          (Scheme.FiniteEtale.fiber s).map φ y :=
        ConcreteCategory.congr_hom (τ.hom_inv_id_app _) _
      have hn : g.hom.app _ ((Scheme.FiniteEtale.fiber s).map φ y) =
          (Scheme.FiniteEtale.fiber s).map φ (g.hom.app _ y) := by
        simpa only [ConcreteCategory.comp_apply] using
          ConcreteCategory.congr_hom (g.hom.naturality φ) y
      change τ.hom.app _ (g.hom.app _ (τ.inv.app _ _)) = _
      exact (congrArg (fun z ↦ τ.hom.app _ (g.hom.app _ (τ.inv.app _ z))) ht.symm).trans
        ((congrArg (fun z ↦ τ.hom.app _ (g.hom.app _ z)) hi).trans
          ((congrArg (τ.hom.app _) hn).trans
            (Scheme.FiniteEtale.pullbackFiberIso_constantCoverToPullback j hp s A _)))
    constructor
    · intro h A z
      obtain ⟨y, rfl⟩ := (Scheme.FiniteEtale.constantCoverFiberMap_bijective j hp s A).2 z
      exact (hact A y).trans
        ((congrArg (Scheme.FiniteEtale.constantCoverFiberMap j hp s A) (h A y)).trans
          (Scheme.FiniteEtale.constantCoverFiberMap_geometricFrobenius_zpow j hp s A _ y))
    · intro h A y
      apply (Scheme.FiniteEtale.constantCoverFiberMap_bijective j hp s A).1
      exact (hact A y).symm.trans ((h A _).trans
        (Scheme.FiniteEtale.constantCoverFiberMap_geometricFrobenius_zpow j hp s A _ y).symm)
  exact weilGroup_lift_surjective _ _ _ _ r hr hmem

/-- The finite-level adjunction unit of a lisse sheaf is invertible on a normal scheme.
Source: blueprint clause (3) (blueprint: lem-wf-dense-open-pi1-surjective).
Proof: Step (3) evaluates on affine etale T over V and uses
lem-fin-etale-normal-components to decompose T into normal integral clopen components.
Every component meets the open. By cor-galois-lisse-representations sections are the
invariants of its geometric stalk. Step (1) says that restriction has the same group
image, hence the same invariants. Thus the unit is an isomorphism on the etale basis. -/
theorem Etale.isIso_lisse_unit_of_normal_dense_open
    {U V : Scheme.{u}} [ConnectedSpace V] [IsNoetherian V]
    (hV : ∀ x : V, IsDomain (V.presheaf.stalk x) ∧
      IsIntegrallyClosed (V.presheaf.stalk x))
    (j : U ⟶ V) [IsOpenImmersion j] (hj : DenseRange j.base)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (N : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteLocallyConstantSheaf N] :
    IsIso ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app N) := by
  exact Etale.isIso_unit_upperStarLowerStarAdjunction_of_isIntegrallyClosed_stalk hV j hj N

/-- The algebraic l-adic adjunction unit of a lisse sheaf is invertible on a normal scheme.
Source: blueprint clause (3) (blueprint: lem-wf-dense-open-pi1-surjective).
Proof: Apply the finite-level assertion to every quotient of a compatible finite-level
O_E-model (E finite over Q_l), as in def-weil-pbc-constructible-complexes. Naturality of
the units makes their inverses compatible with all transition maps. Ordinary direct
image preserves the inverse limit. Inverting l and extending coefficients to Qbar_l
preserves the two inverse identities. This is Step (3), last paragraph. -/
theorem ProEtale.isIso_lisse_unit_of_normal_dense_open
    {U V : Scheme.{u}} [ConnectedSpace V] [IsNoetherian V]
    (hV : ∀ x : V, IsDomain (V.presheaf.stalk x) ∧
      IsIntegrallyClosed (V.presheaf.stalk x))
    (j : U ⟶ V) [IsOpenImmersion j] (hj : DenseRange j.base)
    (l : ℕ) [Fact l.Prime] (N : ProEtale.AdicSheaf l V)
    (hN : ProEtale.IsAdicLisseSheaf N) :
    IsIso ((ProEtale.adicUpperStarLowerStarAdjunction l j).unit.app N) := by
  exact hN.isIso_adicUpperStarLowerStarAdjunction_unit_app_of_isIntegrallyClosed hV j hj

/-- Restriction between the chapter's curves is fully faithful on lisse Weil sheaves,
and preserves irreducibility among lisse subsheaves. Full faithfulness is expressed by
bijectivity of every Hom map between lisse objects, without choosing a new lisse category.
Source: blueprint clause (4) (blueprint: lem-wf-dense-open-pi1-surjective).
Proof: Step (4) uses d-real-setup and lem-sc-smooth-normal to make the geometric curve
normal and integral. Its nonempty open is another such curve and is dense. Under
prop-wf-weil-sheaf-representation-equivalence, pullback is restriction of the generic
stalk representation along the surjection of Step (2). Surjectivity gives equality of
equivariant Hom spaces and of invariant subspaces, proving both assertions. -/
theorem WeilSheaf.dense_open_lisse_restriction
    (D : RealSheaves.Setup.{u, v})
    {U C : Scheme.{u}} [U.Over (Spec (.of D.k₀))] [C.Over (Spec (.of D.k₀))]
    (hC : D.IsCurve C) (j : U ⟶ C) [IsOpenImmersion j]
    [j.IsOver (Spec (.of D.k₀))] [Nonempty U] :
    (∀ F : WeilSheaf D.k₀ D.l C, F.IsLisse →
      ((WeilSheaf.upperStar j).obj F).IsLisse) ∧
    (∀ (F G : WeilSheaf D.k₀ D.l C), F.IsLisse → G.IsLisse →
      Function.Bijective ((WeilSheaf.upperStar j).map : (F ⟶ G) → _)) ∧
    (∀ F : WeilSheaf D.k₀ D.l C, F.IsIrreducibleLisse →
      ((WeilSheaf.upperStar j).obj F).IsIrreducibleLisse) := by
  have : SmoothOfRelativeDimension 1 (C ↘ Spec (.of D.k₀)) :=
    curve_relativeDimension D C hC
  have : Smooth (C ↘ Spec (.of D.k₀)) := hC.2.2.1
  have : LocallyOfFiniteType (C ↘ Spec (.of D.k₀)) := hC.2.2.2.1
  have : QuasiCompact (C ↘ Spec (.of D.k₀)) := hC.2.2.2.2.1
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian
    (C ↘ Spec (.of D.k₀))
  obtain ⟨_, _⟩ := curve_regular_connected D C hC
  have : IrreducibleSpace C := IsRegular.irreducibleSpace C
  have : IsDominant j := ⟨j.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty j)⟩
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have : GeometricallyConnected (C ↘ Spec (.of D.k₀)) :=
    (geometricallyConnected_iff_connectedSpace_of_isAlgClosed (Ω := D.k) C).2 hC.2.2.2.2.2.2
  exact ⟨fun F hF ↦ WeilSheaf.IsLisse.upperStar hF j,
    fun F G _ hG ↦ WeilSheaf.upperStar_map_bijective_of_isLisse j j.denseRange F hG,
    fun F hF ↦ hF.upperStar_of_isDominant j⟩

/-- The geometric version of restriction on curves, with algebraic l-adic coefficients.
The geometric morphism is the base change of the open immersion to the chosen algebraic
closure. Source: blueprint clause (4) (blueprint: lem-wf-dense-open-pi1-surjective).
Proof: As in Step (4), the geometric curves are normal integral and Step (1) gives the
surjection on their fundamental groups. Under cor-galois-lisse-representations the
Hom spaces are unchanged, and precisely the same subspaces are invariant. -/
theorem ProEtale.dense_open_geometric_lisse_restriction
    (D : RealSheaves.Setup.{u, v})
    {U C : Scheme.{u}} [U.Over (Spec (.of D.k₀))] [C.Over (Spec (.of D.k₀))]
    (hC : D.IsCurve C) (j : U ⟶ C) [IsOpenImmersion j]
    [j.IsOver (Spec (.of D.k₀))] [Nonempty U] :
    (∀ F : ProEtale.AdicSheaf D.l (D.geometricCurve C),
      ProEtale.IsAdicLisseSheaf F →
      ProEtale.IsAdicLisseSheaf
        ((ProEtale.adicUpperStar D.l
          (pullback.map (U ↘ Spec (.of D.k₀))
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
            (C ↘ Spec (.of D.k₀))
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) j (𝟙 _) (𝟙 _)
            ((Category.comp_id _).trans (comp_over j _).symm)
            (Category.comp_id _))).obj F)) ∧
    (∀ (F G : ProEtale.AdicSheaf D.l (D.geometricCurve C)),
      ProEtale.IsAdicLisseSheaf F → ProEtale.IsAdicLisseSheaf G →
      Function.Bijective
        ((ProEtale.adicUpperStar D.l
          (pullback.map (U ↘ Spec (.of D.k₀))
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
            (C ↘ Spec (.of D.k₀))
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) j (𝟙 _) (𝟙 _)
            ((Category.comp_id _).trans (comp_over j _).symm)
            (Category.comp_id _))).map : (F ⟶ G) → _)) ∧
    (∀ F : ProEtale.AdicSheaf D.l (D.geometricCurve C),
      ProEtale.IsIrreducibleAdicLocalSystem F →
      ProEtale.IsIrreducibleAdicLocalSystem
        ((ProEtale.adicUpperStar D.l
          (pullback.map (U ↘ Spec (.of D.k₀))
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
            (C ↘ Spec (.of D.k₀))
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) j (𝟙 _) (𝟙 _)
            ((Category.comp_id _).trans (comp_over j _).symm)
            (Category.comp_id _))).obj F)) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  let c := C ↘ Spec (.of D.k₀)
  let a := U ↘ Spec (.of D.k₀)
  let jb : D.geometricCurve U ⟶ D.geometricCurve C :=
    pullback.map a g c g j (𝟙 _) (𝟙 _)
      ((Category.comp_id _).trans (comp_over j _).symm) (Category.comp_id _)
  have hpb : IsPullback jb (pullback.fst a g) (pullback.fst c g) j := by
    refine IsPullback.of_right (h₁₂ := pullback.snd c g) (h₂₂ := c)
      (v₁₃ := g) ?_ (by
        dsimp only [jb]
        simp only [pullback.map, pullback.lift_fst]) (IsPullback.of_hasPullback c g).flip
    have he : j ≫ c = a := comp_over j (Spec (.of D.k₀))
    simpa only [jb, pullback.map, pullback.lift_snd, Category.comp_id, he] using
      (IsPullback.of_hasPullback a g).flip
  have : IsOpenImmersion jb := MorphismProperty.of_isPullback hpb.flip inferInstance
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have : Surjective g := ⟨fun x ↦ ⟨Classical.choice inferInstance, Subsingleton.elim _ _⟩⟩
  have : Nonempty (D.geometricCurve U) := by
    have : Surjective (pullback.fst a g) := inferInstance
    obtain ⟨u⟩ := (inferInstance : Nonempty U)
    obtain ⟨z, _⟩ := (pullback.fst a g).surjective u
    exact ⟨z⟩
  have : Smooth c := hC.2.2.1
  have : QuasiCompact c := hC.2.2.2.2.1
  have : Smooth (pullback.snd c g) := inferInstance
  have : IsRegular (D.geometricCurve C) := IsRegular.of_smooth (pullback.snd c g)
  have : IsLocallyNoetherian (D.geometricCurve C) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd c g)
  have : CompactSpace (D.geometricCurve C) :=
    inferInstanceAs (CompactSpace ↥(Limits.pullback c g : Scheme.{u}))
  have : ConnectedSpace (D.geometricCurve C) := hC.2.2.2.2.2.2
  have : IrreducibleSpace (D.geometricCurve C) := IsRegular.irreducibleSpace _
  have hjb : Dense (Set.range jb) :=
    jb.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty jb)
  change (∀ F, ProEtale.IsAdicLisseSheaf F →
      ProEtale.IsAdicLisseSheaf ((ProEtale.adicUpperStar D.l jb).obj F)) ∧
    (∀ F G, ProEtale.IsAdicLisseSheaf F → ProEtale.IsAdicLisseSheaf G →
      Function.Bijective ((ProEtale.adicUpperStar D.l jb).map : (F ⟶ G) → _)) ∧
    (∀ F, ProEtale.IsIrreducibleAdicLocalSystem F →
      ProEtale.IsIrreducibleAdicLocalSystem ((ProEtale.adicUpperStar D.l jb).obj F))
  refine ⟨?_, ?_, ?_⟩
  · intro F hF
    exact ProEtale.IsAdicLisseSheaf.upperStar (l := D.l)
      (X := D.geometricCurve C) (Y := D.geometricCurve U) (F := F) jb hF
  · intro F G _ hG
    exact ProEtale.IsAdicLisseSheaf.adicUpperStar_map_bijective
      (l := D.l) (Y := D.geometricCurve C) (Y' := D.geometricCurve U)
      (N := G) (fun x ↦ IsRegular.isRegularLocalRing_stalk x) jb hjb F hG
  · intro F hF
    exact ProEtale.IsIrreducibleAdicLocalSystem.adicUpperStar
      (l := D.l) (Y := D.geometricCurve C) (Y' := D.geometricCurve U) (N := F) jb hjb hF

/-- The ordinary middle extension from a nonempty open of a chapter curve is constructible
at every finite coefficient level. Source: blueprint clause (5)
(blueprint: lem-wf-dense-open-pi1-surjective).
Proof: Step (5) uses d-real-setup to get a nonempty smooth finite-type curve. Its connected
geometric base change surjects onto it, so it is connected; lem-sc-smooth-normal makes it
normal. rem-pc-regular-normal (2) then makes it integral. The open is normal and the
finite-level sheaf is finite locally constant. Apply lem-fin-normal-open-lisse-image;
its ordinary direct image is exactly the finite-level middle extension of
 def-wf-middle-extension. -/
theorem Scheme.isConstructible_middleExtension_of_curve_lisse
    (D : RealSheaves.Setup.{u, v})
    {U C : Scheme.{u}} [C.Over (Spec (.of D.k₀))]
    (hC : D.IsCurve C) (j : U ⟶ C) [IsOpenImmersion j] [Nonempty U]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteLocallyConstantSheaf F] :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) j).obj F) := by
  have : Smooth (C ↘ Spec (.of D.k₀)) := hC.2.2.1
  have : LocallyOfFiniteType (C ↘ Spec (.of D.k₀)) := hC.2.2.2.1
  have : QuasiCompact (C ↘ Spec (.of D.k₀)) := hC.2.2.2.2.1
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian
    (C ↘ Spec (.of D.k₀))
  obtain ⟨_, _⟩ := curve_regular_connected D C hC
  have : IsIntegral C := IsRegular.isIntegral C
  have : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  have : IsRegular U := ⟨isRegularLocalRing_stalk_of_etale j fun _ ↦ inferInstance⟩
  have : ConnectedSpace U := Scheme.FiniteEtale.connectedSpace_of_isOpenImmersion j
  have : IsIntegral U := IsRegular.isIntegral U
  exact Scheme.isConstructibleEtaleModuleSheaf_lowerStar_of_normal_open (K := D.k₀) j
    ⟨inferInstance, fun x ↦ ⟨inferInstance, IsRegular.isIntegrallyClosed_stalk x⟩⟩ F

end AlgebraicGeometry
