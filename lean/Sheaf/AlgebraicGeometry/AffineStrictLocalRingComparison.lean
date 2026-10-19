/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q97
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Sheaf.Paper.StrictHenselizationPointEvaluation
public import Sheaf.RingTheory.StrictHenselizationPresentation
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Sheaf.RingTheory.StrictHenselizationPresentationProperties
import Sheaf.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale
import Sheaf.AlgebraicGeometry.StrictHenselizationChartMaximalIdeal
import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
import Sheaf.RingTheory.EtaleHenselianRingLift

/-! # Affine comparison of geometric and algebraic strict local rings

Source: Stacks Project, Etale Cohomology, Tag 04HX, and Algebra, Tag 04GW
(blueprint: lem-exc-affine-strict-local-ring-comparison).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The canonical chart leg into the affine pointed-neighbourhood ring colimit.
The chart with its lifted geometric point is itself an affine pointed neighbourhood.
The inverse of `ΓSpecIso` converts its global-section leg to a map out of `D`.
Source: Stacks Project, Tag 04HX
(blueprint: lem-exc-affine-strict-local-ring-comparison). -/
noncomputable def affineStrictLocalChartMap
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (D : CommRingCat.{u}) (i : Spec D ⟶ X) [IsOpenImmersion i]
    (xD : Spec (.of Ω) ⟶ Spec D) : D →+* strictHenselizationRing (xD ≫ i) :=
  let n : strictHenselizationNeighbourhoods (xD ≫ i) :=
    (AffineEtale.Spec X ⋙ (pointSmallEtale (xD ≫ i)).fiber).elementsMk
      (AffineEtale.mk i) (Over.homMk xD rfl)
  let E := equivSmallModel.{u} (strictHenselizationNeighbourhoods (xD ≫ i))
  ((ΓSpecIso D).inv ≫
    (strictHenselizationCoordinateRings (xD ≫ i)).map (E.unitIso.inv.app n).op ≫
      colimit.ι (strictHenselizationAffineDiagram (xD ≫ i)) (op (E.functor.obj n))).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem chart_structural_map
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (D : CommRingCat.{u}) (i : Spec D ⟶ X) [IsOpenImmersion i]
    (xD : Spec (.of Ω) ⟶ Spec D) :
    strictHenselizationStructuralMap (xD ≫ i) =
      Spec.map (CommRingCat.ofHom (affineStrictLocalChartMap D i xD)) ≫ i := by
  let n : strictHenselizationNeighbourhoods (xD ≫ i) :=
    (AffineEtale.Spec X ⋙ (pointSmallEtale (xD ≫ i)).fiber).elementsMk
      (AffineEtale.mk i) (Over.homMk xD rfl)
  let E := equivSmallModel.{u} (strictHenselizationNeighbourhoods (xD ≫ i))
  let m := E.inverse.obj (E.functor.obj n)
  let a := E.unitIso.inv.app n
  have hρ := Classical.choose_spec (exists_strictHenselizationStructuralMap (xD ≫ i))
    (E.functor.obj n)
  have ha : Spec.map a.val.left.unop ≫ i = ((AffineEtale.Spec X).obj m.1).hom :=
    a.val.w
  change Spec.map (colimit.ι (strictHenselizationAffineDiagram (xD ≫ i))
      (op (E.functor.obj n))) ≫ Spec.map (ΓSpecIso m.1.left.unop).inv ≫
      ((AffineEtale.Spec X).obj m.1).hom =
        strictHenselizationStructuralMap (xD ≫ i) at hρ
  rw [← hρ]
  unfold affineStrictLocalChartMap
  change _ = Spec.map ((ΓSpecIso D).inv ≫
    (strictHenselizationCoordinateRings (xD ≫ i)).map a.op ≫
      colimit.ι (strictHenselizationAffineDiagram (xD ≫ i))
        (op (E.functor.obj n))) ≫ i
  simp only [Spec.map_comp, Category.assoc]
  change _ = Spec.map (colimit.ι (strictHenselizationAffineDiagram (xD ≫ i))
      (op (E.functor.obj n))) ≫ Spec.map (Spec.map a.val.left.unop).appTop ≫
        Spec.map (ΓSpecIso D).inv ≫ i
  have hn := congrArg Spec.map (ΓSpecIso_inv_naturality a.val.left.unop)
  simp only [Spec.map_comp] at hn
  rw [← ha]
  have hn' : Spec.map (ΓSpecIso m.1.left.unop).inv ≫ Spec.map a.val.left.unop =
      Spec.map (Spec.map a.val.left.unop).appTop ≫ Spec.map (ΓSpecIso D).inv := by
    dsimp only [m, n, AffineEtale.mk, MorphismProperty.CostructuredArrow.mk] at hn ⊢
    exact hn
  simpa only [Category.assoc] using
    congrArg (fun f ↦ Spec.map (colimit.ι (strictHenselizationAffineDiagram (xD ≫ i))
      (op (E.functor.obj n))) ≫ f ≫ i) hn'

private theorem etale_algebra_lift
    (R B S K : Type u) [CommRing R] [CommRing B] [CommRing S] [Field K]
    [Algebra R B] [Algebra R S] [Algebra R K] [Algebra.Etale R B]
    [HenselianLocalRing S] (ε : S →ₐ[R] K)
    (hs : Function.Surjective ε) (hk : RingHom.ker ε.toRingHom = IsLocalRing.maximalIdeal S)
    (q : B →ₐ[R] K) : ∃! f : B →ₐ[R] S, ε.comp f = q := by
  obtain ⟨f, hf, hu⟩ := etale_henselian_ring_lift
    (.of R) (.of B) (.of S) (CommRingCat.ofHom (algebraMap R B))
    ((HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance))
    (CommRingCat.ofHom (algebraMap R S)) K ε.toRingHom hs hk q.toRingHom (by
      ext r
      exact (q.commutes r).trans (ε.commutes r).symm)
  let f' : B →ₐ[R] S := { __ := f, commutes' := DFunLike.congr_fun hf.1 }
  refine ⟨f', ?_, ?_⟩
  · exact AlgHom.coe_ringHom_injective hf.2
  · intro g hg
    apply AlgHom.coe_ringHom_injective
    exact hu g.toRingHom ⟨RingHom.ext g.commutes, congrArg AlgHom.toRingHom hg⟩

private theorem etale_colimit_lift
    (R S K : Type u) [CommRing R] [CommRing S] [Field K]
    [Algebra R S] [Algebra R K] [HenselianLocalRing S]
    {J : Type*} [Category J] (D : J ⥤ CommAlgCat.{u} R)
    (c : Cocone D) (hc : IsColimit c) (hD : ∀ j, Algebra.Etale R (D.obj j))
    (ε : S →ₐ[R] K) (hs : Function.Surjective ε)
    (hk : RingHom.ker ε.toRingHom = IsLocalRing.maximalIdeal S)
    (q : c.pt →ₐ[R] K) : ∃! f : c.pt →ₐ[R] S, ε.comp f = q := by
  classical
  have h (j : J) : ∃! f : D.obj j →ₐ[R] S,
      ε.comp f = q.comp (c.ι.app j).hom := by
    let := hD j
    exact etale_algebra_lift R _ S K ε hs hk _
  let l (j : J) := (h j).choose
  have hl (j : J) : ε.comp (l j) = q.comp (c.ι.app j).hom := (h j).choose_spec.1
  have hu (j : J) (f : D.obj j →ₐ[R] S)
      (hf : ε.comp f = q.comp (c.ι.app j).hom) : f = l j := (h j).choose_spec.2 f hf
  let d : Cocone D := {
    pt := CommAlgCat.of R S
    ι := {
      app := fun j ↦ CommAlgCat.ofHom (l j)
      naturality := by
        intro j k r
        apply CommAlgCat.hom_ext
        change (l k).comp (D.map r).hom = (l j).comp (AlgHom.id R _)
        rw [AlgHom.comp_id]
        apply hu
        rw [← AlgHom.comp_assoc, hl, AlgHom.comp_assoc]
        exact congrArg (q.comp ·) (congrArg CommAlgCat.Hom.hom (c.w r)) } }
  let f : c.pt →ₐ[R] S := (hc.desc d).hom
  have hf (j : J) : f.comp (c.ι.app j).hom = l j :=
    congrArg CommAlgCat.Hom.hom (hc.fac d j)
  have he : ε.comp f = q := by
    suffices hh : CommAlgCat.ofHom (ε.comp f) = CommAlgCat.ofHom q from
      congrArg CommAlgCat.Hom.hom hh
    apply hc.hom_ext
    intro j
    apply CommAlgCat.hom_ext
    change (ε.comp f).comp (c.ι.app j).hom = q.comp (c.ι.app j).hom
    rw [AlgHom.comp_assoc, hf, hl]
  refine ⟨f, he, ?_⟩
  intro g hg
  suffices hh : CommAlgCat.ofHom g = CommAlgCat.ofHom f from
    congrArg CommAlgCat.Hom.hom hh
  apply hc.hom_ext
  intro j
  apply CommAlgCat.hom_ext
  change g.comp (c.ι.app j).hom = f.comp (c.ι.app j).hom
  rw [hf]
  apply hu
  rw [← AlgHom.comp_assoc, hg]

private theorem indEtale_lift
    (R B S K : Type u) [CommRing R] [CommRing B] [CommRing S] [Field K]
    [Algebra R B] [Algebra R S] [Algebra R K] [Algebra.IndEtale R B]
    [HenselianLocalRing S] (ε : S →ₐ[R] K)
    (hs : Function.Surjective ε) (hk : RingHom.ker ε.toRingHom = IsLocalRing.maximalIdeal S)
    (q : B →ₐ[R] K) : ∃! f : B →ₐ[R] S, ε.comp f = q := by
  obtain ⟨J, _, _, P, hP⟩ := Algebra.IndEtale.exists_colimitPresentation (R := R) (S := B)
  exact etale_colimit_lift R S K P.diag P.cocone P.isColimit hP ε hs hk q

private theorem pointed_residue_surjective
    (D C k K : Type u) [CommRing D] [CommRing C] [Field k] [Field K]
    [Algebra k K] [Algebra.IsSeparable k K] [IsStrictlyHenselianLocalRing C]
    (p : Ideal D) [p.IsPrime] (e₀ : p.ResidueField ≃+* k)
    (b : D →+* C) (ε : C →+* K)
    (hb : ε.comp b = (algebraMap k K).comp
      (e₀.toRingHom.comp (algebraMap D p.ResidueField)))
    (hk : RingHom.ker ε = IsLocalRing.maximalIdeal C) : Function.Surjective ε := by
  let E := IsLocalRing.ResidueField C
  let q : C →+* E := IsLocalRing.residue C
  let e : E →+* K := Ideal.Quotient.lift _ ε hk.ge
  have he : e.comp q = ε := by rfl
  let b₀ := q.comp b
  have hb₀ : RingHom.ker b₀ = p := by
    ext d
    change q (b d) = 0 ↔ d ∈ p
    rw [← e.injective.eq_iff, map_zero]
    change ε (b d) = 0 ↔ d ∈ p
    rw [← RingHom.comp_apply, hb, RingHom.comp_apply, RingHom.comp_apply,
      map_eq_zero, map_eq_zero]
    exact congrArg (fun j : Ideal D ↦ d ∈ j) (Ideal.ker_algebraMap_residueField p) |>.to_iff
  have units : p.primeCompl ≤ (IsUnit.submonoid E).comap b₀ := by
    intro d hd
    change IsUnit (b₀ d)
    rw [isUnit_iff_ne_zero]
    intro hz
    exact hd (show d ∈ p from by rw [← hb₀]; exact hz)
  let β : p.ResidueField →+* E := Ideal.ResidueField.lift p b₀ hb₀.ge units
  let a := β.comp e₀.symm.toRingHom
  let : Algebra k E := a.toAlgebra
  let : Algebra E K := e.toAlgebra
  have hcomp : e.comp a = algebraMap k K := by
    apply (RingHom.cancel_right (f := e₀.toRingHom) e₀.surjective).mp
    apply Ideal.ResidueField.ringHom_ext
    ext d
    change e (β (e₀.symm (e₀ (algebraMap D p.ResidueField d)))) =
      algebraMap k K (e₀ (algebraMap D p.ResidueField d))
    rw [e₀.symm_apply_apply, Ideal.ResidueField.lift_algebraMap]
    exact DFunLike.congr_fun hb d
  let : IsScalarTower k E K := IsScalarTower.of_algebraMap_eq' hcomp.symm
  have : Algebra.IsSeparable E K := Algebra.isSeparable_tower_top_of_isSeparable k E K
  have hsurj := IsSepClosed.algebraMap_surjective E K
  intro z
  obtain ⟨y, hy⟩ := hsurj z
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨c, (congrArg e hc).trans hy⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The chosen geometric strict local ring is the algebraic strict henselization of
`D_p`, with its specified residue map. The displayed base-map equation is the unbundled
`D`-algebra isomorphism condition. The last equation on quotient representatives says
that its induced residue-field isomorphism is the identity after both identifications
with the very same relative separable closure in `Ω`.
Source: Stacks Project, Tag 04HX (lemma-describe-etale-local-ring), and Algebra,
Tag 04GW (lemma-strict-henselization-different)
(blueprint: lem-exc-affine-strict-local-ring-comparison).

Proof:
1. The geometric point lifts uniquely through the open chart. `hxD` expresses its
prime and residue embedding, using `Spec.residueFieldIso` to identify the scheme
residue field with the residue field of `D_p`. Keep its relative separable closure K.
2. By `lem-weil-pbc-etale-local-ring-triples`, restrict the neighbourhood diagram to
the chart and identify its opposite with the etale residue triples over D, preserving
every coordinate-ring leg and pointing. The identity triple gives exactly
`affineStrictLocalChartMap` as the D-map of this colimit.
3. `lem-weil-pbc-strict-henselization-triples` makes this ring C strictly henselian,
and its evaluation epsilon to K is surjective with maximal-ideal kernel. The triple
pointings followed by K into Ω are the geometric evaluations. Colimit extensionality
therefore identifies their composite with `strictHenselizationPointEvaluation`.
4. The defining cocone in P is also the ring colimit of local-base residue triples:
a pointed map S to K factors uniquely through the residue field at its kernel, and
the inverse construction composes that residue embedding with evaluation. Both
constructions preserve the L-maps and pointings. Competing ring cocones acquire an
L-algebra structure from the identity object, so algebra universality gives ring
universality. Its induced evaluation is exactly `P.residueMap`.
5. Apply the triples theorem over L = D_p. Its colimit is strictly henselian, and
the specified map psi = P.residueMap is surjective with maximal-ideal kernel.
6. Elements of D outside p have nonzero residue in K, hence become units of C by
`lem-weil-pbc-local-ring-unit-criterion`. The localization universal property extends
the chart map uniquely to L to C, and epsilon composed with this map is L to K.
7. Apply `lem-sc-etale-henselian-ring-lift` at every pointed-etale L-algebra stage
of P, with target C and residue epsilon. Unique lifts commute with transitions;
the defining colimit gives f : H to C with its prescribed L-map and residue map.
8. Apply the same lifting lemma at every D-triple stage with target H and residue
psi. Its colimit gives g : C to H respecting the D-map and residue. Localization
uniqueness shows that g also respects the extended L-map.
9. The composites fg and gf are identities: on each defining etale stage the
single-etale uniqueness clause identifies them with the original leg, and colimit
extensionality finishes. Bundle g and f as theta. Its base-map equation gives the
D-algebra condition and psi theta = epsilon.
10. The structural map on the chart is Spec of its leg followed by i. Contravariance
of Spec gives the asserted scheme equation. Surjectivity and the maximal-ideal
kernels give both residue-field identifications, image K and kernel m_C for the
geometric evaluation. On each quotient representative c, both residue values are
epsilon(c) = psi(theta(c)); thus the map on residue fields is the identity of K. -/
theorem affine_strict_local_ring_comparison
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (D : CommRingCat.{u}) (i : Spec D ⟶ X) [IsOpenImmersion i]
    (xD : Spec (.of Ω) ⟶ Spec D) (p : Spec D)
    [Algebra p.asIdeal.ResidueField Ω]
    (hxD : xD = Spec.map ((Spec.residueFieldIso D p).hom ≫
      CommRingCat.ofHom (algebraMap p.asIdeal.ResidueField Ω)) ≫
        (Spec D).fromSpecResidueField p)
    (H : Type u) [CommRing H] [Algebra (Localization.AtPrime p.asIdeal) H]
    [Algebra (Localization.AtPrime p.asIdeal) (separableClosure p.asIdeal.ResidueField Ω)]
    [IsScalarTower (Localization.AtPrime p.asIdeal) p.asIdeal.ResidueField
      (separableClosure p.asIdeal.ResidueField Ω)]
    (P : Algebra.StrictHenselizationPresentation (Localization.AtPrime p.asIdeal)
      (separableClosure p.asIdeal.ResidueField Ω) H) :
    ∃ θ : strictHenselizationRing (xD ≫ i) ≃+* H,
      θ.toRingHom.comp (affineStrictLocalChartMap D i xD) =
        (algebraMap (Localization.AtPrime p.asIdeal) H).comp
          (algebraMap D (Localization.AtPrime p.asIdeal)) ∧
      Spec.map (CommRingCat.ofHom θ.toRingHom) ≫
          strictHenselizationStructuralMap (xD ≫ i) =
        Spec.map (CommRingCat.ofHom
          ((algebraMap (Localization.AtPrime p.asIdeal) H).comp
            (algebraMap D (Localization.AtPrime p.asIdeal)))) ≫ i ∧
      ∃ (_ : IsStrictlyHenselianLocalRing (strictHenselizationRing (xD ≫ i)))
        (_ : IsStrictlyHenselianLocalRing H),
        Function.Surjective P.residueMap ∧
        RingHom.ker P.residueMap = IsLocalRing.maximalIdeal H ∧
        (separableClosure p.asIdeal.ResidueField Ω).subtype.comp
            (P.residueMap.comp θ.toRingHom) = strictHenselizationPointEvaluation (xD ≫ i) ∧
        Set.range (strictHenselizationPointEvaluation (xD ≫ i)) =
          (separableClosure p.asIdeal.ResidueField Ω : Set Ω) ∧
        RingHom.ker (strictHenselizationPointEvaluation (xD ≫ i)) =
          IsLocalRing.maximalIdeal (strictHenselizationRing (xD ≫ i)) ∧
        ∃ (eC : (strictHenselizationRing (xD ≫ i) ⧸
            IsLocalRing.maximalIdeal (strictHenselizationRing (xD ≫ i))) ≃+*
              separableClosure p.asIdeal.ResidueField Ω)
          (eH : (H ⧸ IsLocalRing.maximalIdeal H) ≃+* separableClosure p.asIdeal.ResidueField Ω),
          eC.toRingHom.comp (Ideal.Quotient.mk
              (IsLocalRing.maximalIdeal (strictHenselizationRing (xD ≫ i)))) =
            P.residueMap.comp θ.toRingHom ∧
          eH.toRingHom.comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal H)) = P.residueMap ∧
          ∀ c : strictHenselizationRing (xD ≫ i),
            eH (Ideal.Quotient.mk (IsLocalRing.maximalIdeal H) (θ c)) =
              eC (Ideal.Quotient.mk
                (IsLocalRing.maximalIdeal (strictHenselizationRing (xD ≫ i))) c) := by
  classical
  let A := Localization.AtPrime p.asIdeal
  let K := separableClosure p.asIdeal.ResidueField Ω
  let C := strictHenselizationRing (xD ≫ i)
  let b := affineStrictLocalChartMap D i xD
  obtain ⟨_, hC⟩ := AlgebraicGeometry.strictHenselizationLocalStructure (xD ≫ i)
  let := hC
  have hp : xD (IsLocalRing.closedPoint Ω) = p := by
    rw [hxD]
    simp
  obtain ⟨_, ρ, hρ, hm⟩ := strictHenselization_chart_maximalIdeal D i xD
  have hρb : ρ = CommRingCat.ofHom b := by
    apply Spec.map_injective
    apply (cancel_mono i).mp
    exact hρ.trans (chart_structural_map D i xD)
  have hmax : IsLocalRing.maximalIdeal C = p.asIdeal.map b := by
    rw [hp, hρb] at hm
    change IsLocalRing.maximalIdeal C = p.asIdeal.map b at hm
    exact hm
  let : Algebra D C := b.toAlgebra
  have hInd : Algebra.IndEtale D C :=
    strictHenselization_indEtale_of_affine_chart (xD ≫ i) D i
      ⟨xD (IsLocalRing.closedPoint Ω), rfl⟩ (Iso.refl _) b
      (by simpa using (chart_structural_map D i xD).symm)
  let := hInd
  let k := p.asIdeal.ResidueField
  let dK : D →+* K := (algebraMap k K).comp (algebraMap D k)
  let : Algebra D K := dK.toAlgebra
  have hDK : (algebraMap A K).comp (algebraMap D A) = dK := by
    apply RingHom.ext
    intro d
    change algebraMap A K (algebraMap D A d) = algebraMap k K (algebraMap D k d)
    rw [IsScalarTower.algebraMap_apply A k K,
      ← IsScalarTower.algebraMap_apply D A k]
  let : IsScalarTower D A K := IsScalarTower.of_algebraMap_eq' hDK.symm
  have hbΩ : (strictHenselizationPointEvaluation (xD ≫ i)).comp b =
      (algebraMap k Ω).comp (algebraMap D k) := by
    let n : strictHenselizationNeighbourhoods (xD ≫ i) :=
      (AffineEtale.Spec X ⋙ (pointSmallEtale (xD ≫ i)).fiber).elementsMk
        (AffineEtale.mk i) (Over.homMk xD rfl)
    let E := equivSmallModel.{u} (strictHenselizationNeighbourhoods (xD ≫ i))
    let a := E.unitIso.inv.app n
    have hpoint : (E.inverse.obj (E.functor.obj n)).2.left ≫
        Spec.map a.val.left.unop = xD := congrArg Over.Hom.left a.property
    have heval : CommRingCat.ofHom
        ((strictHenselizationPointEvaluation (xD ≫ i)).comp b) =
        (ΓSpecIso D).inv ≫ xD.appTop ≫ (ΓSpecIso (.of Ω)).hom := by
      change ((ΓSpecIso D).inv ≫
        (strictHenselizationCoordinateRings (xD ≫ i)).map a.op ≫
        colimit.ι (strictHenselizationAffineDiagram (xD ≫ i)) (op (E.functor.obj n))) ≫
          colimit.desc (strictHenselizationAffineDiagram (xD ≫ i))
            (strictHenselizationPointCocone (xD ≫ i)) = _
      rw [Category.assoc, Category.assoc, colimit.ι_desc]
      change (ΓSpecIso D).inv ≫ (Spec.map a.val.left.unop).appTop ≫
        (E.inverse.obj (E.functor.obj n)).2.left.appTop ≫ (ΓSpecIso (.of Ω)).hom = _
      rw [← Category.assoc (Spec.map a.val.left.unop).appTop,
        ← Hom.comp_appTop, hpoint]
    have hpmap : Spec.map (CommRingCat.ofHom
        ((algebraMap k Ω).comp (algebraMap D k))) = xD := by
      rw [hxD]
      have hc := Spec.algebraMap_residueFieldIso_inv D p
      have hf : Spec.map ((ΓSpecIso D).inv ≫ (Spec D).Γevaluation p) =
          (Spec D).fromSpecResidueField p := by
        simp only [fromSpecResidueField, Spec.fromSpecStalk_eq, ← Spec.map_comp]
        rfl
      change CommRingCat.ofHom (algebraMap D p.asIdeal.ResidueField) ≫
        (Spec.residueFieldIso D p).inv =
        (ΓSpecIso D).inv ≫ (Spec D).Γevaluation p at hc
      rw [← hf, ← Spec.map_comp, ← hc]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rfl
    have hr : (ΓSpecIso D).inv ≫ xD.appTop ≫ (ΓSpecIso (.of Ω)).hom =
        CommRingCat.ofHom ((algebraMap k Ω).comp (algebraMap D k)) := by
      rw [← hpmap, ΓSpecIso_naturality]
      change (ΓSpecIso D).inv ≫ (ΓSpecIso D).hom ≫ _ = _
      exact Iso.inv_hom_id_assoc _ _
    exact congrArg CommRingCat.Hom.hom (heval.trans hr)
  let dΩ := (algebraMap k Ω).comp (algebraMap D k)
  let : Algebra D Ω := dΩ.toAlgebra
  let ev : C →ₐ[D] Ω := {
    __ := strictHenselizationPointEvaluation (xD ≫ i)
    commutes' := DFunLike.congr_fun hbΩ }
  let : IsScalarTower D k Ω := IsScalarTower.of_algebraMap_eq' rfl
  have hmem (c : C) : ev c ∈ K := by
    exact mem_separableClosure_iff.mpr
      (Algebra.IndEtale.isSeparable_of_algHom_to_isLocalRing k Ω ev c)
  let ε : C →+* K := ev.toRingHom.codRestrict K.toSubring hmem
  have hεb : ε.comp b = dK := by
    apply RingHom.ext
    intro d
    apply Subtype.ext
    exact DFunLike.congr_fun hbΩ d
  have hker : RingHom.ker ε = IsLocalRing.maximalIdeal C := by
    apply Eq.symm
    apply (IsLocalRing.maximalIdeal.isMaximal C).eq_of_le (RingHom.ker_ne_top ε)
    rw [hmax, Ideal.map_le_iff_le_comap]
    intro d hd
    change ε (b d) = 0
    rw [← RingHom.comp_apply, hεb]
    change algebraMap k K (algebraMap D k d) = 0
    rw [map_eq_zero]
    exact show d ∈ RingHom.ker (algebraMap D k) from by
      simpa only [k, Ideal.ker_algebraMap_residueField] using hd
  have hsurj : Function.Surjective ε :=
    pointed_residue_surjective D C k K p.asIdeal (RingEquiv.refl _) b ε hεb hker
  have hu (s : p.asIdeal.primeCompl) : IsUnit (b (s : D)) := by
    by_contra hn
    have he : ε (b (s : D)) = 0 := by
      change b (s : D) ∈ RingHom.ker ε
      rw [hker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hn
    rw [← RingHom.comp_apply, hεb] at he
    change algebraMap k K (algebraMap D k (s : D)) = 0 at he
    have hz' : algebraMap D k (s : D) = 0 := (map_eq_zero _).mp he
    apply s.property
    change (s : D) ∈ p.asIdeal
    exact (congrArg (fun j : Ideal D ↦ (s : D) ∈ j)
      (Ideal.ker_algebraMap_residueField p.asIdeal)).mp hz'
  let a : A →+* C := IsLocalization.lift (S := A) hu
  let : Algebra A C := a.toAlgebra
  have ha : a.comp (algebraMap D A) = b :=
    RingHom.ext (IsLocalization.lift_eq (S := A) hu)
  have hεa : ε.comp a = algebraMap A K := by
    apply IsLocalization.ringHom_ext p.asIdeal.primeCompl
    rw [RingHom.comp_assoc, ha, hεb]
    apply RingHom.ext
    intro d
    exact DFunLike.congr_fun hDK.symm d
  let ψ := P.residueMap
  have hψ : ψ.comp (algebraMap A H) = algebraMap A K := by
    apply RingHom.ext
    intro a
    exact (P.identification.inv ≫
      P.isColimit.desc (Algebra.strictHenselizationPointingCocone A K)).hom.commutes a
  obtain ⟨hH, hsH, hkH⟩ := P.local_properties A K H
  let := hH
  let εA : C →ₐ[A] K := { __ := ε, commutes' := DFunLike.congr_fun hεa }
  let ψA : H →ₐ[A] K := { __ := ψ, commutes' := DFunLike.congr_fun hψ }
  let cH := P.cocone.extend P.identification.hom
  have hcH : IsColimit cH := P.isColimit.ofIsoColimit
    (P.cocone.extendIso P.identification)
  obtain ⟨fA, hfA, _⟩ := etale_colimit_lift A C K _ cH hcH
    (fun j ↦ j.property) εA hsurj hker ψA
  let hDH := (algebraMap A H).comp (algebraMap D A)
  let : Algebra D H := hDH.toAlgebra
  let εD : C →ₐ[D] K := { __ := ε, commutes' := DFunLike.congr_fun hεb }
  let ψD : H →ₐ[D] K := {
    __ := ψ
    commutes' := fun d ↦ (DFunLike.congr_fun hψ (algebraMap D A d)).trans
      (IsScalarTower.algebraMap_apply D A K d).symm }
  obtain ⟨gD, hgD, huD⟩ := indEtale_lift D C H K ψD hsH hkH εD
  have hgA : gD.toRingHom.comp a = algebraMap A H := by
    apply IsLocalization.ringHom_ext p.asIdeal.primeCompl
    rw [RingHom.comp_assoc, ha]
    exact RingHom.ext gD.commutes
  let gA : C →ₐ[A] H := { __ := gD.toRingHom, commutes' := DFunLike.congr_fun hgA }
  have hgf : gA.comp fA = AlgHom.id A H := by
    obtain ⟨_, _, huH⟩ := etale_colimit_lift A H K _ cH hcH
      (fun j ↦ j.property) ψA hsH hkH ψA
    apply (huH (gA.comp fA) ?_).trans
      (huH (AlgHom.id A H) (AlgHom.comp_id ψA)).symm
    rw [← AlgHom.comp_assoc]
    have hh : ψA.comp gA = εA := AlgHom.coe_ringHom_injective
      (congrArg AlgHom.toRingHom hgD)
    rw [hh, hfA]
  let fD : H →ₐ[D] C := {
    __ := fA.toRingHom
    commutes' := fun d ↦ (fA.commutes (algebraMap D A d)).trans
      (DFunLike.congr_fun ha d) }
  have hfg : fD.comp gD = AlgHom.id D C := by
    obtain ⟨_, _, hu⟩ := indEtale_lift D C C K εD hsurj hker εD
    apply (hu (fD.comp gD) ?_).trans
      (hu (AlgHom.id D C) (AlgHom.comp_id εD)).symm
    rw [← AlgHom.comp_assoc]
    have hh : εD.comp fD = ψD := AlgHom.coe_ringHom_injective
      (congrArg AlgHom.toRingHom hfA)
    rw [hh, hgD]
  let θ : C ≃+* H := {
    __ := gD.toRingHom
    invFun := fA
    left_inv := DFunLike.congr_fun hfg
    right_inv := DFunLike.congr_fun hgf }
  have hθD : θ.toRingHom.comp b = hDH := RingHom.ext gD.commutes
  have hres : ψ.comp θ.toRingHom = ε := congrArg AlgHom.toRingHom hgD
  have hev : K.subtype.comp ε = strictHenselizationPointEvaluation (xD ≫ i) := rfl
  let eC : (C ⧸ IsLocalRing.maximalIdeal C) ≃+* K :=
    (Ideal.quotEquivOfEq hker.symm).trans (ε.quotientKerEquivOfSurjective hsurj)
  let eH : (H ⧸ IsLocalRing.maximalIdeal H) ≃+* K :=
    (Ideal.quotEquivOfEq hkH.symm).trans (ψ.quotientKerEquivOfSurjective hsH)
  have heC : eC.toRingHom.comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal C)) = ε := by
    ext c
    simp [eC]
  have heH : eH.toRingHom.comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal H)) = ψ := by
    apply RingHom.ext
    intro h
    simp only [eH, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hsH h
  refine ⟨θ, hθD, ?_, hC, hH, hsH, hkH, ?_, ?_, ?_, eC, eH, ?_, heH, ?_⟩
  · rw [chart_structural_map D i xD]
    simpa only [b, hDH, A, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc] using
      congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f) ≫ i) hθD
  · rw [hres]
    exact hev
  · rw [← hev]
    ext y
    constructor
    · rintro ⟨c, rfl⟩
      exact (ε c).property
    · intro hy
      obtain ⟨c, hc⟩ := hsurj ⟨y, hy⟩
      exact ⟨c, congrArg Subtype.val hc⟩
  · rw [← hev]
    apply Ideal.ext
    intro c
    change K.subtype (ε c) = 0 ↔ c ∈ IsLocalRing.maximalIdeal C
    change ((ε c : K) : Ω) = ((0 : K) : Ω) ↔ c ∈ IsLocalRing.maximalIdeal C
    rw [Subtype.val_inj]
    change c ∈ RingHom.ker ε ↔ c ∈ IsLocalRing.maximalIdeal C
    exact congrArg (fun j : Ideal C ↦ c ∈ j) hker |>.to_iff
  · exact heC.trans hres.symm
  · intro c
    change (eH.toRingHom.comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal H))) (θ c) =
      (eC.toRingHom.comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal C))) c
    rw [heH, heC]
    exact DFunLike.congr_fun hres c

end AlgebraicGeometry.Scheme
