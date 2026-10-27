/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q63
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.SpaceFlatAtPoint
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceGeometricStalkModels
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import Sheaf.RingTheory.StrictHenselizationPresentationIn
public import WeilConjectures.RingTheory.StrictHenselizationTriples
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.RingHom.Flat
import Sheaf.AlgebraicGeometry.SchemeChartGermCocone
import Sheaf.AlgebraicGeometry.SchemeChartGermCoconeIsColimit
import Sheaf.TraceFormula.EtaleLocalRingFlatness
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Étale local rings of algebraic spaces and flatness

Source: Stacks Project, Properties of Spaces, Tags 04KG, 04KF, 04KH and 04KJ;
Morphisms of Spaces, Tag 04NG; Étale Cohomology, Tag 04HX
(blueprint: lem-sfb-space-strict-local-flatness).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.AlgebraicSpace
open SingleComplex

/-- The actual affine-neighbourhood germ into the recorded strict henselization ring.
The canonical comparison of the two existing affine diagrams transports the colimit leg.
Source: Stacks Project, Tag 04HX (blueprint: lem-sfb-space-strict-local-flatness). -/
def strictLocalSchemeGerm {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) (N : Scheme.AffinePointedEtaleNeighborhood t) :
    Γ(N.obj.1.left, ⊤) ⟶ Scheme.strictHenselizationRing t :=
  colimit.ι (AlgebraicGeometry.Scheme.strictHenselizationDiagram t) (op N) ≫
    (Scheme.smallStrictHenselizationColimitIso t).inv

/-- The scheme geometric stalk is the strict henselization of its ordinary local ring,
with the residue embedding furnished by the geometric point. The first germ equation
fixes the local-ring algebra structure, and the second fixes the residue pointing.
Source: Stacks Project, Tags 04HX and 04GW
(blueprint: lem-sfb-space-strict-local-flatness).

Proof: restrict geometric neighbourhoods to affine ones by
lemma-weil-pbc-affine-neighbourhood-cofinal. The etale-local-ring-triples comparison
identifies their ring diagram and every pointing with etale residue triples on an affine
open containing the center. The strict-henselization-triples theorem gives the local ring
and its residue map. Affine-open-stalk-localization identifies the ordinary local ring
with the localization of that affine ring. Apply
lem-sbc-etale-triples-localized-strict-henselization and
lem-sc-etale-triples-colimit-is-strict-henselization. Uniqueness of the pointed-algebra
colimit supplies the specified presentation. Both displayed equations hold on the
original regular-function representatives and therefore on the colimit. -/
theorem schemeStrictLocal_presentation {T : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    ∃ (K : Type u) (_ : Field K)
      (_ : Algebra (IsLocalRing.ResidueField
        (T.presheaf.stalk (Scheme.SpecToEquivOfField Ω T t).1)) K)
      (_ : IsSepClosure (IsLocalRing.ResidueField
        (T.presheaf.stalk (Scheme.SpecToEquivOfField Ω T t).1)) K)
      (_ : Algebra (T.presheaf.stalk (Scheme.SpecToEquivOfField Ω T t).1) K)
      (_ : IsScalarTower (T.presheaf.stalk (Scheme.SpecToEquivOfField Ω T t).1)
        (IsLocalRing.ResidueField (T.presheaf.stalk (Scheme.SpecToEquivOfField Ω T t).1)) K)
      (η : K →+* Ω)
      (_ : Algebra (T.presheaf.stalk (Scheme.SpecToEquivOfField Ω T t).1)
        (Scheme.strictHenselizationRing t))
      (P : Algebra.StrictHenselizationPresentationIn.{u, u}
        (T.presheaf.stalk (Scheme.SpecToEquivOfField Ω T t).1) K
        (Scheme.strictHenselizationRing t)),
      η.comp (algebraMap (IsLocalRing.ResidueField
          (T.presheaf.stalk (Scheme.SpecToEquivOfField Ω T t).1)) K) =
        (Scheme.SpecToEquivOfField Ω T t).2.hom ∧
      (∀ (W : T.Opens) (ht : (Scheme.SpecToEquivOfField Ω T t).1 ∈ W)
        (N : Scheme.AffinePointedEtaleNeighborhood t)
        (hW : ⊤ ≤ N.obj.1.hom ⁻¹ᵁ W),
        (algebraMap (T.presheaf.stalk (Scheme.SpecToEquivOfField Ω T t).1)
            (Scheme.strictHenselizationRing t)).comp
            (T.presheaf.germ W (Scheme.SpecToEquivOfField Ω T t).1 ht).hom =
          (strictLocalSchemeGerm t N).hom.comp (N.obj.1.hom.appLE W ⊤ hW).hom) ∧
      (∀ N : Scheme.AffinePointedEtaleNeighborhood t,
        (η.comp P.residueMap).comp (strictLocalSchemeGerm t N).hom =
          (N.obj.2.left.appTop ≫ (Scheme.ΓSpecIso (.of Ω)).hom).hom) := by
  sorry

/-- The chart identification of the space stalk with the scheme geometric stalk,
hence with the strict henselization of the chart local ring. It is the unique ring
isomorphism preserving all compatible pointed-neighbourhood germs.
Source: Stacks Project, Tags 04KF and 04HX
(blueprint: lem-sfb-space-strict-local-flatness).

Proof: composition sends pointed etale T-neighbourhoods to X-neighbourhoods, using
lem-sfb-stack-chartwise-smooth-etale-calculus. Conversely pull an X-neighbourhood back
to T; lem-trf-space-fibre-products-etale-covers makes this a scheme. Restrict sections
by the first projection. These maps induce inverse colimit maps: the first projection
on one composite and the pointed diagonal on the other preserve the represented germ.
Affine cofinality and the small-basis equivalence preserve these same germs. Thus the
isomorphism satisfies the displayed formula; common pointed refinements and the two
colimit universal properties prove uniqueness. The preceding presentation theorem
identifies the scheme stalk with the strict henselization with the stipulated residue
embedding. -/
theorem strictLocalChartComparison {S : Scheme.{u}} (X : AlgebraicSpace S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) (T : Over S)
    (e : yoneda.obj T ⟶ X.obj.obj) (he : IsEtale e)
    (t : Over.mk s ⟶ T) (ht : yoneda.map t ≫ e = x) :
    ∃! E : Scheme.strictHenselizationRing t.left ≃+* stalkRing s x,
      ∀ (N : Scheme.AffinePointedEtaleNeighborhood t.left)
        (M : Neighbourhood (Over.mk s) x)
        (a : ((neighbourhoodChart (x := x)).obj M).obj.left ⟶
          Over.mk (N.obj.1.hom ≫ T.hom)),
        yoneda.map (a ≫ Over.homMk N.obj.1.hom) ≫ e =
            ((neighbourhoodChart (x := x)).obj M).obj.hom →
        M.hom.left.left ≫ a.left = N.obj.2.left →
        E.toRingHom.comp (strictLocalSchemeGerm t.left N).hom =
          ((stalkModel s x).ringCocone.ι.app (op M)).hom.comp a.left.appTop.hom := by
  classical
  let c := (stalkModel s x).ringCocone
  obtain ⟨γ, hrefine, hγ⟩ := schemeChart_germCocone X s x T e he t ht c
  obtain ⟨hcγ⟩ := schemeChart_germCocone_isColimit X s x T e he t ht c
    (stalkModel s x).ringIsColimit γ hγ
  let E₀ : Scheme.strictHenselization t.left ≅ c.pt :=
    (colimit.isColimit (Scheme.strictHenselizationDiagram t.left)).coconePointUniqueUpToIso
      hcγ
  let E : Scheme.strictHenselizationRing t.left ≅ c.pt :=
    Scheme.smallStrictHenselizationColimitIso t.left ≪≫ E₀
  have hE (N : Scheme.AffinePointedEtaleNeighborhood t.left) :
      strictLocalSchemeGerm t.left N ≫ E.hom = γ.app (op N) := by
    dsimp only [strictLocalSchemeGerm, E, Iso.trans_hom]
    rw [Category.assoc, ← Category.assoc
      (Scheme.smallStrictHenselizationColimitIso t.left).inv,
      Iso.inv_hom_id, Category.id_comp]
    exact (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom hcγ (op N)
  refine ⟨E.commRingCatIsoToRingEquiv, ?_, ?_⟩
  · intro N M a ha ht'
    have h := (hE N).trans (hγ N M a ha ht')
    exact congrArg CommRingCat.Hom.hom h
  · intro F hF
    have hmaps : CommRingCat.ofHom F.toRingHom = E.hom := by
      apply (cancel_epi (Scheme.smallStrictHenselizationColimitIso t.left).inv).mp
      apply (colimit.isColimit (Scheme.strictHenselizationDiagram t.left)).hom_ext
      intro j
      obtain ⟨M, a, ha, ht'⟩ := hrefine j.unop
      have h₁ := hF j.unop M a ha ht'
      have h₂ := congrArg CommRingCat.Hom.hom
        ((hE j.unop).trans (hγ j.unop M a ha ht'))
      apply CommRingCat.hom_ext
      simpa only [strictLocalSchemeGerm, CommRingCat.hom_comp,
        CommRingCat.hom_ofHom, RingHom.comp_assoc, colimit.cocone_ι] using h₁.trans h₂.symm
    apply RingEquiv.ext
    intro z
    exact congrArg (fun f : Scheme.strictHenselizationRing t.left ⟶ c.pt ↦ f.hom z)
      hmaps

/-- Geometric stalk rings are local, their stipulated morphism is local, and flatness
of that morphism is equivalent to flatness at the underlying point class.
Source: Stacks Project, Tags 04KH, 04KJ and 04NG
(blueprint: lem-sfb-space-strict-local-flatness).

Proof: choose compatible surjective etale charts by
lem-sfb-unramified-etale-compatible-charts and lift the fixed geometric point through
a point above its center by lem-sfb-etale-geometric-point-specified-lift. The chart
comparison and schemeStrictLocal_presentation give strict local rings. Evaluation
into Ω has maximal-ideal kernel by strict-henselization-triples. Pullback of a regular
function and evaluation commute, so the induced stalk map is local. The chart square
of ordinary and strict local rings commutes on every regular-function germ.
Strict-henselization-faithfully-flat and module-flat-transitive show that flatness of
the ordinary chart map implies flatness over its ordinary source of the strict target;
flat-algebra-faithfully-flat-descent proves the converse. Finally
lem-sfb-strict-henselization-module-flatness changes the ordinary source to its strict
henselization. This proves the equivalence for each compatible chart and hence for
the existential chart definition, without any dependence on the choices. -/
theorem geometricStalk_flat_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (g : X ⟶ Y) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) :
    ∃ (_ : IsLocalRing (stalkRing s x)) (_ : IsLocalRing (stalkRing s (x ≫ g.hom.hom))),
      IsLocalHom (stalkMap g s x) ∧
      ((stalkMap g s x).Flat ↔
        MapIsFlatAt g (Quot.mk _ ⟨Ω, s, yonedaEquiv x⟩)) := by
  sorry

-- A common field refinement composes by taking a residue field in a scheme pullback.
private theorem pointRepresentative_rel_equivalence {S : Scheme.{u}}
    (F : (Over S)ᵒᵖ ⥤ Type u) : Equivalence (PointRepresentative.Rel (F := F)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    exact ⟨p.K, inferInstance, p.base, 𝟙 _, 𝟙 _, rfl⟩
  · rintro p q ⟨K, hK, s, a, b, hab⟩
    exact ⟨K, hK, s, b, a, hab.symm⟩
  · rintro p q r ⟨K, hK, s, a, b, hab⟩ ⟨L, hL, t, c, d, hcd⟩
    let P := Limits.pullback b c
    let α : P ⟶ Over.mk s := pullback.fst b c
    let β : P ⟶ Over.mk t := pullback.snd b c
    have sq := (IsPullback.of_hasPullback b c).map (Over.forget S)
    obtain ⟨w, _, _⟩ := Scheme.exists_preimage_of_isPullback sq
      (IsLocalRing.closedPoint K) (IsLocalRing.closedPoint L)
      (Subsingleton.elim (α := Spec (.of q.K)) _ _)
    let v : Over.mk (P.left.fromSpecResidueField w ≫ P.hom) ⟶ P :=
      Over.homMk (P.left.fromSpecResidueField w) rfl
    refine ⟨P.left.residueField w, inferInstance, _, v ≫ α ≫ a, v ≫ β ≫ d, ?_⟩
    have hmid : v ≫ α ≫ b = v ≫ β ≫ c := by
      rw [← Category.assoc, ← Category.assoc]
      exact congrArg (fun f ↦ v ≫ f) (pullback.condition (f := b) (g := c))
    calc
      _ = F.map (v ≫ α).op (F.map a.op p.value) := by
        simp only [op_comp, Functor.map_comp, types_comp_apply, Category.assoc]
      _ = F.map (v ≫ α).op (F.map b.op q.value) := congrArg _ hab
      _ = F.map (v ≫ α ≫ b).op q.value := by
        simp only [op_comp, Functor.map_comp, types_comp_apply, Category.assoc]
      _ = F.map (v ≫ β ≫ c).op q.value := by rw [hmid]
      _ = F.map (v ≫ β).op (F.map c.op q.value) := by
        simp only [op_comp, Functor.map_comp, types_comp_apply, Category.assoc]
      _ = F.map (v ≫ β).op (F.map d.op r.value) := congrArg _ hcd
      _ = _ := by
        simp only [op_comp, Functor.map_comp, types_comp_apply, Category.assoc]

-- Equality of point classes gives a common field-valued section of the pullback.
private theorem exists_chart_fibre_point {S : Scheme.{u}} (E : AlgebraicSpace S)
    (U U' W : Over S) (a : yoneda.obj U ⟶ E.obj.obj)
    (a' : yoneda.obj U' ⟶ E.obj.obj) (p : W ⟶ U) (q : W ⟶ U')
    (sq : IsPullback (yoneda.map p) (yoneda.map q) a a')
    (u : U.left) (u' : U'.left) (hu : schemePointMap a u = schemePointMap a' u') :
    ∃ w : W.left, p.left w = u ∧ q.left w = u' := by
  have hrel := (pointRepresentative_rel_equivalence E.obj.obj).eqvGen_iff.mp
    (Quot.eqvGen_exact hu)
  obtain ⟨K, hK, s, α, β, hαβ⟩ := hrel
  let x : Over.mk (U.left.fromSpecResidueField u ≫ U.hom) ⟶ U :=
    Over.homMk (U.left.fromSpecResidueField u) rfl
  let y : Over.mk (U'.left.fromSpecResidueField u' ≫ U'.hom) ⟶ U' :=
    Over.homMk (U'.left.fromSpecResidueField u') rfl
  have hab : a.app _ (α ≫ x) = a'.app _ (β ≫ y) := by
    change E.obj.obj.map α.op (a.app _ x) = E.obj.obj.map β.op (a'.app _ y) at hαβ
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply] at hαβ
    change a.app _ (α ≫ x) = a'.app _ (β ≫ y) at hαβ
    exact hαβ
  obtain ⟨l, hlp, hlq⟩ := Types.exists_of_isPullback
    (sq.app (op (Over.mk s))) (α ≫ x) (β ≫ y) hab
  have hα : α.left (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint _ :=
    Subsingleton.elim (α := Spec (.of (U.left.residueField u))) _ _
  have hβ : β.left (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint _ :=
    Subsingleton.elim (α := Spec (.of (U'.left.residueField u'))) _ _
  refine ⟨l.left (IsLocalRing.closedPoint K), ?_, ?_⟩
  · have hh := congrArg (fun f : Over.mk s ⟶ U ↦
        f.left (IsLocalRing.closedPoint K)) hlp
    change p.left (l.left (IsLocalRing.closedPoint K)) =
      U.left.fromSpecResidueField u (α.left (IsLocalRing.closedPoint K)) at hh
    simpa only [hα, Scheme.fromSpecResidueField_apply] using hh
  · have hh := congrArg (fun f : Over.mk s ⟶ U' ↦
        f.left (IsLocalRing.closedPoint K)) hlq
    change q.left (l.left (IsLocalRing.closedPoint K)) =
      U'.left.fromSpecResidueField u' (β.left (IsLocalRing.closedPoint K)) at hh
    simpa only [hβ, Scheme.fromSpecResidueField_apply] using hh

-- Scheme tests are independent of which representing pullback square is chosen.
private theorem etale_of_chart_pullback {S : Scheme.{u}}
    {G F : (Over S)ᵒᵖ ⥤ Type u} {f : G ⟶ F} (hf : IsEtale f)
    {T U : Over S} {a : yoneda.obj T ⟶ F} {p : U ⟶ T}
    {q : yoneda.obj U ⟶ G} (h : IsPullback q (yoneda.map p) f a) : Etale p.left := by
  obtain ⟨V, r, b, hb, hr⟩ := hf T a
  let e : U ≅ V := yoneda.preimageIso (h.isoIsPullback _ _ hb)
  have he : e.hom ≫ r = p := by
    apply yoneda.map_injective
    simpa only [Functor.map_comp, e, Functor.preimageIso_hom, Functor.map_preimage] using
      h.isoIsPullback_hom_snd _ _ hb
  have : Etale r.left := hr
  have hh : Etale (e.hom.left ≫ r.left) := inferInstance
  simpa only [← Over.comp_left, he] using hh

-- Scheme flatness is unchanged by an etale refinement of the source.
private theorem flat_stalk_precomp_iff {U V W : Scheme.{u}}
    (h : U ⟶ V) (a : W ⟶ U) [Etale a] (w : W) :
    ((a ≫ h).stalkMap w).hom.Flat ↔ (h.stalkMap (a w)).hom.Flat := by
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
  let R := V.presheaf.stalk (h (a w))
  let B := U.presheaf.stalk (a w)
  let C := W.presheaf.stalk w
  let f : R →+* B := (h.stalkMap (a w)).hom
  let e : B →+* C := (a.stalkMap w).hom
  change (e.comp f).Flat ↔ f.Flat
  let : Algebra R B := f.toAlgebra
  let : Algebra B C := e.toAlgebra
  let : Algebra R C := (e.comp f).toAlgebra
  let : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' rfl
  have he : Module.Flat B C := Flat.stalkMap a w
  let : Module.Flat B C := he
  let : IsLocalHom e := inferInstanceAs (IsLocalHom (a.stalkMap w).hom)
  let : Module.FaithfullyFlat B C := Module.FaithfullyFlat.of_flat_of_isLocalHom
  constructor
  · intro hf
    let : Module.Flat R C := hf
    exact Module.Flat.of_flat_of_faithfullyFlat (A := R) (B := B) (C := C)
  · intro hf
    exact hf.comp (Flat.stalkMap a w)

-- Etale target stalks have the same flat modules as their base stalks.
private theorem flat_stalk_postcomp_iff {W Z V : Scheme.{u}}
    (k : W ⟶ Z) (b : Z ⟶ V) [Etale b] (w : W) :
    ((k ≫ b).stalkMap w).hom.Flat ↔ (k.stalkMap w).hom.Flat := by
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
  let : Module (Z.presheaf.stalk (k w)) (W.presheaf.stalk w) :=
    Module.compHom _ (k.stalkMap w).hom
  exact etale_local_ring_flatness b (k w) (W.presheaf.stalk w)

private theorem flat_stalk_square_iff {U V W Z : Scheme.{u}}
    (h : U ⟶ V) (k : W ⟶ Z) (a : W ⟶ U) (b : Z ⟶ V)
    [Etale a] [Etale b] (sq : a ≫ h = k ≫ b) (w : W) :
    (h.stalkMap (a w)).hom.Flat ↔ (k.stalkMap w).hom.Flat := by
  rw [← flat_stalk_precomp_iff h a w, sq, flat_stalk_postcomp_iff]

/-- The existential definition agrees with every compatible choice of scheme charts
and every point over the given point class.
Source: Stacks Project, Tag 04NG (blueprint: lem-sfb-space-strict-local-flatness).

Proof: lift a geometric representative of the given point to the specified u, using
lem-sfb-etale-geometric-point-specified-lift. Apply the preceding germ computation
and strict-henselization faithful-flatness argument to this particular chart square.
It identifies its ordinary stalk flatness with the fixed geometric stalk flatness,
which geometricStalk_flat_iff identifies with MapIsFlatAt. -/
theorem flatAt_iff_chart_stalk {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (g : X ⟶ Y) (p : Point X.obj.obj)
    (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj) (b : yoneda.obj V ⟶ Y.obj.obj)
    (h : U ⟶ V) (u : U.left) (ha : IsEtale a) (hb : IsEtale b)
    (hh : a ≫ g.hom.hom = yoneda.map h ≫ b) (hu : schemePointMap a u = p) :
    MapIsFlatAt g p ↔ (h.left.stalkMap u).hom.Flat := by
  constructor
  · rintro ⟨U', V', a', b', h', u', ha', hb', hh', hu', hflat⟩
    obtain ⟨W, α, q, sqW, hα⟩ := ha' U a
    let α' : W ⟶ U' := yoneda.preimage q
    have hq : yoneda.map α' = q := yoneda.map_preimage q
    have sqW' : IsPullback (yoneda.map α) (yoneda.map α') a a' := by
      rw [hq]
      exact sqW.flip
    have hα' : Etale α'.left := etale_of_chart_pullback ha sqW'
    obtain ⟨w, hw, hw'⟩ := exists_chart_fibre_point X U U' W a a' α α'
      sqW' u u' (hu.trans hu'.symm)
    obtain ⟨Z, β', qZ, sqZ, hβ'⟩ := hb V' b'
    let β : Z ⟶ V := yoneda.preimage qZ
    have hqZ : yoneda.map β = qZ := yoneda.map_preimage qZ
    have sqZ' : IsPullback (yoneda.map β) (yoneda.map β') b b' := by
      rw [hqZ]
      exact sqZ
    have hβ : Etale β.left := etale_of_chart_pullback hb' sqZ'.flip
    have hcomm : yoneda.map (α ≫ h) ≫ b = yoneda.map (α' ≫ h') ≫ b' := by
      calc
        _ = yoneda.map α ≫ (a ≫ g.hom.hom) := by
          rw [Functor.map_comp, Category.assoc, ← hh]
        _ = yoneda.map α' ≫ (a' ≫ g.hom.hom) := by
          simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ g.hom.hom) sqW'.w
        _ = _ := by rw [hh', Functor.map_comp, Category.assoc]
    let k : W ⟶ Z := yoneda.preimage
      (sqZ'.lift (yoneda.map (α ≫ h)) (yoneda.map (α' ≫ h')) hcomm)
    have hk : yoneda.map k =
        sqZ'.lift (yoneda.map (α ≫ h)) (yoneda.map (α' ≫ h')) hcomm :=
      yoneda.map_preimage _
    have hk₁ : α ≫ h = k ≫ β := by
      apply yoneda.map_injective
      rw [Functor.map_comp yoneda k β, hk, IsPullback.lift_fst]
    have hk₂ : α' ≫ h' = k ≫ β' := by
      apply yoneda.map_injective
      rw [Functor.map_comp yoneda k β', hk, IsPullback.lift_snd]
    have : Etale α.left := hα
    have : Etale α'.left := hα'
    have : Etale β.left := hβ
    have : Etale β'.left := hβ'
    have heq₁ := flat_stalk_square_iff h.left k.left α.left β.left
      (congrArg Over.Hom.left hk₁) w
    have heq₂ := flat_stalk_square_iff h'.left k.left α'.left β'.left
      (congrArg Over.Hom.left hk₂) w
    rw [hw] at heq₁
    rw [hw'] at heq₂
    exact heq₁.mpr (heq₂.mp hflat)
  · intro hf
    exact ⟨U, V, a, b, h, u, ha, hb, hh, hu, hf⟩

end AlgebraicGeometry.AlgebraicSpace
