module

public import Sheaf.Paper.FiniteFreeSystemRestrictionData
import Sheaf.Paper.FiniteFreeSystemScalars
import Sheaf.Paper.FiniteFreeSystemGeometry

public import Sheaf.SixFunctors.SemilinearProperOpenMatePasting
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.IntegralScalarExtensionWellDefined
public import Sheaf.Paper.NormalizedDVRTower
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Finite-free coefficient restriction on entire derived systems

Source: finite-free coefficient tensor in the blueprint coefficient comparison;
Stacks 07A6, 03DI, 03DJ and 0F7B--0F7F
(blueprint: lem-coef-finite-free-system-restriction).

Natural transformations below live on the ordinary unbounded derived categories
of strict semilinear systems, before evaluation and inverse limit. Index n means
positive exponent n+1. The upper coefficients are S/pi^(n+1)S, including ramification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale.SemilinearProperOpen
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
open WeilConjectures.SemilinearSections
namespace WeilConjectures.FiniteFreeSystemRestriction

private theorem quotient_basis_bijective
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (f : R →+* S) (pi : R) (d : ℕ) (b : Fin d → S)
    (hb : Function.Bijective (fun a : Fin d → R ↦ ∑ j, f (a j) * b j))
    (n : ℕ) : Function.Bijective
      (fun a : Fin d → quotient R pi n ↦ ∑ j,
        quotientMap f pi n (a j) * Ideal.Quotient.mk _ (b j)) := by
  classical
  let F : (Fin d → R) → S := fun a ↦ ∑ j, f (a j) * b j
  let qR := Ideal.Quotient.mk ((Ideal.span {pi}) ^ (n + 1))
  let qS := Ideal.Quotient.mk ((Ideal.span {f pi}) ^ (n + 1))
  let Q : (Fin d → quotient R pi n) → quotient S (f pi) n :=
    fun a ↦ ∑ j, quotientMap f pi n (a j) * qS (b j)
  have hQ (a : Fin d → R) : Q (fun j ↦ qR (a j)) = qS (F a) := by
    change (∑ j, qS (f (a j)) * qS (b j)) = qS (F a)
    simp only [F, map_sum, map_mul]
  have hsub (a c : Fin d → R) : F (a - c) = F a - F c := by
    simp only [F, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
  have hmul (t : R) (a : Fin d → R) :
      F (fun j ↦ t * a j) = f t * F a := by
    simp only [F, map_mul, mul_assoc, Finset.mul_sum]
  change Function.Bijective Q
  constructor
  · intro a c hac
    choose a' ha using fun j ↦ Ideal.Quotient.mk_surjective (a j)
    choose c' hc using fun j ↦ Ideal.Quotient.mk_surjective (c j)
    have ha' : (fun j ↦ qR (a' j)) = a := funext ha
    have hc' : (fun j ↦ qR (c' j)) = c := funext hc
    rw [← ha', ← hc', hQ, hQ] at hac
    have hm : F a' - F c' ∈ (Ideal.span {f pi}) ^ (n + 1) :=
      Ideal.Quotient.eq.mp hac
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hm
    obtain ⟨z, hz⟩ := hm
    obtain ⟨t, ht⟩ := hb.2 z
    change F t = z at ht
    have heq : a' - c' = fun j ↦ pi ^ (n + 1) * t j := by
      apply hb.1
      change F (a' - c') = F (fun j ↦ pi ^ (n + 1) * t j)
      rw [hsub, hmul, map_pow, ht]
      exact hz
    funext j
    rw [← ha, ← hc]
    apply Ideal.Quotient.eq.mpr
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨t j, congrFun heq j⟩
  · intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := hb.2 z
    exact ⟨fun j ↦ qR (a j), (hQ a).trans (congrArg qS ha)⟩


private theorem paste_inner {C : Type*} [Category C]
    {A B C₀ D E F G H I J K : C}
    {x : A ⟶ B} {y : B ⟶ C₀} {z : C₀ ⟶ D} {w : D ⟶ E}
    {n : B ⟶ F} {f : F ⟶ D} {h : F ⟶ G} {t : G ⟶ H} {s : H ⟶ E}
    {e : A ⟶ I} {g : I ⟶ J} {γ₀ : J ⟶ G} {v : J ⟶ K} {γ₁ : K ⟶ H}
    (hn : y ≫ z = n ≫ f) (ho : f ≫ w = h ≫ t ≫ s)
    (hg : x ≫ n ≫ h = e ≫ g ≫ γ₀) (ht : γ₀ ≫ t = v ≫ γ₁) :
    x ≫ y ≫ z ≫ w = e ≫ g ≫ v ≫ γ₁ ≫ s := by
  calc
    x ≫ y ≫ z ≫ w = x ≫ n ≫ f ≫ w := by rw [reassoc_of% hn]
    _ = x ≫ n ≫ h ≫ t ≫ s := by rw [ho]
    _ = e ≫ g ≫ γ₀ ≫ t ≫ s := by rw [reassoc_of% hg]
    _ = e ≫ g ≫ v ≫ γ₁ ≫ s := by rw [reassoc_of% ht]


private theorem paste_outer {C : Type*} [Category C]
    {A B C₀ D E F G H I J K : C}
    {x : A ⟶ B} {y : B ⟶ C₀} {z : C₀ ⟶ D} {w : D ⟶ E} {o : E ⟶ F}
    {c₀ : A ⟶ G} {c₁ : B ⟶ H} {c₂ : C₀ ⟶ I}
    {v₀ : G ⟶ H} {v₁ : H ⟶ I} {v₂ : I ⟶ J} {s₀ : J ⟶ E}
    {v₃ : J ⟶ K} {s₁ : K ⟶ F} {rhs : G ⟶ K}
    (hp : z ≫ w = c₂ ≫ v₂ ≫ s₀) (hs : s₀ ≫ o = v₃ ≫ s₁)
    (hy : y ≫ c₂ = c₁ ≫ v₁) (hx : x ≫ c₁ = c₀ ≫ v₀)
    (hi : v₀ ≫ v₁ ≫ v₂ ≫ v₃ = rhs) :
    x ≫ y ≫ z ≫ w ≫ o = c₀ ≫ rhs ≫ s₁ := by
  calc
    x ≫ y ≫ z ≫ w ≫ o = x ≫ y ≫ c₂ ≫ v₂ ≫ v₃ ≫ s₁ := by
      rw [reassoc_of% hp, hs]
    _ = c₀ ≫ v₀ ≫ v₁ ≫ v₂ ≫ v₃ ≫ s₁ := by
      rw [reassoc_of% hy, reassoc_of% hx]
    _ = c₀ ≫ rhs ≫ s₁ := by
      simpa only [Category.assoc] using congrArg (fun t ↦ c₀ ≫ t ≫ s₁) hi


private theorem map_two_three {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y Z U V : C}
    {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ U} {d : U ⟶ V} {e : V ⟶ Z}
    (h : a ≫ b = c ≫ d ≫ e) :
    F.map a ≫ F.map b = F.map c ≫ F.map d ≫ F.map e := by
  simpa only [Functor.map_comp] using congrArg F.map h


private theorem map_four_five {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X A B C₀ Z E G H I : C}
    {a : X ⟶ A} {b : A ⟶ B} {c : B ⟶ C₀} {d : C₀ ⟶ Z}
    {e : X ⟶ E} {f : E ⟶ G} {g : G ⟶ H} {h : H ⟶ I} {j : I ⟶ Z}
    (hh : a ≫ b ≫ c ≫ d = e ≫ f ≫ g ≫ h ≫ j) :
    F.map a ≫ F.map b ≫ F.map c ≫ F.map d =
      F.map e ≫ F.map f ≫ F.map g ≫ F.map h ≫ F.map j := by
  simpa only [Functor.map_comp] using congrArg F.map hh

universe v w

private theorem generic_compact_preservation
    {XB VB WB SB TB ZB XA VA WA SA TA ZA : Type v}
    [Category.{w} XB] [Category.{w} VB] [Category.{w} WB]
    [Category.{w} SB] [Category.{w} TB] [Category.{w} ZB]
    [Category.{w} XA] [Category.{w} VA] [Category.{w} WA]
    [Category.{w} SA] [Category.{w} TA] [Category.{w} ZA]
    (Ux : XB ⥤ XA) (Uv : VB ⥤ VA) (Uw : WB ⥤ WA)
    (Us : SB ⥤ SA) (Ut : TB ⥤ TA) (Uz : ZB ⥤ ZA)
    (Jjb : XB ⥤ VB) (Jkb : VB ⥤ WB) (Jab : SB ⥤ TB) (Jjkb : XB ⥤ WB)
    (Rrb : VB ⥤ SB) (Rpb : WB ⥤ TB) (Rqb : TB ⥤ ZB) (Rpqb : WB ⥤ ZB)
    (Jja : XA ⥤ VA) (Jka : VA ⥤ WA) (Jaa : SA ⥤ TA) (Jjka : XA ⥤ WA)
    (Rra : VA ⥤ SA) (Rpa : WA ⥤ TA) (Rqa : TA ⥤ ZA) (Rpqa : WA ⥤ ZA)
    (gb : Rrb ⋙ Jab ⟶ Jkb ⋙ Rpb) (ga : Rra ⋙ Jaa ⟶ Jka ⋙ Rpa)
    (jb : Jjb ⋙ Jkb ≅ Jjkb) (ja : Jja ⋙ Jka ≅ Jjka)
    (sb : Rpb ⋙ Rqb ≅ Rpqb) (sa : Rpa ⋙ Rqa ≅ Rpqa)
    (cj : Jjb ⋙ Uv ≅ Ux ⋙ Jja) (ck : Jkb ⋙ Uw ≅ Uv ⋙ Jka)
    (ca : Jab ⋙ Ut ≅ Us ⋙ Jaa) (cjk : Jjkb ⋙ Uw ≅ Ux ⋙ Jjka)
    (cr : Rrb ⋙ Us ≅ Uv ⋙ Rra) (cp : Rpb ⋙ Ut ≅ Uw ⋙ Rpa)
    (cq : Rqb ⋙ Uz ≅ Ut ⋙ Rqa) (cpq : Rpqb ⋙ Uz ≅ Uw ⋙ Rpqa)
    (hpush : ∀ N : WB, Uz.map (sb.hom.app N) ≫ cpq.hom.app N =
      cq.hom.app (Rpb.obj N) ≫ Rqa.map (cp.hom.app N) ≫ sa.hom.app (Uw.obj N))
    (hopen : ∀ M : XB, Uw.map (jb.hom.app M) ≫ cjk.hom.app M =
      ck.hom.app (Jjb.obj M) ≫ Jka.map (cj.hom.app M) ≫ ja.hom.app (Ux.obj M))
    (hgamma : ∀ N : VB, Ut.map (gb.app N) ≫ cp.hom.app (Jkb.obj N) ≫
      Rpa.map (ck.hom.app N) = ca.hom.app (Rrb.obj N) ≫
        Jaa.map (cr.hom.app N) ≫ ga.app (Uv.obj N))
    (M : XB) :
    Uz.map ((compactWord Jjb Jkb Jab Jjkb Rrb Rpb Rqb Rpqb gb jb sb).app M) ≫
      (compactScalarIso Ux Uw Uz Jjkb Rpqb Jjka Rpqa cjk cpq).hom.app M =
    (compactScalarIso Us Ut Uz Jab Rqb Jaa Rqa ca cq).hom.app ((Jjb ⋙ Rrb).obj M) ≫
      (Jaa ⋙ Rqa).map ((compactScalarIso Ux Uv Us Jjb Rrb Jja Rra cj cr).hom.app M) ≫
      (compactWord Jja Jka Jaa Jjka Rra Rpa Rqa Rpqa ga ja sa).app (Ux.obj M) := by
  dsimp only [compactWord, compactScalarIso, NatIso.ofComponents, Iso.trans,
    Functor.mapIso, Iso.app, Functor.comp_obj, Functor.comp_map]
  simp only [Functor.map_comp, Category.assoc]
  have hn := cp.hom.naturality (jb.hom.app M)
  have ht := ga.naturality (cj.hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn ht
  have ho := map_two_three Rpa (hopen M)
  have hi := paste_inner hn ho (hgamma (Jjb.obj M)) ht.symm
  have hqi := map_four_five Rqa hi
  have hs := sa.hom.naturality (cjk.hom.app M)
  have hy := cq.hom.naturality (Rpb.map (jb.hom.app M))
  have hx := cq.hom.naturality (gb.app (Jjb.obj M))
  dsimp only [Functor.comp_map, Functor.comp_obj] at hs hy hx
  have hout := paste_outer (hpush (Jjkb.obj M)) hs.symm hy hx hqi
  simpa only [Category.assoc] using hout


variable (l : ℕ) [Fact l.Prime]
  (E L : Type (u + 1)) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (i : E →ₐ[ℚ_[l]] L)


/-- The whole assertion, with canonical scalar and geometric data and their equations.
The reduced basis is the reduction of the one integral basis b supplied to the theorem,
not an independent choice at each level.
Source: all clauses of the node and proof Steps 1--13
(blueprint: lem-coef-finite-free-system-restriction). -/
structure Assertions (D : FiniteFieldDatum.{u}) (d : ℕ)
    (b : Fin d → Padic.coefficientExtensionIntegers l L) (ramification : ℕ) where
  /-- The quotient by pi^nS is the quotient by v^(en), with actual ideal equality. -/
  ramifiedIdeal : ∀ n : ℕ,
    (Ideal.span {integralScalarIntegerInclusion l E L i
      (Padic.coefficientExtensionUniformizer l E)}) ^ (n + 1) =
        Padic.coefficientExtensionIdeal l L (ramification * (n + 1))
  /-- Coordinates are given by the reductions of the one fixed integral basis. -/
  reducedBasis : ∀ n : ℕ, Function.Bijective
    (fun a : Fin d → A l E n ↦ ∑ j,
      (levelMap l E L i n).hom (a j) *
        Ideal.Quotient.mk ((Ideal.span {integralScalarIntegerInclusion l E L i
          (Padic.coefficientExtensionUniformizer l E)}) ^ (n + 1)) (b j))
  /-- Normalization, constructibility, Tor [0,0], exactness and scalar adjunction. -/
  scalars : ∀ X : Spaces D, ScalarAssertions l E L i X.val.left
  /-- The canonical geometric comparisons and their mate normalizations. -/
  geometry : Geometry l E L i D
  /-- All geometric generators used in compactification words are preserved. -/
  compatibility : Compatibility l E L i geometry
  /-- Equality of the actual compactification-composition word before evaluation.
  The square is allowed to be non-Cartesian, including refinement squares. -/
  compact_composition : ∀ (X V W S T Z : Spaces D)
    (j : X.val.left ⟶ V.val.left) (r : V.val.left ⟶ S.val.left)
    (a : S.val.left ⟶ T.val.left) (q : T.val.left ⟶ Z.val.left)
    (k : V.val.left ⟶ W.val.left) (p : W.val.left ⟶ T.val.left)
    [IsOpenImmersion j] [IsOpenImmersion a] [IsOpenImmersion k]
    [QuasiCompact j] [QuasiCompact a] [QuasiCompact k]
    [IsProper r] [IsProper p] [IsProper q]
    (h : k ≫ p = r ≫ a)
    (M : Derived (B l E L i) (bTransition l E L i) X.val.left),
    Normalized.{u + 1, u, u + 1} (Scheme.ProEt.topology X.val.left)
      (coefficients (B l E L i) X.val.left)
      (transition (B l E L i) (bTransition l E L i) X.val.left)
      (scalars X).upper.scalar M →
    levelwiseCtf (B l E L i) (bTransition l E L i) X.val.left (scalars X).upper M →
    (U l E L i Z.val.left).map
        ((compactCompositionWord (B l E L i) (bTransition l E L i) j r a q k p h).app M) ≫
      (geometry.compactIso l E L i X W Z (j ≫ k) (p ≫ q)).hom.app M =
    (geometry.compactIso l E L i S T Z a q).hom.app
        ((compact (B l E L i) (bTransition l E L i) j r).obj M) ≫
      (compact (A l E) (aTransition l E) a q).map
        ((geometry.compactIso l E L i X V S j r).hom.app M) ≫
      (compactCompositionWord (A l E) (aTransition l E) j r a q k p h).app
        ((U l E L i X.val.left).obj M)


set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] R J sComp jComp gamma
attribute [local irreducible] Geometry.pushIso Geometry.openIso systemInclusion

private theorem compact_composition_of_compatibility (D : FiniteFieldDatum.{u})
    (geometry : Geometry l E L i D) (hG : Compatibility l E L i geometry) :
    ∀ (X V W S T Z : Spaces D)
    (j : X.val.left ⟶ V.val.left) (r : V.val.left ⟶ S.val.left)
    (a : S.val.left ⟶ T.val.left) (q : T.val.left ⟶ Z.val.left)
    (k : V.val.left ⟶ W.val.left) (p : W.val.left ⟶ T.val.left)
    [IsOpenImmersion j] [IsOpenImmersion a] [IsOpenImmersion k]
    [QuasiCompact j] [QuasiCompact a] [QuasiCompact k]
    [IsProper r] [IsProper p] [IsProper q]
    (h : k ≫ p = r ≫ a)
    (M : Derived (B l E L i) (bTransition l E L i) X.val.left),
    (U l E L i Z.val.left).map
        ((compactCompositionWord (B l E L i) (bTransition l E L i) j r a q k p h).app M) ≫
      (geometry.compactIso l E L i X W Z (j ≫ k) (p ≫ q)).hom.app M =
    (geometry.compactIso l E L i S T Z a q).hom.app
        ((compact (B l E L i) (bTransition l E L i) j r).obj M) ≫
      (compact (A l E) (aTransition l E) a q).map
        ((geometry.compactIso l E L i X V S j r).hom.app M) ≫
      (compactCompositionWord (A l E) (aTransition l E) j r a q k p h).app
        ((U l E L i X.val.left).obj M) := by
  intro X V W S T Z j r a q k p _ _ _ _ _ _ _ _ _ h M
  exact generic_compact_preservation
    (XB := Derived (B l E L i) (bTransition l E L i) X.val.left)
    (VB := Derived (B l E L i) (bTransition l E L i) V.val.left)
    (WB := Derived (B l E L i) (bTransition l E L i) W.val.left)
    (SB := Derived (B l E L i) (bTransition l E L i) S.val.left)
    (TB := Derived (B l E L i) (bTransition l E L i) T.val.left)
    (ZB := Derived (B l E L i) (bTransition l E L i) Z.val.left)
    (XA := Derived (A l E) (aTransition l E) X.val.left)
    (VA := Derived (A l E) (aTransition l E) V.val.left)
    (WA := Derived (A l E) (aTransition l E) W.val.left)
    (SA := Derived (A l E) (aTransition l E) S.val.left)
    (TA := Derived (A l E) (aTransition l E) T.val.left)
    (ZA := Derived (A l E) (aTransition l E) Z.val.left)
    (U l E L i X.val.left) (U l E L i V.val.left) (U l E L i W.val.left)
    (U l E L i S.val.left) (U l E L i T.val.left) (U l E L i Z.val.left)
    (J (B l E L i) (bTransition l E L i) j)
    (J (B l E L i) (bTransition l E L i) k)
    (J (B l E L i) (bTransition l E L i) a)
    (J (B l E L i) (bTransition l E L i) (j ≫ k))
    (R (B l E L i) (bTransition l E L i) r)
    (R (B l E L i) (bTransition l E L i) p)
    (R (B l E L i) (bTransition l E L i) q)
    (R (B l E L i) (bTransition l E L i) (p ≫ q))
    (J (A l E) (aTransition l E) j) (J (A l E) (aTransition l E) k)
    (J (A l E) (aTransition l E) a) (J (A l E) (aTransition l E) (j ≫ k))
    (R (A l E) (aTransition l E) r) (R (A l E) (aTransition l E) p)
    (R (A l E) (aTransition l E) q) (R (A l E) (aTransition l E) (p ≫ q))
    (gamma (B l E L i) (bTransition l E L i) k r p a h)
    (gamma (A l E) (aTransition l E) k r p a h)
    (jComp (B l E L i) (bTransition l E L i) j k)
    (jComp (A l E) (aTransition l E) j k)
    (sComp (B l E L i) (bTransition l E L i) p q)
    (sComp (A l E) (aTransition l E) p q)
    (geometry.openIso l E L i X V j) (geometry.openIso l E L i V W k)
    (geometry.openIso l E L i S T a) (geometry.openIso l E L i X W (j ≫ k))
    (geometry.pushIso l E L i V S r) (geometry.pushIso l E L i W T p)
    (geometry.pushIso l E L i T Z q) (geometry.pushIso l E L i W Z (p ≫ q))
    (hG.push_comp W T Z p q) (hG.open_comp X V W j k)
    (hG.gamma V W S T k r p a h) M


/-- Finite-free coefficient restriction preserves the simultaneous geometric calculus.
Source: finite-free coefficient tensor in the blueprint coefficient comparison;
Stacks 07A6, 03DI, 03DJ and 0F7B--0F7F
(blueprint: lem-coef-finite-free-system-restriction).

Proof:
1. Use the vertical sequence site and its module-system realization from
   lem-coef-semilinear-derived-sections. The quotient maps define one ring-sheaf map.
2. Reduce the single integral basis b modulo pi^(n+1). Its coordinate bijection
   descends because pi^(n+1)R^d maps onto pi^(n+1)S; the reductions commute with
   all quotient transitions. Associated uniformizers give the displayed ideal equality.
3. The coefficient system is thus finite free over A, normalized under every
   derived reduction, constructible on the one stratum, and of Tor amplitude [0,0].
   Pullback fixes the same constant basis sections at every level.
4. The ordinary scalar adjunction is sheafified tensor/restriction, with unit
   x mapped to 1 tensor x (lem-pur-sheaf-ring-coefficient-ordinary-adjunction).
   Restriction is exact, and the basis identifies restricted extension with d copies
   of the input, so extension is exact (lem-pur-finite-free-scalar-extension).
5. An exact left adjoint makes restriction preserve K-injectives. Localizing this
   exact adjunction gives the specified unbounded derived adjunction and computes
   its scalar extension termwise on every complex.
6. Ordinary restriction/direct image is identity on all system sections. Its
   pullback mate is invertible and exact. K-injective resolutions of entire systems
   give the invertible derived direct-image comparison. The derived adjoint-square
   lemma fixes this comparison by the geometric units and counits; no faithfulness
   of evaluation on morphisms is used.
7. Open extension is identity on the open and zero on its complement. Its
   restriction comparison preserves the open Hom bijection and localizes exactly.
8. Section formulas preserve direct-image compositors. Adjunction conjugation
   preserves pullback and open compositors, identity comparisons and equality
   transports. Clopen projection is (1,0) in the decomposition into the two opens.
9. The beta, clopen projection and compositor word defining alpha is therefore
   preserved. Its proper-adjunction right mate gamma is preserved, with the
   well-typed endpoints R_r followed by J_i and J_k followed by R_p.
10. Restriction past a compactification is the displayed proper then open paste.
    The compact composition word is preserved generator by generator. The same
    applies to refinements and any inverses where already defined, since applying
    a functor preserves an inverse. These equalities hold before evaluation or
    inverse limit; restricting to normalized levelwise bounded constructible
    finite-Tor objects imposes no bound independent of the level.
-/
theorem finiteFreeSystemRestriction (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (d : ℕ) (b : Fin d → Padic.coefficientExtensionIntegers l L)
    (_hb : Function.Bijective (fun a : Fin d → Padic.coefficientExtensionIntegers l E ↦
      ∑ j, integralScalarIntegerInclusion l E L i (a j) * b j))
    (ramification : ℕ) (_he : 0 < ramification)
    (_hram : Associated
      (integralScalarIntegerInclusion l E L i (Padic.coefficientExtensionUniformizer l E))
      (Padic.coefficientExtensionUniformizer l L ^ ramification)) :
    Nonempty (Assertions l E L i D d b ramification) := by
  classical
  have hbq (n : ℕ) : Function.Bijective
      (fun a : Fin d → A l E n ↦ ∑ j,
        (levelMap l E L i n).hom (a j) *
          Ideal.Quotient.mk ((Ideal.span {integralScalarIntegerInclusion l E L i
            (Padic.coefficientExtensionUniformizer l E)}) ^ (n + 1)) (b j)) :=
    quotient_basis_bijective (integralScalarIntegerInclusion l E L i)
      (Padic.coefficientExtensionUniformizer l E) d b _hb n
  let scalars (X : Spaces D) :=
    (scalarAssertions_of_reducedBasis l E L i d b hbq X.val.left).some
  obtain ⟨G, hG⟩ := (geometryCompatibility_of_scalars l E L i D scalars).some
  refine ⟨{
    ramifiedIdeal := ?_
    reducedBasis := hbq
    scalars := scalars
    geometry := G
    compatibility := hG
    compact_composition := ?_
  }⟩
  · intro n
    rw [Ideal.span_singleton_eq_span_singleton.mpr _hram,
      ← Ideal.span_singleton_pow, ← pow_mul]
    rfl
  · intro X V W S T Z j r a q k p _ _ _ _ _ _ _ _ _ h M _ _
    exact compact_composition_of_compatibility l E L i D G hG X V W S T Z
      j r a q k p h M


end WeilConjectures.FiniteFreeSystemRestriction
