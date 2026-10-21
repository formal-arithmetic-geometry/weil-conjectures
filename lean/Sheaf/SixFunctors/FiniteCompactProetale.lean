module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.LocalizingClosure
import Sheaf.AlgebraicGeometry.FiniteDiscreteCtfOrigin
import Mathlib.Algebra.CharP.CharAndCard
import Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleCompact
import Sheaf.AlgebraicGeometry.UnboundedSiteComparison

/-!
# Compactness of finite constructible pro-etale complexes

Source: Weil conjectures blueprint main-20261015, `sec-six-functors-basics`,
`sk-prop-ctf-finite-compact/sk-prop-ctf-finite-compact-proetale.md` and its proof
`sk-prop-ctf-finite-compact-proetale.proof.md`
(blueprint: det-ctf-finite-compact-proetale).

The ambient category is the unbounded derived category of module objects over the
pulled-back condensed ring `A_X` of a finite discrete `ℓ`-primary ring `A`.  The
compactness map is the one of `CategoryTheory.IsCompactObject`
(blueprint: def-pc-compact-object), written out for one family with an ambient coproduct,
because the localizing closure is a full subcategory with the ambient coproducts.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry Scheme DirectSum

open Classical in
private theorem compact_map_cofan
    {B B' : Type*} [Category B] [Category B'] [Preadditive B] [Preadditive B']
    [HasCoproducts.{w} B] (F : B ⥤ B') [F.Additive] [F.Full] [F.Faithful]
    [∀ I : Type w, PreservesColimitsOfShape (Discrete I) F]
    (K : B) (hK : IsCompactObject.{w} K) (K' : B') (eK : F.obj K ≅ K')
    {I : Type w} (E : I → B') (hE : ∀ i, F.essImage (E i))
    (c : Cofan E) (hc : IsColimit c) :
    Function.Bijective (DirectSum.toAddMonoid
      (fun i ↦ Preadditive.rightComp K' (c.inj i))) := by
  classical
  choose M e using hE
  let a : F.obj (∐ M) ⟶ c.pt :=
    (isColimitCofanMkObjOfIsColimit F M _ (coproductIsCoproduct M)).desc
      (Cofan.mk c.pt (fun i ↦ (e i).some.hom ≫ c.inj i))
  let b : c.pt ⟶ F.obj (∐ M) :=
    hc.desc (Cofan.mk _ (fun i ↦ (e i).some.inv ≫ F.map (Sigma.ι M i)))
  have ha (i) : F.map (Sigma.ι M i) ≫ a = (e i).some.hom ≫ c.inj i :=
    (isColimitCofanMkObjOfIsColimit F M _ (coproductIsCoproduct M)).fac _ ⟨i⟩
  have hb (i) : c.inj i ≫ b = (e i).some.inv ≫ F.map (Sigma.ι M i) :=
    hc.fac _ ⟨i⟩
  let q : F.obj (∐ M) ≅ c.pt :=
    { hom := a
      inv := b
      hom_inv_id := by
        apply (isColimitCofanMkObjOfIsColimit F M _ (coproductIsCoproduct M)).hom_ext
        intro ⟨i⟩
        change F.map (Sigma.ι M i) ≫ (a ≫ b) = F.map (Sigma.ι M i) ≫ 𝟙 _
        rw [← Category.assoc, ha, Category.assoc, hb]
        simp
      inv_hom_id := by
        apply hc.hom_ext
        intro ⟨i⟩
        change c.inj i ≫ (b ≫ a) = c.inj i ≫ 𝟙 _
        rw [← Category.assoc, hb, Category.assoc, ha]
        simp }
  let L (i) : (K ⟶ M i) →+ (K' ⟶ E i) :=
    (Preadditive.leftComp _ eK.inv).comp
      ((Preadditive.rightComp _ (e i).some.hom).comp F.mapAddHom)
  let R : (K ⟶ ∐ M) →+ (K' ⟶ c.pt) :=
    (Preadditive.leftComp _ eK.inv).comp
      ((Preadditive.rightComp _ q.hom).comp F.mapAddHom)
  have hL (i) : Function.Bijective (L i) := by
    dsimp only [L, AddMonoidHom.coe_comp]
    exact eK.homFromEquiv.bijective.comp
      ((e i).some.homToEquiv.bijective.comp
        ((Functor.FullyFaithful.ofFullyFaithful F).map_bijective K (M i)))
  have hR : Function.Bijective R :=
    eK.homFromEquiv.bijective.comp (q.homToEquiv.bijective.comp
      ((Functor.FullyFaithful.ofFullyFaithful F).map_bijective _ _))
  have hS : Function.Bijective (DirectSum.map L) :=
    ⟨(DirectSum.map_injective L).2 (fun i ↦ (hL i).1),
      (DirectSum.map_surjective L).2 (fun i ↦ (hL i).2)⟩
  let t := DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp K' (c.inj i))
  let s := DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp K (Sigma.ι M i))
  have hs : t.comp (DirectSum.map L) = R.comp s := by
    apply DirectSum.addHom_ext
    intro i f
    simp only [AddMonoidHom.comp_apply, DirectSum.map_of]
    dsimp [t, s]
    rw [DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
    change (eK.inv ≫ F.map f ≫ (e i).some.hom) ≫ c.inj i =
      eK.inv ≫ F.map (f ≫ Sigma.ι M i) ≫ q.hom
    simp only [Functor.map_comp, Category.assoc, q, ha]
  have ht : Function.Bijective (t ∘ DirectSum.map L) := by
    change Function.Bijective (t.comp (DirectSum.map L))
    rw [hs]
    exact hR.comp (hK I M)
  exact (Function.Bijective.of_comp_iff t hS).mp ht

open Classical in
private theorem cofan_hom_injective
    {B : Type*} [Category B] [Preadditive B] (K : B) {I : Type*} (E : I → B)
    (c : Cofan E) (hc : IsColimit c) :
    Function.Injective (DirectSum.toAddMonoid
      (fun i ↦ Preadditive.rightComp K (c.inj i))) := by
  classical
  let p (i : I) : c.pt ⟶ E i := hc.desc (Cofan.mk _ (Pi.single i (𝟙 (E i))))
  have hp (i j : I) : c.inj j ≫ p i = Pi.single (M := fun j ↦ E j ⟶ E i) i (𝟙 _) j :=
    hc.fac _ ⟨j⟩
  let t := DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp K (c.inj i))
  have heval (i : I) (x : ⨁ i, K ⟶ E i) : t x ≫ p i = x i := by
    induction x using DirectSum.induction_on with
    | zero => simp [t]
    | of j f =>
      dsimp only [t]
      rw [DirectSum.toAddMonoid_of]
      change (f ≫ c.inj j) ≫ p i = _
      rw [Category.assoc, hp]
      by_cases h : j = i
      · subst j; simp
      · simp [h, Ne.symm h, DirectSum.of_eq_of_ne]
    | add x y hx hy =>
      simp only [map_add, Preadditive.add_comp, hx, hy]
      rfl
  intro x y hxy
  ext i
  rw [← heval i x, ← heval i y, hxy]

open Classical in
private theorem compact_cofan_of_small
    {B : Type*} [Category B] [Preadditive B] [LocallySmall.{u} B]
    (K : B) (P : ObjectProperty B)
    (hsmall : ∀ (J : Type u) (E : J → B), (∀ j, P (E j)) →
      ∀ (c : Cofan E), IsColimit c → Function.Bijective
        (DirectSum.toAddMonoid (fun j ↦ Preadditive.rightComp K (c.inj j))))
    {I : Type w} (E : I → B) (hE : ∀ i, P (E i)) (c : Cofan E) (hc : IsColimit c) :
    Function.Bijective (DirectSum.toAddMonoid
      (fun i ↦ Preadditive.rightComp K (c.inj i))) := by
  classical
  refine ⟨cofan_hom_injective K E c hc, ?_⟩
  let p (i : I) : c.pt ⟶ E i := hc.desc (Cofan.mk _ (Pi.single i (𝟙 (E i))))
  have hp (i j : I) : c.inj j ≫ p i = Pi.single (M := fun j ↦ E j ⟶ E i) i (𝟙 _) j :=
    hc.fac _ ⟨j⟩
  have : Small.{u} {i // ¬ IsZero (E i)} := by
    apply small_of_injective (f := fun i : {i // ¬ IsZero (E i)} ↦ p i.val ≫ c.inj i.val)
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have he := congrArg (fun f ↦ c.inj i.val ≫ f ≫ p i.val) hij
    have hi : c.inj i.val ≫ p i.val = 𝟙 (E i.val) := by simp [hp]
    have hj : c.inj i.val ≫ p j.val = 0 := by simp [hp, hne]
    have hid : 𝟙 (E i.val) = 0 := by
      simpa only [← Category.assoc, hi, hj, Category.id_comp, zero_comp] using he
    exact i.property ((IsZero.iff_id_eq_zero _).mpr hid)
  let J := {i // ¬ IsZero (E i)}
  let e : Shrink.{u} J ≃ J := (equivShrink J).symm
  let U : Shrink.{u} J → B := fun j ↦ E (e j).val
  let r : Cofan U := Cofan.mk c.pt (fun j ↦ c.inj (e j).val)
  have hr : IsColimit r := by
    let v : Cofan (fun j : J ↦ E j.val) := Cofan.mk c.pt (fun j ↦ c.inj j.val)
    have hv : IsColimit v := by
      refine Cofan.IsColimit.mk v (fun s ↦ hc.desc (Cofan.mk s.pt
        (fun i ↦ if hi : ¬ IsZero (E i) then s.inj ⟨i, hi⟩ else 0))) ?_ ?_
      · intro s j
        obtain ⟨j, hj⟩ := j
        change c.ι.app ⟨j⟩ ≫ _ = _
        rw [hc.fac]
        simp only [Cofan.mk_ι_app, dif_pos hj]
      · intro s m hm
        apply hc.hom_ext
        intro ⟨i⟩
        rw [hc.fac]
        by_cases hi : ¬ IsZero (E i)
        · simpa only [v, cofan_mk_inj, Cofan.inj, Cofan.mk_ι_app, dif_pos hi]
            using hm ⟨i, hi⟩
        · exact (not_not.mp hi).eq_of_src _ _
    change IsColimit (Cofan.mk c.pt (fun j : Shrink.{u} J ↦ v.inj (e j)))
    exact (Cofan.isColimitEquivOfEquiv e v) hv
  let L : (⨁ j, K ⟶ U j) →+ (⨁ i, K ⟶ E i) :=
    DirectSum.toAddMonoid (fun j ↦ DirectSum.of (fun i ↦ K ⟶ E i) (e j).val)
  let t := DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp K (c.inj i))
  let s := DirectSum.toAddMonoid (fun j ↦ Preadditive.rightComp K (r.inj j))
  have hs : t.comp L = s := by
    apply DirectSum.addHom_ext
    intro j f
    simp only [AddMonoidHom.comp_apply, L, DirectSum.toAddMonoid_of]
    change t ((DirectSum.of (fun i ↦ K ⟶ E i) (e j).val) f) =
      s ((DirectSum.of (fun j ↦ K ⟶ U j) j) f)
    change (DirectSum.toAddMonoid _ : _ →+ (K ⟶ c.pt)) _ =
      (DirectSum.toAddMonoid _ : _ →+ (K ⟶ r.pt)) _
    rw [DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
    rfl
  intro f
  obtain ⟨x, hx⟩ := (hsmall _ U (fun j ↦ hE (e j).val) r hr).2 f
  refine ⟨L x, ?_⟩
  change (t.comp L) x = f
  rw [hs]
  exact hx

open Classical in
private theorem cofan_property_of_small
    {B : Type*} [Category B] [Preadditive B] [LocallySmall.{u} B]
    (P : ObjectProperty B)
    (hsmall : ∀ (J : Type u) (E : J → B), (∀ j, P (E j)) →
      ∀ (c : Cofan E), IsColimit c → P c.pt)
    {I : Type w} (E : I → B) (hE : ∀ i, P (E i)) (c : Cofan E) (hc : IsColimit c) :
    P c.pt := by
  classical
  let p (i : I) : c.pt ⟶ E i := hc.desc (Cofan.mk _ (Pi.single i (𝟙 (E i))))
  have hp (i j : I) : c.inj j ≫ p i = Pi.single (M := fun j ↦ E j ⟶ E i) i (𝟙 _) j :=
    hc.fac _ ⟨j⟩
  have : Small.{u} {i // ¬ IsZero (E i)} := by
    apply small_of_injective (f := fun i : {i // ¬ IsZero (E i)} ↦ p i.val ≫ c.inj i.val)
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have he := congrArg (fun f ↦ c.inj i.val ≫ f ≫ p i.val) hij
    have hi : c.inj i.val ≫ p i.val = 𝟙 (E i.val) := by simp [hp]
    have hj : c.inj i.val ≫ p j.val = 0 := by simp [hp, hne]
    have hid : 𝟙 (E i.val) = 0 := by
      simpa only [← Category.assoc, hi, hj, Category.id_comp, zero_comp] using he
    exact i.property ((IsZero.iff_id_eq_zero _).mpr hid)
  let J := {i // ¬ IsZero (E i)}
  let e : Shrink.{u} J ≃ J := (equivShrink J).symm
  let U : Shrink.{u} J → B := fun j ↦ E (e j).val
  let r : Cofan U := Cofan.mk c.pt (fun j ↦ c.inj (e j).val)
  have hr : IsColimit r := by
    let v : Cofan (fun j : J ↦ E j.val) := Cofan.mk c.pt (fun j ↦ c.inj j.val)
    have hv : IsColimit v := by
      refine Cofan.IsColimit.mk v (fun s ↦ hc.desc (Cofan.mk s.pt
        (fun i ↦ if hi : ¬ IsZero (E i) then s.inj ⟨i, hi⟩ else 0))) ?_ ?_
      · intro s j
        obtain ⟨j, hj⟩ := j
        change c.ι.app ⟨j⟩ ≫ _ = _
        rw [hc.fac]
        simp only [Cofan.mk_ι_app, dif_pos hj]
      · intro s m hm
        apply hc.hom_ext
        intro ⟨i⟩
        rw [hc.fac]
        by_cases hi : ¬ IsZero (E i)
        · simpa only [v, cofan_mk_inj, Cofan.inj, Cofan.mk_ι_app, dif_pos hi]
            using hm ⟨i, hi⟩
        · exact (not_not.mp hi).eq_of_src _ _
    change IsColimit (Cofan.mk c.pt (fun j : Shrink.{u} J ↦ v.inj (e j)))
    exact (Cofan.isColimitEquivOfEquiv e v) hv
  exact hsmall _ U (fun j ↦ hE (e j).val) r hr

private theorem colimit_property_of_small
    {B : Type*} [Category B] [Preadditive B] [LocallySmall.{u} B]
    (P : ObjectProperty B)
    (hsmallImage : ∀ (J : Type u) (E : J → B), (∀ j, P (E j)) →
      ∀ (c : Cofan E), IsColimit c → P c.pt)
    {I : Type w} (E : Discrete I ⥤ B) [HasColimit E]
    (h : ∀ i : I, P (E.obj ⟨i⟩)) : P (colimit E) := by
  let c : Cofan (fun i : I ↦ E.obj ⟨i⟩) :=
    Cofan.mk (colimit E) (fun i ↦ colimit.ι E ⟨i⟩)
  have hc : IsColimit c := by
    refine Cofan.IsColimit.mk c (fun s ↦ colimit.desc E
      { pt := s.pt
        ι := Discrete.natTrans (fun i ↦ s.inj i.as) }) ?_ ?_
    · intro s i
      change colimit.ι E (Discrete.mk i) ≫ _ = _
      exact colimit.ι_desc (F := E) _ (Discrete.mk i)
    · intro s m hm
      change colimit E ⟶ s.pt at m
      change m = colimit.desc E
        { pt := s.pt, ι := Discrete.natTrans (fun i ↦ s.inj i.as) }
      apply colimit.hom_ext
      intro ⟨i⟩
      exact (hm i).trans (colimit.ι_desc
        { pt := s.pt, ι := Discrete.natTrans (fun i ↦ s.inj i.as) } (Discrete.mk i)).symm
  exact cofan_property_of_small P hsmallImage _ h c hc

private theorem localizing_of_small_coproducts
    {B : Type*} [Category B] [Preadditive B] [LocallySmall.{u} B]
    [HasZeroObject B] [HasShift B ℤ] [∀ n : ℤ, (shiftFunctor B n).Additive]
    [Pretriangulated B] (P : ObjectProperty B)
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (hsmall : ∀ (J : Type u) (E : J → B), (∀ j, P (E j)) →
      ∀ (c : Cofan E), IsColimit c → P c.pt) : IsLocalizingSubcategory P := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro I E hE h
  let := hE
  exact colimit_property_of_small P hsmall E h

namespace WeilConjectures

set_option linter.unusedVariables false in
open Classical in
/-- Every bounded constructible finite-Tor pro-etale complex `C` is compact in the
localizing closure `Loc(Dctf(X, A))`: for every family `E` of objects of the closure, with
its ambient coproduct `∐ E` (again in the closure), the canonical map
`⨁ᵢ Hom(C, E i) → Hom(C, ∐ E)`, `f ↦ f ≫ Sigma.ι E i` on the `i`-th summand, is bijective.

Source: blueprint main-20261015, `sk-prop-ctf-finite-compact/`
`sk-prop-ctf-finite-compact-proetale.md` and `.proof.md`
(blueprint: det-ctf-finite-compact-proetale).

Proof (the node's steps).
1. By `lem-weil-pbc-finite-discrete-condensed-ring-constant` and
   `lem-weil-pbc-finite-discrete-scheme-ring-constant`, `θ : A_const ≅ A_X`; transporting
   actions along `θ` identifies the module categories, their derived categories, coproducts,
   derived tensor products and finite constant local models, so the constructibility and
   Tor conventions agree with the constant-`A` ones of `det-ctf-finite-comparison-localizing`.
2. `X` is quasi-compact and quasi-separated (finite affine cover by finitely generated
   `k`-algebras, ascending chain condition on opens, `lem-wf-affine-noetherian-components`),
   and the finite ring `A` is Noetherian; the empty scheme and the zero ring are included.
3. By `lem-sfb-unbounded-site-comparison`, `F = ν_X^*` is exact, fully faithful and preserves
   small coproducts; by `det-pe-finite-tor-comparison-noetherian` there is
   `C₀ ∈ Dctf(X_et, A)` with `c : F C₀ ≅ C`.
4. Via `def-pe-etale-constructible-module`, `lem-weil-pbc-finite-locally-constant-module-values`,
   `lemma-constructible-immersion-independence` and `lem-weil-pbc-constructible-qcqs-affine-local`
   (Stacks 095E), `C₀` lies in the étale `Dctf` of `det-ctf-finite-compact-etale`, hence is
   compact against all ordinary unbounded étale objects.
5. By the first clause of `det-ctf-finite-comparison-localizing`, choose étale `M_i` with
   `a_i : F M_i ≅ E i`; coproduct preservation gives `a : F (∐ M_i) ≅ ∐ E` with
   `a ∘ F ι_i = ι_i ∘ a_i`.
6. `u ↦ a_i F(u) c⁻¹` and `v ↦ a F(v) c⁻¹` are bijections on Hom groups which carry the étale
   compactness map to the displayed map (`a F(ι_i u) c⁻¹ = ι_i a_i F(u) c⁻¹`, then additivity);
   so the displayed map is bijective.  The empty family, `C = 0`, `A = 0` and `X = ∅` give
   zero groups. -/
theorem finiteCompactProEtale
    (D : FiniteFieldDatum.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    (A : Type) [CommRing A] (hA : Finite A)
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (r : ℕ) (hr : ∀ a : A, (ℓ ^ r) • a = 0) :
    ∀ (C : DerivedCategory
        (AlgebraicGeometry.ProEtale.pulledBackModuleObjects
          (Profinite.continuousMapRingObj A) X)),
      (AlgebraicGeometry.ProEtale.constantModelBoundedConstructible
          (Profinite.continuousMapRingObj A) X ⊓
        fun K ↦ DerivedCategory.finiteTorAmplitude _ K) C →
      ∀ (I : Type w)
        (E : I → DerivedCategory
          (AlgebraicGeometry.ProEtale.pulledBackModuleObjects
            (Profinite.continuousMapRingObj A) X)) [hE : HasCoproduct E],
        (∀ i, AlgebraicGeometry.ProEtale.localizingClosureProEtale
          (Profinite.continuousMapRingObj A) X (E i)) →
        AlgebraicGeometry.ProEtale.localizingClosureProEtale
          (Profinite.continuousMapRingObj A) X (∐ E) →
        Function.Bijective
          (DirectSum.toAddMonoid
            (fun i : I => Preadditive.rightComp C (Sigma.ι E i)) :
            (⨁ i : I, (C ⟶ E i)) →+ (C ⟶ ∐ E)) := by
  classical
  let := hA
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  have hcard : Fintype.card D.k₀ = D.p ^ D.a := by
    simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow hcard
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have hunit : IsUnit (ℓ : D.k) :=
    isUnit_iff_ne_zero.mpr (CharP.cast_ne_zero_of_ne_of_prime D.k (Fact.out) hℓ.symm)
  have hnil : ∃ n : ℕ, (ℓ : ULift.{u + 1} A) ^ n = 0 := by
    refine ⟨r, (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).injective ?_⟩
    simpa only [map_pow, map_natCast, map_zero, nsmul_eq_mul, Nat.cast_pow, mul_one]
      using hr (1 : A)
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of D.k))
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of D.k))
  let : IsNoetherian X := {}
  obtain ⟨eR, heR⟩ := Profinite.finiteDiscreteCondensedRing_constant.{u} A
  let := heR
  let L := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).mapDerivedCategory
  let R := (ProEtale.finiteComparisonRealization A X eR).mapDerivedCategory
  let F := L ⋙ R
  let : (ProEtale.finiteComparisonRealization A X eR).IsEquivalence :=
    (ProEtale.finiteComparisonRealization_exact A X eR).1
  let : R.Full := inferInstance
  let : R.Faithful := inferInstance
  let : R.Additive := inferInstance
  let : R.CommShift ℤ := inferInstance
  let : R.IsTriangulated := inferInstance
  let V := (ProEtale.finiteCoefficientRealization X (ULift.{u + 1} A)).mapDerivedCategory
  obtain ⟨_, ⟨hff⟩, hsum⟩ := ProEtale.unboundedSiteComparison.{u, u + 1}
    D.k (Or.inr inferInstance) (by simpa using hunit) (ULift.{u + 1} A) hnil X
  let e := Functor.mapDerivedCategoryCompIso
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X)
    (ProEtale.finiteCoefficientRealization X (ULift.{u + 1} A))
  change ((ProEtale.comparisonUpperStar _ X ⋙
    ProEtale.finiteCoefficientRealization X (ULift.{u + 1} A)).mapDerivedCategory).FullyFaithful
      at hff
  let ffL : L.FullyFaithful := Functor.FullyFaithful.ofCompFaithful (hff.ofIso e)
  let : L.Full := ffL.full
  let : L.Faithful := ffL.faithful
  let (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I) L := by
    let h := (hsum I).some
    change PreservesColimitsOfShape (Discrete I)
      ((ProEtale.comparisonUpperStar _ X ⋙
        ProEtale.finiteCoefficientRealization X (ULift.{u + 1} A)).mapDerivedCategory) at h
    let : PreservesColimitsOfShape (Discrete I) (L ⋙ V) :=
      preservesColimitsOfShape_of_natIso e
    exact preservesColimitsOfShape_of_reflects_of_preserves L V
  obtain ⟨hcop, hcompact⟩ := Etale.finiteTorConstructible_etale_compact
    D ℓ Fact.out hℓ X (ULift.{u + 1} A) hnil
  let := hcop
  let : F.Full := inferInstance
  let : F.Faithful := inferInstance
  let : F.Additive := inferInstance
  let : F.CommShift ℤ := inferInstance
  let : F.IsTriangulated := inferInstance
  let (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I) F := inferInstance
  have horigin : ∀ K, (ProEtale.constantModelBoundedConstructible
      (Profinite.continuousMapRingObj A) X ⊓
      fun M ↦ DerivedCategory.finiteTorAmplitude _ M) K → F.essImage K := by
    intro K hK
    obtain ⟨M, _, _, eM⟩ := ProEtale.finiteDiscreteCtfOrigin X A eR K hK
    exact ⟨M, eM⟩
  have hloc : IsLocalizingSubcategory F.essImage :=
    localizing_of_small_coproducts F.essImage (fun J E hE c hc ↦
      F.essImage.prop_of_isColimit hc (fun i ↦ hE i.as))
  have himage : ∀ K, ProEtale.localizingClosureProEtale
      (Profinite.continuousMapRingObj A) X K → F.essImage K := by
    intro K hK
    exact hK F.essImage hloc horigin
  intro C hC I E _hE hfamily _
  obtain ⟨M, hM, hTor, ⟨eM⟩⟩ := ProEtale.finiteDiscreteCtfOrigin X A eR C hC
  apply compact_cofan_of_small C
    (ProEtale.localizingClosureProEtale (Profinite.continuousMapRingObj A) X)
    (fun J T hT c hc ↦ compact_map_cofan F M (hcompact M hM hTor) C eM
      T (fun j ↦ himage _ (hT j)) c hc) E hfamily (Cofan.mk (∐ E) (Sigma.ι E))
    (coproductIsCoproduct E)

end WeilConjectures
