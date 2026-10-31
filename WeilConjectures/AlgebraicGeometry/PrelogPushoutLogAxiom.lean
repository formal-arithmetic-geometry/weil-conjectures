/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FineSaturatedLogBlowup
import WeilConjectures.AlgebraicGeometry.EtaleLogOfSectionUnits
import WeilConjectures.AlgebraicGeometry.PrelogUnitPushoutPresentation
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.Algebra.Category.MonCat.ForgetCorepresentable
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.MonCat.FilteredColimits

/-!
# The unit pushout of a prelog presheaf

Source: ILO, Exposé VI 1.1, printed p. 69 (PDF p. 75), with its reference to
Kato (1988), §1; the associated-log calculation isolated in the DAG
(blueprint: lem-trf-prelog-pushout-log-axiom).

The kernel and surjectivity of the pair map specify the existing quotient by
`divisorialChartCongruence`, including its canonical quotient map. Its restriction
formula specifies the presheaf. Sheafification is expressed by its universal
property, so the conclusion applies to every choice of sheafification and its unit.

Coefficients lie in the universe `u` of the scheme, the universe of the log
structures `EtaleLogStructure` of def-trf-fs-log-blowup. The small étale site is
essentially `u`-small, so monoid sheafification exists there (Mathlib's
`HasSheafify X.smallEtaleTopology` instance through affine étale objects). The log
condition is stated both as membership in `EtaleLogStructure` and on sections: the
specified natural map from ring units is exactly the inverse of the structural map
on its unit inverse image.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

private noncomputable instance monoid_filtered_colimits (J : Type u)
    [SmallCategory J] [IsFiltered J] : HasColimitsOfShape J CommMonCat.{u} :=
  ⟨fun D ↦ ⟨⟨_, CommMonCat.FilteredColimits.colimitCoconeIsColimit D⟩⟩⟩

private noncomputable instance monoid_sheafify (X : Scheme.{u}) :
    HasSheafify X.smallEtaleTopology CommMonCat.{u} := by
  let : HasSheafify (Scheme.AffineEtale.topology X) CommMonCat.{u} :=
    hasSheafifyEssentiallySmallSite _ _
  exact Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
    (Scheme.AffineEtale.topology X) X.smallEtaleTopology (Scheme.AffineEtale.Spec X)

private noncomputable instance monoid_locally_bijective (X : Scheme.{u}) :
    X.smallEtaleTopology.WEqualsLocallyBijective CommMonCat.{u} := by
  let : (Scheme.AffineEtale.topology X).WEqualsLocallyBijective CommMonCat.{u} :=
    .ofEssentiallySmall _
  exact .transport _ _ _
    (Functor.IsDenseSubsite.coverPreserving (Scheme.AffineEtale.topology X) _
      (Scheme.AffineEtale.Spec X))

private theorem pushout_descends {A P : Type u} {H : Type w} [CommRing A] [CommMonoid P]
    [CommMonoid H] (γ : P →* A) (f : P →* H) (g : Aˣ →* H)
    (h : ∀ (e : P) (b : Aˣ), γ e = b.val → f e = g b) :
    divisorialChartCongruence γ.mrangeRestrict ≤ Con.ker (f.coprod g) := by
  apply Con.conGen_le.mpr
  rintro x y ⟨e, b, he, rfl, rfl⟩
  change f e * g 1 = f 1 * g b
  simpa using h e b he

private def pushout_structure {A P : Type u} [CommRing A] [CommMonoid P]
    (γ : P →* A) : (divisorialChartCongruence γ.mrangeRestrict).Quotient →* A :=
  (divisorialChartCongruence γ.mrangeRestrict).lift
    (γ.coprod (Units.coeHom A)) (pushout_descends γ γ (Units.coeHom A) (by
      intro e b he
      exact he))

private theorem pushout_universal {A P : Type u} {H : Type w} [CommRing A] [CommMonoid P]
    [CommMonoid H] (γ : P →* A) (f : P →* H) (g : Aˣ →* H)
    (h : ∀ (e : P) (b : Aˣ), γ e = b.val → f e = g b) :
    ∃! k : (divisorialChartCongruence γ.mrangeRestrict).Quotient →* H,
      ∀ (m : P) (b : Aˣ),
        k ((divisorialChartCongruence γ.mrangeRestrict).mk' (m, b)) = f m * g b := by
  refine ⟨(divisorialChartCongruence γ.mrangeRestrict).lift
    (f.coprod g) (pushout_descends γ f g h), fun _ _ ↦ rfl, ?_⟩
  intro k hk
  apply Con.hom_ext
  ext x
  exact hk x.1 x.2

private def pushout_alpha {X : Scheme.{u}} {M : X.Etaleᵒᵖ ⥤ CommMonCat.{u}}
    (γ : M ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat) :
    prelogPresentation γ ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat where
  app V := CommMonCat.ofHom (pushout_structure (A := X.etaleStructurePresheaf.obj V) (γ.app V).hom)
  naturality V W h := by
    ext x
    obtain ⟨⟨m, b⟩, rfl⟩ := (prelogPresentationCon γ V.unop).mk'_surjective x
    dsimp only [Scheme.etaleStructurePresheaf] at *
    change @id Γ(W.unop.left, ⊤) (γ.app W (M.map h m)) *
        (Units.map h.unop.left.appTop.hom.toMonoidHom b).val =
      h.unop.left.appTop (@id Γ(V.unop.left, ⊤) (γ.app V m) * b.val)
    rw [map_mul]
    congr 1
    exact γ.naturality_apply h m

private theorem unit_locally_surjective {X : Scheme.{u}}
    (P : X.Etaleᵒᵖ ⥤ CommMonCat.{u}) (L : Sheaf X.smallEtaleTopology CommMonCat.{u})
    (η : P ⟶ L.obj)
    (hη : ∀ H : Sheaf X.smallEtaleTopology CommMonCat.{u},
      Function.Bijective (fun f : L ⟶ H ↦ η ≫ f.hom)) :
    Presheaf.IsLocallySurjective X.smallEtaleTopology η := by
  let K := (presheafToSheaf X.smallEtaleTopology CommMonCat.{u}).obj P
  let ε := toSheafify X.smallEtaleTopology P
  let h := sheafifyLift X.smallEtaleTopology η L.property
  have hh : ε ≫ h = η := toSheafify_sheafifyLift _ _ _
  obtain ⟨k, hk⟩ := (hη K).surjective ε
  change η ≫ k.hom = ε at hk
  have hkh : k.hom ≫ h = 𝟙 L.obj := by
    have e : k ≫ (⟨h⟩ : K ⟶ L) = 𝟙 L := by
      apply (hη L).injective
      change η ≫ (k.hom ≫ h) = η ≫ 𝟙 _
      rw [← Category.assoc, hk, hh, Category.comp_id]
    exact congrArg (fun f ↦ f.hom) e
  have hhk : h ≫ k.hom = 𝟙 K.obj := by
    apply sheafify_hom_ext X.smallEtaleTopology _ _ K.property
    rw [← Category.assoc, hh, hk, Category.comp_id]
  let : IsIso h := ⟨k.hom, hhk, hkh⟩
  rw [← hh]
  infer_instance

private theorem pushout_normalize {A P : Type u} [CommRing A] [CommMonoid P]
    (γ : P →* A) (m : P) (b c : Aˣ) (h : γ m * b.val = c.val) :
    (divisorialChartCongruence γ.mrangeRestrict).mk' (m, b) =
      (divisorialChartCongruence γ.mrangeRestrict).mk' (1, c) := by
  let e := c * b⁻¹
  have he : γ m = e.val := by
    dsimp [e]
    simp only [← h, mul_assoc, Units.mul_inv, mul_one]
  have hr : (divisorialChartCongruence γ.mrangeRestrict).mk' (m, 1) =
      (divisorialChartCongruence γ.mrangeRestrict).mk' (1, e) := by
    apply (divisorialChartCongruence γ.mrangeRestrict).eq.mpr
    exact ConGen.Rel.of _ _ ⟨m, e, he, rfl, rfl⟩
  have := congrArg (fun z ↦ z *
    (divisorialChartCongruence γ.mrangeRestrict).mk' (1, b)) hr
  simpa only [← map_mul, Prod.mk_mul_mk, one_mul, mul_one, e,
    inv_mul_cancel_right] using this

/-- The sectionwise unit pushout is a presheaf, has the pushout universal property,
and its monoid sheafification is a log structure, with the stated canonical maps.
Source: ILO VI 1.1, printed p. 69, referring to Kato (1988), §1; agent-isolated
associated-log calculation (blueprint: lem-trf-prelog-pushout-log-axiom).

Proof:
1. Use the existing generated congruence to quotient `M(V) × B_Vˣ`. A compatible
   product homomorphism kills its generators and descends uniquely; every class is
   the product of the two canonical inclusions.
2. Ring restriction preserves units and naturality of `γ` sends each generator to
   a generator. Thus restrictions descend and satisfy identity and composition on
   representatives. The formula `γ(m)u` also descends and is natural.
3. Construct the filtered-colimit instance for commutative monoids and apply
   Mathlib's sheafification on the essentially small affine étale site. Transport
   this adjunction to the small étale site. The structure presheaf is already a
   sheaf by Mathlib's subcanonical étale-site theorem, so the structural map
   extends uniquely to `α`.
4. Define `i(m) = η([m,1])` and `j(u) = η([1,u])`. Their naturality and the structural
   and factorization identities follow on representatives from multiplicativity.
5. Compare any universal sheafification unit with Mathlib's unit. The comparison
   is an isomorphism, so Mathlib's local-surjectivity theorem gives local
   representatives `η([m,u])`. If the structural image is the unit `a`, then
   `γ(m)u = a` implies
   that `γ(m)` is a unit. The generating relation gives `[m,u] = [1,a]`.
   Separatedness glues this equality to `s = j(a)`. Conversely `α(j(u)) = u`, which
   also gives uniqueness. This is the log unit condition of def-trf-fs-log-blowup:
   by lem-trf-etale-log-of-section-units, pass to the filtered colimits defining
   geometric stalks. A stalk element with
   unit image is the germ of a section with unit image on a smaller neighbourhood,
   hence of some `j(a)`, so `(L, α)` is an `EtaleLogStructure`.
   The argument uses no sheaf condition, integrality or finiteness assumption on `M`.
-/
theorem prelog_pushout_log_axiom (X : Scheme.{u}) [IsLocallyNoetherian X]
    (M : X.Etaleᵒᵖ ⥤ CommMonCat.{u})
    (γ : M ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat) :
    ∃ (P : X.Etaleᵒᵖ ⥤ CommMonCat.{u})
      (q : ∀ V : X.Etaleᵒᵖ, M.obj V × (X.etaleStructurePresheaf.obj V)ˣ →* P.obj V)
      (a : P ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat),
      (∀ V : X.Etaleᵒᵖ, Function.Surjective (q V) ∧
        Con.ker (q V) = divisorialChartCongruence (A := X.etaleStructurePresheaf.obj V)
          (γ.app V).hom.mrangeRestrict) ∧
      (∀ (V W : X.Etaleᵒᵖ) (h : V ⟶ W) (m : M.obj V)
        (b : (X.etaleStructurePresheaf.obj V)ˣ),
        P.map h (q V (m, b)) =
          q W (M.map h m, Units.map (X.etaleStructurePresheaf.map h).hom b)) ∧
      (∀ (V : X.Etaleᵒᵖ) (H : Type w) [CommMonoid H]
        (f : M.obj V →* H) (g : (X.etaleStructurePresheaf.obj V)ˣ →* H),
        (∀ (e : M.obj V) (b : (X.etaleStructurePresheaf.obj V)ˣ),
          γ.app V e = b.val → f e = g b) →
        ∃! k : P.obj V →* H, ∀ (m : M.obj V) (b : (X.etaleStructurePresheaf.obj V)ˣ),
          k (q V (m, b)) = f m * g b) ∧
      (∀ (V : X.Etaleᵒᵖ) (m : M.obj V) (b : (X.etaleStructurePresheaf.obj V)ˣ),
        a.app V (q V (m, b)) = @id (X.etaleStructurePresheaf.obj V) (γ.app V m) * b.val) ∧
      (∃ (L : Sheaf X.smallEtaleTopology CommMonCat.{u}) (η : P ⟶ L.obj),
        ∀ H : Sheaf X.smallEtaleTopology CommMonCat.{u},
          Function.Bijective (fun f : L ⟶ H ↦ η ≫ f.hom)) ∧
      (∀ (L : Sheaf X.smallEtaleTopology CommMonCat.{u}) (η : P ⟶ L.obj),
        (∀ H : Sheaf X.smallEtaleTopology CommMonCat.{u},
          Function.Bijective (fun f : L ⟶ H ↦ η ≫ f.hom)) →
        ∃ (α : L.obj ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat)
          (i : M ⟶ L.obj)
          (j : ∀ V : X.Etaleᵒᵖ, (X.etaleStructurePresheaf.obj V)ˣ →* L.obj.obj V),
          η ≫ α = a ∧
          (∃ Λ : EtaleLogStructure X,
            Λ.toEtalePrelogStructure = { monoidSheaf := L, alpha := α }) ∧
          i ≫ α = γ ∧
          (∀ (V : X.Etaleᵒᵖ) (m : M.obj V), i.app V m = η.app V (q V (m, 1))) ∧
          (∀ (V : X.Etaleᵒᵖ) (b : (X.etaleStructurePresheaf.obj V)ˣ),
            j V b = η.app V (q V (1, b))) ∧
          (∀ (V W : X.Etaleᵒᵖ) (h : V ⟶ W) (b : (X.etaleStructurePresheaf.obj V)ˣ),
            L.obj.map h (j V b) = j W (Units.map (X.etaleStructurePresheaf.map h).hom b)) ∧
          (∀ (V : X.Etaleᵒᵖ) (b : (X.etaleStructurePresheaf.obj V)ˣ),
            α.app V (j V b) = b.val) ∧
          (∀ (V : X.Etaleᵒᵖ) (s : L.obj.obj V), IsUnit (α.app V s) →
            ∃! b : (X.etaleStructurePresheaf.obj V)ˣ, j V b = s) ∧
          (∀ (V : X.Etaleᵒᵖ) (m : M.obj V) (b : (X.etaleStructurePresheaf.obj V)ˣ),
            η.app V (q V (m, b)) = i.app V m * j V b)) := by
  classical
  let P := prelogPresentation γ
  let q : ∀ V : X.Etaleᵒᵖ,
      M.obj V × (X.etaleStructurePresheaf.obj V)ˣ →* P.obj V :=
    fun V ↦ prelogPresentationPair γ V.unop
  let a := pushout_alpha γ
  have hq (V : X.Etaleᵒᵖ) : Function.Surjective (q V) ∧
      Con.ker (q V) = divisorialChartCongruence (A := X.etaleStructurePresheaf.obj V)
        (γ.app V).hom.mrangeRestrict :=
    ⟨Con.mk'_surjective, Con.mk'_ker _⟩
  have hres (V W : X.Etaleᵒᵖ) (h : V ⟶ W) (m : M.obj V)
      (b : (X.etaleStructurePresheaf.obj V)ˣ) :
      P.map h (q V (m, b)) =
        q W (M.map h m, Units.map (X.etaleStructurePresheaf.map h).hom.toMonoidHom b) := rfl
  have ha (V : X.Etaleᵒᵖ) (m : M.obj V) (b : (X.etaleStructurePresheaf.obj V)ˣ) :
      a.app V (q V (m, b)) = @id (X.etaleStructurePresheaf.obj V) (γ.app V m) * b.val := rfl
  refine ⟨P, q, a, hq, hres, ?_, ha, ?_, ?_⟩
  · intro V H _ f g h
    exact pushout_universal (A := X.etaleStructurePresheaf.obj V) (γ.app V).hom f g h
  · refine ⟨(presheafToSheaf X.smallEtaleTopology CommMonCat.{u}).obj P,
      toSheafify X.smallEtaleTopology P, ?_⟩
    intro H
    exact (sheafificationAdjunction X.smallEtaleTopology CommMonCat.{u}).homEquiv P H |>.bijective
  · intro L η hη
    have hO : Presheaf.IsSheaf X.smallEtaleTopology
        (X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat) :=
      Presheaf.isSheaf_comp_of_isSheaf _ _ _ X.isSheaf_etaleStructurePresheaf
    obtain ⟨f, hf⟩ := (hη ⟨_, hO⟩).surjective a
    let α := f.hom
    have hα : η ≫ α = a := hf
    let i := prelogPresentationIota γ L η
    let j : ∀ V : X.Etaleᵒᵖ, (X.etaleStructurePresheaf.obj V)ˣ →* L.obj.obj V :=
      fun V ↦ prelogPresentationUnits γ L η V.unop
    have hi (V : X.Etaleᵒᵖ) (m : M.obj V) :
        i.app V m = η.app V (q V (m, 1)) := rfl
    have hj (V : X.Etaleᵒᵖ) (b : (X.etaleStructurePresheaf.obj V)ˣ) :
        j V b = η.app V (q V (1, b)) := rfl
    have hjnat (V W : X.Etaleᵒᵖ) (h : V ⟶ W)
        (b : (X.etaleStructurePresheaf.obj V)ˣ) :
        L.obj.map h (j V b) =
          j W (Units.map (X.etaleStructurePresheaf.map h).hom.toMonoidHom b) := by
      rw [hj, ← η.naturality_apply, hres, map_one, hj]
    have hαpair (V : X.Etaleᵒᵖ) (m : M.obj V)
        (b : (X.etaleStructurePresheaf.obj V)ˣ) :
        α.app V (η.app V (q V (m, b))) =
          @id (X.etaleStructurePresheaf.obj V) (γ.app V m) * b.val := by
      exact (congrArg (fun t ↦ t.app V (q V (m, b))) hα).trans (ha V m b)
    dsimp only [id] at hαpair
    have hαj (V : X.Etaleᵒᵖ) (b : (X.etaleStructurePresheaf.obj V)ˣ) :
        α.app V (j V b) = b.val := by
      rw [hj, hαpair, map_one, one_mul]
    have hunit (V : X.Etaleᵒᵖ) (s : L.obj.obj V) (hs : IsUnit (α.app V s)) :
        ∃! b : (X.etaleStructurePresheaf.obj V)ˣ, j V b = s := by
      let b := hs.unit
      have hb : b.val = α.app V s := hs.unit_spec
      have := unit_locally_surjective P L η hη
      have hset : Presieve.IsSheaf X.smallEtaleTopology
          (L.obj ⋙ forget CommMonCat.{u}) :=
        Presieve.isSheaf_iso _ (Functor.isoWhiskerLeft L.obj CommMonCat.coyonedaObjIsoForget)
          (L.property _)
      refine ⟨b, ?_, ?_⟩
      · apply (hset _ (Presheaf.imageSieve_mem X.smallEtaleTopology η s)).isSeparatedFor.ext
        intro W h hh
        obtain ⟨z, hz⟩ := hh
        obtain ⟨⟨m, d⟩, rfl⟩ := (hq (op W)).1 z
        change L.obj.map h.op (j V b) = L.obj.map h.op s
        rw [hjnat, ← hz, hj]
        congr 1
        symm
        apply pushout_normalize (A := X.etaleStructurePresheaf.obj (op W))
          (P := M.obj (op W)) (γ.app (op W)).hom
        calc
          _ = α.app (op W) (η.app (op W) (q (op W) (m, d))) :=
            (hαpair (op W) m d).symm
          _ = _ := by
            rw [hz, α.naturality_apply, ← hb]
            rfl
      · intro c hc
        apply Units.ext
        rw [← hαj V c, hc, hb]
    refine ⟨α, i, j, hα, ?_, ?_, hi, hj, hjnat, hαj, hunit, ?_⟩
    · apply etale_log_of_section_units (M := { monoidSheaf := L, alpha := α })
      · intro V s hs
        obtain ⟨b, hb, _⟩ := hunit V s hs
        rw [← hb]
        exact ((j V).toHomUnits b).isUnit
      · intro V
        have hinv (s : L.obj.obj V) (b : (X.etaleStructurePresheaf.obj V)ˣ)
            (hs : α.app V s = b.val) : j V b = s := by
          obtain ⟨c, hc, _⟩ := hunit V s (hs.symm ▸ b.isUnit)
          have hcb : c = b := Units.ext ((hαj V c).symm.trans
            ((congrArg (fun z ↦ α.app V z) hc).trans hs))
          exact hcb ▸ hc
        apply Function.bijective_iff_has_inverse.mpr
        refine ⟨(j V).toHomUnits, ?_, ?_⟩
        · intro e
          apply Units.ext
          exact hinv e.val (Units.map (α.app V).hom e) rfl
        · intro b
          apply Units.ext
          exact hαj V b
    · ext V m
      change α.app V (i.app V m) = γ.app V m
      simp only [hi, hαpair, Units.val_one, mul_one]
    · intro V m b
      rw [hi, hj, ← map_mul, ← map_mul]
      simp only [Prod.mk_mul_mk, mul_one, one_mul]

end

end AlgebraicGeometry
