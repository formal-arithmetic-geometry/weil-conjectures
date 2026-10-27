module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.TensorIso
public import WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import WeilConjectures.AlgebraicGeometry.Modules.AffineHom
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import WeilConjectures.AlgebraicGeometry.ProjTwistFractionDescent
import WeilConjectures.AlgebraicGeometry.ProjBasicOpenLocalizationDetection

/-! # Canonical tensor comparisons for shifted graded-module sheaves

Source: Stacks Project, constructions.tex, Tags 01MS and 01MT, and equations
multiply and multiply-more-generally (blueprint: lem-sfb-standard-proj-twist-tensor).

The chart interface is that of `gradedModuleSheaf_exists`, applied to every shift.
It specifies representatives of the associated sheaves, without choosing new sheaves.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace LocalizedModule HomogeneousLocalization
open MonoidalCategory AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

variable {S M : Type u} [CommRing S] [AddCommGroup M] [Module S M]
variable (𝒜 : ℕ → AddSubgroup S) [GradedRing 𝒜]

-- Use the scheme tensor instance without changing the imported instance registrations.
attribute [local instance 2000]
  AlgebraicGeometry.Scheme.Modules.instMonoidalCategory_weilConjectures
attribute [local instance 2000] SheafOfModules.isMonoidal_W

/-- The chart equations of the existing associated-sheaf interface, for all shifts
`M(n)_k = M_(n+k)`. This predicate packages chart injectivity, the fraction range,
scalar compatibility and the canonical localization restrictions; it constructs no sheaf.
Source: Stacks 01M7 and 01MN (blueprint: lem-sfb-standard-proj-twist-tensor). -/
def IsStandardProjShiftSheaf (𝓜 : ℤ → AddSubgroup M) (F : ℤ → (Proj 𝒜).Modules)
    (chart : ∀ (n : ℤ) (f : S) (d : ℕ), 0 < d → f ∈ 𝒜 d →
      Γ(F n, basicOpen 𝒜 f) →+ LocalizedModule.Away f M) : Prop :=
  (∀ (n : ℤ) (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d),
    Function.Injective (chart n f d hd hf) ∧
    Set.range (chart n f d hd hf) = degreeZeroFractions
      (fun k : ℕ ↦ (𝒜 k : Set S)) (fun k : ℕ ↦ (𝓜 (n + k) : Set M))
      (Submonoid.powers f)) ∧
  (∀ (n : ℤ) (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d)
    (r : HomogeneousLocalization.Away 𝒜 f) (s : Γ(F n, basicOpen 𝒜 f)),
    chart n f d hd hf (awayToSection 𝒜 f r • s) =
      algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f) r •
        chart n f d hd hf s) ∧
  (∀ (n : ℤ) (f g : S) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
    (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 b) (inc : basicOpen 𝒜 g ≤ basicOpen 𝒜 f)
    (e k : ℕ) (a : S), 0 < e → a ∈ 𝒜 k → g ^ e = a * f →
    ∀ (r : ℕ) (y : M) (s : Γ(F n, basicOpen 𝒜 f)),
    chart n f d hd hf s = mk y (⟨f ^ r, ⟨r, rfl⟩⟩ : Submonoid.powers f) →
    chart n g b hb hg ((F n).presheaf.map (homOfLE inc).op s) =
      mk (a ^ r • y) (⟨g ^ (e * r), ⟨e * r, rfl⟩⟩ : Submonoid.powers g))

/-- The fraction characterization of the canonical tensor multiplication. The
second input is an actual section of the existing twist, specified pointwise as
`v/f^s`; the first and output use the associated-sheaf chart maps.
Source: Stacks, equation-multiply-more-generally and 01MS.
(blueprint: lem-sfb-standard-proj-twist-tensor) -/
def IsStandardProjTensorMultiplication (F : ℤ → (Proj 𝒜).Modules)
    (chart : ∀ (n : ℤ) (f : S) (d : ℕ), 0 < d → f ∈ 𝒜 d →
      Γ(F n, basicOpen 𝒜 f) →+ LocalizedModule.Away f M)
    (mult : ∀ a b : ℤ, F a ⊗ twist 𝒜 b ⟶ F (a + b)) : Prop :=
  ∀ (a b : ℤ) (f : S) (hf : f ∈ 𝒜 1) (r s : ℕ) (y : M) (v : S)
    (x : Γ(F a, basicOpen 𝒜 f)) (t : Γ(twist 𝒜 b, basicOpen 𝒜 f)),
    chart a f 1 (by decide) hf x = mk y (⟨f ^ r, ⟨r, rfl⟩⟩ : Submonoid.powers f) →
    (∀ p : basicOpen 𝒜 f,
      ((t.1 p : Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal)) =
        Localization.mk v ⟨f ^ s, pow_mem_primeCompl p s⟩) →
    chart (a + b) f 1 (by decide) hf
      ((mult a b).app (basicOpen 𝒜 f) (tmulSection x t)) =
        mk (v • y) (⟨f ^ (r + s), ⟨r + s, rfl⟩⟩ : Submonoid.powers f)

/-- A map of the associated-sheaf representatives is induced by a graded module
map exactly when it sends every homogeneous fraction to the image fraction.
Source: Stacks 01M7, functoriality (blueprint: lem-sfb-standard-proj-twist-tensor). -/
def IsStandardProjGradedMap {N : Type u} [AddCommGroup N] [Module S N]
    (F G : ℤ → (Proj 𝒜).Modules)
    (chartF : ∀ (n : ℤ) (f : S) (d : ℕ), 0 < d → f ∈ 𝒜 d →
      Γ(F n, basicOpen 𝒜 f) →+ LocalizedModule.Away f M)
    (chartG : ∀ (n : ℤ) (f : S) (d : ℕ), 0 < d → f ∈ 𝒜 d →
      Γ(G n, basicOpen 𝒜 f) →+ LocalizedModule.Away f N)
    (phi : M →ₗ[S] N) (chi : ∀ n : ℤ, F n ⟶ G n) : Prop :=
  ∀ (n : ℤ) (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d) (r : ℕ)
    (y : M) (x : Γ(F n, basicOpen 𝒜 f)),
    chartF n f d hd hf x = mk y (⟨f ^ r, ⟨r, rfl⟩⟩ : Submonoid.powers f) →
    chartG n f d hd hf ((chi n).app (basicOpen 𝒜 f) x) =
      mk (phi y) (⟨f ^ r, ⟨r, rfl⟩⟩ : Submonoid.powers f)

private theorem internal_shift (𝓜 : ℤ → AddSubgroup M)
    (h𝓜 : DirectSum.IsInternal 𝓜) (a : ℤ) :
    DirectSum.IsInternal (fun n ↦ 𝓜 (a + n)) := by
  classical
  let e := (Equiv.addLeft a).symm
  let E := DirectSum.equivCongrLeft (β := fun n ↦ 𝓜 n) e
  have h : (DirectSum.coeAddMonoidHom (fun n ↦ 𝓜 (a + n))).comp
      E.toAddMonoidHom = DirectSum.coeAddMonoidHom 𝓜 := by
    apply DirectSum.addHom_ext
    intro i x
    obtain ⟨k, rfl⟩ := e.symm.surjective i
    have he := DirectSum.equivCongrLeft_of (β := fun j ↦ ↥(𝓜 j)) e k x
    change (DirectSum.coeAddMonoidHom (fun j ↦ 𝓜 (a + j)))
      (E (DirectSum.of (fun j ↦ ↥(𝓜 j)) (e.symm k) x)) = _
    rw [he]
    change (DirectSum.coeAddMonoidHom (fun j ↦ 𝓜 (e.symm j)))
      (DirectSum.of (fun j ↦ ↥(𝓜 (e.symm j))) k x) = _
    rw [DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]
  exact (Function.Bijective.of_comp_iff _ E.bijective).mp
    (show Function.Bijective ((DirectSum.coeAddMonoidHom (fun n ↦ 𝓜 (a + n))).comp
      E.toAddMonoidHom) from h.symm ▸ h𝓜)

private theorem shift_quasicoherent
    (𝓜 : ℤ → AddSubgroup M) (h𝓜 : DirectSum.IsInternal 𝓜)
    (hsmul : ∀ (k : ℕ) (n : ℤ) (s : S) (y : M),
      s ∈ 𝒜 k → y ∈ 𝓜 n → s • y ∈ 𝓜 (k + n))
    (F : ℤ → (Proj 𝒜).Modules)
    (chart : ∀ (n : ℤ) (f : S) (d : ℕ), 0 < d → f ∈ 𝒜 d →
      Γ(F n, basicOpen 𝒜 f) →+ LocalizedModule.Away f M)
    (hF : IsStandardProjShiftSheaf 𝒜 𝓜 F chart) (n : ℤ) :
    (F n).IsQuasicoherent := by
  classical
  have hshift (k : ℕ) (z : ℤ) (s : S) (y : M)
      (hs : s ∈ 𝒜 k) (hy : y ∈ 𝓜 (n + z)) :
      s • y ∈ 𝓜 (n + (k + z)) := by
    simpa only [add_left_comm (k : ℤ) n z] using hsmul k (n + z) s y hs hy
  obtain ⟨Z, hZ, rhoS, rho, hlaws, _, _, _, F0, alpha, hscalar,
    hres, _, hunique, hqc, _⟩ :=
    gradedModuleSheaf_exists 𝒜 (fun z ↦ 𝓜 (n + z)) (internal_shift 𝓜 h𝓜 n) hshift
  let betaMap (f : {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}) :
      Γ(F n, basicOpen 𝒜 f.val.1) →+ Z f :=
    { toFun := fun s ↦ ⟨chart n f.val.1 f.val.2 f.property.1 f.property.2 s, by
        change _ ∈ (Z f : Set (LocalizedModule.Away f.val.1 M))
        rw [hZ f, ← (hF.1 n f.val.1 f.val.2 f.property.1 f.property.2).2]
        exact ⟨s, rfl⟩⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y ↦ Subtype.ext (map_add _ x y) }
  have hbeta (f) : Function.Bijective (betaMap f) := by
    constructor
    · intro s t h
      exact (hF.1 n f.val.1 f.val.2 f.property.1 f.property.2).1
        (congrArg Subtype.val h)
    · intro z
      have hz := z.property
      change _ ∈ (Z f : Set (LocalizedModule.Away f.val.1 M)) at hz
      rw [hZ f, ← (hF.1 n f.val.1 f.val.2 f.property.1 f.property.2).2] at hz
      obtain ⟨s, hs⟩ := hz
      exact ⟨s, Subtype.ext hs⟩
  let beta (f) := AddEquiv.ofBijective (betaMap f) (hbeta f)
  obtain ⟨phi, ⟨hIso, hphi⟩, _⟩ := hunique (F n) beta (by
    intro f r s
    apply Subtype.ext
    exact hF.2.1 n f.val.1 f.val.2 f.property.1 f.property.2 r s) (by
    intro f g inc s
    apply Subtype.ext
    obtain ⟨y, r, hy⟩ : ∃ (y : M) (r : ℕ),
        chart n f.val.1 f.val.2 f.property.1 f.property.2 s =
          mk y (⟨f.val.1 ^ r, ⟨r, rfl⟩⟩ : Submonoid.powers f.val.1) := by
      induction chart n f.val.1 f.val.2 f.property.1 f.property.2 s
          using LocalizedModule.induction_on with
      | h y q =>
        obtain ⟨r, hr⟩ := q.2
        exact ⟨y, r, congrArg (mk y) (Subtype.ext hr.symm)⟩
    obtain ⟨e, k, v, he, hv, hrel⟩ := (hlaws f g inc).1
    exact (hF.2.2 n f.val.1 g.val.1 f.val.2 g.val.2 f.property.1 g.property.1
      f.property.2 g.property.2 inc e k v he hv hrel r y s hy).trans
        ((hlaws f g inc).2.2 e k v he hv hrel r y (beta f s) hy).symm)
  have : IsIso phi := hIso
  exact (SheafOfModules.isQuasicoherent (Proj 𝒜).ringCatSheaf).prop_of_iso
    (asIso phi) hqc

set_option maxHeartbeats 50000 in
-- Bound elaboration while comparing restrictions to affine opens.
set_option backward.isDefEq.respectTransparency false in
private theorem hom_ext_affine_cover {X : Scheme.{u}} {I : Type u}
    (U : I → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (hAffine : ∀ i, IsAffine (U i))
    {P Q : X.Modules} [P.IsQuasicoherent] {alpha beta : P ⟶ Q}
    (h : ∀ i (s : Γ(P, U i)), alpha.app _ s = beta.app _ s) : alpha = beta := by
  have hr (i : I) :
      (restrictFunctor (U i).ι).map alpha = (restrictFunctor (U i).ι).map beta := by
    have : IsAffine (U i) := hAffine i
    apply hom_ext_of_isAffine
    change ∀ s : Γ(P, (U i).ι ''ᵁ ⊤), alpha.app _ s = beta.app _ s
    rw [Scheme.Opens.ι_image_top]
    exact h i
  refine hom_ext _ _ fun W ↦ ?_
  ext s
  let T : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨Q.presheaf, Q.isSheaf⟩
  refine T.eq_of_locally_eq' (fun i : I ↦ (U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ W))
    W (fun i ↦ homOfLE ((U i).ι.image_preimage_le W)) (fun x hx ↦ ?_) _ _ ?_
  · obtain ⟨i, hxi⟩ := hU x
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨i, ?_⟩
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact ⟨hxi, hx⟩
  · intro i
    rw [← Hom.app_presheaf_map, ← Hom.app_presheaf_map]
    exact congrArg (fun k ↦ k.app ((U i).ι ⁻¹ᵁ W)
      (P.presheaf.map (homOfLE ((U i).ι.image_preimage_le W)).op s)) (hr i)

private theorem hom_ext_degreeOne
    (cover : ∀ x : Proj 𝒜, ∃ f ∈ 𝒜 1, x ∈ basicOpen 𝒜 f)
    {P Q : (Proj 𝒜).Modules} [P.IsQuasicoherent] {alpha beta : P ⟶ Q}
    (h : ∀ (f : S) (_hf : f ∈ 𝒜 1) (s : Γ(P, basicOpen 𝒜 f)),
      alpha.app _ s = beta.app _ s) : alpha = beta := by
  apply hom_ext_affine_cover (fun i : {f : S // f ∈ 𝒜 1} ↦ basicOpen 𝒜 i.val)
    (fun x ↦ by obtain ⟨f, hf, hxf⟩ := cover x; exact ⟨⟨f, hf⟩, hxf⟩)
    (fun i ↦ isAffineOpen_basicOpen 𝒜 i.val i.property (by decide))
  exact fun i ↦ h i.val i.property

private theorem twist_eqToHom_app {a b : ℤ} (h : a = b)
    (U : (Proj 𝒜).Opens) (s : Γ(twist 𝒜 a, U)) (p : U) :
    (((eqToHom (congrArg (twist 𝒜) h)).app U s).1 p :
      Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) = s.1 p := by
  subst b
  rfl

private theorem twistTensorIso_product_on_subopen
    (cover : ∀ x : Proj 𝒜, ∃ f ∈ 𝒜 1, x ∈ basicOpen 𝒜 f)
    (a b : ℤ) (f : S) (hf : f ∈ 𝒜 1) (W : (Proj 𝒜).Opens)
    (hW : W ≤ basicOpen 𝒜 f) (s : Γ(twist 𝒜 a, W))
    (t : Γ(twist 𝒜 b, W)) (p : W) :
    (((twistTensorIso 𝒜 cover a b).hom.app W (tmulSection s t)).1 p :
      Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) =
      (s.1 p : Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) * t.1 p := by
  obtain ⟨r, hr⟩ := ((isFreeGenerator_twistPowSection a hf).map hW).exists_smul_eq s
  obtain ⟨q, hq⟩ := ((isFreeGenerator_twistPowSection b hf).map hW).exists_smul_eq t
  let ea := (twist 𝒜 a).presheaf.map (homOfLE hW).op (twistPowSection a hf)
  let eb := (twist 𝒜 b).presheaf.map (homOfLE hW).op (twistPowSection b hf)
  have htensor : tmulSection s t = (r * q) • tmulSection ea eb := by
    calc
      _ = tmulSection (r • ea) (q • eb) := congrArg₂ tmulSection hr.symm hq.symm
      _ = r • tmulSection ea (q • eb) := smul_tmulSection r ea (q • eb)
      _ = r • q • tmulSection ea eb :=
        congrArg (r • ·) (tmulSection_smul q ea eb)
      _ = _ := smul_smul r q _
  have he : (twistTensorIso 𝒜 cover a b).hom.app W (tmulSection s t) =
      (r * q) • (twist 𝒜 (a + b)).presheaf.map (homOfLE hW).op
        (twistPowSection (a + b) hf) := by
    calc
      _ = (twistTensorIso 𝒜 cover a b).hom.app W
          ((r * q) • (twist 𝒜 a ⊗ twist 𝒜 b).presheaf.map (homOfLE hW).op
            (tmulSection (twistPowSection a hf) (twistPowSection b hf))) :=
        congrArg ((twistTensorIso 𝒜 cover a b).hom.app W)
          (htensor.trans (congrArg ((r * q) • ·) (tmulSection_map hW _ _).symm))
      _ = _ := twistTensorIso_hom_app_smul cover a b hf hW (r * q)
  have hs := congrArg (fun z : Γ(twist 𝒜 a, W) ↦
    (z.1 p : Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal)) hr
  have ht := congrArg (fun z : Γ(twist 𝒜 b, W) ↦
    (z.1 p : Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal)) hq
  have hh := congrArg (fun z : Γ(twist 𝒜 (a + b), W) ↦
    (z.1 p : Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal)) he
  simp only [coe_twist_smul_apply, twist_presheaf_map_apply] at hs ht hh
  rw [hh, ← hs, ← ht]
  change (r.1 p * q.1 p).val * _ = _
  rw [HomogeneousLocalization.val_mul]
  rw [← val_twistPowSection_mul a hf rfl]
  ring

private theorem twistTensorIso_product
    (cover : ∀ x : Proj 𝒜, ∃ f ∈ 𝒜 1, x ∈ basicOpen 𝒜 f)
    (a b : ℤ) (U : (Proj 𝒜).Opens) (s : Γ(twist 𝒜 a, U))
    (t : Γ(twist 𝒜 b, U)) (p : U) :
    (((twistTensorIso 𝒜 cover a b).hom.app U (tmulSection s t)).1 p :
      Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) =
      (s.1 p : Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) * t.1 p := by
  obtain ⟨f, hf, hp⟩ := cover p.1
  let W := U ⊓ basicOpen 𝒜 f
  have h := twistTensorIso_product_on_subopen 𝒜 cover a b f hf W inf_le_right
    ((twist 𝒜 a).presheaf.map (homOfLE inf_le_left).op s)
    ((twist 𝒜 b).presheaf.map (homOfLE inf_le_left).op t) ⟨p.1, p.2, hp⟩
  rw [← tmulSection_map, Hom.app_presheaf_map] at h
  exact h

-- Its generator formula is now the complete interface to the glued comparison.
attribute [local irreducible] twistTensorIso

private noncomputable def fractionEval (f : S) (p : basicOpen 𝒜 f) :
    Localization.Away f →+* Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal :=
  IsLocalization.map (M := Submonoid.powers f)
    (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl) _ (RingHom.id S)
    (Submonoid.powers_le.mpr p.2)

private noncomputable def twistChart (n : ℤ) (f : S) (d : ℕ)
    (hd : 0 < d) (hf : f ∈ 𝒜 d) :
    Γ(twist 𝒜 n, basicOpen 𝒜 f) →+ Localization.Away f :=
  { toFun := fun s ↦ (twist_fraction_descent 𝒜 n f d hd hf s).choose
    map_zero' := by
      apply basicOpen_localization_detection 𝒜 f d hd hf
      intro p
      exact ((twist_fraction_descent 𝒜 n f d hd hf 0).choose_spec.2 p).trans
        (map_zero (fractionEval 𝒜 f p)).symm
    map_add' := by
      intro s t
      apply basicOpen_localization_detection 𝒜 f d hd hf
      intro p
      rw [map_add]
      exact ((twist_fraction_descent 𝒜 n f d hd hf (s + t)).choose_spec.2 p).trans
        (congrArg₂ (· + ·)
          ((twist_fraction_descent 𝒜 n f d hd hf s).choose_spec.2 p)
          ((twist_fraction_descent 𝒜 n f d hd hf t).choose_spec.2 p)).symm }

private theorem twistChart_eval (n : ℤ) (f : S) (d : ℕ) (hd : 0 < d)
    (hf : f ∈ 𝒜 d) (s : Γ(twist 𝒜 n, basicOpen 𝒜 f)) (p : basicOpen 𝒜 f) :
    fractionEval 𝒜 f p (twistChart 𝒜 n f d hd hf s) = (s.1 p).1 :=
  (twist_fraction_descent 𝒜 n f d hd hf s).choose_spec.2 p

private theorem twistChart_mem (n : ℤ) (f : S) (d : ℕ) (hd : 0 < d)
    (hf : f ∈ 𝒜 d) (s : Γ(twist 𝒜 n, basicOpen 𝒜 f)) :
    twistChart 𝒜 n f d hd hf s ∈ degreeZeroFractions
      (fun k : ℕ ↦ (𝒜 k : Set S))
      (fun k : ℕ ↦ {y : S | if 0 ≤ n + k then y ∈ 𝒜 (n + k).toNat else y = 0})
      (Submonoid.powers f) :=
  (twist_fraction_descent 𝒜 n f d hd hf s).choose_spec.1

-- All later arguments use the chart equations, not the choice of its representatives.
attribute [local irreducible] twistChart

private theorem twistChart_smul (n : ℤ) (f : S) (d : ℕ) (hd : 0 < d)
    (hf : f ∈ 𝒜 d) (r : HomogeneousLocalization.Away 𝒜 f)
    (s : Γ(twist 𝒜 n, basicOpen 𝒜 f)) :
    twistChart 𝒜 n f d hd hf (awayToSection 𝒜 f r • s) =
      r.val * twistChart 𝒜 n f d hd hf s := by
  apply basicOpen_localization_detection 𝒜 f d hd hf
  intro p
  change fractionEval 𝒜 f p _ = fractionEval 𝒜 f p _
  rw [twistChart_eval, map_mul, twistChart_eval, coe_twist_smul_apply]
  congr 1
  exact ProjectiveSpectrum.Proj.awayToSection_apply 𝒜 f r p

private theorem twistChart_fraction (n : ℤ) (f : S) (d : ℕ) (hd : 0 < d)
    (hf : f ∈ 𝒜 d) (s : Γ(twist 𝒜 n, basicOpen 𝒜 f)) (y : S) (r : ℕ)
    (hs : ∀ p : basicOpen 𝒜 f,
      (s.1 p : Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) =
        Localization.mk y ⟨f ^ r, pow_mem_primeCompl p r⟩) :
    twistChart 𝒜 n f d hd hf s =
      Localization.mk y (⟨f ^ r, ⟨r, rfl⟩⟩ : Submonoid.powers f) := by
  apply basicOpen_localization_detection 𝒜 f d hd hf
  intro p
  change fractionEval 𝒜 f p _ = fractionEval 𝒜 f p _
  rw [twistChart_eval, hs]
  simp only [fractionEval, Localization.mk_eq_mk', IsLocalization.map_mk', RingHom.id_apply]

private theorem chart_product_exists
    (𝓜 : ℤ → AddSubgroup M)
    (hsmul : ∀ (k : ℕ) (n : ℤ) (s : S) (y : M),
      s ∈ 𝒜 k → y ∈ 𝓜 n → s • y ∈ 𝓜 (k + n))
    (F : ℤ → (Proj 𝒜).Modules)
    (chart : ∀ (n : ℤ) (f : S) (d : ℕ), 0 < d → f ∈ 𝒜 d →
      Γ(F n, basicOpen 𝒜 f) →+ LocalizedModule.Away f M)
    (hF : IsStandardProjShiftSheaf 𝒜 𝓜 F chart)
    (a b : ℤ) (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d)
    (x : Γ(F a, basicOpen 𝒜 f)) (t : Γ(twist 𝒜 b, basicOpen 𝒜 f)) :
    ∃ z : Γ(F (a + b), basicOpen 𝒜 f),
      chart (a + b) f d hd hf z =
        twistChart 𝒜 b f d hd hf t • chart a f d hd hf x := by
  have hx : chart a f d hd hf x ∈ degreeZeroFractions
      (fun k : ℕ ↦ (𝒜 k : Set S)) (fun k : ℕ ↦ (𝓜 (a + k) : Set M))
      (Submonoid.powers f) := by
    rw [← (hF.1 a f d hd hf).2]
    exact ⟨x, rfl⟩
  obtain ⟨i, y, q, hy, hq, hxy⟩ := hx
  obtain ⟨j, v, r, hv, hr, htv⟩ := twistChart_mem 𝒜 b f d hd hf t
  rw [← Set.mem_range, (hF.1 (a + b) f d hd hf).2]
  rw [← hxy, ← htv]
  change Localization.mk v r • mk y q ∈ _
  rw [mk_smul_mk]
  by_cases hj : 0 ≤ b + j
  · have hv' : v ∈ 𝒜 (b + j).toNat := by simpa [hj] using hv
    refine ⟨i + j, v • y, r * q, ?_, ?_, rfl⟩
    · have hn : ((b + (j : ℤ)).toNat : ℤ) = b + j := Int.toNat_of_nonneg hj
      have hy' : y ∈ 𝓜 (a + (i : ℤ)) := hy
      have hh := hsmul (b + j).toNat (a + i) v y hv' hy'
      change v • y ∈ 𝓜 (a + b + ((i + j : ℕ) : ℤ))
      have he : ((b + (j : ℤ)).toNat : ℤ) + (a + i) =
          a + b + ((i + j : ℕ) : ℤ) := by omega
      rw [he] at hh
      exact hh
    · change (r : S) * (q : S) ∈ 𝒜 (i + j)
      simpa only [Nat.add_comm] using SetLike.mul_mem_graded hr hq
  · have hv' : v = 0 := by simpa [hj] using hv
    rw [hv', zero_smul, LocalizedModule.zero_mk]
    rw [← (hF.1 (a + b) f d hd hf).2]
    exact ⟨0, map_zero _⟩

private theorem twistChart_restrict (n : ℤ) (f g : S) (d k : ℕ)
    (hd : 0 < d) (hk : 0 < k) (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 k)
    (inc : basicOpen 𝒜 g ≤ basicOpen 𝒜 f) (e l : ℕ) (v : S)
    (_he : 0 < e) (_hv : v ∈ 𝒜 l) (hrel : g ^ e = v * f)
    (r : ℕ) (y : S) (t : Γ(twist 𝒜 n, basicOpen 𝒜 f))
    (ht : twistChart 𝒜 n f d hd hf t =
      Localization.mk y (⟨f ^ r, ⟨r, rfl⟩⟩ : Submonoid.powers f)) :
    twistChart 𝒜 n g k hk hg ((twist 𝒜 n).presheaf.map (homOfLE inc).op t) =
      Localization.mk (v ^ r * y)
        (⟨g ^ (e * r), ⟨e * r, rfl⟩⟩ : Submonoid.powers g) := by
  apply basicOpen_localization_detection 𝒜 g k hk hg
  intro p
  change fractionEval 𝒜 g p _ = fractionEval 𝒜 g p _
  rw [twistChart_eval]
  change (t.1 ⟨p.1, inc p.2⟩).1 = _
  rw [← twistChart_eval 𝒜 n f d hd hf t ⟨p.1, inc p.2⟩, ht]
  simp only [fractionEval, Localization.mk_eq_mk', IsLocalization.map_mk', RingHom.id_apply]
  apply IsLocalization.mk'_eq_of_eq
  change f ^ r * (v ^ r * y) = g ^ (e * r) * y
  rw [pow_mul, hrel, mul_pow]
  ring

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_hom_ext {X : AlgebraicGeometry.Scheme.{u}} {P Q R : X.Modules}
    {a b : P ⊗ Q ⟶ R}
    (h : ∀ (U : X.Opens) (s : Γ(P, U)) (t : Γ(Q, U)),
      a.app U (tmulSection s t) = b.app U (tmulSection s t)) : a = b := by
  let := presheafMonoidalCategory X
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification P Q).inv).mp
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).homEquiv (P.val ⊗ Q.val) R).injective
  have hh (U : (Opens X)ᵒᵖ) (x : Γ(P, U.unop)) (y : Γ(Q, U.unop)) :
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).homEquiv (P.val ⊗ Q.val) R)
          ((SheafOfModules.tensorObjIsoSheafification P Q).inv ≫ a)).app U (x ⊗ₜ y) =
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).homEquiv (P.val ⊗ Q.val) R)
          ((SheafOfModules.tensorObjIsoSheafification P Q).inv ≫ b)).app U (x ⊗ₜ y) :=
    h U.unop x y
  generalize he : ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).homEquiv (P.val ⊗ Q.val) R)
      ((SheafOfModules.tensorObjIsoSheafification P Q).inv ≫ a) = f at hh ⊢
  generalize he' : ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).homEquiv (P.val ⊗ Q.val) R)
      ((SheafOfModules.tensorObjIsoSheafification P Q).inv ≫ b) = g at hh ⊢
  apply PresheafOfModules.hom_ext
  intro U
  ext z
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero (f.app U).hom).trans (map_zero (g.app U).hom).symm
  | tmul x y => exact hh U x y
  | add z w hz hw =>
    exact (map_add (f.app U).hom z w).trans
      ((congrArg₂ (· + ·) hz hw).trans (map_add (g.app U).hom z w).symm)

private theorem twist_triple_hom_ext
    (cover : ∀ x : Proj 𝒜, ∃ f ∈ 𝒜 1, x ∈ basicOpen 𝒜 f)
    {P H : (Proj 𝒜).Modules} [P.IsQuasicoherent] (b c : ℤ)
    {alpha beta : (P ⊗ twist 𝒜 b) ⊗ twist 𝒜 c ⟶ H}
    (h : ∀ (U : (Proj 𝒜).Opens) (x : Γ(P, U))
      (t : Γ(twist 𝒜 b, U)) (w : Γ(twist 𝒜 c, U)),
      alpha.app U (tmulSection (tmulSection x t) w) =
        beta.app U (tmulSection (tmulSection x t) w)) : alpha = beta := by
  have : (twist 𝒜 b).IsInvertible := isInvertible_twist 𝒜 b cover
  have : (twist 𝒜 c).IsInvertible := isInvertible_twist 𝒜 c cover
  have : (P ⊗ twist 𝒜 b).IsQuasicoherent := isQuasicoherent_tensorObj _ _
  have : ((P ⊗ twist 𝒜 b) ⊗ twist 𝒜 c).IsQuasicoherent :=
    isQuasicoherent_tensorObj _ _
  apply hom_ext_degreeOne 𝒜 cover
  intro f hf z
  obtain ⟨s, rfl⟩ := ((isFreeGenerator_twistPowSection c hf).bijective_tmulSection_right
    (M := P ⊗ twist 𝒜 b) le_rfl).surjective z
  obtain ⟨x, rfl⟩ := ((isFreeGenerator_twistPowSection b hf).bijective_tmulSection_right
    (M := P) le_rfl).surjective s
  exact h _ _ _ _

private theorem section_ext_basis {X : Scheme.{u}} {I : Type u}
    (D : I → X.Opens) (hB : Opens.IsBasis (Set.range D)) (F : X.Modules)
    (U : X.Opens) (s t : Γ(F, U))
    (h : ∀ (i : I) (inc : D i ≤ U),
      F.presheaf.map (homOfLE inc).op s = F.presheaf.map (homOfLE inc).op t) : s = t := by
  apply TopCat.Presheaf.IsSheaf.section_ext F.isSheaf
  intro p hp
  obtain ⟨_, ⟨V, ⟨i, rfl⟩, rfl⟩, hpi, hiU⟩ := hB.exists_subset_of_mem_open hp U.2
  exact ⟨D i, hiU, hpi, h i hiU⟩

private theorem standard_basis :
    Opens.IsBasis (Set.range (fun i : {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2} ↦
      basicOpen 𝒜 i.val.1)) := by
  have he : Set.range (fun i : {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2} ↦
      basicOpen 𝒜 i.val.1) =
      {U | ∃ (f : S) (d : ℕ), 0 < d ∧ f ∈ 𝒜 d ∧ U = basicOpen 𝒜 f} := by
    ext U
    constructor
    · rintro ⟨⟨⟨f, d⟩, hd, hf⟩, rfl⟩
      exact ⟨f, d, hd, hf, rfl⟩
    · rintro ⟨f, d, hd, hf, rfl⟩
      exact ⟨⟨⟨f, d⟩, hd, hf⟩, rfl⟩
  rw [he]
  exact (standardOpenProperties.{u, u, u} 𝒜).1

private theorem section_ext_standard (F : (Proj 𝒜).Modules)
    (U : (Proj 𝒜).Opens) (s t : Γ(F, U))
    (h : ∀ (f : S) (d : ℕ) (_hd : 0 < d) (_hf : f ∈ 𝒜 d)
      (inc : basicOpen 𝒜 f ≤ U),
      F.presheaf.map (homOfLE inc).op s = F.presheaf.map (homOfLE inc).op t) :
    s = t := by
  apply section_ext_basis _ (standard_basis 𝒜) F U s t
  exact fun i inc ↦ h i.val.1 i.val.2 i.property.1 i.property.2 inc

private theorem chart_eqToHom
    (F : ℤ → (Proj 𝒜).Modules)
    (chart : ∀ (n : ℤ) (f : S) (d : ℕ), 0 < d → f ∈ 𝒜 d →
      Γ(F n, basicOpen 𝒜 f) →+ LocalizedModule.Away f M)
    {a b : ℤ} (h : a = b) (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d)
    (s : Γ(F a, basicOpen 𝒜 f)) :
    chart b f d hd hf ((eqToHom (congrArg F h)).app _ s) = chart a f d hd hf s := by
  subst b
  rfl

private theorem twistChart_product
    (cover : ∀ x : Proj 𝒜, ∃ f ∈ 𝒜 1, x ∈ basicOpen 𝒜 f)
    (a b : ℤ) (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d)
    (s : Γ(twist 𝒜 a, basicOpen 𝒜 f)) (t : Γ(twist 𝒜 b, basicOpen 𝒜 f)) :
    twistChart 𝒜 (a + b) f d hd hf
        ((twistTensorIso 𝒜 cover a b).hom.app _ (tmulSection s t)) =
      twistChart 𝒜 a f d hd hf s * twistChart 𝒜 b f d hd hf t := by
  apply basicOpen_localization_detection 𝒜 f d hd hf
  intro p
  change fractionEval 𝒜 f p _ = fractionEval 𝒜 f p _
  rw [twistChart_eval, map_mul, twistChart_eval, twistChart_eval, twistTensorIso_product]

private theorem twistChart_unit (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d) :
    twistChart 𝒜 0 f d hd hf
      (Hom.app (unitIsoTwistZero (𝒜 := 𝒜)).hom _ (unitSectionsEquiv _ 1)) = 1 := by
  apply basicOpen_localization_detection 𝒜 f d hd hf
  intro p
  change fractionEval 𝒜 f p _ = fractionEval 𝒜 f p _
  rw [twistChart_eval]
  change ((degreePart.zeroEquiv (1 : HomogeneousLocalization.AtPrime 𝒜
    p.1.asHomogeneousIdeal.toIdeal) : degreePart 𝒜
      p.1.asHomogeneousIdeal.toIdeal.primeCompl 0) :
        Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) = _
  rw [degreePart.coe_zeroEquiv_apply, HomogeneousLocalization.val_one, map_one]

private theorem away_exists_fraction (f : S) (z : LocalizedModule.Away f M) :
    ∃ (y : M) (r : ℕ), z = mk y (⟨f ^ r, ⟨r, rfl⟩⟩ : Submonoid.powers f) := by
  induction z using LocalizedModule.induction_on with
  | h y q =>
    obtain ⟨r, hr⟩ := q.2
    refine ⟨y, r, ?_⟩
    congr 1
    exact Subtype.ext hr.symm

private theorem extend_linear_basis {X : Scheme.{u}} {I : Type u}
    (D : I → X.Opens) (hB : Opens.IsBasis (Set.range D))
    (P : PresheafOfModules.{u} X.ringCatSheaf.obj) (Q : X.Modules)
    (C : ∀ i, P.obj (op (D i)) →ₗ[Γ(X, D i)] Γ(Q, D i))
    (hc : ∀ (i j : I) (inc : D j ≤ D i) (z : P.obj (op (D i))),
      C j (P.map (homOfLE inc).op z) = Q.val.presheaf.map (homOfLE inc).op (C i z)) :
    ∃ chi : P ⟶ Q.val,
      ∀ i (z : P.obj (op (D i))), chi.app (op (D i)) z = C i z := by
  let beta : (inducedFunctor D).op ⋙ P.presheaf ⟶
      (inducedFunctor D).op ⋙ Q.val.presheaf :=
    { app := fun U ↦ AddCommGrpCat.ofHom (C U.unop).toAddMonoidHom
      naturality := by
        intro U V inc
        ext z
        exact hc U.unop V.unop ((inducedFunctor D).map inc.unop).le z }
  let H : P.presheaf ⟶ Q.val.presheaf :=
    TopCat.Sheaf.restrictHomEquivHom P.presheaf ⟨Q.val.presheaf, Q.isSheaf⟩ hB beta
  have hHB (i : I) (z : P.obj (op (D i))) : H.app (op (D i)) z = C i z := by
    exact congrArg (fun k ↦ k z)
      (TopCat.Sheaf.extend_hom_app P.presheaf ⟨Q.val.presheaf, Q.isSheaf⟩ hB beta i)
  have hlinear (U : (Opens X)ᵒᵖ) (r : X.ringCatSheaf.obj.obj U) (z : P.obj U) :
      H.app U (r • z) = r • (H.app U z : Q.val.obj U) := by
    apply TopCat.Presheaf.IsSheaf.section_ext Q.isSheaf
    intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := hB.exists_subset_of_mem_open hx U.unop.2
    obtain ⟨i, rfl⟩ := hV
    refine ⟨D i, hVU, hxV, ?_⟩
    have hnat := H.naturality_apply (homOfLE hVU).op
    change Q.val.map (homOfLE hVU).op (H.app U (r • z)) =
      Q.val.map (homOfLE hVU).op (r • (H.app U z : Q.val.obj U))
    let r' : Γ(X, D i) := X.ringCatSheaf.obj.map (homOfLE hVU).op r
    exact (hnat (r • z)).symm.trans
      ((congrArg (H.app (op (D i))) (P.map_smul (homOfLE hVU).op r z)).trans
        ((hHB i _).trans
          (((C i).map_smul r' (P.map (homOfLE hVU).op z)).trans
            ((congrArg (fun v : Γ(Q, D i) ↦ r' • v)
              ((hHB i _).symm.trans (hnat z))).trans
                (Q.val.map_smul (homOfLE hVU).op r (H.app U z)).symm))))
  let chi : P ⟶ Q.val :=
    { app := fun U ↦ ModuleCat.ofHom
        { toFun := H.app U
          map_add' := (H.app U).hom.map_add
          map_smul' := hlinear U }
      naturality := by
        intro U V inc
        ext z
        exact H.naturality_apply inc z }
  exact ⟨chi, hHB⟩

attribute [local instance] presheafMonoidalCategory

private theorem tensor_desc {X : Scheme.{u}} (P Q H : X.Modules)
    (chi : (P.val ⊗ Q.val) ⟶ H.val) :
    ∃ m : P ⊗ Q ⟶ H, ∀ (U : X.Opens) (x : Γ(P, U)) (y : Γ(Q, U)),
      m.app U (tmulSection x y) = chi.app (op U) (x ⊗ₜ[Γ(X, U)] y) := by
  let := presheafMonoidalCategory X
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let m : P ⊗ Q ⟶ H := (SheafOfModules.tensorObjIsoSheafification P Q).hom ≫
    (adj.homEquiv (P.val ⊗ Q.val) H).symm chi
  refine ⟨m, ?_⟩
  intro U x y
  change Hom.app ((SheafOfModules.tensorObjIsoSheafification P Q).inv ≫
    (SheafOfModules.tensorObjIsoSheafification P Q).hom ≫
      (adj.homEquiv (P.val ⊗ Q.val) H).symm chi) U
    ((toSheafifyTensor P Q).app (op U) (x ⊗ₜ y)) = _
  rw [Iso.inv_hom_id_assoc]
  exact congrArg (fun k ↦ k.app (op U) (x ⊗ₜ y))
    ((adj.homEquiv (P.val ⊗ Q.val) H).apply_symm_apply chi)

private theorem addHom_tensor_ext {R A B H : Type u} [CommSemiring R]
    [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid H] [Module R A] [Module R B]
    {f g : TensorProduct R A B →+ H}
    (h : ∀ x y, f (x ⊗ₜ[R] y) = g (x ⊗ₜ[R] y)) : ∀ z, f z = g z := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero f).trans (map_zero g).symm
  | tmul x y => exact h x y
  | add z w hz hw =>
    exact (map_add f z w).trans ((congrArg₂ (· + ·) hz hw).trans (map_add g z w).symm)


private theorem tensor_desc_basis {X : Scheme.{u}} {I : Type u}
    (D : I → X.Opens) (hB : Opens.IsBasis (Set.range D)) (P Q H : X.Modules)
    (C : ∀ i, TensorProduct Γ(X, D i) Γ(P, D i) Γ(Q, D i) →ₗ[Γ(X, D i)] Γ(H, D i))
    (hc : ∀ (i j : I) (inc : D j ≤ D i) (x : Γ(P, D i)) (t : Γ(Q, D i)),
      C j (P.presheaf.map (homOfLE inc).op x ⊗ₜ
        Q.presheaf.map (homOfLE inc).op t) =
      H.presheaf.map (homOfLE inc).op (C i (x ⊗ₜ t))) :
    ∃ m : P ⊗ Q ⟶ H, ∀ (i : I) (x : Γ(P, D i)) (t : Γ(Q, D i)),
      m.app (D i) (tmulSection x t) = C i (x ⊗ₜ t) := by
  let T := P.val ⊗ Q.val
  obtain ⟨chi, hchi⟩ := extend_linear_basis D hB T H C (by
    intro i j inc
    apply addHom_tensor_ext
      (f := (C j).toAddMonoidHom.comp ((T.map (homOfLE inc).op).hom.toAddMonoidHom))
      (g := (H.val.map (homOfLE inc).op).hom.toAddMonoidHom.comp (C i).toAddMonoidHom)
    intro x t
    exact (congrArg (C j) (PresheafOfModules.Monoidal.tensorObj_map_tmul
      (M₁ := P.val) (M₂ := Q.val) (homOfLE inc).op x t)).trans (hc i j inc x t))
  obtain ⟨m, hm⟩ := tensor_desc P Q H chi
  exact ⟨m, fun i x t ↦ (hm (D i) x t).trans (hchi i (x ⊗ₜ t))⟩

section

attribute [local irreducible] AlgebraicGeometry.Proj basicOpen twist fractionEval

set_option maxHeartbeats 40000 in
-- Avoid expensive unfolding of the localized tensor construction.
set_option backward.isDefEq.respectTransparency false in
private theorem multiplication_exists
    (𝓜 : ℤ → AddSubgroup M)
    (hsmul : ∀ (k : ℕ) (n : ℤ) (s : S) (y : M),
      s ∈ 𝒜 k → y ∈ 𝓜 n → s • y ∈ 𝓜 (k + n))
    (F : ℤ → (Proj 𝒜).Modules)
    (chart : ∀ (n : ℤ) (f : S) (d : ℕ), 0 < d → f ∈ 𝒜 d →
      Γ(F n, basicOpen 𝒜 f) →+ LocalizedModule.Away f M)
    (hF : IsStandardProjShiftSheaf 𝒜 𝓜 F chart) :
    ∃ mult : ∀ a b : ℤ, F a ⊗ twist 𝒜 b ⟶ F (a + b),
      ∀ (a b : ℤ) (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d)
        (x : Γ(F a, basicOpen 𝒜 f)) (t : Γ(twist 𝒜 b, basicOpen 𝒜 f)),
      chart (a + b) f d hd hf
        ((mult a b).app (basicOpen 𝒜 f) (tmulSection x t)) =
          twistChart 𝒜 b f d hd hf t • chart a f d hd hf x := by
  classical
  let := presheafMonoidalCategory (Proj 𝒜)
  choose c hc using chart_product_exists 𝒜 𝓜 hsmul F chart hF
  -- The chart equation determines the chosen product; keep its construction abstract.
  generalize hcdef : c = c₀ at hc
  clear c hcdef
  have hcadd (a b : ℤ) (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d)
      (x y : Γ(F a, basicOpen 𝒜 f)) (t : Γ(twist 𝒜 b, basicOpen 𝒜 f)) :
      c₀ a b f d hd hf (x + y) t = c₀ a b f d hd hf x t + c₀ a b f d hd hf y t := by
    apply (hF.1 (a + b) f d hd hf).1
    rw [hc, map_add, map_add, hc, hc, smul_add]
  have hctadd (a b : ℤ) (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d)
      (x : Γ(F a, basicOpen 𝒜 f)) (s t : Γ(twist 𝒜 b, basicOpen 𝒜 f)) :
      c₀ a b f d hd hf x (s + t) = c₀ a b f d hd hf x s + c₀ a b f d hd hf x t := by
    apply (hF.1 (a + b) f d hd hf).1
    rw [hc, map_add, map_add, hc, hc, add_smul]
  have hcsmul (a b : ℤ) (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d)
      (r : Γ(Proj 𝒜, basicOpen 𝒜 f))
      (x : Γ(F a, basicOpen 𝒜 f)) (t : Γ(twist 𝒜 b, basicOpen 𝒜 f)) :
      c₀ a b f d hd hf (r • x) t = r • c₀ a b f d hd hf x t ∧
      c₀ a b f d hd hf x (r • t) = r • c₀ a b f d hd hf x t := by
    let iso := basicOpenIsoAway 𝒜 f hf hd
    obtain ⟨q, rfl⟩ := (ConcreteCategory.bijective_of_isIso iso.hom).2 r
    change c₀ a b f d hd hf (awayToSection 𝒜 f q • x) t =
      awayToSection 𝒜 f q • c₀ a b f d hd hf x t ∧
      c₀ a b f d hd hf x (awayToSection 𝒜 f q • t) =
      awayToSection 𝒜 f q • c₀ a b f d hd hf x t
    constructor
    · apply (hF.1 (a + b) f d hd hf).1
      rw [hc, hF.2.1 a f d hd hf q x,
        hF.2.1 (a + b) f d hd hf q (c₀ a b f d hd hf x t), hc]
      exact smul_comm _ _ _
    · apply (hF.1 (a + b) f d hd hf).1
      rw [hc, twistChart_smul 𝒜 b f d hd hf q t,
        hF.2.1 (a + b) f d hd hf q (c₀ a b f d hd hf x t), hc, mul_smul]
      rfl
  let bil (a b : ℤ) (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d) :
      Γ(F a, basicOpen 𝒜 f) →ₗ[Γ(Proj 𝒜, basicOpen 𝒜 f)]
        Γ(twist 𝒜 b, basicOpen 𝒜 f) →ₗ[Γ(Proj 𝒜, basicOpen 𝒜 f)]
          Γ(F (a + b), basicOpen 𝒜 f) :=
    { toFun := fun x ↦
        { toFun := c₀ a b f d hd hf x
          map_add' := hctadd a b f d hd hf x
          map_smul' := fun r t ↦ (hcsmul a b f d hd hf r x t).2 }
      map_add' := fun x y ↦ LinearMap.ext (fun t ↦ hcadd a b f d hd hf x y t)
      map_smul' := fun r x ↦ LinearMap.ext (fun t ↦ (hcsmul a b f d hd hf r x t).1) }
  let C (a b : ℤ) (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d) :=
    TensorProduct.lift (bil a b f d hd hf)
  have hC (a b : ℤ) (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d)
      (x : Γ(F a, basicOpen 𝒜 f)) (t : Γ(twist 𝒜 b, basicOpen 𝒜 f)) :
      C a b f d hd hf (x ⊗ₜ t) = c₀ a b f d hd hf x t := rfl
  -- Subsequent descent needs only the pure-tensor equation, not the lifted term.
  generalize hCdef : C = C₀ at hC
  clear C hCdef bil hcadd hctadd hcsmul
  have hcompat (a b : ℤ) (f g : S) (d k : ℕ) (hd : 0 < d) (hk : 0 < k)
      (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 k) (inc : basicOpen 𝒜 g ≤ basicOpen 𝒜 f)
      (x : Γ(F a, basicOpen 𝒜 f)) (t : Γ(twist 𝒜 b, basicOpen 𝒜 f)) :
      c₀ a b g k hk hg ((F a).presheaf.map (homOfLE inc).op x)
          ((twist 𝒜 b).presheaf.map (homOfLE inc).op t) =
        (F (a + b)).presheaf.map (homOfLE inc).op (c₀ a b f d hd hf x t) := by
    obtain ⟨e, l, v, he, hv, hrel⟩ :=
      ((standardOpenProperties.{u, u, u} 𝒜).2.2.1 f g d k hd hk hf hg).1.mp inc
    obtain ⟨y, r, hx⟩ := away_exists_fraction f (chart a f d hd hf x)
    obtain ⟨w, q, ht'⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers f)
      (twistChart 𝒜 b f d hd hf t)
    have ht : twistChart 𝒜 b f d hd hf t = Localization.mk w q :=
      ht'.symm.trans (Localization.mk_eq_mk'_apply w q).symm
    obtain ⟨s, hq⟩ := q.property
    have hq' : q = (⟨f ^ s, ⟨s, rfl⟩⟩ : Submonoid.powers f) := Subtype.ext hq.symm
    subst q
    have hcfrac : chart (a + b) f d hd hf (c₀ a b f d hd hf x t) =
        mk (w • y) (⟨f ^ (r + s), ⟨r + s, rfl⟩⟩ : Submonoid.powers f) := by
      rw [hc, hx, ht]
      change Localization.mk w _ • mk y _ = _
      rw [mk_smul_mk]
      congr 1
      apply Subtype.ext
      simp only [Submonoid.coe_mul, ← pow_add, Nat.add_comm]
    apply (hF.1 (a + b) g k hk hg).1
    rw [hc, hF.2.2 a f g d k hd hk hf hg inc e l v he hv hrel r y x hx,
      twistChart_restrict 𝒜 b f g d k hd hk hf hg inc e l v he hv hrel s w t ht,
      hF.2.2 (a + b) f g d k hd hk hf hg inc e l v he hv hrel (r + s) (w • y)
        (c₀ a b f d hd hf x t) hcfrac]
    change Localization.mk (v ^ s * w) _ • mk (v ^ r • y) _ = _
    rw [mk_smul_mk]
    congr 1
    · simp only [smul_smul, pow_add]
      congr 1
      ring
    · apply Subtype.ext
      simp only [Submonoid.coe_mul, ← pow_add, mul_add, Nat.add_comm]
  let I := {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}
  let D : I → Opens (Proj 𝒜) := fun f ↦ basicOpen 𝒜 f.val.1
  have hB : Opens.IsBasis (Set.range D) := standard_basis 𝒜
  have hex (a b : ℤ) : ∃ m : F a ⊗ twist 𝒜 b ⟶ F (a + b),
      ∀ (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d)
        (x : Γ(F a, basicOpen 𝒜 f)) (t : Γ(twist 𝒜 b, basicOpen 𝒜 f)),
      chart (a + b) f d hd hf (m.app (basicOpen 𝒜 f) (tmulSection x t)) =
        twistChart 𝒜 b f d hd hf t • chart a f d hd hf x := by
    obtain ⟨m, hm⟩ := tensor_desc_basis D hB (F a) (twist 𝒜 b) (F (a + b))
      (fun i ↦ C₀ a b i.val.1 i.val.2 i.property.1 i.property.2) (by
        intro i j inc x t
        exact (hC a b j.val.1 j.val.2 j.property.1 j.property.2 _ _).trans
          ((hcompat a b i.val.1 j.val.1 i.val.2 j.val.2 i.property.1 j.property.1
            i.property.2 j.property.2 inc x t).trans
              (congrArg ((F (a + b)).val.map (homOfLE inc).op)
                (hC a b i.val.1 i.val.2 i.property.1 i.property.2 x t).symm)))
    refine ⟨m, ?_⟩
    intro f d hd hf x t
    have he : m.app (basicOpen 𝒜 f) (tmulSection x t) = c₀ a b f d hd hf x t :=
      (hm ⟨⟨f, d⟩, hd, hf⟩ x t).trans (hC a b f d hd hf x t)
    exact (congrArg (chart (a + b) f d hd hf) he).trans (hc a b f d hd hf x t)
  choose mult hmult using hex
  exact ⟨mult, hmult⟩

end

private theorem twist_left_unit
    (cover : ∀ x : Proj 𝒜, ∃ f ∈ 𝒜 1, x ∈ basicOpen 𝒜 f) (a : ℤ) :
    (unitIsoTwistZero.hom ▷ twist 𝒜 a) ≫ (twistTensorIso 𝒜 cover 0 a).hom ≫
      eqToHom (congrArg (twist 𝒜) (zero_add a)) = (λ_ (twist 𝒜 a)).hom := by
  apply tensor_hom_ext
  intro U s t
  obtain ⟨r, rfl⟩ := (unitSectionsEquiv U).surjective s
  change (eqToHom (congrArg (twist 𝒜) (zero_add a))).app U
    ((twistTensorIso 𝒜 cover 0 a).hom.app U
      (Hom.app (unitIsoTwistZero.hom ▷ twist 𝒜 a) U
        (tmulSection (unitSectionsEquiv U r) t))) = _
  calc
    _ = (eqToHom (congrArg (twist 𝒜) (zero_add a))).app U
        ((twistTensorIso 𝒜 cover 0 a).hom.app U
          (tmulSection (Hom.app (unitIsoTwistZero (𝒜 := 𝒜)).hom U (unitSectionsEquiv U r)) t)) :=
      congrArg (fun z ↦ (eqToHom (congrArg (twist 𝒜) (zero_add a))).app U
        ((twistTensorIso 𝒜 cover 0 a).hom.app U z))
        (whiskerRight_app_tmulSection unitIsoTwistZero.hom (unitSectionsEquiv U r) t)
    _ = r • t := by
      apply Subtype.ext
      funext p
      apply Subtype.ext
      rw [twist_eqToHom_app 𝒜 (zero_add a), twistTensorIso_product,
        coe_twist_smul_apply]
      change ((degreePart.zeroEquiv (r.1 p) : degreePart 𝒜
        p.1.asHomogeneousIdeal.toIdeal.primeCompl 0) :
          Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) * _ = _
      rw [degreePart.coe_zeroEquiv_apply]
    _ = _ := (leftUnitor_hom_app_tmulSection r t).symm

private theorem twist_right_unit
    (cover : ∀ x : Proj 𝒜, ∃ f ∈ 𝒜 1, x ∈ basicOpen 𝒜 f) (a : ℤ) :
    (twist 𝒜 a ◁ unitIsoTwistZero.hom) ≫ (twistTensorIso 𝒜 cover a 0).hom ≫
      eqToHom (congrArg (twist 𝒜) (add_zero a)) = (ρ_ (twist 𝒜 a)).hom := by
  apply tensor_hom_ext
  intro U t s
  obtain ⟨r, rfl⟩ := (unitSectionsEquiv U).surjective s
  change (eqToHom (congrArg (twist 𝒜) (add_zero a))).app U
    ((twistTensorIso 𝒜 cover a 0).hom.app U
      (Hom.app (twist 𝒜 a ◁ unitIsoTwistZero.hom) U
        (tmulSection t (unitSectionsEquiv U r)))) = _
  calc
    _ = (eqToHom (congrArg (twist 𝒜) (add_zero a))).app U
        ((twistTensorIso 𝒜 cover a 0).hom.app U
          (tmulSection t (Hom.app (unitIsoTwistZero (𝒜 := 𝒜)).hom U (unitSectionsEquiv U r)))) :=
      congrArg (fun z ↦ (eqToHom (congrArg (twist 𝒜) (add_zero a))).app U
        ((twistTensorIso 𝒜 cover a 0).hom.app U z))
        (whiskerLeft_app_tmulSection unitIsoTwistZero.hom t (unitSectionsEquiv U r))
    _ = r • t := by
      apply Subtype.ext
      funext p
      apply Subtype.ext
      rw [twist_eqToHom_app 𝒜 (add_zero a), twistTensorIso_product,
        coe_twist_smul_apply]
      change _ * ((degreePart.zeroEquiv (r.1 p) : degreePart 𝒜
        p.1.asHomogeneousIdeal.toIdeal.primeCompl 0) :
          Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) = _
      rw [degreePart.coe_zeroEquiv_apply, mul_comm]
    _ = _ := (rightUnitor_hom_app_tmulSection r t).symm

private theorem twist_associativity
    (cover : ∀ x : Proj 𝒜, ∃ f ∈ 𝒜 1, x ∈ basicOpen 𝒜 f) (a b c : ℤ) :
    ((twistTensorIso 𝒜 cover a b).hom ▷ twist 𝒜 c) ≫
      (twistTensorIso 𝒜 cover (a + b) c).hom ≫
      eqToHom (congrArg (twist 𝒜) (add_assoc a b c)) =
    (α_ (twist 𝒜 a) (twist 𝒜 b) (twist 𝒜 c)).hom ≫
      (twist 𝒜 a ◁ (twistTensorIso 𝒜 cover b c).hom) ≫
      (twistTensorIso 𝒜 cover a (b + c)).hom := by
  have : (twist 𝒜 a).IsInvertible := isInvertible_twist 𝒜 a cover
  apply twist_triple_hom_ext 𝒜 cover b c
  intro U s t w
  change (eqToHom (congrArg (twist 𝒜) (add_assoc a b c))).app U
    ((twistTensorIso 𝒜 cover (a + b) c).hom.app U
      (Hom.app ((twistTensorIso 𝒜 cover a b).hom ▷ twist 𝒜 c) U
        (tmulSection (tmulSection s t) w))) =
    (twistTensorIso 𝒜 cover a (b + c)).hom.app U
      (Hom.app (twist 𝒜 a ◁ (twistTensorIso 𝒜 cover b c).hom) U
        ((α_ (twist 𝒜 a) (twist 𝒜 b) (twist 𝒜 c)).hom.app U
          (tmulSection (tmulSection s t) w)))
  have hleft := whiskerRight_app_tmulSection (twistTensorIso 𝒜 cover a b).hom
    (tmulSection s t) w
  have hright := associator_hom_app_tmulSection s t w
  have hright' := whiskerLeft_app_tmulSection (twistTensorIso 𝒜 cover b c).hom
    s (tmulSection t w)
  rw [hleft, hright, hright']
  apply Subtype.ext
  funext p
  apply Subtype.ext
  rw [twist_eqToHom_app 𝒜 (add_assoc a b c), twistTensorIso_product,
    twistTensorIso_product, twistTensorIso_product, twistTensorIso_product, mul_assoc]

section

attribute [local irreducible] twist

private theorem multiplication_isIso {C : Type u} [Category C] [MonoidalCategory C]
    [Balanced C] (L : ℤ → C) (unit : 𝟙_ C ≅ L 0)
    (prod : ∀ a b : ℤ, L a ⊗ L b ≅ L (a + b))
    (F : ℤ → C)
    (mult : ∀ a b : ℤ, F a ⊗ L b ⟶ F (a + b))
    (hu : ∀ a, (F a ◁ unit.hom) ≫ mult a 0 ≫
      eqToHom (congrArg F (add_zero a)) = (ρ_ (F a)).hom)
    (ha : ∀ a b c,
      (mult a b ▷ L c) ≫ mult (a + b) c ≫
        eqToHom (congrArg F (add_assoc a b c)) =
      (α_ (F a) (L b) (L c)).hom ≫
        (F a ◁ (prod b c).hom) ≫ mult a (b + c)) :
    ∀ a b, IsIso (mult a b) := by
  have hzero (a : ℤ) : IsIso (mult a 0) := by
    have h : IsIso ((F a ◁ unit.hom) ≫ mult a 0 ≫
        eqToHom (congrArg F (add_zero a))) := by
      rw [hu]
      infer_instance
    have : IsIso (mult a 0 ≫ eqToHom (congrArg F (add_zero a))) :=
      IsIso.of_isIso_comp_left (F a ◁ unit.hom) _
    exact IsIso.of_isIso_comp_right (mult a 0) (eqToHom (congrArg F (add_zero a)))
  have hcomp (a b : ℤ) :
      IsIso ((mult a b ▷ L (-b)) ≫ mult (a + b) (-b)) := by
    have : IsIso (mult a (b + -b)) := by
      rw [show b + -b = 0 from add_neg_cancel b]
      exact hzero a
    have : IsIso ((mult a b ▷ L (-b)) ≫ mult (a + b) (-b) ≫
        eqToHom (congrArg F (add_assoc a b (-b)))) := by
      rw [ha]
      infer_instance
    rw [← Category.assoc] at this
    exact IsIso.of_isIso_comp_right _ (eqToHom (congrArg F (add_assoc a b (-b))))
  have hepi (a b : ℤ) : Epi (mult a b) := by
    have := hcomp (a + b) (-b)
    have h : Epi (mult (a + b + -b) (- -b)) :=
      epi_of_epi (mult (a + b) (-b) ▷ L (- -b)) _
    have transport (c d : ℤ) (hc : c = a) (hd : d = b) (h : Epi (mult c d)) :
        Epi (mult a b) := by
      subst c
      subst d
      exact h
    exact transport _ _ (by omega) (by omega) h
  intro a b
  let e : L (-b) ⊗ L b ≅ 𝟙_ C :=
    prod (-b) b ≪≫
      eqToIso (congrArg (L) (neg_add_cancel b)) ≪≫ unit.symm
  let e' : L b ⊗ L (-b) ≅ 𝟙_ C :=
    prod b (-b) ≪≫
      eqToIso (congrArg (L) (add_neg_cancel b)) ≪≫ unit.symm
  let E := tensorRightEquivalenceOfTensorIso e e'
  have : (tensorRight (L (-b))).Faithful := E.faithful_functor
  have := hcomp a b
  have : Mono (mult a b ▷ L (-b)) :=
    mono_of_mono _ (mult (a + b) (-b))
  have : Mono (mult a b) := (tensorRight (L (-b))).mono_of_mono_map this
  have := hepi a b
  exact isIso_of_mono_of_epi _

end

set_option maxHeartbeats 40000 in
-- Bound elaboration of affine restriction and its tensor generator.
private theorem multiplication_naturality
    (cover : ∀ x : Proj 𝒜, ∃ f ∈ 𝒜 1, x ∈ basicOpen 𝒜 f)
    (𝓜 : ℤ → AddSubgroup M) (h𝓜 : DirectSum.IsInternal 𝓜)
    (hsmul : ∀ (k : ℕ) (n : ℤ) (s : S) (y : M),
      s ∈ 𝒜 k → y ∈ 𝓜 n → s • y ∈ 𝓜 (k + n))
    (F : ℤ → (Proj 𝒜).Modules)
    (chart : ∀ (n : ℤ) (f : S) (d : ℕ), 0 < d → f ∈ 𝒜 d →
      Γ(F n, basicOpen 𝒜 f) →+ LocalizedModule.Away f M)
    (hF : IsStandardProjShiftSheaf 𝒜 𝓜 F chart)
    (mult : ∀ a b : ℤ, F a ⊗ twist 𝒜 b ⟶ F (a + b))
    (hm : IsStandardProjTensorMultiplication 𝒜 F chart mult)
    {N : Type u} [AddCommGroup N] [Module S N]
    (𝓝 : ℤ → AddSubgroup N) (G : ℤ → (Proj 𝒜).Modules)
    (chartG : ∀ (n : ℤ) (f : S) (d : ℕ), 0 < d → f ∈ 𝒜 d →
      Γ(G n, basicOpen 𝒜 f) →+ LocalizedModule.Away f N)
    (hG : IsStandardProjShiftSheaf 𝒜 𝓝 G chartG)
    (phi : M →ₗ[S] N) (chi : ∀ n : ℤ, F n ⟶ G n)
    (hchi : IsStandardProjGradedMap 𝒜 F G chart chartG phi chi)
    (beta : ∀ a b : ℤ, G a ⊗ twist 𝒜 b ⟶ G (a + b))
    (hbeta : IsStandardProjTensorMultiplication 𝒜 G chartG beta)
    (a b : ℤ) : (chi a ▷ twist 𝒜 b) ≫ beta a b = mult a b ≫ chi (a + b) := by
  have : (F a).IsQuasicoherent := shift_quasicoherent 𝒜 𝓜 h𝓜 hsmul F chart hF a
  have : (twist 𝒜 b).IsInvertible := isInvertible_twist 𝒜 b cover
  have : (F a ⊗ twist 𝒜 b).IsQuasicoherent := isQuasicoherent_tensorObj _ _
  apply hom_ext_degreeOne 𝒜 cover
  intro f hf z
  obtain ⟨x, hx⟩ := ((isFreeGenerator_twistPowSection b hf).bijective_tmulSection_right
    (M := F a) le_rfl).surjective z
  let t := (twist 𝒜 b).presheaf.map (homOfLE le_rfl).op (twistPowSection b hf)
  change tmulSection x t = z at hx
  rw [← hx]
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, whiskerRight_app_tmulSection]
  obtain ⟨y, r, hy⟩ := away_exists_fraction f (chart a f 1 (by decide) hf x)
  obtain ⟨v, q, ht⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers f)
    (twistChart 𝒜 b f 1 (by decide) hf t)
  obtain ⟨s, hs⟩ := q.property
  have ht' : ∀ p : basicOpen 𝒜 f,
      (t.1 p : Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) =
        Localization.mk v ⟨f ^ s, pow_mem_primeCompl p s⟩ := by
    intro p
    rw [← twistChart_eval 𝒜 b f 1 (by decide) hf t p, ← ht]
    simp only [fractionEval, IsLocalization.map_mk', RingHom.id_apply]
    rw [Localization.mk_eq_mk']
    congr 1
    exact Subtype.ext hs.symm
  apply (hG.1 (a + b) f 1 (by decide) hf).1
  rw [hbeta a b f hf r s (phi y) v ((chi a).app _ x) t
    (hchi a f 1 (by decide) hf r y x hy) ht',
    hchi (a + b) f 1 (by decide) hf (r + s) (v • y)
      ((mult a b).app _ (tmulSection x t)) (hm a b f hf r s y v x t hy ht'),
    phi.map_smul]

-- The final argument uses only the established twist equations.
attribute [local irreducible] unitIsoTwistZero

set_option linter.unusedVariables false in
/-- On a degree-one covered Proj, all twists are invertible and canonical twist
multiplication is associative and unital. For any graded module, the canonical
fraction multiplication identifies its tensor twists with its shifted sheaves,
unitally, associatively and naturally in every degree-preserving linear map.
The parameter `a` applies the same assertion to `M(a)`; `a = 0` is the stated
comparison for `M`. No finiteness or Noetherian assumption is imposed.

Source: Stacks, constructions.tex, 01MT and 01MS; equations multiply and
multiply-more-generally (blueprint: lem-sfb-standard-proj-twist-tensor).

Proof:
1. The standard opens form a basis. The associated sheaf of each shifted grading
   is quasi-coherent; uniqueness of the chart interface transfers this to `F n`.
2. Descend twist sections to homogeneous fractions. Multiplication of localized
   fractions lands in the required shifted degree, is bilinear, and commutes
   with restrictions. Extend its tensor lift from the standard-open basis and
   descend through module sheafification.
3. The existing degree-one trivializations give invertible twists. Their tensor
   comparison multiplies germs, as one checks on the free local generators.
4. Compare maps out of a tensor on pure sections using sheafification. For the
   iterated tensors, quasi-coherence and the two free twist generators on affine
   degree-one charts reduce to pure triples. Scalar identities give coherence.
5. Associativity at `b,-b` and the unit law make multiplication followed by
   multiplication by the inverse twist an isomorphism. All multiplication maps
   are epic. Tensoring with an invertible twist is faithful, so the same composite
   shows that each multiplication map is monic, hence an isomorphism.
6. On degree-one affine charts, quasi-coherence of the source detects equality
   on sections. The free twist generator reduces naturality to the fraction
   formula and linearity of the given graded map. -/
theorem standardProjTwistTensor
    (cover : ∀ x : Proj 𝒜, ∃ f ∈ 𝒜 1, x ∈ basicOpen 𝒜 f)
    (𝓜 : ℤ → AddSubgroup M) (h𝓜 : DirectSum.IsInternal 𝓜)
    (hsmul : ∀ (k : ℕ) (n : ℤ) (s : S) (y : M),
      s ∈ 𝒜 k → y ∈ 𝓜 n → s • y ∈ 𝓜 (k + n))
    (F : ℤ → (Proj 𝒜).Modules)
    (chart : ∀ (n : ℤ) (f : S) (d : ℕ), 0 < d → f ∈ 𝒜 d →
      Γ(F n, basicOpen 𝒜 f) →+ LocalizedModule.Away f M)
    (hF : IsStandardProjShiftSheaf 𝒜 𝓜 F chart) :
    (∀ n : ℤ, (twist 𝒜 n).IsInvertible) ∧
    (∀ (a b : ℤ) (U : (Proj 𝒜).Opens)
      (s : Γ(twist 𝒜 a, U)) (t : Γ(twist 𝒜 b, U)) (p : U),
      (((twistTensorIso 𝒜 cover a b).hom.app U (tmulSection s t)).1 p :
        Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) =
      (s.1 p : Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) * t.1 p) ∧
    (∀ a : ℤ,
      (unitIsoTwistZero.hom ▷ twist 𝒜 a) ≫ (twistTensorIso 𝒜 cover 0 a).hom ≫
        eqToHom (congrArg (twist 𝒜) (zero_add a)) = (λ_ (twist 𝒜 a)).hom) ∧
    (∀ a : ℤ,
      (twist 𝒜 a ◁ unitIsoTwistZero.hom) ≫ (twistTensorIso 𝒜 cover a 0).hom ≫
        eqToHom (congrArg (twist 𝒜) (add_zero a)) = (ρ_ (twist 𝒜 a)).hom) ∧
    (∀ a b c : ℤ,
      ((twistTensorIso 𝒜 cover a b).hom ▷ twist 𝒜 c) ≫
        (twistTensorIso 𝒜 cover (a + b) c).hom ≫
        eqToHom (congrArg (twist 𝒜) (add_assoc a b c)) =
      (α_ (twist 𝒜 a) (twist 𝒜 b) (twist 𝒜 c)).hom ≫
        (twist 𝒜 a ◁ (twistTensorIso 𝒜 cover b c).hom) ≫
        (twistTensorIso 𝒜 cover a (b + c)).hom) ∧
    ∃ mult : ∀ a b : ℤ, F a ⊗ twist 𝒜 b ⟶ F (a + b),
      IsStandardProjTensorMultiplication 𝒜 F chart mult ∧
      (∀ a b : ℤ, IsIso (mult a b)) ∧
      (∀ a : ℤ, (F a ◁ unitIsoTwistZero.hom) ≫ mult a 0 ≫
        eqToHom (congrArg F (add_zero a)) = (ρ_ (F a)).hom) ∧
      (∀ a b c : ℤ,
        (mult a b ▷ twist 𝒜 c) ≫ mult (a + b) c ≫
          eqToHom (congrArg F (add_assoc a b c)) =
        (α_ (F a) (twist 𝒜 b) (twist 𝒜 c)).hom ≫
          (F a ◁ (twistTensorIso 𝒜 cover b c).hom) ≫ mult a (b + c)) ∧
      (∀ (N : Type u) [AddCommGroup N] [Module S N]
        (𝓝 : ℤ → AddSubgroup N) (G : ℤ → (Proj 𝒜).Modules)
        (chartG : ∀ (n : ℤ) (f : S) (d : ℕ), 0 < d → f ∈ 𝒜 d →
          Γ(G n, basicOpen 𝒜 f) →+ LocalizedModule.Away f N)
        (hG : IsStandardProjShiftSheaf 𝒜 𝓝 G chartG)
        (phi : M →ₗ[S] N)
        (hphi : ∀ (n : ℤ) (y : M), y ∈ 𝓜 n → phi y ∈ 𝓝 n)
        (chi : ∀ n : ℤ, F n ⟶ G n),
        IsStandardProjGradedMap 𝒜 F G chart chartG phi chi →
        ∀ beta : ∀ a b : ℤ, G a ⊗ twist 𝒜 b ⟶ G (a + b),
        IsStandardProjTensorMultiplication 𝒜 G chartG beta →
        ∀ a b : ℤ, (chi a ▷ twist 𝒜 b) ≫ beta a b = mult a b ≫ chi (a + b)) := by
  refine ⟨fun n ↦ isInvertible_twist 𝒜 n cover, twistTensorIso_product 𝒜 cover,
    ?_, ?_, ?_, ?_⟩
  · exact twist_left_unit 𝒜 cover
  · exact twist_right_unit 𝒜 cover
  · exact twist_associativity 𝒜 cover
  · obtain ⟨mult, hm⟩ := multiplication_exists 𝒜 𝓜 hsmul F chart hF
    have hu (a : ℤ) : (F a ◁ unitIsoTwistZero.hom) ≫ mult a 0 ≫
        eqToHom (congrArg F (add_zero a)) = (ρ_ (F a)).hom := by
      apply (cancel_epi (ρ_ (F a)).inv).mp
      rw [Iso.inv_hom_id]
      apply hom_ext _ _ fun U ↦ ?_
      ext x
      change (eqToHom (congrArg F (add_zero a))).app U
        ((mult a 0).app U (Hom.app (F a ◁ unitIsoTwistZero.hom) U
          ((ρ_ (F a)).inv.app U x))) = x
      have hr := rightUnitor_inv_app (M := F a) x
      rw [hr, whiskerLeft_app_tmulSection]
      apply section_ext_standard 𝒜
      intro f d hd hf inc
      rw [← Hom.app_presheaf_map, ← Hom.app_presheaf_map, tmulSection_map,
        ← Hom.app_presheaf_map]
      have he := presheaf_map_unitSectionsEquiv (X := Proj 𝒜) (homOfLE inc)
        (1 : Γ(Proj 𝒜, U))
      change (show (Proj 𝒜).Modules from
        SheafOfModules.unit (Proj 𝒜).ringCatSheaf).presheaf.map
          (homOfLE inc).op (unitSectionsEquiv U 1) = _ at he
      rw [he, map_one]
      apply (hF.1 a f d hd hf).1
      rw [chart_eqToHom 𝒜 F chart (add_zero a), hm, twistChart_unit, one_smul]
    have hassoc (a b c : ℤ) :
        (mult a b ▷ twist 𝒜 c) ≫ mult (a + b) c ≫
          eqToHom (congrArg F (add_assoc a b c)) =
        (α_ (F a) (twist 𝒜 b) (twist 𝒜 c)).hom ≫
          (F a ◁ (twistTensorIso 𝒜 cover b c).hom) ≫ mult a (b + c) := by
      have : (F a).IsQuasicoherent := shift_quasicoherent 𝒜 𝓜 h𝓜 hsmul F chart hF a
      apply twist_triple_hom_ext 𝒜 cover b c
      intro U x t w
      simp only [Hom.comp_app, ConcreteCategory.comp_apply,
        whiskerRight_app_tmulSection, whiskerLeft_app_tmulSection,
        associator_hom_app_tmulSection]
      apply section_ext_standard 𝒜
      intro f d hd hf inc
      rw [← Hom.app_presheaf_map, ← Hom.app_presheaf_map, tmulSection_map,
        ← Hom.app_presheaf_map, tmulSection_map,
        ← Hom.app_presheaf_map, tmulSection_map, ← Hom.app_presheaf_map,
        tmulSection_map]
      apply (hF.1 (a + (b + c)) f d hd hf).1
      rw [chart_eqToHom 𝒜 F chart (add_assoc a b c), hm, hm, hm,
        twistChart_product 𝒜 cover]
      exact (smul_comm _ _ _).trans (mul_smul _ _ _).symm
    refine ⟨mult, ?_, ?_, hu, hassoc, ?_⟩
    · intro a b f hf r s y v x t hx ht
      rw [hm, hx, twistChart_fraction 𝒜 b f 1 (by decide) hf t v s ht]
      change Localization.mk v _ • mk y _ = _
      rw [mk_smul_mk]
      congr 1
      apply Subtype.ext
      simp only [Submonoid.coe_mul, ← pow_add, Nat.add_comm]
    · exact multiplication_isIso (twist 𝒜) unitIsoTwistZero (twistTensorIso 𝒜 cover)
        F mult hu hassoc
    · intro N _ _ 𝓝 G chartG hG phi _hphi chi hchi beta hbeta a b
      apply multiplication_naturality 𝒜 cover 𝓜 h𝓜 hsmul F chart hF mult
        ?_ 𝓝 G chartG hG phi chi hchi beta hbeta a b
      intro a b f hf r s y v x t hx ht
      rw [hm, hx, twistChart_fraction 𝒜 b f 1 (by decide) hf t v s ht]
      change Localization.mk v _ • mk y _ = _
      rw [mk_smul_mk]
      congr 1
      apply Subtype.ext
      simp only [Submonoid.coe_mul, ← pow_add, Nat.add_comm]

end AlgebraicGeometry.Proj
