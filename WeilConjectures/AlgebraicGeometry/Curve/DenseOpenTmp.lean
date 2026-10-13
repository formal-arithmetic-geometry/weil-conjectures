module

public import WeilConjectures.AlgebraicGeometry.Curve.DenseOpen
public import WeilConjectures.ConstructibleSheaf.Simple
public import WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport
public import WeilConjectures.SixFunctors.OpenClosed.AxiomCensus
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Forget

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

lemma nsmul_sheafFiber_eq_zero_of_nsmul_id_eq_zero
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} {r : ℕ} (hG : r • 𝟙 G = 0)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (x : ↥((pointSmallEtale s).sheafFiber.obj G)) : r • x = 0 := by
  have := (pointSmallEtale s).sheafFiber_additive (A := ModuleCat.{u + 1} Λ)
  have h := congrArg (fun φ ↦ φ.hom x) ((pointSmallEtale s).sheafFiber.congr_map hG)
  simpa [Functor.map_nsmul] using h

lemma IsPrimaryTorsionSheaf.of_nsmul_id_eq_zero
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} {r p : ℕ} (hG : r • 𝟙 G = 0)
    (hrp : r ∣ p) : IsPrimaryTorsionSheaf Λ G p := fun Ω _ _ s x ↦ by
  obtain ⟨m, rfl⟩ := hrp
  refine ⟨1, ?_⟩
  rw [pow_one, mul_nsmul, nsmul_sheafFiber_eq_zero_of_nsmul_id_eq_zero hG s x,
    nsmul_zero]

lemma exists_ne_zero_sheafFiber_of_not_isZero
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hz : ¬ IsZero G) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsSepClosed Ω) (s : Spec (.of Ω) ⟶ X)
      (x : ↥((pointSmallEtale s).sheafFiber.obj G)), x ≠ 0 := by
  by_contra! h
  refine hz ((Etale.isZero_iff_stalkZeroLocus_eq_univ G).2
    (Set.eq_univ_of_forall fun _ Ω _ _ s _ ↦ ?_))
  exact @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun a b ↦ by rw [h Ω _ _ s a, h Ω _ _ s b]⟩

lemma eq_zero_of_coprime_of_nsmul {M : Type*} [AddCommGroup M] {a b : ℕ} (hab : a.Coprime b)
    {x : M} (ha : a • x = 0) (hb : b • x = 0) : x = 0 := by
  have h1 := addOrderOf_dvd_of_nsmul_eq_zero ha
  have h2 := addOrderOf_dvd_of_nsmul_eq_zero hb
  exact AddMonoid.addOrderOf_eq_one_iff.1
    ((Nat.coprime_self _).1 ((hab.coprime_dvd_left h1).coprime_dvd_right h2))

lemma IsPrimaryTorsionSheaf.dvd_of_nsmul_id_eq_zero
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} {r p : ℕ} (hr : r.Prime)
    (hG : r • 𝟙 G = 0) (hp : IsPrimaryTorsionSheaf Λ G p) (hz : ¬ IsZero G) : r ∣ p := by
  obtain ⟨Ω, _, _, s, x, hx⟩ := exists_ne_zero_sheafFiber_of_not_isZero hz
  by_contra hrp
  obtain ⟨n, hn⟩ := hp Ω s x
  exact hx (eq_zero_of_coprime_of_nsmul (((Nat.Prime.coprime_iff_not_dvd hr).2 hrp).pow_right n)
    (nsmul_sheafFiber_eq_zero_of_nsmul_id_eq_zero hG s x) hn)

lemma IsTorsionSheafOfInvertibleOrder.of_nsmul_id_eq_zero (S : Scheme.{u})
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} {r : ℕ} (hr : 0 < r)
    (hG : r • 𝟙 G = 0) (hu : IsUnit (r : Γ(S, ⊤))) : IsTorsionSheafOfInvertibleOrder S G where
  exists_isUnit_nsmul_eq_zero _ _ _ s x :=
    ⟨r, hr, hu, nsmul_sheafFiber_eq_zero_of_nsmul_id_eq_zero hG s x⟩

lemma IsTorsionSheafOfInvertibleOrder.isUnit_of_nsmul_id_eq_zero (S : Scheme.{u})
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} {r : ℕ} (hr : r.Prime)
    (hG : r • 𝟙 G = 0) [IsTorsionSheafOfInvertibleOrder S G] (hz : ¬ IsZero G) :
    IsUnit (r : Γ(S, ⊤)) := by
  obtain ⟨Ω, _, _, s, x, hx⟩ := exists_ne_zero_sheafFiber_of_not_isZero hz
  obtain ⟨n, -, hu, hn⟩ :=
    IsTorsionSheafOfInvertibleOrder.exists_isUnit_nsmul_eq_zero (S := S) Ω s x
  by_contra hr'
  have hrn : ¬ r ∣ n := by
    rintro ⟨m, rfl⟩
    exact hr' (isUnit_of_mul_isUnit_left (by simpa using hu))
  exact hx (eq_zero_of_coprime_of_nsmul ((Nat.Prime.coprime_iff_not_dvd hr).2 hrn)
    (nsmul_sheafFiber_eq_zero_of_nsmul_id_eq_zero hG s x) hn)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

open Etale

/-- A subobject of an object killed by `r` is killed by `r`. -/
lemma _root_.CategoryTheory.Preadditive.nsmul_id_eq_zero_of_mono {C : Type*} [Category C]
    [Preadditive C] {G F : C} (ι : G ⟶ F) [Mono ι] {r : ℕ}
    (hF : r • 𝟙 F = 0) : r • 𝟙 G = 0 := by
  rw [← cancel_mono ι, Preadditive.nsmul_comp, Category.id_comp, zero_comp,
    ← Category.comp_id ι, ← Preadditive.comp_nsmul, hF, comp_zero]

/-- A quotient of an object killed by `r` is killed by `r`. -/
lemma _root_.CategoryTheory.Preadditive.nsmul_id_eq_zero_of_epi {C : Type*} [Category C]
    [Preadditive C] {G F : C} (π : F ⟶ G) [Epi π] {r : ℕ}
    (hF : r • 𝟙 F = 0) : r • 𝟙 G = 0 := by
  rw [← cancel_epi π, Preadditive.comp_nsmul, Category.comp_id, comp_zero,
    ← Category.id_comp π, ← Preadditive.nsmul_comp, hF, zero_comp]

/-- Vanishing of positive-degree cohomology of an abelian étale sheaf on a scheme locally of
finite type over an algebraically closed field which vanishes off finitely many closed points,
also after restriction to an open subscheme. -/
theorem Etale.subsingleton_H_upperStar_of_isZero_upperStar {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (U : X.Opens) (hfin : (U : Set X)ᶜ.Finite) (hcl : ∀ x ∉ U, IsClosed ({x} : Set X))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : IsZero ((U.ι)^*[AddCommGrpCat.{u + 1}].obj G)) {W : Scheme.{u}} (a : W ⟶ X)
    [IsOpenImmersion a] (n : ℕ) :
    Subsingleton (Sheaf.H ((a)^*[AddCommGrpCat.{u + 1}].obj G) (n + 1)) := by
  have hinj := a.isOpenEmbedding.injective
  have hcl' : ∀ x ∉ a ⁻¹ᵁ U, IsClosed ({x} : Set W) := fun x hx ↦ by
    have h := (hcl (a x) hx).preimage a.continuous
    rwa [show a.base ⁻¹' {a x} = {x} from Set.ext fun y ↦ by simp [hinj.eq_iff]] at h
  refine Etale.subsingleton_H_of_isZero_upperStar (a ⁻¹ᵁ U)
    (hfin.preimage hinj.injOn) hcl' (fun x hx ↦ ?_) _ ?_ n
  · have := Scheme.isAlgClosed_residueField_of_isClosed (a ≫ f) x (hcl' x hx)
    infer_instance
  · refine (Functor.map_isZero ((a ∣_ U))^*[AddCommGrpCat.{u + 1}] hG).of_iso ?_
    exact ((Etale.upperStarComp AddCommGrpCat.{u + 1} (a ⁻¹ᵁ U).ι a).app G).symm ≪≫
      (Etale.upperStarComp AddCommGrpCat.{u + 1} (a ∣_ U) U.ι ((a ⁻¹ᵁ U).ι ≫ a)
        (by simp)).app G

end AlgebraicGeometry

namespace AlgebraicGeometry

open Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Localisation of the eight assertions to a dense open.** -/
theorem IsCurve.assertions_iff_openImmersionLowerShriek_of_dense [Finite Λ] {k : Type u}
    [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f]
    (r : ℕ) [hr : Fact r.Prime] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsConstructibleSheaf F] (hF : r • 𝟙 F = 0) (U : X.Opens)
    (hU : Dense (U : Set X)) :
    IsCurve.Assertions Λ f F ↔ IsCurve.Assertions Λ f
      ((U.ι)_!open[ModuleCat.{u + 1} Λ].obj ((U.ι)^*[ModuleCat.{u + 1} Λ].obj F)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  have hfin := U.isOpen.finite_compl_of_dense (IsCurve.krullDim_le_one f) hU
  have hcl : ∀ x ∉ U, IsClosed ({x} : Set X) := fun x hx ↦
    U.isOpen.isClosed_singleton_of_dense (IsCurve.krullDim_le_one f) hU hx
  let I := Scheme.IdealSheafData.vanishingIdeal ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩
  let i := I.subschemeι
  have hij : Set.range i.base = (Set.range U.ι.base)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal, Scheme.Opens.range_ι]
    rfl
  have hji : Disjoint (Set.range U.ι.base) (Set.range i.base) := by
    rw [hij]
    exact disjoint_compl_right
  have hS := Etale.shortExact_openClosedShortComplex_moduleCat U.ι i Λ F hij
  set S := Etale.openClosedShortComplex (ModuleCat.{u + 1} Λ) U.ι i
    (disjoint_range_of_range_eq_compl U.ι i hij) F
  have := hS.mono_f
  have := hS.epi_g
  -- the closed complement is a finite discrete curve
  have hnot : ∀ z, i z ∉ U := fun z h ↦ by
    have : i z ∈ Set.range i.base := ⟨z, rfl⟩
    rw [hij] at this
    exact this ⟨⟨_, h⟩, rfl⟩
  have hZT1 : T1Space I.subscheme := ⟨fun z ↦ by
    have h := (hcl _ (hnot z)).preimage i.continuous
    rwa [show i.base ⁻¹' {i z} = {z} from Set.ext fun y ↦ by
      simp [i.isClosedEmbedding.injective.eq_iff]] at h⟩
  have := hfin.to_subtype
  have hZfin : Finite I.subscheme :=
    Finite.of_injective (β := ↥((U : Set X)ᶜ)) (fun z ↦ ⟨i z, hnot z⟩) fun z z' h ↦
      i.isClosedEmbedding.injective (congrArg Subtype.val h)
  have hZdim : topologicalKrullDim I.subscheme ≤ 0 :=
    topologicalKrullDim_zero_of_discreteTopology _
  have : IsCurve (i ≫ f) :=
    { krullDim_le_one := hZdim.trans (by norm_num) }
  have hC : IsCurve.Assertions Λ f S.X₃ :=
    IsCurve.Assertions.lowerStar_of_isFinite Λ (i ≫ f) f i rfl _
      (IsCurve.Assertions.of_topologicalKrullDim_le_zero Λ (i ≫ f) hZdim _)
  have hX₁ : r • 𝟙 S.X₁ = 0 := Preadditive.nsmul_id_eq_zero_of_mono S.f hF
  have hX₃ : r • 𝟙 S.X₃ = 0 := Preadditive.nsmul_id_eq_zero_of_epi S.g hF
  have hzero : IsZero ((U.ι)^*[AddCommGrpCat.{u + 1}].obj
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj S.X₃)) :=
    (Functor.map_isZero _ (Etale.isZero_upperStar_lowerStar_of_disjoint_range _ U.ι i hji
      _)).of_iso (asIso (upperStarForget₂Comparison Λ U.ι S.X₃))
  have : IsNoetherianRing Λ := inferInstance
  refine ⟨fun hFa ↦ ?_, fun h₁ ↦ IsCurve.Assertions.of_shortExact Λ f hS h₁ hC⟩
  refine IsCurve.Assertions.of_shortExact_of_subsingleton hS hFa hC
    (fun q ↦ ?_) (fun a _ q ↦ Etale.subsingleton_H_upperStar_of_isZero_upperStar f U hfin hcl
      _ hzero a q) (fun p hp ↦ ?_) (fun _ ↦ ⟨(‹_› : Scheme.IsConstructibleSheaf F), ?_⟩)
    (fun h ↦ ?_)
  · refine Etale.subsingleton_H_of_isZero_upperStar U hfin hcl (fun x hx ↦ ?_) _ hzero q
    have := Scheme.isAlgClosed_residueField_of_isClosed f x (hcl x hx)
    infer_instance
  · by_cases hz : IsZero S.X₁
    · exact .inr hz
    · exact .inl (Scheme.IsPrimaryTorsionSheaf.of_nsmul_id_eq_zero hF
        (Scheme.IsPrimaryTorsionSheaf.dvd_of_nsmul_id_eq_zero hr.out hX₁ hp hz))
  · have : Scheme.IsConstructibleSheaf ((i)^*[ModuleCat.{u + 1} Λ].obj F) :=
      Scheme.IsConstructibleSheaf.upperStar i F
    exact Scheme.IsConstructibleSheaf.lowerStar_of_isClosedImmersion U.ι i hij _
  · by_cases hz : IsZero S.X₁
    · exact .inr hz
    · have hu := Scheme.IsTorsionSheafOfInvertibleOrder.isUnit_of_nsmul_id_eq_zero
        (Spec (.of k)) hr.out hX₁ hz
      exact .inl ⟨Scheme.IsTorsionSheafOfInvertibleOrder.of_nsmul_id_eq_zero _
        hr.out.pos hF hu, Scheme.IsTorsionSheafOfInvertibleOrder.of_nsmul_id_eq_zero _
        hr.out.pos hX₃ hu⟩

end AlgebraicGeometry
