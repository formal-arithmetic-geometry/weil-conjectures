module
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalSystems
public import WeilConjectures.ConstructibleSheaf.OfForget

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory

/-- A functor to types preserving a binary product sends it to the cartesian product. -/
lemma Functor.bijective_map_prod_fst_snd {C : Type*} [Category* C] (H : C ⥤ Type _)
    (A B : C) [HasBinaryProduct A B] [PreservesLimit (pair A B) H] :
    Function.Bijective (fun z : H.obj (A ⨯ B) ↦ (H.map prod.fst z, H.map prod.snd z)) := by
  have : (fun z : H.obj (A ⨯ B) ↦ (H.map prod.fst z, H.map prod.snd z)) =
      ((PreservesLimitPair.iso H A B).hom ≫ (Types.binaryProductIso _ _).hom) := by
    funext z
    ext
    · rw [ConcreteCategory.comp_apply, Types.binaryProductIso_hom_comp_fst_apply,
        ← ConcreteCategory.comp_apply, PreservesLimitPair.iso_hom, prodComparison_fst]
    · rw [ConcreteCategory.comp_apply, Types.binaryProductIso_hom_comp_snd_apply,
        ← ConcreteCategory.comp_apply, PreservesLimitPair.iso_hom, prodComparison_snd]
  rw [this]
  exact (isIso_iff_bijective _).mp inferInstance

section PairAux

variable {C : Type*} [Category* C] (H : C ⥤ Type _)

/-- The bijection `H(A ⨯ B) ≃ H(A) × H(B)` for a functor to types preserving the product. -/
noncomputable def Functor.prodEquiv (A B : C) [HasBinaryProduct A B] [PreservesLimit (pair A B) H] :
    H.obj (A ⨯ B) ≃ H.obj A × H.obj B :=
  Equiv.ofBijective _ (H.bijective_map_prod_fst_snd A B)

variable {H} {A B : C} [HasBinaryProduct A B] [PreservesLimit (pair A B) H]

@[simp]
lemma Functor.map_fst_prodEquiv_symm (u : H.obj A) (v : H.obj B) :
    H.map prod.fst ((H.prodEquiv A B).symm (u, v)) = u :=
  congrArg _root_.Prod.fst ((H.prodEquiv A B).apply_symm_apply (u, v))

@[simp]
lemma Functor.map_snd_prodEquiv_symm (u : H.obj A) (v : H.obj B) :
    H.map prod.snd ((H.prodEquiv A B).symm (u, v)) = v :=
  congrArg _root_.Prod.snd ((H.prodEquiv A B).apply_symm_apply (u, v))

@[simp]
lemma Functor.map_prod_lift {X : C} (f : X ⟶ A) (g : X ⟶ B) (t : H.obj X) :
    H.map (prod.lift f g) t = (H.prodEquiv A B).symm (H.map f t, H.map g t) := by
  apply (H.prodEquiv A B).injective
  rw [Equiv.apply_symm_apply]
  change (H.map prod.fst (H.map (prod.lift f g) t), H.map prod.snd (H.map (prod.lift f g) t)) = _
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, prod.lift_fst,
    prod.lift_snd]

lemma Functor.subsingleton_obj_terminal [HasTerminal C] [PreservesLimit (Functor.empty.{0} C) H] :
    Subsingleton (H.obj (⊤_ C)) :=
  (PreservesTerminal.iso H ≪≫ Types.terminalIso).toEquiv.subsingleton

end PairAux

end CategoryTheory

namespace AlgebraicGeometry

variable {Y : Scheme.{u}}


/-- Products of sheaves of sets trivialised over `U` are trivialised over `U`. -/
lemma Scheme.isConstant_over_prod (U : Y.Etale) {S T : Sheaf Y.smallEtaleTopology (Type (u + 1))}
    [(S.over U).IsConstant (Y.smallEtaleTopology.over U)]
    [(T.over U).IsConstant (Y.smallEtaleTopology.over U)] :
    ((S ⨯ T).over U).IsConstant (Y.smallEtaleTopology.over U) := by
  obtain ⟨X, ⟨eX⟩⟩ := Sheaf.mem_essImage_of_isConstant _ (S.over U)
  obtain ⟨X', ⟨eX'⟩⟩ := Sheaf.mem_essImage_of_isConstant _ (T.over U)
  exact Sheaf.isConstant_of_iso _
    (PreservesLimitPair.iso (Y.smallEtaleTopology.overPullback (Type (u + 1)) U) S T ≪≫
      prod.mapIso eX.symm eX'.symm ≪≫
      (PreservesLimitPair.iso (constantSheaf (Y.smallEtaleTopology.over U) (Type (u + 1)))
        X X').symm)

/-- The terminal sheaf of sets is trivialised over every `U`. -/
lemma Scheme.isConstant_over_terminal (U : Y.Etale) :
    ((⊤_ Sheaf Y.smallEtaleTopology (Type (u + 1))).over U).IsConstant
      (Y.smallEtaleTopology.over U) :=
  Sheaf.isConstant_of_iso _
    (PreservesTerminal.iso (Y.smallEtaleTopology.overPullback (Type (u + 1)) U) ≪≫
      (PreservesTerminal.iso (constantSheaf (Y.smallEtaleTopology.over U) (Type (u + 1)))).symm)

/-- A finite discrete `G`-set with open stabilisers has a continuous action. -/
lemma continuousSMul_of_isOpen_stabilizer (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {X : Type*} [TopologicalSpace X] [DiscreteTopology X] [MulAction G X]
    (h : ∀ x : X, IsOpen {g : G | g • x = x}) : ContinuousSMul G X := by
  refine ⟨continuous_discrete_rng.mpr fun y ↦ ?_⟩
  have : (fun p : G × X ↦ p.1 • p.2) ⁻¹' {y} = ⋃ x : X, {g : G | g • x = y} ×ˢ {x} := by
    ext ⟨g, x⟩
    simp
  rw [this]
  refine isOpen_iUnion fun x ↦ (?_ : IsOpen _).prod (isOpen_discrete _)
  by_cases hx : ∃ g₀ : G, g₀ • x = y
  · obtain ⟨g₀, rfl⟩ := hx
    have : {g : G | g • x = g₀ • x} = (fun g ↦ g₀⁻¹ * g) ⁻¹' {g | g • x = x} := by
      ext g
      simp [mul_smul, inv_smul_eq_iff]
    rw [this]
    exact (h x).preimage (continuous_const_mul _)
  · push Not at hx
    convert isOpen_empty
    ext g
    simpa using hx g

section EssSurj

variable [ConnectedSpace Y] {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((Scheme.FiniteEtale.fiber s).obj P)]
  [PreGaloisCategory.IsFundamentalGroup (Scheme.FiniteEtale.fiber s) G]

open scoped FintypeCatDiscrete

/-- **Finite continuous `G`-sets are stalks.** Every finite set with a continuous action of the
fundamental group `G` is, equivariantly, the stalk at `s` of a finite locally constant sheaf of
sets. -/
lemma Scheme.FiniteLocallyConstant.exists_stalkEquiv {X : Type (u + 1)} [Finite X]
    [MulAction G X] (hX : ∀ x : X, IsOpen {g : G | g • x = x}) :
    ∃ (S : Y.FiniteLocallyConstant) (e : (Scheme.pointSmallEtale s).sheafFiber.obj S.obj ≃ X),
      ∀ g x, e (Scheme.FiniteLocallyConstant.galoisSMul s G g S x) = g • e x := by
  classical
  let eq2 : X ≃ ULift.{u} (Fin (Nat.card X)) := (Finite.equivFin X).trans Equiv.ulift.symm
  let : MulAction G (ULift.{u} (Fin (Nat.card X))) := eq2.symm.mulAction G
  have heq (g : G) (y : ULift.{u} (Fin (Nat.card X))) : eq2.symm (g • y) = g • eq2.symm y := by
    change eq2.symm (eq2 (g • eq2.symm y)) = _
    rw [Equiv.symm_apply_apply]
  let X0 : FintypeCat.{u} := FintypeCat.of (ULift.{u} (Fin (Nat.card X)))
  let XA : Action FintypeCat.{u} G := Action.FintypeCat.ofMulAction G X0
  have hcont : XA.IsContinuous := by
    let : DiscreteTopology ((CategoryTheory.forget₂ _ TopCat).obj XA) := ⟨rfl⟩
    refine continuousSMul_of_isOpen_stabilizer G fun y ↦ ?_
    convert hX (eq2.symm (show ULift.{u} (Fin (Nat.card X)) from y)) using 1
    ext g
    change g • (show ULift.{u} (Fin (Nat.card X)) from y) = y ↔
      g • eq2.symm (show ULift.{u} (Fin (Nat.card X)) from y) = eq2.symm y
    rw [← heq, eq2.symm.injective.eq_iff]
  let XC : ContAction FintypeCat.{u} G := ⟨XA, hcont⟩
  let A := Scheme.FiniteEtale.equivalenceContAction s G
  let E := Scheme.FiniteEtale.equivalenceFiniteLocallyConstant Y
  let P := A.inverse.obj XC
  let S := E.functor.obj P
  let iP : A.functor.obj P ≅ XC := A.counitIso.app XC
  let jP : E.inverse.obj S ≅ P := (E.unitIso.app P).symm
  let f1 : (Scheme.FiniteEtale.fiber s).obj (E.inverse.obj S) ≃
      (Scheme.FiniteEtale.fiber s).obj P :=
    FintypeCat.equivEquivIso.symm ((Scheme.FiniteEtale.fiber s).mapIso jP)
  let f2 : (Scheme.FiniteEtale.fiber s).obj P ≃ X0 :=
    FintypeCat.equivEquivIso.symm ((ObjectProperty.ι _ ⋙ Action.forget _ _).mapIso iP)
  refine ⟨S, (stalkEquiv s S).trans (Equiv.ulift.trans (f1.trans (f2.trans eq2.symm))),
    fun g x ↦ ?_⟩
  simp only [Equiv.trans_apply, galoisSMul, Equiv.apply_symm_apply]
  rw [← heq]
  congr 1
  let a : (Scheme.FiniteEtale.fiber s).obj (E.inverse.obj S) := (stalkEquiv s S x).down
  have h1 : f1 (g • a) = g • f1 a := PreGaloisCategory.IsNaturalSMul.naturality g jP.hom a
  have h2 : f2 (g • f1 a) = g • f2 (f1 a) :=
    ConcreteCategory.congr_hom (iP.hom.hom.comm g) (f1 a)
  exact (congrArg f2 h1).trans h2

section Construction

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

omit [ConnectedSpace Y] in
/-- A product of finite sheaves of sets is finite. -/
lemma Scheme.isFiniteSheaf_prod {S T : Sheaf Y.smallEtaleTopology (Type (u + 1))}
    (hS : Scheme.IsFiniteSheaf S) (hT : Scheme.IsFiniteSheaf T) :
    Scheme.IsFiniteSheaf (S ⨯ T) where
  isFinitelyGenerated_sheafFiber Ω _ _ s := by
    have hS' := hS.isFinitelyGenerated_sheafFiber Ω s
    have hT' := hT.isFinitelyGenerated_sheafFiber Ω s
    rw [ConcreteCategory.isFinitelyGenerated_iff_finite] at hS' hT' ⊢
    have : AB5OfSize.{u, u} (Type (u + 1)) := AB5OfSize_shrink.{u, u, u + 1, u + 1} _
    exact Finite.of_injective _ ((pointSmallEtale s).sheafFiber.bijective_map_prod_fst_snd S T).1

omit [ConnectedSpace Y] in
/-- The terminal sheaf of sets is finite. -/
lemma Scheme.isFiniteSheaf_terminal :
    Scheme.IsFiniteSheaf (⊤_ Sheaf Y.smallEtaleTopology (Type (u + 1))) where
  isFinitelyGenerated_sheafFiber Ω _ _ s := by
    rw [ConcreteCategory.isFinitelyGenerated_iff_finite]
    have : AB5OfSize.{u, u} (Type (u + 1)) := AB5OfSize_shrink.{u, u, u + 1, u + 1} _
    exact Finite.of_equiv _
      (PreservesTerminal.iso (pointSmallEtale s).sheafFiber ≪≫ Types.terminalIso).toEquiv.symm

/-- **Finite continuous representations are stalks.** -/
theorem Scheme.exists_galoisRepFunctor_obj_iso (M : Rep.{u + 1} Λ G)
    (hM : Rep.IsFiniteContinuous M) :
    ∃ (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (hF : IsFiniteLocallyConstantSheaf F),
      Nonempty ((Scheme.galoisRepFunctor (s := s) (G := G) (Λ := Λ)).obj ⟨F, hF⟩ ≅ M) := by
  classical
  have : Finite M.V := hM.1
  let : MulAction G M.V :=
    { smul g x := M.ρ g x
      one_smul x := by
        change M.ρ 1 x = x
        simp
      mul_smul g h x := by
        change M.ρ (g * h) x = M.ρ g (M.ρ h x)
        simp [map_mul] }
  obtain ⟨S, e, he⟩ := Scheme.FiniteLocallyConstant.exists_stalkEquiv s G (X := M.V) hM.2
  let 𝒮 := S.obj
  obtain ⟨⟨𝒰, h𝒰⟩, hfin⟩ := S.property
  have triv2 : ∀ i, ((𝒮 ⨯ 𝒮).over (𝒰.etalePrecoverageToEtale i)).IsConstant
      (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i)) := fun i ↦ by
    have := h𝒰 i
    exact Scheme.isConstant_over_prod _
  have triv3 : ∀ i, ((𝒮 ⨯ (𝒮 ⨯ 𝒮)).over (𝒰.etalePrecoverageToEtale i)).IsConstant
      (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i)) := fun i ↦ by
    have := h𝒰 i
    have := triv2 i
    exact Scheme.isConstant_over_prod _
  let S2 : Y.FiniteLocallyConstant := ⟨𝒮 ⨯ 𝒮, ⟨𝒰, triv2⟩, Scheme.isFiniteSheaf_prod hfin hfin⟩
  let S3 : Y.FiniteLocallyConstant :=
    ⟨𝒮 ⨯ (𝒮 ⨯ 𝒮), ⟨𝒰, triv3⟩, Scheme.isFiniteSheaf_prod hfin (Scheme.isFiniteSheaf_prod hfin hfin)⟩
  let S0 : Y.FiniteLocallyConstant :=
    ⟨⊤_ _, ⟨𝒰, fun i ↦ Scheme.isConstant_over_terminal _⟩, Scheme.isFiniteSheaf_terminal⟩
  have : AB5OfSize.{u, u} (Type (u + 1)) := AB5OfSize_shrink.{u, u, u + 1, u + 1} _
  let St := (Scheme.pointSmallEtale s).sheafFiber (A := Type (u + 1))
  have he' (g : G) (x : M.V) :
      Scheme.FiniteLocallyConstant.galoisSMul s G g S (e.symm x) = e.symm (M.ρ g x) := by
    apply e.injective
    rw [he, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl
  have hfst (g : G) (w : St.obj (𝒮 ⨯ 𝒮)) :
      St.map prod.fst (Scheme.FiniteLocallyConstant.galoisSMul s G g S2 w) =
        Scheme.FiniteLocallyConstant.galoisSMul s G g S (St.map prod.fst w) :=
    Scheme.FiniteLocallyConstant.galoisSMul_naturality s G g (S := S2) (S' := S)
      (ObjectProperty.homMk prod.fst) w
  have hsnd (g : G) (w : St.obj (𝒮 ⨯ 𝒮)) :
      St.map prod.snd (Scheme.FiniteLocallyConstant.galoisSMul s G g S2 w) =
        Scheme.FiniteLocallyConstant.galoisSMul s G g S (St.map prod.snd w) :=
    Scheme.FiniteLocallyConstant.galoisSMul_naturality s G g (S := S2) (S' := S)
      (ObjectProperty.homMk prod.snd) w
  -- the addition, scalar multiplications and zero of `𝒮`, from those of the stalk `M`
  obtain ⟨ψa, hψa⟩ := Scheme.FiniteLocallyConstant.exists_hom_of_equivariant s G (S := S2)
    (S' := S) (fun w ↦ e.symm (e (St.map prod.fst w) + e (St.map prod.snd w))) fun g w ↦ by
      erw [hfst g w, hsnd g w, he, he, he', LinearMap.map_add]
      rfl
  have hm : ∀ c : Λ, ∃ ψ : S ⟶ S, ∀ w, St.map ψ.hom w = e.symm (c • e w) := fun c ↦
    Scheme.FiniteLocallyConstant.exists_hom_of_equivariant s G (fun w ↦ e.symm (c • e w))
      fun g w ↦ by
        simp only [he, he', map_smul]
        rfl
  choose ψm hψm using hm
  obtain ⟨ψz, hψz⟩ := Scheme.FiniteLocallyConstant.exists_hom_of_equivariant s G (S := S0)
    (S' := S) (fun _ ↦ e.symm 0) fun g w ↦ by rw [he', LinearMap.map_zero]
  let a : 𝒮 ⨯ 𝒮 ⟶ 𝒮 := ψa.hom
  let m (c : Λ) : 𝒮 ⟶ 𝒮 := (ψm c).hom
  let z : ⊤_ _ ⟶ 𝒮 := ψz.hom
  have ha (u : St.obj (𝒮 ⨯ 𝒮)) :
      e (St.map a u) = e (St.map prod.fst u) + e (St.map prod.snd u) := by
    rw [hψa]
    exact e.apply_symm_apply _
  have hmc (c : Λ) (x : St.obj 𝒮) : e (St.map (m c) x) = c • e x := by
    rw [hψm]
    simp
  have hz (x : St.obj (⊤_ _)) : e (St.map z x) = 0 := by
    rw [hψz]
    simp
  have hA {A : Sheaf Y.smallEtaleTopology (Type (u + 1))} (χ : A ⟶ 𝒮 ⨯ 𝒮) (w : St.obj A) :
      e (St.map (χ ≫ a) w) = e (St.map (χ ≫ prod.fst) w) + e (St.map (χ ≫ prod.snd) w) := by
    rw [Functor.map_comp_apply, ha, Functor.map_comp_apply, Functor.map_comp_apply]
  have hM {A : Sheaf Y.smallEtaleTopology (Type (u + 1))} (χ : A ⟶ 𝒮) (c : Λ) (w : St.obj A) :
      e (St.map (χ ≫ m c) w) = c • e (St.map χ w) := by
    rw [Functor.map_comp_apply, hmc]
  have hZ {A : Sheaf Y.smallEtaleTopology (Type (u + 1))} (χ : A ⟶ ⊤_ _) (w : St.obj A) :
      e (St.map (χ ≫ z) w) = 0 := by
    rw [Functor.map_comp_apply, hz]
  have ext3 {A : Y.FiniteLocallyConstant} (φ ψ : A.obj ⟶ 𝒮)
      (h : ∀ w, e (St.map φ w) = e (St.map ψ w)) : φ = ψ :=
    congrArg (·.hom) (Scheme.FiniteLocallyConstant.hom_ext_of_sheafFiber s
      (φ := (ObjectProperty.homMk φ : A ⟶ S)) (ψ := ObjectProperty.homMk ψ)
      fun w ↦ e.injective (h w))
  -- the module laws, as identities of morphisms of sheaves
  have L_assoc : (prod.lift (prod.lift prod.fst (prod.snd ≫ prod.fst) ≫ a)
      (prod.snd ≫ prod.snd) ≫ a : 𝒮 ⨯ (𝒮 ⨯ 𝒮) ⟶ 𝒮) = prod.lift prod.fst (prod.snd ≫ a) ≫ a :=
    ext3 (A := S3) _ _ fun w ↦ by
      simp only [hA, prod.lift_fst, prod.lift_snd, add_assoc]
  have L_zero_add : prod.lift (terminal.from 𝒮 ≫ z) (𝟙 𝒮) ≫ a = 𝟙 𝒮 :=
    ext3 (A := S) _ _ fun w ↦ by
      simp only [hA, hZ, prod.lift_fst, prod.lift_snd, zero_add]
  have L_add_comm : prod.lift prod.snd prod.fst ≫ a = a :=
    ext3 (A := S2) _ _ fun w ↦ by
      rw [hA, ha, prod.lift_fst, prod.lift_snd, add_comm]
  have L_neg : prod.lift (m (-1)) (𝟙 𝒮) ≫ a = terminal.from 𝒮 ≫ z :=
    ext3 (A := S) _ _ fun w ↦ by
      rw [hA, hZ, prod.lift_fst, prod.lift_snd, ← Category.id_comp (m (-1)), hM,
        neg_one_smul, neg_add_cancel]
  have L_one : m 1 = 𝟙 𝒮 :=
    ext3 (A := S) _ _ fun w ↦ by
      rw [← Category.id_comp (m 1), hM, one_smul]
  have L_mul (c d : Λ) : m (c * d) = m d ≫ m c :=
    ext3 (A := S) _ _ fun w ↦ by
      rw [← Category.id_comp (m (c * d)), hM, hM, ← Category.id_comp (m d), hM, mul_smul]
  have L_smul_add (c : Λ) : a ≫ m c = prod.lift (prod.fst ≫ m c) (prod.snd ≫ m c) ≫ a :=
    ext3 (A := S2) _ _ fun w ↦ by
      rw [hM, ha, hA, prod.lift_fst, prod.lift_snd, hM, hM, smul_add]
  have L_add_smul (c d : Λ) : m (c + d) = prod.lift (m c) (m d) ≫ a :=
    ext3 (A := S) _ _ fun w ↦ by
      rw [hA, prod.lift_fst, prod.lift_snd, ← Category.id_comp (m (c + d)), hM,
        ← Category.id_comp (m c), hM, ← Category.id_comp (m d), hM, add_smul]
  have L_smul_zero (c : Λ) : z ≫ m c = z :=
    ext3 (A := S0) _ _ fun w ↦ by
      rw [hM, ← Category.id_comp z, hZ, smul_zero]
  have L_zero_smul : m 0 = terminal.from 𝒮 ≫ z :=
    ext3 (A := S) _ _ fun w ↦ by
      rw [hZ, ← Category.id_comp (m 0), hM, zero_smul]
  sorry

end Construction

end EssSurj

end AlgebraicGeometry
