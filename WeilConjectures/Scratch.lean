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
  have hSm {A : Sheaf Y.smallEtaleTopology (Type (u + 1))} (χ : A ⟶ 𝒮) (c : Λ) (w : St.obj A) :
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
      rw [hA, hZ, prod.lift_fst, prod.lift_snd, ← Category.id_comp (m (-1)), hSm,
        neg_one_smul, neg_add_cancel]
  have L_one : m 1 = 𝟙 𝒮 :=
    ext3 (A := S) _ _ fun w ↦ by
      rw [← Category.id_comp (m 1), hSm, one_smul]
  have L_mul (c d : Λ) : m (c * d) = m d ≫ m c :=
    ext3 (A := S) _ _ fun w ↦ by
      rw [← Category.id_comp (m (c * d)), hSm, hSm, ← Category.id_comp (m d), hSm, mul_smul]
  have L_smul_add (c : Λ) : a ≫ m c = prod.lift (prod.fst ≫ m c) (prod.snd ≫ m c) ≫ a :=
    ext3 (A := S2) _ _ fun w ↦ by
      rw [hSm, ha, hA, prod.lift_fst, prod.lift_snd, hSm, hSm, smul_add]
  have L_add_smul (c d : Λ) : m (c + d) = prod.lift (m c) (m d) ≫ a :=
    ext3 (A := S) _ _ fun w ↦ by
      rw [hA, prod.lift_fst, prod.lift_snd, ← Category.id_comp (m (c + d)), hSm,
        ← Category.id_comp (m c), hSm, ← Category.id_comp (m d), hSm, add_smul]
  have L_smul_zero (c : Λ) : z ≫ m c = z :=
    ext3 (A := S0) _ _ fun w ↦ by
      rw [hSm, ← Category.id_comp z, hZ, smul_zero]
  have L_zero_smul : m 0 = terminal.from 𝒮 ≫ z :=
    ext3 (A := S) _ _ fun w ↦ by
      rw [hZ, ← Category.id_comp (m 0), hSm, zero_smul]
  -- the module structure on the sections of `𝒮`
  let Hv (V : (Y.Etale)ᵒᵖ) : Sheaf Y.smallEtaleTopology (Type (u + 1)) ⥤ Type (u + 1) :=
    sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj V
  let unitV (V : (Y.Etale)ᵒᵖ) : (Hv V).obj (⊤_ _) :=
    (PreservesTerminal.iso (Hv V) ≪≫ Types.terminalIso).inv PUnit.unit
  have hunit (V : (Y.Etale)ᵒᵖ) (t : (Hv V).obj (⊤_ _)) : t = unitV V :=
    @Subsingleton.elim _ ((Hv V).subsingleton_obj_terminal) _ _
  let addV (V : (Y.Etale)ᵒᵖ) (x y : (Hv V).obj 𝒮) : (Hv V).obj 𝒮 :=
    (Hv V).map a (((Hv V).prodEquiv 𝒮 𝒮).symm (x, y))
  let zeroV (V : (Y.Etale)ᵒᵖ) : (Hv V).obj 𝒮 := (Hv V).map z (unitV V)
  let smulV (V : (Y.Etale)ᵒᵖ) (c : Λ) (x : (Hv V).obj 𝒮) : (Hv V).obj 𝒮 := (Hv V).map (m c) x
  have s_assoc (V) (x y w : (Hv V).obj 𝒮) :
      addV V (addV V x y) w = addV V x (addV V y w) := by
    have := congrArg (fun φ ↦ (Hv V).map φ
      (((Hv V).prodEquiv 𝒮 (𝒮 ⨯ 𝒮)).symm (x, ((Hv V).prodEquiv 𝒮 𝒮).symm (y, w)))) L_assoc
    simpa only [Functor.map_comp_apply, Functor.map_prod_lift, Functor.map_fst_prodEquiv_symm,
      Functor.map_snd_prodEquiv_symm] using this
  have s_zero_add (V) (x : (Hv V).obj 𝒮) : addV V (zeroV V) x = x := by
    have := congrArg (fun φ ↦ (Hv V).map φ x) L_zero_add
    simp only [Functor.map_comp_apply, Functor.map_prod_lift, Functor.map_id_apply] at this
    rwa [hunit V ((Hv V).map (terminal.from 𝒮) x)] at this
  have s_add_comm (V) (x y : (Hv V).obj 𝒮) : addV V x y = addV V y x := by
    have := congrArg (fun φ ↦ (Hv V).map φ (((Hv V).prodEquiv 𝒮 𝒮).symm (y, x))) L_add_comm
    simpa only [Functor.map_comp_apply, Functor.map_prod_lift, Functor.map_fst_prodEquiv_symm,
      Functor.map_snd_prodEquiv_symm] using this
  have s_neg (V) (x : (Hv V).obj 𝒮) : addV V (smulV V (-1) x) x = zeroV V := by
    have := congrArg (fun φ ↦ (Hv V).map φ x) L_neg
    simp only [Functor.map_comp_apply, Functor.map_prod_lift, Functor.map_id_apply] at this
    rwa [hunit V ((Hv V).map (terminal.from 𝒮) x)] at this
  have s_one (V) (x : (Hv V).obj 𝒮) : smulV V 1 x = x := by
    have := congrArg (fun φ ↦ (Hv V).map φ x) L_one
    simpa only [Functor.map_id_apply] using this
  have s_mul (V) (c d : Λ) (x : (Hv V).obj 𝒮) : smulV V (c * d) x = smulV V c (smulV V d x) := by
    have := congrArg (fun φ ↦ (Hv V).map φ x) (L_mul c d)
    simpa only [Functor.map_comp_apply] using this
  have s_smul_add (V) (c : Λ) (x y : (Hv V).obj 𝒮) :
      smulV V c (addV V x y) = addV V (smulV V c x) (smulV V c y) := by
    have := congrArg (fun φ ↦ (Hv V).map φ (((Hv V).prodEquiv 𝒮 𝒮).symm (x, y))) (L_smul_add c)
    simpa only [Functor.map_comp_apply, Functor.map_prod_lift, Functor.map_fst_prodEquiv_symm,
      Functor.map_snd_prodEquiv_symm] using this
  have s_add_smul (V) (c d : Λ) (x : (Hv V).obj 𝒮) :
      smulV V (c + d) x = addV V (smulV V c x) (smulV V d x) := by
    have := congrArg (fun φ ↦ (Hv V).map φ x) (L_add_smul c d)
    simpa only [Functor.map_comp_apply, Functor.map_prod_lift] using this
  have s_smul_zero (V) (c : Λ) : smulV V c (zeroV V) = zeroV V := by
    have := congrArg (fun φ ↦ (Hv V).map φ (unitV V)) (L_smul_zero c)
    simpa only [Functor.map_comp_apply] using this
  have s_zero_smul (V) (x : (Hv V).obj 𝒮) : smulV V 0 x = zeroV V := by
    have := congrArg (fun φ ↦ (Hv V).map φ x) L_zero_smul
    simp only [Functor.map_comp_apply] at this
    rwa [hunit V ((Hv V).map (terminal.from 𝒮) x)] at this
  let grp (V : (Y.Etale)ᵒᵖ) : AddCommGroup ((Hv V).obj 𝒮) :=
    letI : Add ((Hv V).obj 𝒮) := ⟨addV V⟩
    letI : Zero ((Hv V).obj 𝒮) := ⟨zeroV V⟩
    letI : Neg ((Hv V).obj 𝒮) := ⟨smulV V (-1)⟩
    { add_assoc := s_assoc V
      zero_add := s_zero_add V
      add_zero x := (s_add_comm V x (zeroV V)).trans (s_zero_add V x)
      add_comm := s_add_comm V
      neg_add_cancel := s_neg V
      nsmul := nsmulRec
      zsmul := zsmulRec }
  let modV (V : (Y.Etale)ᵒᵖ) : @Module Λ ((Hv V).obj 𝒮) _ (grp V).toAddCommMonoid :=
    letI := grp V
    { smul := smulV V
      one_smul := s_one V
      mul_smul := s_mul V
      smul_zero := s_smul_zero V
      smul_add := s_smul_add V
      add_smul := s_add_smul V
      zero_smul := s_zero_smul V }
  -- the presheaf of modules
  have nat_pair {V W : (Y.Etale)ᵒᵖ} (f : V ⟶ W) (x y : (Hv V).obj 𝒮) :
      (𝒮 ⨯ 𝒮).obj.map f (((Hv V).prodEquiv 𝒮 𝒮).symm (x, y)) =
        ((Hv W).prodEquiv 𝒮 𝒮).symm (𝒮.obj.map f x, 𝒮.obj.map f y) := by
    apply ((Hv W).prodEquiv 𝒮 𝒮).injective
    rw [Equiv.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · change (prod.fst : 𝒮 ⨯ 𝒮 ⟶ 𝒮).hom.app W ((𝒮 ⨯ 𝒮).obj.map f _) = _
      rw [NatTrans.naturality_apply]
      exact congrArg (𝒮.obj.map f) ((Hv V).map_fst_prodEquiv_symm x y)
    · change (prod.snd : 𝒮 ⨯ 𝒮 ⟶ 𝒮).hom.app W ((𝒮 ⨯ 𝒮).obj.map f _) = _
      rw [NatTrans.naturality_apply]
      exact congrArg (𝒮.obj.map f) ((Hv V).map_snd_prodEquiv_symm x y)
  have nat_add {V W : (Y.Etale)ᵒᵖ} (f : V ⟶ W) (x y : (Hv V).obj 𝒮) :
      𝒮.obj.map f (addV V x y) = addV W (𝒮.obj.map f x) (𝒮.obj.map f y) := by
    change 𝒮.obj.map f (a.hom.app V _) = a.hom.app W _
    rw [← NatTrans.naturality_apply a.hom f, nat_pair]
  have nat_smul {V W : (Y.Etale)ᵒᵖ} (f : V ⟶ W) (c : Λ) (x : (Hv V).obj 𝒮) :
      𝒮.obj.map f (smulV V c x) = smulV W c (𝒮.obj.map f x) :=
    (NatTrans.naturality_apply (m c).hom f x).symm
  let Fp : (Y.Etale)ᵒᵖ ⥤ ModuleCat.{u + 1} Λ :=
    { obj V := letI := grp V; letI := modV V; ModuleCat.of Λ ((Hv V).obj 𝒮)
      map {V W} f :=
        letI := grp V; letI := modV V; letI := grp W; letI := modV W
        ModuleCat.ofHom
          { toFun := 𝒮.obj.map f
            map_add' := nat_add f
            map_smul' := nat_smul f }
      map_id V := by
        ext x
        change 𝒮.obj.map (𝟙 V) x = x
        simp
      map_comp f g := by
        ext x
        exact 𝒮.obj.map_comp_apply f g x }
  have hFp : Presheaf.IsSheaf Y.smallEtaleTopology Fp :=
    (Presheaf.isSheaf_iff_isSheaf_forget _ Fp (CategoryTheory.forget _)).mpr 𝒮.property
  let F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) := ⟨Fp, hFp⟩
  have hFt : IsFiniteLocallyConstantSheafOfTypes
      ((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj F) := S.property
  have hF := IsFiniteLocallyConstantSheaf.of_forget F hFt
  refine ⟨F, hF, ⟨?_⟩⟩
  sorry

end Construction

end EssSurj

end AlgebraicGeometry
