# etale_limit_finite_cech_complex_colimit

## Reason

The returned arbitrary-data colimit declaration is false. In a singleton constant
nonzero Čech diagram, its identity-map equation follows from functoriality, its
κ equation is reflexive, and its leg equation only gives a name to a zero leg.
Replace it with an interface that fixes the descended covering and nerves and
prescribes all transition and cocone-leg maps by coefficient adjunction units.
The item theorem and its direct importer keep their existing signatures.

## Old

Verbatim prior arbitrary-data colimit signature:

```lean
theorem finite_cech_stage_data_is_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G) (hL : IsColimit L)
    (U : c.pt.Etale) [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    (K : Type (u + 1)) [Finite K] (V : K → c.pt.Etale) (f : ∀ k, V k ⟶ U)
    (hV : ∀ k, CompactSpace (V k).left ∧ QuasiSeparatedSpace (V k).left)
    (hf : Sieve.ofArrows V f ∈ c.pt.smallEtaleTopology U)
    (i₀ : I) (A : {j : I // i₀ ≤ j} ⥤ CochainComplex AddCommGrpCat.{u + 1} ℕ)
    (Uj : ∀ j : {j : I // i₀ ≤ j}, (D.obj (op j.val)).Etale)
    (Vj : ∀ j : {j : I // i₀ ≤ j}, K → (D.obj (op j.val)).Etale)
    (fj : ∀ (j : {j : I // i₀ ≤ j}) (k : K), Vj j k ⟶ Uj j)
    (_eA : ∀ j : {j : I // i₀ ≤ j}, A.obj j ≅
      (cechComplexFunctor (fun k : K ↦ Over.mk (fj j k))).obj
        ((Over.forget (Uj j)).op ⋙ (F j.val).obj))
    (cA : Cocone A)
    (_eK : cA.pt ≅ (cechComplexFunctor (fun k : K ↦ Over.mk (f k))).obj
      ((Over.forget U).op ⋙ L.pt.obj))
    (κ : ∀ j : {j : I // i₀ ≤ j}, A.obj j ⟶ cA.pt)
    (hA_map : ∀ (j : {j : I // i₀ ≤ j}),
      A.map (𝟙 j) ≫ (_eA j).hom = (_eA j).hom)
    (hcA_ι : ∀ j : {j : I // i₀ ≤ j}, cA.ι.app j = κ j)
    (hκ_desc : ∀ j : {j : I // i₀ ≤ j}, κ j ≫ _eK.hom = κ j ≫ _eK.hom)
    (hcover : ∀ j : {j : I // i₀ ≤ j},
      Sieve.ofArrows (Vj j) (fj j) ∈ (D.obj (op j.val)).smallEtaleTopology (Uj j)) :
    Nonempty (IsColimit cA)
```

Verbatim prior stage-data signature:

```lean
theorem exists_etale_limit_finite_cech_stage_data
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G) (hL : IsColimit L)
    (U : c.pt.Etale) [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    (K : Type (u + 1)) [Finite K] (V : K → c.pt.Etale) (f : ∀ k, V k ⟶ U)
    (hV : ∀ k, CompactSpace (V k).left ∧ QuasiSeparatedSpace (V k).left)
    (hf : Sieve.ofArrows V f ∈ c.pt.smallEtaleTopology U) :
    ∃ (i₀ : I) (A : {j : I // i₀ ≤ j} ⥤ CochainComplex AddCommGrpCat.{u + 1} ℕ)
      (Uj : ∀ j : {j : I // i₀ ≤ j}, (D.obj (op j.val)).Etale)
      (Vj : ∀ j : {j : I // i₀ ≤ j}, K → (D.obj (op j.val)).Etale)
      (fj : ∀ (j : {j : I // i₀ ≤ j}) (k : K), Vj j k ⟶ Uj j)
      (eA : ∀ j : {j : I // i₀ ≤ j}, A.obj j ≅
        (cechComplexFunctor (fun k : K ↦ Over.mk (fj j k))).obj
          ((Over.forget (Uj j)).op ⋙ (F j.val).obj))
      (cA : Cocone A)
      (eK : cA.pt ≅ (cechComplexFunctor (fun k : K ↦ Over.mk (f k))).obj
        ((Over.forget U).op ⋙ L.pt.obj))
      (κ : ∀ j : {j : I // i₀ ≤ j}, A.obj j ⟶ cA.pt)
      (hA_map : ∀ (j : {j : I // i₀ ≤ j}),
        A.map (𝟙 j) ≫ (eA j).hom = (eA j).hom)
      (hcA_ι : ∀ j : {j : I // i₀ ≤ j}, cA.ι.app j = κ j)
      (hκ_desc : ∀ j : {j : I // i₀ ≤ j},
        κ j ≫ eK.hom = κ j ≫ eK.hom),
      (∀ j : {j : I // i₀ ≤ j},
        Sieve.ofArrows (Vj j) (fj j) ∈
          (D.obj (op j.val)).smallEtaleTopology (Uj j)) ∧ True
```

## New

Exact corrected colimit signature, including all construction and canonical-map equations:

```lean
theorem finite_cech_stage_data_is_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G) (hL : IsColimit L)
    (U : c.pt.Etale) [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    (K : Type (u + 1)) [Finite K] (V : K → c.pt.Etale) (f : ∀ k, V k ⟶ U)
    (hV : ∀ k, CompactSpace (V k).left ∧ QuasiSeparatedSpace (V k).left)
    (hf : Sieve.ofArrows V f ∈ c.pt.smallEtaleTopology U)
    (i₀ : I) (U₀ : (D.obj (op i₀)).Etale)
    (V₀ : K → (D.obj (op i₀)).Etale) (f₀ : ∀ k, V₀ k ⟶ U₀)
    (eU : (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj U₀ ≅ U)
    (eV : ∀ k,
      (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj (V₀ k) ≅ V k) :
    let J := {j : I // i₀ ≤ j}
    let B := fun j : J ↦
      MorphismProperty.Over.pullback @Etale ⊤ (D.map (homOfLE j.property).op)
    let Blim := MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))
    let Uj := fun j : J ↦ (B j).obj U₀
    let Vj := fun (j : J) (k : K) ↦ (B j).obj (V₀ k)
    let fj := fun (j : J) (k : K) ↦ (B j).map (f₀ k)
    let W₀ := fun (n : ℕ) (t : Fin (n + 1) → K) ↦
      (∏ᶜ fun a ↦ Over.mk (f₀ (t a))).left
    let pr₀ := fun (n : ℕ) (t : Fin (n + 1) → K) (a : Fin (n + 1)) ↦
      (Pi.π (fun a ↦ Over.mk (f₀ (t a))) a).left
    let Wj := fun (j : J) (n : ℕ) (t : Fin (n + 1) → K) ↦ (B j).obj (W₀ n t)
    let Wlim := fun (n : ℕ) (t : Fin (n + 1) → K) ↦ Blim.obj (W₀ n t)
    let Nj := fun (j : J) (n : ℕ) (t : Fin (n + 1) → K) ↦
      (∏ᶜ fun a ↦ Over.mk (fj j (t a))).left
    let Nlim := fun (n : ℕ) (t : Fin (n + 1) → K) ↦
      (∏ᶜ fun a ↦ Over.mk (f (t a))).left
    let Pj := fun (j : J) (n : ℕ) ↦
      fun t : Fin (n + 1) → K ↦ (F j.val).obj.obj (op (Nj j n t))
    let Plim := fun (n : ℕ) ↦
      fun t : Fin (n + 1) → K ↦ L.pt.obj.obj (op (Nlim n t))
    ∀ (A : J ⥤ CochainComplex AddCommGrpCat.{u + 1} ℕ)
      (eA : ∀ j : J, A.obj j ≅
        (cechComplexFunctor (fun k : K ↦ Over.mk (fj j k))).obj
          ((Over.forget (Uj j)).op ⋙ (F j.val).obj))
      (cA : Cocone A)
      (eK : cA.pt ≅ (cechComplexFunctor (fun k : K ↦ Over.mk (f k))).obj
        ((Over.forget U).op ⋙ L.pt.obj))
      (eNj : ∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K),
        Wj j n t ≅ Nj j n t)
      (eNlim : ∀ (n : ℕ) (t : Fin (n + 1) → K), Wlim n t ≅ Nlim n t)
      (γ : ∀ (j k : J) (a : j ⟶ k) (n : ℕ) (t : Fin (n + 1) → K),
        (MorphismProperty.Over.pullback @Etale ⊤
          (D.map (show j.val ⟶ k.val from a).op)).obj (Wj j n t) ≅ Wj k n t)
      (δ : ∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K),
        (MorphismProperty.Over.pullback @Etale ⊤
          (c.π.app (op j.val))).obj (Wj j n t) ≅ Wlim n t),
      (CompactSpace U₀.left ∧ QuasiSeparatedSpace U₀.left) ∧
      (∀ k, CompactSpace (V₀ k).left ∧ QuasiSeparatedSpace (V₀ k).left) ∧
      (∀ k, Blim.map (f₀ k) ≫ eU.hom = (eV k).hom ≫ f k) ∧
      (∀ j : J, Sieve.ofArrows (Vj j) (fj j) ∈
        (D.obj (op j.val)).smallEtaleTopology (Uj j)) ∧
      (∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K) (a : Fin (n + 1)),
        (eNj j n t).hom ≫ (Pi.π (fun a ↦ Over.mk (fj j (t a))) a).left =
          (B j).map (pr₀ n t a)) ∧
      (∀ (n : ℕ) (t : Fin (n + 1) → K) (a : Fin (n + 1)),
        (eNlim n t).hom ≫ (Pi.π (fun a ↦ Over.mk (f (t a))) a).left =
          Blim.map (pr₀ n t a) ≫ (eV (t a)).hom) ∧
      (∀ (j k : J) (a : j ⟶ k) (n : ℕ) (t : Fin (n + 1) → K),
        (γ j k a n t).hom.left ≫
            pullback.fst (W₀ n t).hom (D.map (homOfLE k.property).op) =
          pullback.fst (Wj j n t).hom (D.map (show j.val ⟶ k.val from a).op) ≫
            pullback.fst (W₀ n t).hom (D.map (homOfLE j.property).op)) ∧
      (∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K),
        (δ j n t).hom.left ≫ pullback.fst (W₀ n t).hom (c.π.app (op i₀)) =
          pullback.fst (Wj j n t).hom (c.π.app (op j.val)) ≫
            pullback.fst (W₀ n t).hom (D.map (homOfLE j.property).op)) ∧
      (∀ (j k : J) (a : j ⟶ k) (n : ℕ) (t : Fin (n + 1) → K),
        (eA j).inv.f n ≫ (A.map a).f n ≫ (eA k).hom.f n ≫
            Pi.π (Pj k n) t ≫ (F k.val).obj.map (eNj k n t).hom.op =
          Pi.π (Pj j n) t ≫ (F j.val).obj.map (eNj j n t).hom.op ≫
            ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
              (D.map (show j.val ⟶ k.val from a).op)).unit.app (F j.val)).hom.app
                (op (Wj j n t)) ≫
            (φ (show j.val ⟶ k.val from a)).hom.app
              (op ((MorphismProperty.Over.pullback @Etale ⊤
                (D.map (show j.val ⟶ k.val from a).op)).obj (Wj j n t))) ≫
            (F k.val).obj.map (γ j k a n t).inv.op) ∧
      (∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K),
        (eA j).inv.f n ≫ (cA.ι.app j).f n ≫ eK.hom.f n ≫
            Pi.π (Plim n) t ≫ L.pt.obj.map (eNlim n t).hom.op =
          Pi.π (Pj j n) t ≫ (F j.val).obj.map (eNj j n t).hom.op ≫
            ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
              (c.π.app (op j.val))).unit.app (F j.val)).hom.app (op (Wj j n t)) ≫
            (eG j.val).inv.hom.app
              (op ((MorphismProperty.Over.pullback @Etale ⊤
                (c.π.app (op j.val))).obj (Wj j n t))) ≫
            (L.ι.app j.val).hom.app
              (op ((MorphismProperty.Over.pullback @Etale ⊤
                (c.π.app (op j.val))).obj (Wj j n t))) ≫
            L.pt.obj.map (δ j n t).inv.op) →
      Nonempty (IsColimit cA)
```

Exact corrected stage-data signature with witnesses for the same constructions and equations:

```lean
theorem exists_etale_limit_finite_cech_stage_data
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G) (hL : IsColimit L)
    (U : c.pt.Etale) [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    (K : Type (u + 1)) [Finite K] (V : K → c.pt.Etale) (f : ∀ k, V k ⟶ U)
    (hV : ∀ k, CompactSpace (V k).left ∧ QuasiSeparatedSpace (V k).left)
    (hf : Sieve.ofArrows V f ∈ c.pt.smallEtaleTopology U) :
    ∃ (i₀ : I) (U₀ : (D.obj (op i₀)).Etale)
    (V₀ : K → (D.obj (op i₀)).Etale) (f₀ : ∀ k, V₀ k ⟶ U₀)
    (eU : (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj U₀ ≅ U)
    (eV : ∀ k,
      (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj (V₀ k) ≅ V k),
    let J := {j : I // i₀ ≤ j}
    let B := fun j : J ↦
      MorphismProperty.Over.pullback @Etale ⊤ (D.map (homOfLE j.property).op)
    let Blim := MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))
    let Uj := fun j : J ↦ (B j).obj U₀
    let Vj := fun (j : J) (k : K) ↦ (B j).obj (V₀ k)
    let fj := fun (j : J) (k : K) ↦ (B j).map (f₀ k)
    let W₀ := fun (n : ℕ) (t : Fin (n + 1) → K) ↦
      (∏ᶜ fun a ↦ Over.mk (f₀ (t a))).left
    let pr₀ := fun (n : ℕ) (t : Fin (n + 1) → K) (a : Fin (n + 1)) ↦
      (Pi.π (fun a ↦ Over.mk (f₀ (t a))) a).left
    let Wj := fun (j : J) (n : ℕ) (t : Fin (n + 1) → K) ↦ (B j).obj (W₀ n t)
    let Wlim := fun (n : ℕ) (t : Fin (n + 1) → K) ↦ Blim.obj (W₀ n t)
    let Nj := fun (j : J) (n : ℕ) (t : Fin (n + 1) → K) ↦
      (∏ᶜ fun a ↦ Over.mk (fj j (t a))).left
    let Nlim := fun (n : ℕ) (t : Fin (n + 1) → K) ↦
      (∏ᶜ fun a ↦ Over.mk (f (t a))).left
    let Pj := fun (j : J) (n : ℕ) ↦
      fun t : Fin (n + 1) → K ↦ (F j.val).obj.obj (op (Nj j n t))
    let Plim := fun (n : ℕ) ↦
      fun t : Fin (n + 1) → K ↦ L.pt.obj.obj (op (Nlim n t))
    ∃ (A : J ⥤ CochainComplex AddCommGrpCat.{u + 1} ℕ)
      (eA : ∀ j : J, A.obj j ≅
        (cechComplexFunctor (fun k : K ↦ Over.mk (fj j k))).obj
          ((Over.forget (Uj j)).op ⋙ (F j.val).obj))
      (cA : Cocone A)
      (eK : cA.pt ≅ (cechComplexFunctor (fun k : K ↦ Over.mk (f k))).obj
        ((Over.forget U).op ⋙ L.pt.obj))
      (eNj : ∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K),
        Wj j n t ≅ Nj j n t)
      (eNlim : ∀ (n : ℕ) (t : Fin (n + 1) → K), Wlim n t ≅ Nlim n t)
      (γ : ∀ (j k : J) (a : j ⟶ k) (n : ℕ) (t : Fin (n + 1) → K),
        (MorphismProperty.Over.pullback @Etale ⊤
          (D.map (show j.val ⟶ k.val from a).op)).obj (Wj j n t) ≅ Wj k n t)
      (δ : ∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K),
        (MorphismProperty.Over.pullback @Etale ⊤
          (c.π.app (op j.val))).obj (Wj j n t) ≅ Wlim n t),
      (CompactSpace U₀.left ∧ QuasiSeparatedSpace U₀.left) ∧
      (∀ k, CompactSpace (V₀ k).left ∧ QuasiSeparatedSpace (V₀ k).left) ∧
      (∀ k, Blim.map (f₀ k) ≫ eU.hom = (eV k).hom ≫ f k) ∧
      (∀ j : J, Sieve.ofArrows (Vj j) (fj j) ∈
        (D.obj (op j.val)).smallEtaleTopology (Uj j)) ∧
      (∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K) (a : Fin (n + 1)),
        (eNj j n t).hom ≫ (Pi.π (fun a ↦ Over.mk (fj j (t a))) a).left =
          (B j).map (pr₀ n t a)) ∧
      (∀ (n : ℕ) (t : Fin (n + 1) → K) (a : Fin (n + 1)),
        (eNlim n t).hom ≫ (Pi.π (fun a ↦ Over.mk (f (t a))) a).left =
          Blim.map (pr₀ n t a) ≫ (eV (t a)).hom) ∧
      (∀ (j k : J) (a : j ⟶ k) (n : ℕ) (t : Fin (n + 1) → K),
        (γ j k a n t).hom.left ≫
            pullback.fst (W₀ n t).hom (D.map (homOfLE k.property).op) =
          pullback.fst (Wj j n t).hom (D.map (show j.val ⟶ k.val from a).op) ≫
            pullback.fst (W₀ n t).hom (D.map (homOfLE j.property).op)) ∧
      (∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K),
        (δ j n t).hom.left ≫ pullback.fst (W₀ n t).hom (c.π.app (op i₀)) =
          pullback.fst (Wj j n t).hom (c.π.app (op j.val)) ≫
            pullback.fst (W₀ n t).hom (D.map (homOfLE j.property).op)) ∧
      (∀ (j k : J) (a : j ⟶ k) (n : ℕ) (t : Fin (n + 1) → K),
        (eA j).inv.f n ≫ (A.map a).f n ≫ (eA k).hom.f n ≫
            Pi.π (Pj k n) t ≫ (F k.val).obj.map (eNj k n t).hom.op =
          Pi.π (Pj j n) t ≫ (F j.val).obj.map (eNj j n t).hom.op ≫
            ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
              (D.map (show j.val ⟶ k.val from a).op)).unit.app (F j.val)).hom.app
                (op (Wj j n t)) ≫
            (φ (show j.val ⟶ k.val from a)).hom.app
              (op ((MorphismProperty.Over.pullback @Etale ⊤
                (D.map (show j.val ⟶ k.val from a).op)).obj (Wj j n t))) ≫
            (F k.val).obj.map (γ j k a n t).inv.op) ∧
      (∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K),
        (eA j).inv.f n ≫ (cA.ι.app j).f n ≫ eK.hom.f n ≫
            Pi.π (Plim n) t ≫ L.pt.obj.map (eNlim n t).hom.op =
          Pi.π (Pj j n) t ≫ (F j.val).obj.map (eNj j n t).hom.op ≫
            ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
              (c.π.app (op j.val))).unit.app (F j.val)).hom.app (op (Wj j n t)) ≫
            (eG j.val).inv.hom.app
              (op ((MorphismProperty.Over.pullback @Etale ⊤
                (c.π.app (op j.val))).obj (Wj j n t))) ≫
            (L.ι.app j.val).hom.app
              (op ((MorphismProperty.Over.pullback @Etale ⊤
                (c.π.app (op j.val))).obj (Wj j n t))) ≫
            L.pt.obj.map (δ j n t).inv.op)
```

All Uj, Vj and fj are actual base changes of a fixed qcqs finite stage family.
The eU/eV arrow equation identifies that family's pullback with the given family.
The eNj/eNlim projection equations prescribe the nerve identifications.
The γ/δ first-projection equations, together with the fixed base maps, prescribe
pullback pasting. The final two equations prescribe EVERY transition and EVERY
cocone leg, degree by degree and tuple by tuple. In the reviewer's singleton
identity example the last equation forces a nonzero identity section map;
a zero cocone leg fails it. No IsColimit assumption was added to the stage data.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleLimitFiniteCechStageData | V1 new module | existential now supplies fixed descended covering, canonical nerve comparisons, and all map equations; no colimit witness |
| Sheaf.AlgebraicGeometry.EtaleLimitFiniteCechColimit | V1 new module | false arbitrary-data signature replaced by canonical-map hypotheses and actual universal-property argument |
| Sheaf.AlgebraicGeometry.EtaleLimitFiniteCechComplexColimit | V1 | signature unchanged; proof passes every witness and equation, then forgets the extra data |
| Sheaf.AlgebraicGeometry.EtaleLimitInjectiveColimitAcyclic | unclaimed | direct importer unchanged; its call uses the identical item signature |

These intermediate modules are new relative to the library, so there are no
other library callers to adapt. There is no change to any definition used by
Challenge.lean and no target statement change.

## Status

landed 20261012T194148-L-467380 2026-10-12 (merge of deliver/V1/Sheaf.AlgebraicGeometry.EtaleLimitFiniteCechComplexColimit)
