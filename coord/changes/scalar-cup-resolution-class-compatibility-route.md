# scalarCup_resolution_class_compatibility

## Reason

The unsigned scalar cup formula is false for odd-by-odd bidegrees. `scalarExtCup`
composes the left class first, and moving the left shift out before the right shift
contributes `(-1)^(p*q)`. The prior private `scalarCup_yoneda_order`,
`oddShiftTensor_component`, `oddTensorSummand_ne_neg`, and
`oddShiftTensor_not_unsigned` proofs verify the order, the degree-one sign and its
nontriviality over the rationals. The launcher explicitly authorized the minimal
signed correction on 2026-10-15. This repairs reviewer X-8bf90, H2/H3/H7 and A3.

Source: Stacks Project, Cohomology Tags 01F7, 07MB and 0FKV; Varieties Tag 0BED;
Mathlib's two `mapBifunctorShift` tensor-summand formulas.

The resolution and front/back Cech pairings are the given unsigned pairings.
The scalar/module comparison has `(-1 : ℤ) ^ (p * q) •` on its right. The Picard
Cech comparison and the cochain/homology normalization predicates have
`(-1 : ℤ) ^ (i.val.1 * i.val.2) •` on their left. Squaring this unit gives one,
so the constructed cochain and the homology uniqueness proof cancel its two factors.
The correction adds no hypothesis. The factor is one for degree zero, even products,
and characteristic two; zero classes are unchanged. No declaration in Challenge.lean
is edited, and the blueprint unit statement and route are retained.

## Old

Formatting-only repair of the public H1 bypass signature (same type):

```lean
theorem picard_h1_product_spanning_bypass (k : Type u) [Field k] (X Y : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [IsProper (X ↘ Spec (CommRingCat.of k))] [IsProper (Y ↘ Spec (CommRingCat.of k))]
    (hX : Function.Bijective (globalSectionsRingHom k (X := X)))
    (hY : Function.Bijective (globalSectionsRingHom k (X := Y))) :
    ∀ c : Sheaf.H (structureSheafAb
      (pullback (X ↘ Spec (CommRingCat.of k)) (Y ↘ Spec (CommRingCat.of k)))) 1,
      ∃ a : Sheaf.H (structureSheafAb X) 1,
        ∃ b : Sheaf.H (structureSheafAb Y) 1,
          structureSheafCohomologyPullback
              (pullback.fst (X ↘ Spec (CommRingCat.of k)) (Y ↘ Spec (CommRingCat.of k))) 1 a +
            structureSheafCohomologyPullback
              (pullback.snd (X ↘ Spec (CommRingCat.of k)) (Y ↘ Spec (CommRingCat.of k))) 1 b = c
```


Private H1 axiom replaced by a theorem with exactly the same type:

```lean
private axiom picardExternalCupCochain_h1_isIso
    (k : Type u) [Field k] (X Y : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (c : Modules.picardExternalTotal f g F G ⟶
      Modules.picardScalarModel (pullback.fst f g ≫ f)
        (Modules.externalCupCoefficients f g F G))
    (hc : Modules.IsPicardExternalCupCochain f g F G c) :
    IsIso (HomologicalComplex.homologyMap c (1 : ℤ))
```


`AlgebraicGeometry.Scheme.Modules.picardExternalCup_left_cech_generators`:

```lean
theorem picardExternalCup_left_cech_generators
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (G : Y.Modules) [G.IsQuasicoherent] :
    ∃ θ : picardLeftTensorCechFunctor f g G ⟶ picardLeftProductCechFunctor f g G,
      ∀ (F : X.Modules) (_ : F.IsQuasicoherent) (n : ℕ),
        ∃ (e : (⨁ i : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
              (picardScalarModel f F).homology (i.val.1 : ℤ) ⊗[k]
                (picardScalarModel g G).homology (i.val.2 : ℤ)) ≃ₗ[k]
              ((picardLeftTensorCechFunctor f g G).obj F).homology (n : ℤ))
          (b : ((picardLeftProductCechFunctor f g G).obj F).homology (n : ℤ) ≅
            (picardScalarModel (pullback.fst f g ≫ f)
              (externalCupCoefficients f g F G)).homology (n : ℤ)),
          ∀ (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
            (x : (picardScalarModel f F).homology (i.val.1 : ℤ))
            (y : (picardScalarModel g G).homology (i.val.2 : ℤ)),
            picardScalarModelEquiv (pullback.fst f g ≫ f)
                (externalCupCoefficients f g F G) n
              (b.hom (HomologicalComplex.homologyMap (θ.app F) (n : ℤ)
                (e (DirectSum.lof k _ _ i (x ⊗ₜ[k] y))))) =
              cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
                (externalCupCoefficients f g F G) d)) i.property)
                (externalCup f g F G i.val.1 i.val.2
                  (picardScalarModelEquiv f F i.val.1 x)
                  (picardScalarModelEquiv g G i.val.2 y))
```


The following signatures and predicate definitions are copied verbatim from the base.

`AlgebraicGeometry.Scheme.Modules.IsPicardExternalCupCochain`:

```lean
def IsPicardExternalCupCochain
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules)
    (c : picardExternalTotal f g F G ⟶
      picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)) : Prop :=
  ∀ (n : ℕ) (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    (a : (picardScalarModel f F).cycles (i.val.1 : ℤ))
    (b : (picardScalarModel g G).cycles (i.val.2 : ℤ))
    (z : (picardExternalTotal f g F G).cycles (n : ℤ)),
    (picardExternalTotal f g F G).iCycles (n : ℤ) z =
      HomologicalComplex.ιMapBifunctor (picardScalarModel f F) (picardScalarModel g G)
        (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℤ)
        (i.val.1 : ℤ) (i.val.2 : ℤ) (n : ℤ) (by
          change (i.val.1 : ℤ) + (i.val.2 : ℤ) = (n : ℤ)
          exact_mod_cast i.property)
        (((picardScalarModel f F).iCycles (i.val.1 : ℤ) a) ⊗ₜ[k]
          ((picardScalarModel g G).iCycles (i.val.2 : ℤ) b)) →
    picardScalarModelEquiv (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) n
        (HomologicalComplex.homologyMap c (n : ℤ)
          ((picardExternalTotal f g F G).homologyπ (n : ℤ) z)) =
      cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
        (externalCupCoefficients f g F G) d)) i.property)
        (externalCup f g F G i.val.1 i.val.2
          (picardScalarModelEquiv f F i.val.1
            ((picardScalarModel f F).homologyπ (i.val.1 : ℤ) a))
          (picardScalarModelEquiv g G i.val.2
            ((picardScalarModel g G).homologyπ (i.val.2 : ℤ) b)))
```

`AlgebraicGeometry.Scheme.Modules.IsPicardExternalCupHomology`:

```lean
def IsPicardExternalCupHomology
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules)
    (φ : ∀ n : ℕ, (picardExternalTotal f g F G).homology (n : ℤ) ⟶
      (picardScalarModel (pullback.fst f g ≫ f)
        (externalCupCoefficients f g F G)).homology (n : ℤ)) : Prop :=
  ∀ (n : ℕ) (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    (a : (picardScalarModel f F).cycles (i.val.1 : ℤ))
    (b : (picardScalarModel g G).cycles (i.val.2 : ℤ))
    (z : (picardExternalTotal f g F G).cycles (n : ℤ)),
    (picardExternalTotal f g F G).iCycles (n : ℤ) z =
      HomologicalComplex.ιMapBifunctor (picardScalarModel f F) (picardScalarModel g G)
        (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℤ)
        (i.val.1 : ℤ) (i.val.2 : ℤ) (n : ℤ) (by
          change (i.val.1 : ℤ) + (i.val.2 : ℤ) = (n : ℤ)
          exact_mod_cast i.property)
        (((picardScalarModel f F).iCycles (i.val.1 : ℤ) a) ⊗ₜ[k]
          ((picardScalarModel g G).iCycles (i.val.2 : ℤ) b)) →
    picardScalarModelEquiv (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) n
        (φ n
          ((picardExternalTotal f g F G).homologyπ (n : ℤ) z)) =
      cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
        (externalCupCoefficients f g F G) d)) i.property)
        (externalCup f g F G i.val.1 i.val.2
          (picardScalarModelEquiv f F i.val.1
            ((picardScalarModel f F).homologyπ (i.val.1 : ℤ) a))
          (picardScalarModelEquiv g G i.val.2
            ((picardScalarModel g G).homologyπ (i.val.2 : ℤ) b)))
```

`AlgebraicGeometry.Scheme.Modules.picardRightCechCup_cycle_comparison`:

```lean
theorem picardRightCechCup_cycle_comparison
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (F : X.Modules) [F.IsQuasicoherent]
    {ι κ : Type w} [Finite ι] [Finite κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hUc : iSup U = ⊤) (hVc : iSup V = ⊤)
    (θ : picardRightTensorCechFunctor f g U V F ⟶
      picardRightProductCechFunctor f g U V F)
    (hθ : IsPicardRightCechCup f g U V F θ)
    (G : Y.Modules) [G.IsQuasicoherent] :
    let A := (picardCechFunctor f U).obj F
    let B := (picardCechFunctor g V).obj G
    let T := HomologicalComplex.mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
      (ComplexShape.up ℕ)
    ∃ (alpha : ∀ p : ℕ, A.homology p ≃ₗ[k] (picardScalarModel f F).homology (p : ℤ))
      (beta : ∀ q : ℕ, B.homology q ≃ₗ[k] (picardScalarModel g G).homology (q : ℤ))
      (b : ∀ n : ℕ,
        ((picardRightProductCechFunctor f g U V F).obj G).homology (n : ℤ) ≅
          (picardScalarModel (pullback.fst f g ≫ f)
            (externalCupCoefficients f g F G)).homology (n : ℤ)),
      ∀ (n : ℕ) (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
        (a : A.cycles i.val.1) (v : B.cycles i.val.2) (z : T.cycles n),
        T.iCycles n z =
          HomologicalComplex.ιMapBifunctor A B (curriedTensor (ModuleCat.{w} k))
            (ComplexShape.up ℕ) i.val.1 i.val.2 n i.property
              ((A.iCycles i.val.1 a) ⊗ₜ[k] (B.iCycles i.val.2 v)) →
        picardScalarModelEquiv (pullback.fst f g ≫ f)
            (externalCupCoefficients f g F G) n
          ((b n).hom (HomologicalComplex.homologyMap (θ.app G) (n : ℤ)
            ((T.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).inv
              (T.homologyπ n z)))) =
          cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
            (externalCupCoefficients f g F G) d)) i.property)
            (externalCup f g F G i.val.1 i.val.2
              (picardScalarModelEquiv f F i.val.1 (alpha i.val.1 (A.homologyπ _ a)))
              (picardScalarModelEquiv g G i.val.2 (beta i.val.2 (B.homologyπ _ v))))
```

`AlgebraicGeometry.Scheme.Modules.picardRightCechCup_generators`:

```lean
theorem picardRightCechCup_generators
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (F : X.Modules) [F.IsQuasicoherent]
    {ι κ : Type w} [Finite ι] [Finite κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hUc : iSup U = ⊤) (hVc : iSup V = ⊤)
    (θ : picardRightTensorCechFunctor f g U V F ⟶
      picardRightProductCechFunctor f g U V F)
    (hθ : IsPicardRightCechCup f g U V F θ)
    (G : Y.Modules) [G.IsQuasicoherent] (n : ℕ) :
        ∃ (e : (⨁ i : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
              (picardScalarModel f F).homology (i.val.1 : ℤ) ⊗[k]
                (picardScalarModel g G).homology (i.val.2 : ℤ)) ≃ₗ[k]
              ((picardRightTensorCechFunctor f g U V F).obj G).homology (n : ℤ))
          (b : ((picardRightProductCechFunctor f g U V F).obj G).homology (n : ℤ) ≅
            (picardScalarModel (pullback.fst f g ≫ f)
              (externalCupCoefficients f g F G)).homology (n : ℤ)),
          ∀ (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
            (x : (picardScalarModel f F).homology (i.val.1 : ℤ))
            (y : (picardScalarModel g G).homology (i.val.2 : ℤ)),
            picardScalarModelEquiv (pullback.fst f g ≫ f)
                (externalCupCoefficients f g F G) n
              (b.hom (HomologicalComplex.homologyMap (θ.app G) (n : ℤ)
                (e (DirectSum.lof k _ _ i (x ⊗ₜ[k] y))))) =
              cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
                (externalCupCoefficients f g F G) d)) i.property)
                (externalCup f g F G i.val.1 i.val.2
                  (picardScalarModelEquiv f F i.val.1 x)
                  (picardScalarModelEquiv g G i.val.2 y))
```

`AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup_core`:

```lean
theorem picardScalarCech_externalCup_core
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) [F.IsQuasicoherent] (G : Y.Modules) [G.IsQuasicoherent]
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens)
    (hUc : iSup U = ⊤) (hVc : iSup V = ⊤)
    (c : HomologicalComplex.mapBifunctor ((picardCechFunctor f U).obj F)
        ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ) ⟶
      (picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G))
    (hc : IsPicardExternalCechCupComponent f g U V F G c)
    (eX : ∀ p : ℕ, ((picardCechFunctor f U).obj F).homology p →ₗ[k]
      scalarCohomology f F p)
    (heX : ∀ p, IsPicardScalarCechComparison f U F p (eX p))
    (eY : ∀ q : ℕ, ((picardCechFunctor g V).obj G).homology q →ₗ[k]
      scalarCohomology g G q)
    (heY : ∀ q, IsPicardScalarCechComparison g V G q (eY q))
    (eP : ∀ n : ℕ,
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj
            (externalCupCoefficients f g F G)).homology n →ₗ[k]
        scalarCohomology (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) n)
    (heP : ∀ n, IsPicardScalarCechComparison (pullback.fst f g ≫ f)
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2) (externalCupCoefficients f g F G) n (eP n)) :
    let A := (picardCechFunctor f U).obj F
    let B := (picardCechFunctor g V).obj G
    let T := HomologicalComplex.mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
      (ComplexShape.up ℕ)
    ∀ (n : ℕ) (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    (a : A.cycles i.val.1) (v : B.cycles i.val.2) (z : T.cycles n),
    T.iCycles n z = HomologicalComplex.ιMapBifunctor A B
        (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℕ) i.val.1 i.val.2 n
        i.property ((A.iCycles i.val.1 a) ⊗ₜ[k] (B.iCycles i.val.2 v)) →
      eP n (HomologicalComplex.homologyMap c n (T.homologyπ n z)) =
        cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
          (externalCupCoefficients f g F G) d)) i.property)
          (externalCup f g F G i.val.1 i.val.2
            (eX i.val.1 (A.homologyπ _ a)) (eY i.val.2 (B.homologyπ _ v)))
```

`AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup`:

```lean
theorem picardScalarCech_externalCup
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) [F.IsQuasicoherent] (G : Y.Modules) [G.IsQuasicoherent]
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens)
    (hUc : iSup U = ⊤) (hVc : iSup V = ⊤)
    (c : HomologicalComplex.mapBifunctor ((picardCechFunctor f U).obj F)
        ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ) ⟶
      (picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G))
    (hc : IsPicardExternalCechCupComponent f g U V F G c)
    (eX : ∀ p : ℕ, ((picardCechFunctor f U).obj F).homology p →ₗ[k]
      scalarCohomology f F p)
    (heX : ∀ p, IsPicardScalarCechComparison f U F p (eX p))
    (eY : ∀ q : ℕ, ((picardCechFunctor g V).obj G).homology q →ₗ[k]
      scalarCohomology g G q)
    (heY : ∀ q, IsPicardScalarCechComparison g V G q (eY q))
    (eP : ∀ n : ℕ,
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj
            (externalCupCoefficients f g F G)).homology n →ₗ[k]
        scalarCohomology (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) n)
    (heP : ∀ n, IsPicardScalarCechComparison (pullback.fst f g ≫ f)
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2) (externalCupCoefficients f g F G) n (eP n)) :
    let A := (picardCechFunctor f U).obj F
    let B := (picardCechFunctor g V).obj G
    let T := HomologicalComplex.mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
      (ComplexShape.up ℕ)
    ∀ (n : ℕ) (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
      (a : A.cycles i.val.1) (v : B.cycles i.val.2) (z : T.cycles n),
      T.iCycles n z =
        HomologicalComplex.ιMapBifunctor A B (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ) i.val.1 i.val.2 n i.property
            ((A.iCycles i.val.1 a) ⊗ₜ[k] (B.iCycles i.val.2 v)) →
      eP n (HomologicalComplex.homologyMap c n (T.homologyπ n z)) =
        cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
          (externalCupCoefficients f g F G) d)) i.property)
          (externalCup f g F G i.val.1 i.val.2
            (eX i.val.1 (A.homologyπ _ a)) (eY i.val.2 (B.homologyπ _ v)))
```

`AlgebraicGeometry.Scheme.Modules.scalarCup_moduleCup_compatibility`:

```lean
theorem scalarCup_moduleCup_compatibility
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F G : X.Modules) (p q : ℕ)
    (cup : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj
        (@id X.Modules (F ⊗ G)))
    (hcup :
      ∀ (D : CupResolutionPairing F G)
        (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
        (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
        (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K),
        c.val = D.pair p q ⊤ a.val b.val →
          cup (D.left.class p a) (D.right.class q b) = D.target.class (p + q) c)
    (a : scalarCohomology f F p) (b : scalarCohomology f G q) :
    scalarCohomologyCup f F G p q a b = cup a b
```

`AlgebraicGeometry.Scheme.Modules.scalarCup_resolution_class_compatibility`:

```lean
theorem scalarCup_resolution_class_compatibility
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F G : X.Modules) (p q : ℕ)
    (D : CupResolutionPairing F G)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
    (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
    (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K)
    (hc : c.val = D.pair p q ⊤ a.val b.val) :
    scalarCohomologyCup f F G p q (D.left.class p a) (D.right.class q b) =
      D.target.class (p + q) c
```

`AlgebraicGeometry.Scheme.Modules.scalarExternalCup_moduleComparison`:

```lean
theorem scalarExternalCup_moduleComparison
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) (p q : ℕ)
    (cup : (RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace p).obj
        ((tensorPullback (pullback.fst f g)).obj F) →ₗ[Γ(Limits.pullback f g, ⊤)]
      (RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace q).obj
        ((tensorPullback (pullback.snd f g)).obj G) →ₗ[Γ(Limits.pullback f g, ⊤)]
      (RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace (p + q)).obj
        (externalCupCoefficients f g F G))
    (hcup :
      ∀ (D : CupResolutionPairing
            ((tensorPullback (pullback.fst f g)).obj F)
            ((tensorPullback (pullback.snd f g)).obj G))
        (a : ((((RingedSpace.globalSectionsFunctor
          (Limits.pullback f g).toRingedSpace).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          D.left.K).sc p).moduleCatLeftHomologyData.K)
        (b : ((((RingedSpace.globalSectionsFunctor
          (Limits.pullback f g).toRingedSpace).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          D.right.K).sc q).moduleCatLeftHomologyData.K)
        (c : ((((RingedSpace.globalSectionsFunctor
          (Limits.pullback f g).toRingedSpace).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          D.target.K).sc (p + q)).moduleCatLeftHomologyData.K),
        c.val = D.pair p q ⊤ a.val b.val →
          cup (D.left.class p a) (D.right.class q b) = D.target.class (p + q) c)
    (x : scalarCohomology f F p) (y : scalarCohomology g G q) :
    externalCup f g F G p q x y =
      cup (moduleCohomologyPullback (pullback.fst f g) F p x)
        (moduleCohomologyPullback (pullback.snd f g) G q y)
```

## New

Formatting-only repair of the public H1 bypass signature (same type):

```lean
theorem picard_h1_product_spanning_bypass (k : Type u) [Field k] (X Y : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [IsProper (X ↘ Spec (CommRingCat.of k))] [IsProper (Y ↘ Spec (CommRingCat.of k))]
    (hX : Function.Bijective (globalSectionsRingHom k (X := X)))
    (hY : Function.Bijective (globalSectionsRingHom k (X := Y))) :
    ∀ c : Sheaf.H (structureSheafAb
      (pullback (X ↘ Spec (CommRingCat.of k)) (Y ↘ Spec (CommRingCat.of k)))) 1,
      ∃ a : Sheaf.H (structureSheafAb X) 1,
        ∃ b : Sheaf.H (structureSheafAb Y) 1,
          structureSheafCohomologyPullback
              (pullback.fst (X ↘ Spec (CommRingCat.of k)) (Y ↘ Spec (CommRingCat.of k))) 1 a +
            structureSheafCohomologyPullback
              (pullback.snd (X ↘ Spec (CommRingCat.of k))
                (Y ↘ Spec (CommRingCat.of k))) 1 b = c
```


Private H1 theorem proved by the existing general cup invertibility theorem:

```lean
private theorem picardExternalCupCochain_h1_isIso
    (k : Type u) [Field k] (X Y : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (c : Modules.picardExternalTotal f g F G ⟶
      Modules.picardScalarModel (pullback.fst f g ≫ f)
        (Modules.externalCupCoefficients f g F G))
    (hc : Modules.IsPicardExternalCupCochain f g F G c) :
    IsIso (HomologicalComplex.homologyMap c (1 : ℤ))
```


`AlgebraicGeometry.Scheme.Modules.picardExternalCup_left_cech_generators`:

```lean
theorem picardExternalCup_left_cech_generators
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (G : Y.Modules) [G.IsQuasicoherent] :
    ∃ θ : picardLeftTensorCechFunctor f g G ⟶ picardLeftProductCechFunctor f g G,
      ∀ (F : X.Modules) (_ : F.IsQuasicoherent) (n : ℕ),
        ∃ (e : (⨁ i : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
              (picardScalarModel f F).homology (i.val.1 : ℤ) ⊗[k]
                (picardScalarModel g G).homology (i.val.2 : ℤ)) ≃ₗ[k]
              ((picardLeftTensorCechFunctor f g G).obj F).homology (n : ℤ))
          (b : ((picardLeftProductCechFunctor f g G).obj F).homology (n : ℤ) ≅
            (picardScalarModel (pullback.fst f g ≫ f)
              (externalCupCoefficients f g F G)).homology (n : ℤ)),
          ∀ (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
            (x : (picardScalarModel f F).homology (i.val.1 : ℤ))
            (y : (picardScalarModel g G).homology (i.val.2 : ℤ)),
            (-1 : ℤ) ^ (i.val.1 * i.val.2) •
              picardScalarModelEquiv (pullback.fst f g ≫ f)
                (externalCupCoefficients f g F G) n
              (b.hom (HomologicalComplex.homologyMap (θ.app F) (n : ℤ)
                (e (DirectSum.lof k _ _ i (x ⊗ₜ[k] y))))) =
              cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
                (externalCupCoefficients f g F G) d)) i.property)
                (externalCup f g F G i.val.1 i.val.2
                  (picardScalarModelEquiv f F i.val.1 x)
                  (picardScalarModelEquiv g G i.val.2 y))
```


`AlgebraicGeometry.Scheme.Modules.IsPicardExternalCupCochain`:

```lean
def IsPicardExternalCupCochain
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules)
    (c : picardExternalTotal f g F G ⟶
      picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)) : Prop :=
  ∀ (n : ℕ) (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    (a : (picardScalarModel f F).cycles (i.val.1 : ℤ))
    (b : (picardScalarModel g G).cycles (i.val.2 : ℤ))
    (z : (picardExternalTotal f g F G).cycles (n : ℤ)),
    (picardExternalTotal f g F G).iCycles (n : ℤ) z =
      HomologicalComplex.ιMapBifunctor (picardScalarModel f F) (picardScalarModel g G)
        (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℤ)
        (i.val.1 : ℤ) (i.val.2 : ℤ) (n : ℤ) (by
          change (i.val.1 : ℤ) + (i.val.2 : ℤ) = (n : ℤ)
          exact_mod_cast i.property)
        (((picardScalarModel f F).iCycles (i.val.1 : ℤ) a) ⊗ₜ[k]
          ((picardScalarModel g G).iCycles (i.val.2 : ℤ) b)) →
    (-1 : ℤ) ^ (i.val.1 * i.val.2) •
      picardScalarModelEquiv (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) n
        (HomologicalComplex.homologyMap c (n : ℤ)
          ((picardExternalTotal f g F G).homologyπ (n : ℤ) z)) =
      cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
        (externalCupCoefficients f g F G) d)) i.property)
        (externalCup f g F G i.val.1 i.val.2
          (picardScalarModelEquiv f F i.val.1
            ((picardScalarModel f F).homologyπ (i.val.1 : ℤ) a))
          (picardScalarModelEquiv g G i.val.2
            ((picardScalarModel g G).homologyπ (i.val.2 : ℤ) b)))
```

`AlgebraicGeometry.Scheme.Modules.IsPicardExternalCupHomology`:

```lean
def IsPicardExternalCupHomology
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules)
    (φ : ∀ n : ℕ, (picardExternalTotal f g F G).homology (n : ℤ) ⟶
      (picardScalarModel (pullback.fst f g ≫ f)
        (externalCupCoefficients f g F G)).homology (n : ℤ)) : Prop :=
  ∀ (n : ℕ) (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    (a : (picardScalarModel f F).cycles (i.val.1 : ℤ))
    (b : (picardScalarModel g G).cycles (i.val.2 : ℤ))
    (z : (picardExternalTotal f g F G).cycles (n : ℤ)),
    (picardExternalTotal f g F G).iCycles (n : ℤ) z =
      HomologicalComplex.ιMapBifunctor (picardScalarModel f F) (picardScalarModel g G)
        (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℤ)
        (i.val.1 : ℤ) (i.val.2 : ℤ) (n : ℤ) (by
          change (i.val.1 : ℤ) + (i.val.2 : ℤ) = (n : ℤ)
          exact_mod_cast i.property)
        (((picardScalarModel f F).iCycles (i.val.1 : ℤ) a) ⊗ₜ[k]
          ((picardScalarModel g G).iCycles (i.val.2 : ℤ) b)) →
    (-1 : ℤ) ^ (i.val.1 * i.val.2) •
      picardScalarModelEquiv (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) n
        (φ n
          ((picardExternalTotal f g F G).homologyπ (n : ℤ) z)) =
      cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
        (externalCupCoefficients f g F G) d)) i.property)
        (externalCup f g F G i.val.1 i.val.2
          (picardScalarModelEquiv f F i.val.1
            ((picardScalarModel f F).homologyπ (i.val.1 : ℤ) a))
          (picardScalarModelEquiv g G i.val.2
            ((picardScalarModel g G).homologyπ (i.val.2 : ℤ) b)))
```

`AlgebraicGeometry.Scheme.Modules.picardRightCechCup_cycle_comparison`:

```lean
theorem picardRightCechCup_cycle_comparison
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (F : X.Modules) [F.IsQuasicoherent]
    {ι κ : Type w} [Finite ι] [Finite κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hUc : iSup U = ⊤) (hVc : iSup V = ⊤)
    (θ : picardRightTensorCechFunctor f g U V F ⟶
      picardRightProductCechFunctor f g U V F)
    (hθ : IsPicardRightCechCup f g U V F θ)
    (G : Y.Modules) [G.IsQuasicoherent] :
    let A := (picardCechFunctor f U).obj F
    let B := (picardCechFunctor g V).obj G
    let T := HomologicalComplex.mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
      (ComplexShape.up ℕ)
    ∃ (alpha : ∀ p : ℕ, A.homology p ≃ₗ[k] (picardScalarModel f F).homology (p : ℤ))
      (beta : ∀ q : ℕ, B.homology q ≃ₗ[k] (picardScalarModel g G).homology (q : ℤ))
      (b : ∀ n : ℕ,
        ((picardRightProductCechFunctor f g U V F).obj G).homology (n : ℤ) ≅
          (picardScalarModel (pullback.fst f g ≫ f)
            (externalCupCoefficients f g F G)).homology (n : ℤ)),
      ∀ (n : ℕ) (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
        (a : A.cycles i.val.1) (v : B.cycles i.val.2) (z : T.cycles n),
        T.iCycles n z =
          HomologicalComplex.ιMapBifunctor A B (curriedTensor (ModuleCat.{w} k))
            (ComplexShape.up ℕ) i.val.1 i.val.2 n i.property
              ((A.iCycles i.val.1 a) ⊗ₜ[k] (B.iCycles i.val.2 v)) →
        (-1 : ℤ) ^ (i.val.1 * i.val.2) •
          picardScalarModelEquiv (pullback.fst f g ≫ f)
            (externalCupCoefficients f g F G) n
          ((b n).hom (HomologicalComplex.homologyMap (θ.app G) (n : ℤ)
            ((T.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).inv
              (T.homologyπ n z)))) =
          cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
            (externalCupCoefficients f g F G) d)) i.property)
            (externalCup f g F G i.val.1 i.val.2
              (picardScalarModelEquiv f F i.val.1 (alpha i.val.1 (A.homologyπ _ a)))
              (picardScalarModelEquiv g G i.val.2 (beta i.val.2 (B.homologyπ _ v))))
```

`AlgebraicGeometry.Scheme.Modules.picardRightCechCup_generators`:

```lean
theorem picardRightCechCup_generators
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (F : X.Modules) [F.IsQuasicoherent]
    {ι κ : Type w} [Finite ι] [Finite κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hUc : iSup U = ⊤) (hVc : iSup V = ⊤)
    (θ : picardRightTensorCechFunctor f g U V F ⟶
      picardRightProductCechFunctor f g U V F)
    (hθ : IsPicardRightCechCup f g U V F θ)
    (G : Y.Modules) [G.IsQuasicoherent] (n : ℕ) :
        ∃ (e : (⨁ i : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
              (picardScalarModel f F).homology (i.val.1 : ℤ) ⊗[k]
                (picardScalarModel g G).homology (i.val.2 : ℤ)) ≃ₗ[k]
              ((picardRightTensorCechFunctor f g U V F).obj G).homology (n : ℤ))
          (b : ((picardRightProductCechFunctor f g U V F).obj G).homology (n : ℤ) ≅
            (picardScalarModel (pullback.fst f g ≫ f)
              (externalCupCoefficients f g F G)).homology (n : ℤ)),
          ∀ (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
            (x : (picardScalarModel f F).homology (i.val.1 : ℤ))
            (y : (picardScalarModel g G).homology (i.val.2 : ℤ)),
            (-1 : ℤ) ^ (i.val.1 * i.val.2) •
              picardScalarModelEquiv (pullback.fst f g ≫ f)
                (externalCupCoefficients f g F G) n
              (b.hom (HomologicalComplex.homologyMap (θ.app G) (n : ℤ)
                (e (DirectSum.lof k _ _ i (x ⊗ₜ[k] y))))) =
              cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
                (externalCupCoefficients f g F G) d)) i.property)
                (externalCup f g F G i.val.1 i.val.2
                  (picardScalarModelEquiv f F i.val.1 x)
                  (picardScalarModelEquiv g G i.val.2 y))
```

`AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup_core`:

```lean
theorem picardScalarCech_externalCup_core
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) [F.IsQuasicoherent] (G : Y.Modules) [G.IsQuasicoherent]
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens)
    (hUc : iSup U = ⊤) (hVc : iSup V = ⊤)
    (c : HomologicalComplex.mapBifunctor ((picardCechFunctor f U).obj F)
        ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ) ⟶
      (picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G))
    (hc : IsPicardExternalCechCupComponent f g U V F G c)
    (eX : ∀ p : ℕ, ((picardCechFunctor f U).obj F).homology p →ₗ[k]
      scalarCohomology f F p)
    (heX : ∀ p, IsPicardScalarCechComparison f U F p (eX p))
    (eY : ∀ q : ℕ, ((picardCechFunctor g V).obj G).homology q →ₗ[k]
      scalarCohomology g G q)
    (heY : ∀ q, IsPicardScalarCechComparison g V G q (eY q))
    (eP : ∀ n : ℕ,
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj
            (externalCupCoefficients f g F G)).homology n →ₗ[k]
        scalarCohomology (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) n)
    (heP : ∀ n, IsPicardScalarCechComparison (pullback.fst f g ≫ f)
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2) (externalCupCoefficients f g F G) n (eP n)) :
    let A := (picardCechFunctor f U).obj F
    let B := (picardCechFunctor g V).obj G
    let T := HomologicalComplex.mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
      (ComplexShape.up ℕ)
    ∀ (n : ℕ) (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    (a : A.cycles i.val.1) (v : B.cycles i.val.2) (z : T.cycles n),
    T.iCycles n z = HomologicalComplex.ιMapBifunctor A B
        (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℕ) i.val.1 i.val.2 n
        i.property ((A.iCycles i.val.1 a) ⊗ₜ[k] (B.iCycles i.val.2 v)) →
      (-1 : ℤ) ^ (i.val.1 * i.val.2) •
        eP n (HomologicalComplex.homologyMap c n (T.homologyπ n z)) =
        cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
          (externalCupCoefficients f g F G) d)) i.property)
          (externalCup f g F G i.val.1 i.val.2
            (eX i.val.1 (A.homologyπ _ a)) (eY i.val.2 (B.homologyπ _ v)))
```

`AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup`:

```lean
theorem picardScalarCech_externalCup
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) [F.IsQuasicoherent] (G : Y.Modules) [G.IsQuasicoherent]
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens)
    (hUc : iSup U = ⊤) (hVc : iSup V = ⊤)
    (c : HomologicalComplex.mapBifunctor ((picardCechFunctor f U).obj F)
        ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ) ⟶
      (picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G))
    (hc : IsPicardExternalCechCupComponent f g U V F G c)
    (eX : ∀ p : ℕ, ((picardCechFunctor f U).obj F).homology p →ₗ[k]
      scalarCohomology f F p)
    (heX : ∀ p, IsPicardScalarCechComparison f U F p (eX p))
    (eY : ∀ q : ℕ, ((picardCechFunctor g V).obj G).homology q →ₗ[k]
      scalarCohomology g G q)
    (heY : ∀ q, IsPicardScalarCechComparison g V G q (eY q))
    (eP : ∀ n : ℕ,
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj
            (externalCupCoefficients f g F G)).homology n →ₗ[k]
        scalarCohomology (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) n)
    (heP : ∀ n, IsPicardScalarCechComparison (pullback.fst f g ≫ f)
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2) (externalCupCoefficients f g F G) n (eP n)) :
    let A := (picardCechFunctor f U).obj F
    let B := (picardCechFunctor g V).obj G
    let T := HomologicalComplex.mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
      (ComplexShape.up ℕ)
    ∀ (n : ℕ) (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
      (a : A.cycles i.val.1) (v : B.cycles i.val.2) (z : T.cycles n),
      T.iCycles n z =
        HomologicalComplex.ιMapBifunctor A B (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ) i.val.1 i.val.2 n i.property
            ((A.iCycles i.val.1 a) ⊗ₜ[k] (B.iCycles i.val.2 v)) →
      (-1 : ℤ) ^ (i.val.1 * i.val.2) •
        eP n (HomologicalComplex.homologyMap c n (T.homologyπ n z)) =
        cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
          (externalCupCoefficients f g F G) d)) i.property)
          (externalCup f g F G i.val.1 i.val.2
            (eX i.val.1 (A.homologyπ _ a)) (eY i.val.2 (B.homologyπ _ v)))
```

`AlgebraicGeometry.Scheme.Modules.scalarCup_moduleCup_compatibility`:

```lean
theorem scalarCup_moduleCup_compatibility
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F G : X.Modules) (p q : ℕ)
    (cup : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj
        (@id X.Modules (F ⊗ G)))
    (hcup :
      ∀ (D : CupResolutionPairing F G)
        (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
        (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
        (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K),
        c.val = D.pair p q ⊤ a.val b.val →
          cup (D.left.class p a) (D.right.class q b) = D.target.class (p + q) c)
    (a : scalarCohomology f F p) (b : scalarCohomology f G q) :
    scalarCohomologyCup f F G p q a b =
      (-1 : ℤ) ^ (p * q) • cup a b
```

`AlgebraicGeometry.Scheme.Modules.scalarCup_resolution_class_compatibility`:

```lean
theorem scalarCup_resolution_class_compatibility
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F G : X.Modules) (p q : ℕ)
    (D : CupResolutionPairing F G)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
    (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
    (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K)
    (hc : c.val = D.pair p q ⊤ a.val b.val) :
    scalarCohomologyCup f F G p q (D.left.class p a) (D.right.class q b) =
      (-1 : ℤ) ^ (p * q) • D.target.class (p + q) c
```

`AlgebraicGeometry.Scheme.Modules.scalarExternalCup_moduleComparison`:

```lean
theorem scalarExternalCup_moduleComparison
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) (p q : ℕ)
    (cup : (RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace p).obj
        ((tensorPullback (pullback.fst f g)).obj F) →ₗ[Γ(Limits.pullback f g, ⊤)]
      (RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace q).obj
        ((tensorPullback (pullback.snd f g)).obj G) →ₗ[Γ(Limits.pullback f g, ⊤)]
      (RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace (p + q)).obj
        (externalCupCoefficients f g F G))
    (hcup :
      ∀ (D : CupResolutionPairing
            ((tensorPullback (pullback.fst f g)).obj F)
            ((tensorPullback (pullback.snd f g)).obj G))
        (a : ((((RingedSpace.globalSectionsFunctor
          (Limits.pullback f g).toRingedSpace).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          D.left.K).sc p).moduleCatLeftHomologyData.K)
        (b : ((((RingedSpace.globalSectionsFunctor
          (Limits.pullback f g).toRingedSpace).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          D.right.K).sc q).moduleCatLeftHomologyData.K)
        (c : ((((RingedSpace.globalSectionsFunctor
          (Limits.pullback f g).toRingedSpace).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          D.target.K).sc (p + q)).moduleCatLeftHomologyData.K),
        c.val = D.pair p q ⊤ a.val b.val →
          cup (D.left.class p a) (D.right.class q b) = D.target.class (p + q) c)
    (x : scalarCohomology f F p) (y : scalarCohomology g G q) :
    externalCup f g F G p q x y =
      (-1 : ℤ) ^ (p * q) •
        cup (moduleCohomologyPullback (pullback.fst f g) F p x)
          (moduleCohomologyPullback (pullback.snd f g) G q y)
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ScalarCupResolutionClassCompatibility | K1 | Corrected signed statement; original named proof obligation remains open. |
| Sheaf.AlgebraicGeometry.ScalarCupModuleCupCompatibility | unclaimed | Signed conclusion and representative proof retained. |
| Sheaf.AlgebraicGeometry.ScalarExternalCupModuleComparison | unclaimed | Signed conclusion; equality congruence under the sign. |
| Sheaf.AlgebraicGeometry.PicardScalarCechExternalCup | unclaimed | Both core and enclosing conclusions receive the sign on the left. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupCycleComparison | unclaimed | Signed conclusion; transports the sign through extension homology. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupGenerators | unclaimed | Signed conclusion; applies the signed cycle comparison. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupHomology | unclaimed | Signature identical; proof uses the signed generator normalization. |
| Sheaf.AlgebraicGeometry.PicardExternalCupCochain | unclaimed | Signed normalization definition and explicit signed bilinear construction. |
| Sheaf.AlgebraicGeometry.PicardExternalCupHomologyUnique | unclaimed | Signed normalization definition; cancels the squared sign in uniqueness. |
| Sheaf.AlgebraicGeometry.PicardExternalRightCechComparison | unclaimed | Compiles unchanged against the final signed overlay; omitted under reviewer X-67490, A3. |
| Sheaf.AlgebraicGeometry.PicardLeftCechCupHomology | unclaimed | Original source is identical to the former packet; unchanged and omitted. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechGenerators | unclaimed | Propagate signed homology predicate to generator conclusion. |
| Sheaf.AlgebraicGeometry.PicardExternalCupAcyclic | unclaimed | Signature unchanged; simplify the sign at (0,0). |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechComparison | unclaimed | Signature unchanged; cancel the common sign from both coordinate equations. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftComparisonComplexes | unclaimed | Names the normalization predicate; interface user with no direct coordinate formula changed here. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftHomologyLadder | unclaimed | Signature unchanged; use the existing homology uniqueness theorem. |
| Sheaf.AlgebraicGeometry.PicardExternalCupQuasiIso | unclaimed | Names the normalization predicate; interface user with no direct coordinate formula changed here. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightCechDiagram | unclaimed | Names the normalization predicate; interface user with no direct coordinate formula changed here. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightExactLadder | unclaimed | Signature unchanged; use the existing homology uniqueness theorem. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightShortExact | unclaimed | Names the normalization predicate; interface user with no direct coordinate formula changed here. |
| Sheaf.AlgebraicGeometry.PicardExternalCupShiftLeft | unclaimed | Names the normalization predicate; interface user with no direct coordinate formula changed here. |
| Sheaf.AlgebraicGeometry.PicardExternalCupShiftRight | unclaimed | Names the normalization predicate; interface user with no direct coordinate formula changed here. |
| Sheaf.AlgebraicGeometry.PicardH1ProductSpanningBypass | unclaimed | Signature unchanged; simplify the sign at total degree one and replace the private axiom by proved cup invertibility. |
| Sheaf.AlgebraicGeometry.PicardH1ProductSpanning | unclaimed | Sole direct importer of the bypass; signature and proof unchanged, compiled against the private proof imports and repaired helper. |

## Repair details

The three scalar-comparison nodes now have the exact signed prose requested by H3/H7.
The four Picard Cech nodes now have their delivered signatures verbatim and describe
`(-1)^(i.val.1*i.val.2)` on the left. All seven carry `statement_change` records with
the old statement verbatim, source, sign justification, and every base DAG citer's
`holds`/`note`. Each citer has a coordinated signed correction or proof adaptation in
this packet. The core node retains its earlier cover-correction record under `previous`.
Changed proof plans are retained under the records' `old_proof` fields.

Reviewer X-67490 (head 6749012ac), A3, confirmed that the original
PicardExternalRightCechComparison compiles against the final signed dependency
overlay (exit 0, 4.1 s). Its original call is:

```lean
      (fun n ↦ HomologicalComplex.homologyMap d (n : ℤ)) hab hd n
```

The repair worker repeated the unchanged caller check through lcompile.py against
the rebuilt fifteen-module sandbox overlay: exit 0 (3.9 s).
The extra pointwise conversion was unnecessary. The module is unchanged and omitted
from this delivery. The earlier claimed counterfactual failure is superseded by
this final-overlay result. PicardLeftCechCupHomology is also unchanged and omitted.
No library module is withdrawn and there is no deleted.txt entry.

Reviewer X-67490, H7: set holds to false for the six breaking citer entries in
new-sc-scalar-cup-resolution-class-compatibility,
lem-sc-scalar-cup-module-cup-compatibility,
lem-sc-scalar-external-cup-module-comparison,
lem-sc-picard-scalar-cech-external-cup-core,
lem-sc-picard-scalar-cech-external-cup, and
lem-sc-picard-right-cech-cup-cycle-comparison.
The notes explaining their coordinated signed corrections are retained verbatim.
The old unsigned conclusions do not survive these corrections.

The second reader also updated the existing cochain-existence and right-Cech-homology
node statements to spell out the signed normalization, with statement_change and
complete citer records, and updated the homology-uniqueness proof to cancel the sign.
Their Lean theorem signatures are unchanged; their named predicates carry the
previously documented correction. No Challenge definition refers to these predicates.

The second reader removed the proposed ScalarizedModuleCupRealization module and
its new node: hevaluation already identifies its right-hand side with the original
paired class, so that split restated the unresolved comparison. The original named
theorem remains sorry with the corrected sign and a complete proof outline. No hole
is closed or added by this correction, and no new module or node is delivered.

## Additional caller repairs found by the second reader

Compiling original direct predicate users against the changed dependencies found
failures in PicardExternalCupAcyclic (rewrite with signed hc at degree zero),
PicardExternalCupLeftCechComparison (unsigned/signed coordinates),
PicardExternalCupLeftHomologyLadder and PicardExternalCupRightExactLadder (equality
of signed values used as equality of unsigned values), and
PicardH1ProductSpanningBypass (degree-one factor not simplified).
PicardExternalCupLeftCechGenerators also needs the signed generator conclusion:
its proof ends by applying the signed normalization from PicardLeftCechCupHomology.
These original failures are captured in scratch users and repaired together.

The two ladder helpers now call picardExternalCupHomology_unique, removing their
redundant Kunneth proofs and imports. The acyclic proof simplifies (-1)^(0*0).
The left comparison cancels the square of the common sign. The H1 helper uses
p+q=1 to prove p*q=0 and simplifies the sign. Its pre-existing private axiom
picardExternalCupCochain_h1_isIso is replaced by a theorem with the same signature,
proved by picardExternalCupCochain_isIso at n=1. This removes an arbitrary axiom;
no new data construction or theorem hole is introduced. Existing unscoped
maxHeartbeats and long lines in that adapted module are corrected to avoid
compiler warnings, keeping the same budget on the two declarations that need it.

The H1 bypass module imports ProperBasic and TensorKunnethNat only for proofs;
these imports are made plain imports. The defining Mathlib Proper module is
imported publicly because the public theorem signature uses IsProper. Its sole direct importer, PicardH1ProductSpanning,
is checked against the resulting module interface.

## Status

landed 20261015T040627-L-472947 2026-10-15 (merge of deliver/K1/Sheaf.AlgebraicGeometry.ScalarCupResolutionClassCompatibility)
