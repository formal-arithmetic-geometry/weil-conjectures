# scalarCup_resolution_class_compatibility

## Reason

The original unsigned comparison conflicts with the library's left-then-right
Yoneda shift convention in odd bidegrees. The private audit in the original module
proves that order, the minus sign on the (1,1) tensor summand, and a nonzero rational
single-complex test before localization. This test fixes the chain-level sign;
it is not itself a counterexample consisting of scheme cohomology classes, nor
a proof of the all-degree localized comparison. That comparison remains the
explicit positive-degree obligation in this delivery. The launcher explicitly
instructed this worker to repair the sign and every caller in one delivery. The corrected
formula multiplies the unsigned resolution class by (-1)^(p*q). Its degree-zero
specialization is unchanged. All six direct caller modules were unclaimed when checked.

The factor propagates through scalar/module cup comparison, external comparison, and the
canonical Cech comparison. The repair keeps the canonical factor and product comparisons
in PicardRightCechCupCycleComparison and states its signed formula explicitly. Its direct
caller PicardRightCechCupGenerators absorbs the sign in its existential tensor-homology
equivalence: precompose with the direct sum of (-1)^(p*q) scalar automorphisms. This
preserves its exact public signature, both external-cup normalization predicates, and
all higher interfaces. In particular PicardExternalCupLeftCechGenerators and
PicardKunnethCechModels keep their original source and normalization formulas. No target
statement or definition changes. All adapted modules are unclaimed in the claims snapshot.
The unit route is retained.

Sources: [Stacks 0FKV](https://stacks.math.columbia.edu/tag/0FKV),
[Stacks 01F7](https://stacks.math.columbia.edu/tag/01F7), and Mathlib's
mapBifunctorShift₁Iso_trans_mapBifunctorShift₂Iso. The two Stacks tag pages were read on
2026-10-15; the Koszul orientation is fixed by this library's scalarExtCup definition and
the existing private audit, rather than imposed by the source's notation.

The latest landing return found identical private `d_transport` lemmas in the
main and positive-degree modules. Both are removed in this repair: the two
chain-map proofs invoke Mathlib's `eqToHom_naturality` and
`HomologicalComplex.d_comp_eqToHom` directly. This is a proof-only repair to
the returned set; none of the six corrected public signatures changes again.

The current second reader also removed the six copied resolution-naturality
helpers from the main module and reused `computingClass_naturality` from
`ModuleCupCoefficientResolutionMaps` through a proof-only `import all`. The
redundant direct injective-resolution proof import is removed. This additional
repair changes no existing signature or definition and adds no hole.

## Old

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

## New

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

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechComparison | unclaimed | Transitive user; interface unchanged because existential comparison absorbs the sign. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechGenerators | unclaimed | Transitive user; interface unchanged because existential comparison absorbs the sign. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftComparisonComplexes | unclaimed | Transitive user; interface unchanged because existential comparison absorbs the sign. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftHomologyLadder | unclaimed | Transitive user; interface unchanged because existential comparison absorbs the sign. |
| Sheaf.AlgebraicGeometry.PicardExternalCupQuasiIso | unclaimed | Transitive user; interface unchanged because existential comparison absorbs the sign. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightCechDiagram | unclaimed | Transitive user; interface unchanged because existential comparison absorbs the sign. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightExactLadder | unclaimed | Transitive user; interface unchanged because existential comparison absorbs the sign. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightShortExact | unclaimed | Transitive user; interface unchanged because existential comparison absorbs the sign. |
| Sheaf.AlgebraicGeometry.PicardExternalCupShiftLeft | unclaimed | Transitive user; interface unchanged because existential comparison absorbs the sign. |
| Sheaf.AlgebraicGeometry.PicardExternalCupShiftRight | unclaimed | Transitive user; interface unchanged because existential comparison absorbs the sign. |
| Sheaf.AlgebraicGeometry.PicardExternalRightCechComparison | unclaimed | Transitive user; interface unchanged because existential comparison absorbs the sign. |
| Sheaf.AlgebraicGeometry.PicardKunnethCechModels | unclaimed | Transitive user; interface unchanged because existential comparison absorbs the sign. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcoh | unclaimed | Transitive user; interface unchanged because existential comparison absorbs the sign. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcohIso | unclaimed | Transitive user; interface unchanged because existential comparison absorbs the sign. |
| Sheaf.AlgebraicGeometry.PicardLeftCechCupHomology | unclaimed | Transitive user; interface unchanged because existential comparison absorbs the sign. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupCycleComparison | unclaimed | Canonical comparisons; add the bidegree sign to the cycle formula. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupGenerators | unclaimed | Proof adaptation only: tensor-summand sign equivalence; public signature identical. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupHomology | unclaimed | Transitive user; interface unchanged because existential comparison absorbs the sign. |
| Sheaf.AlgebraicGeometry.PicardScalarCechExternalCup | unclaimed | Corrected core and wrapper: sign on the canonical product comparison. |
| Sheaf.AlgebraicGeometry.ScalarCupModuleCupCompatibility | unclaimed | Corrected conclusion: sign times ordinary cup; proof uses corrected child. |
| Sheaf.AlgebraicGeometry.ScalarCupResolutionClassCompatibility | K1 | Corrected RHS to signed resolution class; both degree-zero axes proved. |
| Sheaf.AlgebraicGeometry.ScalarExternalCupModuleComparison | unclaimed | Corrected conclusion: sign times ordinary external cup; proof transports pullback equality. |

The direct theorem uses are scalarCup_resolution_class_compatibility in
ScalarCupModuleCupCompatibility, scalarCup_moduleCup_compatibility in
ScalarExternalCupModuleComparison, scalarExternalCup_moduleComparison in
PicardScalarCechExternalCup, the core theorem in its wrapper, the wrapper in
PicardRightCechCupCycleComparison, and the cycle formula in PicardRightCechCupGenerators.
All six direct callers are adapted together. Higher users retain their exact statements.
The repair does not deliver changes to IsPicardExternalCupCochain or
IsPicardExternalCupHomology: both definitions keep their original unsigned formula.
The signed cycle formula is consumed before those interfaces are reached, resolving
both compiler mismatches in the return. No target meaning review is reopened by a
definition change.

## Status

landed 20261015T091817-L-780521 2026-10-15 (merge of deliver/K1/Sheaf.AlgebraicGeometry.ScalarCupResolutionClassCompatibility)
