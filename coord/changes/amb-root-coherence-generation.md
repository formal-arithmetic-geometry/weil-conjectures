# AlgebraicGeometry.Scheme.AmbRootTowerPullbackCoherence

## Reason

The concrete dependent record repeatedly expands scalar-extension modules while checking
its fields and generated declarations. Its original interface alone took 55–60 seconds;
the complete proof exceeded 60 seconds. Parameterize the record by the two tensor modules
and their pure-section functions, then specialize it to exactly the original constructions.
Each original law is named once as a proposition and kept abstract during record generation.
Four proved canonical-instance facts cache sheafification and the existing root-tower limit.
The construction and its proof remain together in the original single module, which
compiled cleanly in 55.2 seconds during this repair (2026-10-24).

No hypothesis, map, normalization, or coherence equation is removed. The theorem's text
is unchanged. The old definitions of the tensor modules and pure sections stay verbatim.
Local reduction settings keep chosen scalar actions abstract during elaboration.
Unused generated constructor-index, SizeOf and injectivity declarations are disabled.

## Old

```lean
structure AmbRootTowerPullbackCoherence where
  /-- Constant-ring comparisons are the specified structure maps and are invertible. -/
  constant_iso : ∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    IsIso (proEtaleConstantInverseImageMap v CommRingCat.{u + 1}
      (CommRingCat.of (ULift.{u + 1} ℤ_[l]))) ∧
    (∀ s : ℕ, IsIso (proEtaleConstantInverseImageMap v CommRingCat.{u + 1}
      (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (s + 1))))))) ∧
    ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B],
      IsIso (proEtaleCoefficientInverseImageMap v B)
  /-- Finite root maps commute with the power transitions. -/
  root_transition : ∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T) (s : ℕ),
    (proEtaleSheafInverseImage v AddCommGrpCat.{u + 1}).map
        ((proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)).map
          (homOfLE (Nat.le_succ s)).op) ≫
        proEtaleRootsOfUnityInverseImageMap v (l ^ (s + 1)) =
      proEtaleRootsOfUnityInverseImageMap v (l ^ (s + 2)) ≫
        (proEtaleRootsOfUnityTower T' l (Fact.out : l.Prime)).map
          (homOfLE (Nat.le_succ s)).op
  /-- Semilinearity over the actual inverse-image finite ring structure map. -/
  root_linear : ∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T) (s : ℕ) (U : T'.ProEtᵒᵖ)
    (a : (proEtaleRootsOfUnityInverseImageRing v (l ^ (s + 1))).obj.obj U)
    (x : ((proEtaleSheafInverseImage v AddCommGrpCat.{u + 1}).obj
      (proEtaleRootsOfUnitySheaf T (l ^ (s + 1)))).obj.obj U),
    (proEtaleRootsOfUnityInverseImageMap v (l ^ (s + 1))).hom.app U
      (@SMul.smul _ _ (proEtaleRootsOfUnityInverseImageAction v (l ^ (s + 1))
        (pow_pos (Fact.out : l.Prime).pos _) U).toSMul a x) =
      @SMul.smul _ _ (torsionSheafModuleStructure.{u + 1} (ProEt.topology T')
        (l ^ (s + 1)) (pow_pos (Fact.out : l.Prime).pos _)
        (proEtaleRootsOfUnitySheaf T' (l ^ (s + 1)))
        (proEtaleRootsOfUnity_nsmul T' (l ^ (s + 1))) U).toSMul
        ((proEtaleConstantInverseImageMap v RingCat.{u + 1}
          (RingCat.of (ULift.{u + 1} (ZMod (l ^ (s + 1)))))).hom.app U a)
        ((proEtaleRootsOfUnityInverseImageMap v (l ^ (s + 1))).hom.app U x)
  /-- Identity of finite root maps, transposed under the specified adjunction. -/
  root_id : ∀ (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.presheaf.stalk x)] (s : ℕ) (U : T.ProEt)
    (x : (proEtaleRootsOfUnitySheaf T (l ^ (s + 1))).obj.obj (op U)),
    (proEtaleRootsOfUnityDirectImageMap (𝟙 T) (l ^ (s + 1))).hom.app (op U) x =
      (proEtaleRootsOfUnitySheaf T (l ^ (s + 1))).obj.map
        ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).hom.app U).op x
  /-- Composition of the specified finite root maps. -/
  root_comp : ∀ {T T' T'' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)]
    [∀ x : T'', Invertible (l : T''.presheaf.stalk x)] (v : T' ⟶ T) (w : T'' ⟶ T')
    (s : ℕ) (U : T.ProEt)
    (x : (proEtaleRootsOfUnitySheaf T (l ^ (s + 1))).obj.obj (op U)),
    (proEtaleRootsOfUnityDirectImageMap (w ≫ v) (l ^ (s + 1))).hom.app (op U) x =
      (proEtaleRootsOfUnitySheaf T'' (l ^ (s + 1))).obj.map
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) w v).hom.app U).op
        ((proEtaleRootsOfUnityDirectImageMap w (l ^ (s + 1))).hom.app
          (op ((proEtaleBaseChange v).obj U))
          ((proEtaleRootsOfUnityDirectImageMap v (l ^ (s + 1))).hom.app (op U) x))
  /-- The adjunct of the map to the target inverse limit. -/
  c : ∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    purTwistZlOne T l ⟶
      (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).obj (purTwistZlOne T' l)
  /-- The specified projection equation, transposed under adjunction. -/
  c_projection : ∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T) (s : ℕ),
    c v ≫ (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).map
        (limit.π (proEtaleRootsOfUnityTower T' l (Fact.out : l.Prime)) (op s)) =
      limit.π (proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) (op s) ≫
        proEtaleRootsOfUnityDirectImageMap v (l ^ (s + 1))
  /-- Uniqueness among all additive maps with the specified projections. -/
  c_unique : ∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T)
    (f : purTwistZlOne T l ⟶
      (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).obj (purTwistZlOne T' l)),
    (∀ s : ℕ, f ≫ (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).map
        (limit.π (proEtaleRootsOfUnityTower T' l (Fact.out : l.Prime)) (op s)) =
      limit.π (proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) (op s) ≫
        proEtaleRootsOfUnityDirectImageMap v (l ^ (s + 1))) → f = c v
  /-- Constant Z_l-linearity of c_L, in its equivalent adjunct form. -/
  c_linear : ∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T) (U : T.ProEt)
    (a : (purTwistZlConstant T l).obj.obj (op U))
    (x : (purTwistZlOne T l).obj.obj (op U)),
    (c v).hom.app (op U) (ambRootAction l T (op U) a x) =
      ambRootAction l T' (op ((proEtaleBaseChange v).obj U))
        ((proEtaleConstantDirectImageMap v CommRingCat.{u + 1}
          (CommRingCat.of (ULift.{u + 1} ℤ_[l]))).hom.app (op U) a)
        ((c v).hom.app (op U) x)
  /-- Identity of c_L under the canonical fibre-product identity. -/
  c_id : ∀ (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.presheaf.stalk x)] (U : T.ProEt)
    (x : (purTwistZlOne T l).obj.obj (op U)),
    (c (𝟙 T)).hom.app (op U) x = (purTwistZlOne T l).obj.map
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).hom.app U).op x
  /-- Composition of c_L under the canonical fibre-product associator. -/
  c_comp : ∀ {T T' T'' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)]
    [∀ x : T'', Invertible (l : T''.presheaf.stalk x)] (v : T' ⟶ T) (w : T'' ⟶ T')
    (U : T.ProEt)
    (x : (purTwistZlOne T l).obj.obj (op U)),
    (c (w ≫ v)).hom.app (op U) x = (purTwistZlOne T'' l).obj.map
      ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) w v).hom.app U).op
      ((c w).hom.app (op ((proEtaleBaseChange v).obj U)) ((c v).hom.app (op U) x))
  /-- The B-linear adjunct of h_v. -/
  h : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    ambRootTensor l B T ⟶
      (proEtaleConstantModuleDirectImage v B).obj (ambRootTensor l B T')
  /-- Tensor normalization: h_v is c_L tensor 1, not an arbitrary map. -/
  h_pure : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T) (U : T.ProEt)
    (b : (proEtaleConstantRing T B).obj.obj (op U))
    (x : (purTwistZlOne T l).obj.obj (op U)),
    (h B v).val.app (op U) (ambRootTensorPure l B T U b x) =
      ambRootTensorPure l B T' ((proEtaleBaseChange v).obj U)
        ((proEtaleCoefficientDirectImageMap v B).hom.app (op U) b)
        ((c v).hom.app (op U) x)
  /-- Identity of h_v on all sections. -/
  h_id : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.presheaf.stalk x)] (U : T.ProEt)
    (x : (ambRootTensor l B T).val.obj (op U)),
    (h B (𝟙 T)).val.app (op U) x = (ambRootTensor l B T).val.map
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).hom.app U).op x
  /-- Composition of h_v on all sections, with the canonical associator. -/
  h_comp : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    {T T' T'' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)]
    [∀ x : T'', Invertible (l : T''.presheaf.stalk x)] (v : T' ⟶ T) (w : T'' ⟶ T')
    (U : T.ProEt) (x : (ambRootTensor l B T).val.obj (op U)),
    (h B (w ≫ v)).val.app (op U) x = (ambRootTensor l B T'').val.map
      ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) w v).hom.app U).op
      ((h B w).val.app (op ((proEtaleBaseChange v).obj U)) ((h B v).val.app (op U) x))
  /-- The B-linear projection-induced reduction, without an invertibility claim. -/
  alpha : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (r : ℕ)
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.presheaf.stalk x)],
    ambRootTensor l B T ⟶ ambRootFiniteTensor l B r hB T
  /-- The projection formula determining alpha. -/
  alpha_pure : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (r : ℕ)
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.presheaf.stalk x)] (U : T.ProEt)
    (b : (proEtaleConstantRing T B).obj.obj (op U))
    (x : (purTwistZlOne T l).obj.obj (op U)),
    (alpha B r hB T).val.app (op U) (ambRootTensorPure l B T U b x) =
      ambRootFinitePure l B r hB T U b
        ((limit.π (proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) (op r)).hom.app (op U) x)
  /-- The B-linear adjunct of the finite root map tensor 1. -/
  d : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (r : ℕ)
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    ambRootFiniteTensor l B r hB T ⟶
      (proEtaleConstantModuleDirectImage v B).obj (ambRootFiniteTensor l B r hB T')
  /-- Normalization of the finite tensor map by the specified root adjunct. -/
  d_pure : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (r : ℕ)
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T) (U : T.ProEt)
    (b : (proEtaleConstantRing T B).obj.obj (op U))
    (x : (proEtaleRootsOfUnitySheaf T (l ^ (r + 1))).obj.obj (op U)),
    (d B r hB v).val.app (op U) (ambRootFinitePure l B r hB T U b x) =
      ambRootFinitePure l B r hB T' ((proEtaleBaseChange v).obj U)
        ((proEtaleCoefficientDirectImageMap v B).hom.app (op U) b)
        ((proEtaleRootsOfUnityDirectImageMap v (l ^ (r + 1))).hom.app (op U) x)
  /-- Exactly the displayed reduction square, transposed under module adjunction. -/
  square : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (r : ℕ)
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    h B v ≫ (proEtaleConstantModuleDirectImage v B).map (alpha B r hB T') =
      alpha B r hB T ≫ d B r hB v
```

## New

```lean
/-- A named component of canonical root pullback coherence.
Source: Stacks Tags 03CB and 03CO (blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootConstantIso : Prop :=
∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    IsIso (proEtaleConstantInverseImageMap v CommRingCat.{u + 1}
      (CommRingCat.of (ULift.{u + 1} ℤ_[l]))) ∧
    (∀ s : ℕ, IsIso (proEtaleConstantInverseImageMap v CommRingCat.{u + 1}
      (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (s + 1))))))) ∧
    ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B],
      IsIso (proEtaleCoefficientInverseImageMap v B)

attribute [local irreducible] AmbRootConstantIso

/-- A named component of canonical root pullback coherence.
Source: Stacks Tags 03CB and 03CO (blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootTransition : Prop :=
∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T) (s : ℕ),
    (proEtaleSheafInverseImage v AddCommGrpCat.{u + 1}).map
        ((proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)).map
          (homOfLE (Nat.le_succ s)).op) ≫
        proEtaleRootsOfUnityInverseImageMap v (l ^ (s + 1)) =
      proEtaleRootsOfUnityInverseImageMap v (l ^ (s + 2)) ≫
        (proEtaleRootsOfUnityTower T' l (Fact.out : l.Prime)).map
          (homOfLE (Nat.le_succ s)).op

attribute [local irreducible] AmbRootTransition

/-- The specified finite-root semilinearity proposition, kept abstract during record generation.
Source: Stacks Tag 03CY (blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootFiniteSemilinear : Prop :=
∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T) (s : ℕ) (U : T'.ProEtᵒᵖ)
    (a : (proEtaleRootsOfUnityInverseImageRing v (l ^ (s + 1))).obj.obj U)
    (x : ((proEtaleSheafInverseImage v AddCommGrpCat.{u + 1}).obj
      (proEtaleRootsOfUnitySheaf T (l ^ (s + 1)))).obj.obj U),
    (proEtaleRootsOfUnityInverseImageMap v (l ^ (s + 1))).hom.app U
      (@SMul.smul _ _ (proEtaleRootsOfUnityInverseImageAction v (l ^ (s + 1))
        (pow_pos (Fact.out : l.Prime).pos _) U).toSMul a x) =
      @SMul.smul _ _ (torsionSheafModuleStructure.{u + 1} (ProEt.topology T')
        (l ^ (s + 1)) (pow_pos (Fact.out : l.Prime).pos _)
        (proEtaleRootsOfUnitySheaf T' (l ^ (s + 1)))
        (proEtaleRootsOfUnity_nsmul T' (l ^ (s + 1))) U).toSMul
        ((proEtaleConstantInverseImageMap v RingCat.{u + 1}
          (RingCat.of (ULift.{u + 1} (ZMod (l ^ (s + 1)))))).hom.app U a)
        ((proEtaleRootsOfUnityInverseImageMap v (l ^ (s + 1))).hom.app U x)

attribute [local irreducible] AmbRootFiniteSemilinear

/-- Identity of finite root maps, transposed under the specified adjunction. 
Source: Stacks Tags 03CO and 03EK
(blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootLawRootId : Prop :=
∀ (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.presheaf.stalk x)] (s : ℕ) (U : T.ProEt)
    (x : (proEtaleRootsOfUnitySheaf T (l ^ (s + 1))).obj.obj (op U)),
    (proEtaleRootsOfUnityDirectImageMap (𝟙 T) (l ^ (s + 1))).hom.app (op U) x =
      (proEtaleRootsOfUnitySheaf T (l ^ (s + 1))).obj.map
        ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).hom.app U).op x

attribute [local irreducible] AmbRootLawRootId

/-- Composition of the specified finite root maps. 
Source: Stacks Tags 03CO and 03EK
(blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootLawRootComp : Prop :=
∀ {T T' T'' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)]
    [∀ x : T'', Invertible (l : T''.presheaf.stalk x)] (v : T' ⟶ T) (w : T'' ⟶ T')
    (s : ℕ) (U : T.ProEt)
    (x : (proEtaleRootsOfUnitySheaf T (l ^ (s + 1))).obj.obj (op U)),
    (proEtaleRootsOfUnityDirectImageMap (w ≫ v) (l ^ (s + 1))).hom.app (op U) x =
      (proEtaleRootsOfUnitySheaf T'' (l ^ (s + 1))).obj.map
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) w v).hom.app U).op
        ((proEtaleRootsOfUnityDirectImageMap w (l ^ (s + 1))).hom.app
          (op ((proEtaleBaseChange v).obj U))
          ((proEtaleRootsOfUnityDirectImageMap v (l ^ (s + 1))).hom.app (op U) x))

attribute [local irreducible] AmbRootLawRootComp

/-- The specified projection equation, transposed under adjunction. 
Source: Stacks Tags 03CO and 03EK
(blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootLawCProjection
    (c : ∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    purTwistZlOne T l ⟶
      (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).obj (purTwistZlOne T' l)) : Prop :=
∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T) (s : ℕ),
    c v ≫ (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).map
        (limit.π (proEtaleRootsOfUnityTower T' l (Fact.out : l.Prime)) (op s)) =
      limit.π (proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) (op s) ≫
        proEtaleRootsOfUnityDirectImageMap v (l ^ (s + 1))

attribute [local irreducible] AmbRootLawCProjection

/-- Uniqueness among all additive maps with the specified projections. 
Source: Stacks Tags 03CO and 03EK
(blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootLawCUnique
    (c : ∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    purTwistZlOne T l ⟶
      (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).obj (purTwistZlOne T' l)) : Prop :=
∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T)
    (f : purTwistZlOne T l ⟶
      (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).obj (purTwistZlOne T' l)),
    (∀ s : ℕ, f ≫ (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).map
        (limit.π (proEtaleRootsOfUnityTower T' l (Fact.out : l.Prime)) (op s)) =
      limit.π (proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) (op s) ≫
        proEtaleRootsOfUnityDirectImageMap v (l ^ (s + 1))) → f = c v

attribute [local irreducible] AmbRootLawCUnique

/-- Constant Z_l-linearity of c_L, in its equivalent adjunct form. 
Source: Stacks Tags 03CO and 03EK
(blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootLawCLinear
    (c : ∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    purTwistZlOne T l ⟶
      (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).obj (purTwistZlOne T' l)) : Prop :=
∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T) (U : T.ProEt)
    (a : (purTwistZlConstant T l).obj.obj (op U))
    (x : (purTwistZlOne T l).obj.obj (op U)),
    (c v).hom.app (op U) (ambRootAction l T (op U) a x) =
      ambRootAction l T' (op ((proEtaleBaseChange v).obj U))
        ((proEtaleConstantDirectImageMap v CommRingCat.{u + 1}
          (CommRingCat.of (ULift.{u + 1} ℤ_[l]))).hom.app (op U) a)
        ((c v).hom.app (op U) x)

attribute [local irreducible] AmbRootLawCLinear

/-- Identity of c_L under the canonical fibre-product identity. 
Source: Stacks Tags 03CO and 03EK
(blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootLawCId
    (c : ∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    purTwistZlOne T l ⟶
      (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).obj (purTwistZlOne T' l)) : Prop :=
∀ (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.presheaf.stalk x)] (U : T.ProEt)
    (x : (purTwistZlOne T l).obj.obj (op U)),
    (c (𝟙 T)).hom.app (op U) x = (purTwistZlOne T l).obj.map
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).hom.app U).op x

attribute [local irreducible] AmbRootLawCId

/-- Composition of c_L under the canonical fibre-product associator. 
Source: Stacks Tags 03CO and 03EK
(blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootLawCComp
    (c : ∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    purTwistZlOne T l ⟶
      (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).obj (purTwistZlOne T' l)) : Prop :=
∀ {T T' T'' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)]
    [∀ x : T'', Invertible (l : T''.presheaf.stalk x)] (v : T' ⟶ T) (w : T'' ⟶ T')
    (U : T.ProEt)
    (x : (purTwistZlOne T l).obj.obj (op U)),
    (c (w ≫ v)).hom.app (op U) x = (purTwistZlOne T'' l).obj.map
      ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) w v).hom.app U).op
      ((c w).hom.app (op ((proEtaleBaseChange v).obj U)) ((c v).hom.app (op U) x))

attribute [local irreducible] AmbRootLawCComp

/-- Tensor normalization: h_v is c_L tensor 1, not an arbitrary map. 
Source: Stacks Tags 03CO and 03EK
(blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootLawHPure
    (H : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (T : Scheme.{u}),
      SheafOfModules.{u + 1} (purTwistRing T (proEtaleConstantRing T B)))
    (HP : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
      (T : Scheme.{u}) (U : T.ProEt)
      (_b : (proEtaleConstantRing T B).obj.obj (op U))
      (_x : (purTwistZlOne T l).obj.obj (op U)), (H B T).val.obj (op U))
    (c : ∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    purTwistZlOne T l ⟶
      (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).obj (purTwistZlOne T' l))
    (h : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    H B T ⟶
      (proEtaleConstantModuleDirectImage v B).obj (H B T')) : Prop :=
∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T) (U : T.ProEt)
    (b : (proEtaleConstantRing T B).obj.obj (op U))
    (x : (purTwistZlOne T l).obj.obj (op U)),
    (h B v).val.app (op U) (HP B T U b x) =
      HP B T' ((proEtaleBaseChange v).obj U)
        ((proEtaleCoefficientDirectImageMap v B).hom.app (op U) b)
        ((c v).hom.app (op U) x)

attribute [local irreducible] AmbRootLawHPure

/-- Identity of h_v on all sections. 
Source: Stacks Tags 03CO and 03EK
(blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootLawHId
    (H : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (T : Scheme.{u}),
      SheafOfModules.{u + 1} (purTwistRing T (proEtaleConstantRing T B)))
    (h : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    H B T ⟶
      (proEtaleConstantModuleDirectImage v B).obj (H B T')) : Prop :=
∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.presheaf.stalk x)] (U : T.ProEt)
    (x : (H B T).val.obj (op U)),
    (h B (𝟙 T)).val.app (op U) x = (H B T).val.map
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).hom.app U).op x

attribute [local irreducible] AmbRootLawHId

/-- Composition of h_v on all sections, with the canonical associator. 
Source: Stacks Tags 03CO and 03EK
(blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootLawHComp
    (H : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (T : Scheme.{u}),
      SheafOfModules.{u + 1} (purTwistRing T (proEtaleConstantRing T B)))
    (h : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    H B T ⟶
      (proEtaleConstantModuleDirectImage v B).obj (H B T')) : Prop :=
∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    {T T' T'' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)]
    [∀ x : T'', Invertible (l : T''.presheaf.stalk x)] (v : T' ⟶ T) (w : T'' ⟶ T')
    (U : T.ProEt) (x : (H B T).val.obj (op U)),
    (h B (w ≫ v)).val.app (op U) x = (H B T'').val.map
      ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) w v).hom.app U).op
      ((h B w).val.app (op ((proEtaleBaseChange v).obj U)) ((h B v).val.app (op U) x))

attribute [local irreducible] AmbRootLawHComp

/-- The projection formula determining alpha. 
Source: Stacks Tags 03CO and 03EK
(blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootLawAlphaPure
    (H : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (T : Scheme.{u}),
      SheafOfModules.{u + 1} (purTwistRing T (proEtaleConstantRing T B)))
    (HP : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
      (T : Scheme.{u}) (U : T.ProEt)
      (_b : (proEtaleConstantRing T B).obj.obj (op U))
      (_x : (purTwistZlOne T l).obj.obj (op U)), (H B T).val.obj (op U))
    (D : ∀ (B : Type u) [CommRing B] (n : ℕ)
      (_hB : ((l ^ (n + 1) : ℕ) : B) = 0) (T : Scheme.{u}),
      SheafOfModules.{u + 1} (purTwistRing T (proEtaleConstantRing T B)))
    (DP : ∀ (B : Type u) [CommRing B] (n : ℕ)
      (_hB : ((l ^ (n + 1) : ℕ) : B) = 0) (T : Scheme.{u}) (U : T.ProEt)
      (_b : (proEtaleConstantRing T B).obj.obj (op U))
      (_x : (proEtaleRootsOfUnitySheaf T (l ^ (n + 1))).obj.obj (op U)),
      (D B n _hB T).val.obj (op U))
    (alpha : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (r : ℕ)
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.presheaf.stalk x)],
    H B T ⟶ D B r hB T) : Prop :=
∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (r : ℕ)
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.presheaf.stalk x)] (U : T.ProEt)
    (b : (proEtaleConstantRing T B).obj.obj (op U))
    (x : (purTwistZlOne T l).obj.obj (op U)),
    (alpha B r hB T).val.app (op U) (HP B T U b x) =
      DP B r hB T U b
        ((limit.π (proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) (op r)).hom.app (op U) x)

attribute [local irreducible] AmbRootLawAlphaPure

/-- Normalization of the finite tensor map by the specified root adjunct. 
Source: Stacks Tags 03CO and 03EK
(blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootLawDPure
    (D : ∀ (B : Type u) [CommRing B] (n : ℕ)
      (_hB : ((l ^ (n + 1) : ℕ) : B) = 0) (T : Scheme.{u}),
      SheafOfModules.{u + 1} (purTwistRing T (proEtaleConstantRing T B)))
    (DP : ∀ (B : Type u) [CommRing B] (n : ℕ)
      (_hB : ((l ^ (n + 1) : ℕ) : B) = 0) (T : Scheme.{u}) (U : T.ProEt)
      (_b : (proEtaleConstantRing T B).obj.obj (op U))
      (_x : (proEtaleRootsOfUnitySheaf T (l ^ (n + 1))).obj.obj (op U)),
      (D B n _hB T).val.obj (op U))
    (d : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (r : ℕ)
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    D B r hB T ⟶
      (proEtaleConstantModuleDirectImage v B).obj (D B r hB T')) : Prop :=
∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (r : ℕ)
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T) (U : T.ProEt)
    (b : (proEtaleConstantRing T B).obj.obj (op U))
    (x : (proEtaleRootsOfUnitySheaf T (l ^ (r + 1))).obj.obj (op U)),
    (d B r hB v).val.app (op U) (DP B r hB T U b x) =
      DP B r hB T' ((proEtaleBaseChange v).obj U)
        ((proEtaleCoefficientDirectImageMap v B).hom.app (op U) b)
        ((proEtaleRootsOfUnityDirectImageMap v (l ^ (r + 1))).hom.app (op U) x)

attribute [local irreducible] AmbRootLawDPure

/-- Exactly the displayed reduction square, transposed under module adjunction. 
Source: Stacks Tags 03CO and 03EK
(blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootLawSquare
    (H : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (T : Scheme.{u}),
      SheafOfModules.{u + 1} (purTwistRing T (proEtaleConstantRing T B)))
    (D : ∀ (B : Type u) [CommRing B] (n : ℕ)
      (_hB : ((l ^ (n + 1) : ℕ) : B) = 0) (T : Scheme.{u}),
      SheafOfModules.{u + 1} (purTwistRing T (proEtaleConstantRing T B)))
    (h : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    H B T ⟶
      (proEtaleConstantModuleDirectImage v B).obj (H B T'))
    (alpha : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (r : ℕ)
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.presheaf.stalk x)],
    H B T ⟶ D B r hB T)
    (d : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (r : ℕ)
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    D B r hB T ⟶
      (proEtaleConstantModuleDirectImage v B).obj (D B r hB T')) : Prop :=
∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (r : ℕ)
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    h B v ≫ (proEtaleConstantModuleDirectImage v B).map (alpha B r hB T') =
      alpha B r hB T ≫ d B r hB v

attribute [local irreducible] AmbRootLawSquare

-- Keep large dependent constructor equations out of the generated API.
set_option genCtorIdx false in
set_option genSizeOf false in
set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- All canonical maps and their normalizations. The maps c, h and d are direct-image
adjuncts of c_L, h_v and c_r tensor 1; their section equations are equations on the
original unit sections, not an assertion that pulled-back sections are pure tensors.
Source: Stacks Tags 03CO, 03DB, 03CB, 03EL and 03D7
(blueprint: lem-amb-root-tower-pullback-coherence). -/
structure AmbRootTowerPullbackCoherenceData
    (H : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (T : Scheme.{u}),
      SheafOfModules.{u + 1} (purTwistRing T (proEtaleConstantRing T B)))
    (HP : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
      (T : Scheme.{u}) (U : T.ProEt)
      (_b : (proEtaleConstantRing T B).obj.obj (op U))
      (_x : (purTwistZlOne T l).obj.obj (op U)), (H B T).val.obj (op U))
    (D : ∀ (B : Type u) [CommRing B] (n : ℕ)
      (_hB : ((l ^ (n + 1) : ℕ) : B) = 0) (T : Scheme.{u}),
      SheafOfModules.{u + 1} (purTwistRing T (proEtaleConstantRing T B)))
    (DP : ∀ (B : Type u) [CommRing B] (n : ℕ)
      (_hB : ((l ^ (n + 1) : ℕ) : B) = 0) (T : Scheme.{u}) (U : T.ProEt)
      (_b : (proEtaleConstantRing T B).obj.obj (op U))
      (_x : (proEtaleRootsOfUnitySheaf T (l ^ (n + 1))).obj.obj (op U)),
      (D B n _hB T).val.obj (op U)) where
  /-- Constant-ring comparisons are the specified structure maps and are invertible. -/
  constant_iso : AmbRootConstantIso.{u} l
  /-- Finite root maps commute with the power transitions. -/
  root_transition : AmbRootTransition.{u} l
  /-- Semilinearity over the actual inverse-image finite ring structure map. -/
  root_linear : AmbRootFiniteSemilinear.{u} l
  /-- Identity of finite root maps, transposed under the specified adjunction. -/
  root_id : AmbRootLawRootId.{u} l
  /-- Composition of the specified finite root maps. -/
  root_comp : AmbRootLawRootComp.{u} l
  /-- The adjunct of the map to the target inverse limit. -/
  c : ∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    purTwistZlOne T l ⟶
      (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).obj (purTwistZlOne T' l)
  /-- The specified projection equation, transposed under adjunction. -/
  c_projection : AmbRootLawCProjection.{u} l c
  /-- Uniqueness among all additive maps with the specified projections. -/
  c_unique : AmbRootLawCUnique.{u} l c
  /-- Constant Z_l-linearity of c_L, in its equivalent adjunct form. -/
  c_linear : AmbRootLawCLinear.{u} l c
  /-- Identity of c_L under the canonical fibre-product identity. -/
  c_id : AmbRootLawCId.{u} l c
  /-- Composition of c_L under the canonical fibre-product associator. -/
  c_comp : AmbRootLawCComp.{u} l c
  /-- The B-linear adjunct of h_v. -/
  h : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    H B T ⟶
      (proEtaleConstantModuleDirectImage v B).obj (H B T')
  /-- Tensor normalization: h_v is c_L tensor 1, not an arbitrary map. -/
  h_pure : AmbRootLawHPure.{u} l H HP c h
  /-- Identity of h_v on all sections. -/
  h_id : AmbRootLawHId.{u} l H h
  /-- Composition of h_v on all sections, with the canonical associator. -/
  h_comp : AmbRootLawHComp.{u} l H h
  /-- The B-linear projection-induced reduction, without an invertibility claim. -/
  alpha : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (r : ℕ)
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.presheaf.stalk x)],
    H B T ⟶ D B r hB T
  /-- The projection formula determining alpha. -/
  alpha_pure : AmbRootLawAlphaPure.{u} l H HP D DP alpha
  /-- The B-linear adjunct of the finite root map tensor 1. -/
  d : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (r : ℕ)
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    D B r hB T ⟶
      (proEtaleConstantModuleDirectImage v B).obj (D B r hB T')
  /-- Normalization of the finite tensor map by the specified root adjunct. -/
  d_pure : AmbRootLawDPure.{u} l D DP d
  /-- Exactly the displayed reduction square, transposed under module adjunction. -/
  square : AmbRootLawSquare.{u} l H D h alpha d

/-- The coherence data for the specified ordinary root tensors.
Source: Stacks Tags 03CO, 03DB, 03CB, 03EL and 03D7
(blueprint: lem-amb-root-tower-pullback-coherence). -/
abbrev AmbRootTowerPullbackCoherence :=
  AmbRootTowerPullbackCoherenceData l (ambRootTensor l) (ambRootTensorPure l)
    (ambRootFiniteTensor l) (ambRootFinitePure l)

attribute [local semireducible] AmbRootFiniteSemilinear AmbRootTransition AmbRootConstantIso
attribute [local semireducible]
  AmbRootLawRootId
  AmbRootLawRootComp
  AmbRootLawCProjection
  AmbRootLawCUnique
  AmbRootLawCLinear
  AmbRootLawCId
  AmbRootLawCComp
  AmbRootLawHPure
  AmbRootLawHId
  AmbRootLawHComp
  AmbRootLawAlphaPure
  AmbRootLawDPure
  AmbRootLawSquare
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AmbRootTowerPullbackCoherence | T8 | Constructs the specialized record with all 20 original fields. |
| Sheaf.Paper.AmbTateRootProjectionReduction | unclaimed | Direct importer; uses the record through field notation, including alpha, c, h, d and their laws. The specialized fields retain their types; no source adaptation. |
| Sheaf.Paper.CartierRelativeKummerRealization | unclaimed | Transitive importer through AmbTateRootProjectionReduction; no direct reference to this record and no source adaptation. |
| Sheaf.Paper.SignedTwistSiteTransport | unclaimed | Transitive importer through AmbTateRootProjectionReduction; no direct reference to this record and no source adaptation. |

On 2026-10-24, `tools/downstream.py Sheaf.Paper.AmbRootTowerPullbackCoherence --uses
AmbRootTowerPullbackCoherence` lists the item and `AmbTateRootProjectionReduction` as
users of the record name, and the three downstream modules above. The direct importer
uses field notation rather than the old projection namespace. Its source is checked
unchanged against the specialized record: `lcompile.py --all` compiled the item in
55.2 seconds and that consumer in 95.9 seconds, both with exit code 0 and no warnings.
The unchanged consumer is not included in the delivery; no consumer adaptation is required.
The DAG parents and unit route are preserved. No target statement uses this representation
in its signature; only proofs below the targets use the item.

## Status

landed 20261024T191301-L-292404 2026-10-24 (merge of deliver/T8/Sheaf.Paper.AmbRootTowerPullbackCoherence)

Repair of returned head `1b22ee7668d`, 2026-10-24: the prior reader accepted the proof;
landing failed because its change-record override used the plain `.md` basename.
This record is delivered at `coord/changes/amb-root-coherence-generation.md`.
For `--apply-fixes`, the landing tool recognizes its flat override basename as
`amb-root-coherence-generation.change.md`. The repair corrects the field count and
updates the consumer inventory to current `sheaf-dag`.

## Canonical instance caches

```lean
set_option maxHeartbeats 100000 in
-- Bound the one-time search for the cached sheafification proof.
/-- The canonical constant-ring sheafification instance, cached for the constructions below. -/
theorem ambRootCommRingSheafify (S : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology S) CommRingCat.{u + 1} := inferInstance

set_option maxHeartbeats 100000 in
-- Bound the one-time search for the cached sheafification proof.
/-- The canonical ring sheafification instance, cached for the constructions below. -/
theorem ambRootRingSheafify (S : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology S) RingCat.{u + 1} := inferInstance

set_option maxHeartbeats 100000 in
-- Bound the one-time search for the cached sheafification proof.
/-- The canonical abelian sheafification instance, cached for the constructions below. -/
theorem ambRootAbSheafify (S : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology S) AddCommGrpCat.{u + 1} :=
  (CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
    AddCommGrpCat.{u + 1} S).isRightAdjoint

attribute [local instance] ambRootCommRingSheafify ambRootRingSheafify ambRootAbSheafify

/-- The canonical limit instance of the existing root tower, cached for its projections. -/
theorem ambRootHasLimit (S : Scheme.{u}) :
    HasLimit (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) := inferInstance

attribute [local instance] ambRootHasLimit
```
