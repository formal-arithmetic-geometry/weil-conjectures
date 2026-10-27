# ComponentDerivedSquareData derived comparisons

## Reason

The original module repeatedly exceeds the 60-second compile limit before a worker can import it. Profiling locates expensive elaboration and kernel comparisons in the derived comparison signatures, Square.monoidal, and the large System and OrdinarySystem structures. Explicit result types for the ordinary module functors and irreducible derived functors/comparison bodies keep their fixed localization terms folded. A generic tensor-square predicate elaborates the same tensor and unit equations once, over arbitrary functors, rather than recomputing four derived tensor instances at each use. Generic squareIdentity and squareComposition predicates also factor the exact same identity and composition formulas out of System and OrdinarySystem. Their fields retain definitionally equal propositions and application behavior. No target statement changes.

## Old

```lean
def Corner.modules (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u}) [IsAffine X]
    (s : Corner Λ X) :=
  s.inverse.mapMod (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X)) ⋙
    Mod.comap s.coefficient.inv.hom

def Slice.modules (Λ : Profinite.CondensedRing.{u}) {P Q : Profinite.{u}} {h : Q ⟶ P}
    (s : Slice Λ h) :=
  s.inverse.mapMod (CondensedRing.profiniteCoefficient Λ.X P) ⋙
    Mod.comap s.coefficient.inv.hom

def Corner.derived (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u}) [IsAffine X]
    (s : Corner Λ X) := (s.modules Λ X).mapDerivedCategory

def Slice.derived (Λ : Profinite.CondensedRing.{u})
    {P Q : Profinite.{u}} {h : Q ⟶ P} (s : Slice Λ h) :=
  (s.modules Λ).mapDerivedCategory

def Square.theta (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] {f : Y ⟶ X}
    {sX : Corner Λ X} {sY : Corner Λ Y} {sh : Slice Λ (affineComponentMap f)}
    (sq : Square Λ f sX sY sh) : leftPath Λ sX f ≅ rightPath Λ sY f sh :=
  letI : (CondensedRing.upperStar Λ.X f).Additive :=
    CondensedRing.upperStar_additive Λ.X f
  letI : PreservesFiniteLimits (CondensedRing.upperStar Λ.X f) :=
    CondensedRing.preservesFiniteLimits_upperStar Λ.X f
  letI : PreservesFiniteColimits (CondensedRing.upperStar Λ.X f) :=
    CondensedRing.preservesFiniteColimits_upperStar Λ.X f
  letI := comp_preservesFiniteLimits (sX.modules Λ X) (CondensedRing.upperStar Λ.X f)
  letI := comp_preservesFiniteColimits (sX.modules Λ X) (CondensedRing.upperStar Λ.X f)
  letI := comp_preservesFiniteLimits (sh.modules Λ) (sY.modules Λ Y)
  letI := comp_preservesFiniteColimits (sh.modules Λ) (sY.modules Λ Y)
  letI : (sX.modules Λ X ⋙ CondensedRing.upperStar Λ.X f).Additive :=
    inferInstance
  letI : (sh.modules Λ ⋙ sY.modules Λ Y).Additive := inferInstance
  (Functor.mapDerivedCategoryCompIso (sX.modules Λ X)
      (CondensedRing.upperStar Λ.X f)).symm ≪≫
    Functor.mapDerivedCategoryNatIso sq.ordinary ≪≫
      Functor.mapDerivedCategoryCompIso (sh.modules Λ) (sY.modules Λ Y)

def SliceIdentity.derived (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u}) [IsAffine X]
    {s : Slice Λ (affineComponentMap (𝟙 X))} (i : SliceIdentity Λ X s) :=
  Functor.mapDerivedCategoryNatIso i.ordinary ≪≫ Functor.mapDerivedCategoryIdIso _

def SliceComposition.derived (Λ : Profinite.CondensedRing.{u})
    {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    {f : Y ⟶ X} {g : Z ⟶ Y}
    {sf : Slice Λ (affineComponentMap f)} {sg : Slice Λ (affineComponentMap g)}
    {sfg : Slice Λ (affineComponentMap (g ≫ f))}
    (c : SliceComposition Λ f g sf sg sfg) :=
  letI := comp_preservesFiniteLimits (sf.modules Λ) (sg.modules Λ)
  letI := comp_preservesFiniteColimits (sf.modules Λ) (sg.modules Λ)
  Functor.mapDerivedCategoryNatIso c.ordinary ≪≫
    Functor.mapDerivedCategoryCompIso (sf.modules Λ) (sg.modules Λ)

def schemeIdentity (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u}) :=
  Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarId Λ.X X) ≪≫
    Functor.mapDerivedCategoryIdIso _

def schemeComposition (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) :=
  letI := comp_preservesFiniteLimits (CondensedRing.upperStar Λ.X f)
    (CondensedRing.upperStar Λ.X g)
  letI := comp_preservesFiniteColimits (CondensedRing.upperStar Λ.X f)
    (CondensedRing.upperStar Λ.X g)
  Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp Λ.X g f) ≪≫
    Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar Λ.X f)
      (CondensedRing.upperStar Λ.X g)

def Square.monoidal (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] {f : Y ⟶ X}
    {sX : Corner Λ X} {sY : Corner Λ Y} {sh : Slice Λ (affineComponentMap f)}
    (sq : Square Λ f sX sY sh)
    (tX : TensorLift (sX.modules Λ X)) (tY : TensorLift (sY.modules Λ Y))
    (tf : TensorLift (CondensedRing.upperStar Λ.X f)) (th : TensorLift (sh.modules Λ)) : Prop :=
  letI := tX.monoidal
  letI := tY.monoidal
  letI := tf.monoidal
  letI := th.monoidal
  (∀ K L,
    Functor.LaxMonoidal.μ (CondensedRing.upperStar Λ.X f).mapDerivedCategory
        (((sX.modules Λ X).mapDerivedCategory).obj K)
        (((sX.modules Λ X).mapDerivedCategory).obj L) ≫
      (CondensedRing.upperStar Λ.X f).mapDerivedCategory.map
        (Functor.LaxMonoidal.μ (sX.modules Λ X).mapDerivedCategory K L) ≫
      (sq.theta Λ).hom.app (K ⊗ L) =
    ((sq.theta Λ).hom.app K ⊗ₘ (sq.theta Λ).hom.app L) ≫
      Functor.LaxMonoidal.μ (sY.modules Λ Y).mapDerivedCategory
        ((sh.modules Λ).mapDerivedCategory.obj K)
        ((sh.modules Λ).mapDerivedCategory.obj L) ≫
      (sY.modules Λ Y).mapDerivedCategory.map
        (Functor.LaxMonoidal.μ (sh.modules Λ).mapDerivedCategory K L)) ∧
  (Functor.LaxMonoidal.ε (CondensedRing.upperStar Λ.X f).mapDerivedCategory ≫
      (CondensedRing.upperStar Λ.X f).mapDerivedCategory.map
        (Functor.LaxMonoidal.ε (sX.modules Λ X).mapDerivedCategory) ≫
      (sq.theta Λ).hom.app (𝟙_ _) =
    Functor.LaxMonoidal.ε (sY.modules Λ Y).mapDerivedCategory ≫
      (sY.modules Λ Y).mapDerivedCategory.map
        (Functor.LaxMonoidal.ε (sh.modules Λ).mapDerivedCategory))

structure System (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] where
  corner : ∀ (X : Scheme.{u}) [IsAffine X], Corner Λ X
  slice : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
    Slice Λ (affineComponentMap f)
  square : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
    Square Λ f (corner X) (corner Y) (slice f)
  cornerTensor : ∀ (X : Scheme.{u}) [IsAffine X], TensorLift ((corner X).modules Λ X)
  sliceTensor : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
    TensorLift ((slice f).modules Λ)
  schemeTensor : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
    TensorLift (CondensedRing.upperStar Λ.X f)
  monoidal : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
    (square f).monoidal Λ (cornerTensor X) (cornerTensor Y) (schemeTensor f) (sliceTensor f)
  sliceIdentity : ∀ (X : Scheme.{u}) [IsAffine X], SliceIdentity Λ X (slice (𝟙 X))
  sliceComposition : ∀ {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (f : Y ⟶ X) (g : Z ⟶ Y),
    SliceComposition Λ f g (slice f) (slice g) (slice (g ≫ f))
  identity : ∀ (X : Scheme.{u}) [IsAffine X]
      (K : CondensedRing.Evaluation.D
        ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
        (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X))),
    ((square (𝟙 X)).theta Λ).hom.app K ≫
        ((corner X).derived Λ X).map (((sliceIdentity X).derived Λ X).hom.app K) =
      (schemeIdentity Λ X).hom.app (((corner X).derived Λ X).obj K)
  composition : ∀ (X Y Z : Scheme.{u}) [IsAffine X] [IsAffine Y] [IsAffine Z]
      (f : Y ⟶ X) (g : Z ⟶ Y)
      (K : CondensedRing.Evaluation.D
        ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
        (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X))),
    (schemeComposition Λ f g).hom.app (((corner X).derived Λ X).obj K) ≫
        (CondensedRing.upperStar Λ.X g).mapDerivedCategory.map
          (((square f).theta Λ).hom.app K) ≫
        ((square g).theta Λ).hom.app (((slice f).derived Λ).obj K) =
      ((square (g ≫ f)).theta Λ).hom.app K ≫
        ((corner Z).derived Λ Z).map (((sliceComposition f g).derived Λ).hom.app K)
  cornerDuals : ∀ (X : Scheme.{u}) [IsAffine X]
      (K : CondensedRing.Evaluation.D
        ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
        (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X))),
    IsDualizable K → IsDualizable (((corner X).derived Λ X).obj K)
  sliceDuals : ∀ (X Y : Scheme.{u}) [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
      (K : CondensedRing.Evaluation.D
        ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
        (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X))),
    IsDualizable K → IsDualizable (((slice f).derived Λ).obj K)
  schemeDuals : ∀ (X Y : Scheme.{u}) [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
      (K : CondensedRing.Evaluation.D (Scheme.ProEt.topology X) (condensedRingObj Λ.X X)),
    IsDualizable K → IsDualizable ((CondensedRing.upperStar Λ.X f).mapDerivedCategory.obj K)

structure OrdinarySystem (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] where
  corner : ∀ (X : Scheme.{u}) [IsAffine X], Corner Λ X
  slice : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
    Slice Λ (affineComponentMap f)
  square : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
    Square Λ f (corner X) (corner Y) (slice f)
  sliceIdentity : ∀ (X : Scheme.{u}) [IsAffine X], SliceIdentity Λ X (slice (𝟙 X))
  sliceComposition : ∀ {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (f : Y ⟶ X) (g : Z ⟶ Y),
    SliceComposition Λ f g (slice f) (slice g) (slice (g ≫ f))
  identity : ∀ (X : Scheme.{u}) [IsAffine X]
      (M : Mod (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
        Ab.{u + 1}) (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X))),
    ((square (𝟙 X)).ordinary).hom.app M ≫
        ((corner X).modules Λ X).map ((sliceIdentity X).ordinary.hom.app M) =
      (CondensedRing.upperStarId Λ.X X).hom.app (((corner X).modules Λ X).obj M)
  composition : ∀ (X Y Z : Scheme.{u}) [IsAffine X] [IsAffine Y] [IsAffine Z]
      (f : Y ⟶ X) (g : Z ⟶ Y)
      (M : Mod (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
        Ab.{u + 1}) (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X))),
    (CondensedRing.upperStarComp Λ.X g f).hom.app (((corner X).modules Λ X).obj M) ≫
        (CondensedRing.upperStar Λ.X g).map (((square f).ordinary).hom.app M) ≫
        ((square g).ordinary).hom.app (((slice f).modules Λ).obj M) =
      ((square (g ≫ f)).ordinary).hom.app M ≫
        ((corner Z).modules Λ Z).map ((sliceComposition f g).ordinary.hom.app M)
```

## New

The ordinary module functors retain their original bodies and transparency. Their result types are now stated explicitly, avoiding the much larger inferred composite type. Their instance proofs use `unfold` with the same definitions.

```lean
def Corner.modules (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u}) [IsAffine X]
    (s : Corner Λ X) :
    Mod (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace X)) Ab.{u + 1})
      (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X)) ⥤
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X) :=
  s.inverse.mapMod (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X)) ⋙
    Mod.comap s.coefficient.inv.hom

def Slice.modules (Λ : Profinite.CondensedRing.{u}) {P Q : Profinite.{u}} {h : Q ⟶ P}
    (s : Slice Λ h) :
    Mod (Sheaf ((coherentTopology Profinite.{u}).over P) Ab.{u + 1})
      (CondensedRing.profiniteCoefficient Λ.X P) ⥤
    Mod (Sheaf ((coherentTopology Profinite.{u}).over Q) Ab.{u + 1})
      (CondensedRing.profiniteCoefficient Λ.X Q) :=
  s.inverse.mapMod (CondensedRing.profiniteCoefficient Λ.X P) ⋙
    Mod.comap s.coefficient.inv.hom
```

The two derived functors and five comparison definitions keep their constructions and mathematical types; their bodies receive
`@[irreducible]`. Eight formerly inferred result types are now explicit: the two ordinary module functors, the two derived functors, the two slice comparisons and the two scheme comparisons.

```lean
def tensorSquareMonoidal
    {A : Type w₁} [Category.{v₁} A] [MonoidalCategory A]
    {B : Type w₂} [Category.{v₂} B] [MonoidalCategory B]
    {C : Type w₃} [Category.{v₃} C] [MonoidalCategory C]
    {D : Type w₄} [Category.{v₄} D] [MonoidalCategory D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    (tF : F.Monoidal) (tG : G.Monoidal) (tH : H.Monoidal) (tI : I.Monoidal)
    (e : F ⋙ G ≅ H ⋙ I) : Prop :=
  letI := tF
  letI := tG
  letI := tH
  letI := tI
  NatTrans.IsMonoidal e.hom

end TensorSquare

def squareIdentity
    {A : Type w₁} [Category.{v₁} A] {B : Type w₂} [Category.{v₂} B]
    (F : A ⥤ B) (G : B ⥤ B) (H : A ⥤ A)
    (e : F ⋙ G ≅ H ⋙ F) (i : H ≅ 𝟭 A) (j : G ≅ 𝟭 B) : Prop :=
  ∀ M, e.hom.app M ≫ F.map (i.hom.app M) = j.hom.app (F.obj M)

def squareComposition
    {A : Type w₁} [Category.{v₁} A] {B : Type w₂} [Category.{v₂} B]
    {C : Type w₃} [Category.{v₃} C] {D : Type w₄} [Category.{v₄} D]
    {E : Type w₅} [Category.{v₅} E] {T : Type w₆} [Category.{v₆} T]
    (a : A ⥤ B) (b : C ⥤ D) (c : E ⥤ T)
    (f : B ⥤ D) (g : D ⥤ T) (fg : B ⥤ T)
    (h : A ⥤ C) (k : C ⥤ E) (hk : A ⥤ E)
    (ef : a ⋙ f ≅ h ⋙ b) (eg : b ⋙ g ≅ k ⋙ c) (efg : a ⋙ fg ≅ hk ⋙ c)
    (i : fg ≅ f ⋙ g) (j : hk ≅ h ⋙ k) : Prop :=
  ∀ M, i.hom.app (a.obj M) ≫ g.map (ef.hom.app M) ≫ eg.hom.app (h.obj M) =
    efg.hom.app M ≫ c.map (j.hom.app M)

end SquareCoherence

@[irreducible]
def Corner.derived (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u}) [IsAffine X]
    (s : Corner Λ X) := (s.modules Λ X).mapDerivedCategory

@[irreducible]
def Slice.derived (Λ : Profinite.CondensedRing.{u})
    {P Q : Profinite.{u}} {h : Q ⟶ P} (s : Slice Λ h) :=
  (s.modules Λ).mapDerivedCategory

@[irreducible]
def Square.theta (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] {f : Y ⟶ X}
    {sX : Corner Λ X} {sY : Corner Λ Y} {sh : Slice Λ (affineComponentMap f)}
    (sq : Square Λ f sX sY sh) : leftPath Λ sX f ≅ rightPath Λ sY f sh := by
  unfold leftPath rightPath Corner.derived Slice.derived
  exact
    letI : (CondensedRing.upperStar Λ.X f).Additive :=
      CondensedRing.upperStar_additive Λ.X f
    letI : PreservesFiniteLimits (CondensedRing.upperStar Λ.X f) :=
      CondensedRing.preservesFiniteLimits_upperStar Λ.X f
    letI : PreservesFiniteColimits (CondensedRing.upperStar Λ.X f) :=
      CondensedRing.preservesFiniteColimits_upperStar Λ.X f
    letI := comp_preservesFiniteLimits (sX.modules Λ X) (CondensedRing.upperStar Λ.X f)
    letI := comp_preservesFiniteColimits (sX.modules Λ X) (CondensedRing.upperStar Λ.X f)
    letI := comp_preservesFiniteLimits (sh.modules Λ) (sY.modules Λ Y)
    letI := comp_preservesFiniteColimits (sh.modules Λ) (sY.modules Λ Y)
    letI : (sX.modules Λ X ⋙ CondensedRing.upperStar Λ.X f).Additive :=
      inferInstance
    letI : (sh.modules Λ ⋙ sY.modules Λ Y).Additive := inferInstance
    (Functor.mapDerivedCategoryCompIso (sX.modules Λ X)
        (CondensedRing.upperStar Λ.X f)).symm ≪≫
      Functor.mapDerivedCategoryNatIso sq.ordinary ≪≫
        Functor.mapDerivedCategoryCompIso (sh.modules Λ) (sY.modules Λ Y)

@[irreducible]
def SliceIdentity.derived (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u}) [IsAffine X]
    {s : Slice Λ (affineComponentMap (𝟙 X))} (i : SliceIdentity Λ X s) :
    s.derived Λ ≅ 𝟭 _ := by
  unfold Slice.derived
  exact Functor.mapDerivedCategoryNatIso i.ordinary ≪≫ Functor.mapDerivedCategoryIdIso _

@[irreducible]
def SliceComposition.derived (Λ : Profinite.CondensedRing.{u})
    {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    {f : Y ⟶ X} {g : Z ⟶ Y}
    {sf : Slice Λ (affineComponentMap f)} {sg : Slice Λ (affineComponentMap g)}
    {sfg : Slice Λ (affineComponentMap (g ≫ f))}
    (c : SliceComposition Λ f g sf sg sfg) :
    sfg.derived Λ ≅ sf.derived Λ ⋙ sg.derived Λ := by
  unfold Slice.derived
  exact
    letI := comp_preservesFiniteLimits (sf.modules Λ) (sg.modules Λ)
    letI := comp_preservesFiniteColimits (sf.modules Λ) (sg.modules Λ)
    Functor.mapDerivedCategoryNatIso c.ordinary ≪≫
      Functor.mapDerivedCategoryCompIso (sf.modules Λ) (sg.modules Λ)

@[irreducible]
def schemeIdentity (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u}) :
    (CondensedRing.upperStar Λ.X (𝟙 X)).mapDerivedCategory ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarId Λ.X X) ≪≫
    Functor.mapDerivedCategoryIdIso _

@[irreducible]
def schemeComposition (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) :
    (CondensedRing.upperStar Λ.X (g ≫ f)).mapDerivedCategory ≅
      (CondensedRing.upperStar Λ.X f).mapDerivedCategory ⋙
        (CondensedRing.upperStar Λ.X g).mapDerivedCategory :=
  letI := comp_preservesFiniteLimits (CondensedRing.upperStar Λ.X f)
    (CondensedRing.upperStar Λ.X g)
  letI := comp_preservesFiniteColimits (CondensedRing.upperStar Λ.X f)
    (CondensedRing.upperStar Λ.X g)
  Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp Λ.X g f) ≪≫
    Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar Λ.X f)
      (CondensedRing.upperStar Λ.X g)


section TensorSquare
universe v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄

def Square.monoidal (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] {f : Y ⟶ X}
    {sX : Corner Λ X} {sY : Corner Λ Y} {sh : Slice Λ (affineComponentMap f)}
    (sq : Square Λ f sX sY sh)
    (tX : TensorLift (sX.modules Λ X)) (tY : TensorLift (sY.modules Λ Y))
    (tf : TensorLift (CondensedRing.upperStar Λ.X f)) (th : TensorLift (sh.modules Λ)) : Prop :=
  tensorSquareMonoidal (sX.derived Λ X)
    (CondensedRing.upperStar Λ.X f).mapDerivedCategory
    (sh.derived Λ) (sY.derived Λ Y)
    (by unfold Corner.derived; exact tX.monoidal) tf.monoidal
    (by unfold Slice.derived; exact th.monoidal)
    (by unfold Corner.derived; exact tY.monoidal) (sq.theta Λ)

section SquareCoherence
universe v₁ v₂ v₃ v₄ v₅ v₆ w₁ w₂ w₃ w₄ w₅ w₆

structure System (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] where
  corner : ∀ (X : Scheme.{u}) [IsAffine X], Corner Λ X
  slice : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
    Slice Λ (affineComponentMap f)
  square : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
    Square Λ f (corner X) (corner Y) (slice f)
  cornerTensor : ∀ (X : Scheme.{u}) [IsAffine X], TensorLift ((corner X).modules Λ X)
  sliceTensor : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
    TensorLift ((slice f).modules Λ)
  schemeTensor : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
    TensorLift (CondensedRing.upperStar Λ.X f)
  monoidal : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
    (square f).monoidal Λ (cornerTensor X) (cornerTensor Y) (schemeTensor f) (sliceTensor f)
  sliceIdentity : ∀ (X : Scheme.{u}) [IsAffine X], SliceIdentity Λ X (slice (𝟙 X))
  sliceComposition : ∀ {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (f : Y ⟶ X) (g : Z ⟶ Y),
    SliceComposition Λ f g (slice f) (slice g) (slice (g ≫ f))
  identity : ∀ (X : Scheme.{u}) [IsAffine X],
    squareIdentity ((corner X).derived Λ X)
      (CondensedRing.upperStar Λ.X (𝟙 X)).mapDerivedCategory ((slice (𝟙 X)).derived Λ)
      ((square (𝟙 X)).theta Λ) ((sliceIdentity X).derived Λ X) (schemeIdentity Λ X)
  composition : ∀ (X Y Z : Scheme.{u}) [IsAffine X] [IsAffine Y] [IsAffine Z]
      (f : Y ⟶ X) (g : Z ⟶ Y),
    squareComposition ((corner X).derived Λ X) ((corner Y).derived Λ Y)
      ((corner Z).derived Λ Z) (CondensedRing.upperStar Λ.X f).mapDerivedCategory
      (CondensedRing.upperStar Λ.X g).mapDerivedCategory
      (CondensedRing.upperStar Λ.X (g ≫ f)).mapDerivedCategory
      ((slice f).derived Λ) ((slice g).derived Λ) ((slice (g ≫ f)).derived Λ)
      ((square f).theta Λ) ((square g).theta Λ) ((square (g ≫ f)).theta Λ)
      (schemeComposition Λ f g) ((sliceComposition f g).derived Λ)
  cornerDuals : ∀ (X : Scheme.{u}) [IsAffine X]
      (K : CondensedRing.Evaluation.D
        ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
        (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X))),
    IsDualizable K → IsDualizable (((corner X).derived Λ X).obj K)
  sliceDuals : ∀ (X Y : Scheme.{u}) [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
      (K : CondensedRing.Evaluation.D
        ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
        (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X))),
    IsDualizable K → IsDualizable (((slice f).derived Λ).obj K)
  schemeDuals : ∀ (X Y : Scheme.{u}) [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
      (K : CondensedRing.Evaluation.D (Scheme.ProEt.topology X) (condensedRingObj Λ.X X)),
    IsDualizable K → IsDualizable ((CondensedRing.upperStar Λ.X f).mapDerivedCategory.obj K)

structure OrdinarySystem (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] where
  corner : ∀ (X : Scheme.{u}) [IsAffine X], Corner Λ X
  slice : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
    Slice Λ (affineComponentMap f)
  square : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
    Square Λ f (corner X) (corner Y) (slice f)
  sliceIdentity : ∀ (X : Scheme.{u}) [IsAffine X], SliceIdentity Λ X (slice (𝟙 X))
  sliceComposition : ∀ {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (f : Y ⟶ X) (g : Z ⟶ Y),
    SliceComposition Λ f g (slice f) (slice g) (slice (g ≫ f))
  identity : ∀ (X : Scheme.{u}) [IsAffine X],
    squareIdentity ((corner X).modules Λ X)
      (CondensedRing.upperStar Λ.X (𝟙 X)) ((slice (𝟙 X)).modules Λ)
      (square (𝟙 X)).ordinary (sliceIdentity X).ordinary (CondensedRing.upperStarId Λ.X X)
  composition : ∀ (X Y Z : Scheme.{u}) [IsAffine X] [IsAffine Y] [IsAffine Z]
      (f : Y ⟶ X) (g : Z ⟶ Y),
    squareComposition ((corner X).modules Λ X) ((corner Y).modules Λ Y)
      ((corner Z).modules Λ Z) (CondensedRing.upperStar Λ.X f)
      (CondensedRing.upperStar Λ.X g) (CondensedRing.upperStar Λ.X (g ≫ f))
      ((slice f).modules Λ) ((slice g).modules Λ) ((slice (g ≫ f)).modules Λ)
      (square f).ordinary (square g).ordinary (square (g ≫ f)).ordinary
      (CondensedRing.upperStarComp Λ.X g f) (sliceComposition f g).ordinary
```

The generic predicate is `NatTrans.IsMonoidal`, whose tensor and unit fields are exactly
the two original equations after unfolding the monoidal structures on composite functors.
Its unit field is listed first in the class, while the old conjunction listed tensor first;
the predicates are logically equivalent, with no strengthening or weakening.
Square.monoidal retains the same tensor and coefficient-unit requirements. The result type annotations merely name the types already
inferred before. The comparison definitions are still the existing termwise localization
constructions, not arbitrary witnesses. The two functor bodies have not changed. Comparison bodies explicitly unfold the folded functors where needed; the resulting construction is the same localization term.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ComponentOrdinaryPullbackSquare | Z6 | Uses only ordinary data; proof reduction in this packet. |
| Sheaf.Paper.ComponentDerivedSquareCoherence | unclaimed | Original proof fails to identify the newly irreducible comparisons; explicitly unfold only those comparisons in its two proof branches. Statement and visibility unchanged. |
| Sheaf.Paper.ComponentDerivedTensorLifts | S6 | Statement-only consumer; definitions have the same meaning and its original file is compiled against the repair. |
| Sheaf.Paper.ComponentDerivedPullbackSquare | unclaimed | Original monoidal instance assignments fail after folding Corner.derived and Slice.derived. Added an explicit unfold in each of the two proof branches; the tensor structures are unchanged. |
| Sheaf.AlgebraicGeometry.CondensedGenericScalarModelData | unclaimed | Original cornerScalarComparison, SectionComparison.identityDerived and SectionComparison.scalarDerived fail to match the folded derived functors. Each now explicitly unfolds the corresponding derived functor before its original localization term; signatures unchanged. |

The direct-import scan reports exactly the first four modules. `tools/downstream.py --uses schemeComposition` additionally reports CondensedGenericScalarModelData. The --uses scans of theta and derived over-approximate by matching their last name throughout 2064 transitive importers; reading the component-specific references identifies the scalar-model and henselian-rigidity consumers adapted below. All other transitive importers see identical mathematical signatures and unchanged projection APIs. The generic coherence predicates are definitions whose bodies are literally the previous equations with functor parameters; no hypothesis or conclusion changes. No source-library declaration is changed.

The complete conservative textual-use scan (the final name segments `theta` and
`derived` are common) also lists the following modules. Their matches were checked
as unrelated names, statement-only uses or uses handled by the explicit adaptations listed here.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RingedForgetTensorTransposition | U1 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Algebra.Homology.RingedForgetTwoInjectiveHom | U2 | Unrelated last-name match; public interface unchanged. |
| Sheaf.AlgebraicGeometry.CondensedContractibleCornerLisseLift | unclaimed | Statement-only use of Corner.derived; functor meaning unchanged. |
| Sheaf.AlgebraicGeometry.CondensedGenericFiberCornerFullyFaithful | unclaimed | Statement-only use of Corner.derived; functor meaning unchanged. |
| Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity | unclaimed | Original corner-equivalence comparison and three slice-instance steps fail after folding. Explicitly unfold the corresponding derived functors at these four points; all original proof terms and signatures retained. |
| Sheaf.AlgebraicGeometry.CondensedIrreducibleGenericScalarModel | unclaimed | Uses mapped isomorphisms of Corner/Slice.derived without unfolding; functor meaning unchanged. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.AdicOperationDomainsSourceComparison | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.AdicRealizationFamilyData | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.AffineLineCompositeTranspose | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | F7 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.BoundaryComparisonCompositionTransport | A2 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.BrownTowerBoundedTransport | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.BrownTowerFiniteEvaluation | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.BrownTowerFiniteSiteComparison | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.BrownTowerGeometricTransport | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.BrownTowerRealization | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.BrownTowerSite | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.ClassicalTwoFibreScalarData | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.ClopenCanonicalFiniteEvaluation | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.ClopenCanonicalRestrictionEvaluation | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.ClopenCounitAdjointComparison | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.ClopenExceptionalScalarDescent | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.ClopenStrictSystemSupport | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.ClopenSystemIntegralRealization | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.ClopenSystemOrdinaryRestrictionRealization | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.ClopenSystemRealizationData | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.ClosedSectionCompactOrigin | B9 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.CoefTowerCoaugmentation | R5 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.CommonStageRestrictionTensorDescent | U6 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.CompactSupportCompositeTransposeDomains | M2 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.CompactSupportCondensedRealization | Y5 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.CompactifiedTowerComparisons | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.CompleteProjectionMateDescent | C8 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.CompositionTensorMate | G8 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.CondensedExceptionalReconstruction | Q3 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.ConstructibleTensorComposition | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.CoordinateTowerNormalizationInduction | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.DiagonalCoefficientReference | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.DiagonalCompletedDiagramRealization | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.DiagonalCompletedFrame | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.DiagonalCompletedPushSquare | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.DiagonalOrdinaryOrientationGluing | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.DiagonalOrdinaryOrientationNormalization | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.DiagonalOrientationRefinement | T8 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.EtaleBrownCoefficientCoherence | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.EtaleBrownGeometricComparisons | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.EtaleBrownProjectionRealization | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.EtaleBrownSupportTransition | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | E1 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.EtaleCofinalSupportComposition | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.EtaleSystemBrownConstruction | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.EtaleSystemCofinalData | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.EtaleSystemCofinalMate | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.EtaleSystemEvaluationBound | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.EtaleSystemProjectionData | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.EtaleSystemQuotientNormalization | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.EtaleSystemScalarMateCoherence | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.EtaleTowerBrownAdjunction | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | S6 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.ExceptionalOriginAdjunctionEvaluation | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.ExceptionalProOriginExactLinear | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.ExceptionalSystemInterfaces | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.ExchangeFunctoriality | R6 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.FiniteExceptionalSiteNormalization | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.FiniteProjectionExchangeData | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.FiniteProjectionExchangeTransposes | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.FiniteProjectionTensorSquare | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.FiniteSpanModuleDerivedComparison | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.FreeInsertionCompactSupportCoherence | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | M3 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.FrobeniusEvaluationProjectionCoherence | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.FrobeniusSquareExchange | H6 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.IntegralDirectImageTower | B8 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.IntegralExceptionalInverseImage | J2 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.IntegralSemilinearGermSquare | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.InverseContravariantBidual | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.KummerStratumScalarMaps | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.LevelwiseNormalizedStrictSystems | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.LocallyClosedRelativeTransposeNormalization | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.NativeAdicReindexingData | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.NativeProperCoefficientOperations | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.NormalizedFiniteFibreModels | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.OrientedDoubleHomCancellation | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.OrientedPerfectDuality | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.PointEquivariantDiagramLift | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.PointSystemNormalizedComparisonData | H3 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.PointSystemPowerRoosCoherence | W8 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.PointWeilPairingRealization | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.ProperCoefficientDescent | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.PurIntegralReductionUniformTor | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.PurIntegralRepresentingPair | B9 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.PurIntegralSupportComparison | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.PurIntegralSupportComparisonData | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.PurRepresentingPairFiniteScalar | V6 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.PurStrictIntegralExchangeNormalization | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | Z9 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.ResidueCompatiblePullbackFrobenius | Q8 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.RetaggingCoefficientTowerTransfer | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.SfNormalizedRationalWeilSquares | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.SmoothPurityCoordinateRightComparisons | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.SmoothPurityCoordinateTensorComparisons | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerGluing | F3 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.StrictDirectImageMixedUnit | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.StrictReductionCompactSupportNormalization | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.SupportedCommonFieldScalarData | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.SupportedRootScalarSiteComparison | A7 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.SystemCompactSupportRestrictionData | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.SystemCompactSupportRestrictionEvaluation | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.SystemCompactSupportTransitions | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.SystemEnrichedProjectionAdjunction | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.SystemInternalHomRepresentability | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.SystemRefinementConstructibleDomain | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.TowerAdjointCompositorRealization | M4 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.TowerP1GeometricCoordinates | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.TowerP1LevelWords | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.TowerP1PushCoordinates | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.TowerP1TensorCoordinates | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.TwistedPullbackReductionData | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.TwistedPullbackReductionTower | X2 | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.WeilBaseChangeSemilinearPasting | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.WeilChosenDualityExchangeData | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.Paper.ZlOpenCompactSupportRestriction | G7 | Unrelated last-name match; public interface unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.CoefFinitePairingEvaluationData | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.CoefFiniteProjectionEvaluationData | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.CoefPairingFiniteNormalization | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.CoefPairingSystemDinaturality | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.CoefSystemProjectionEvaluation | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.CoefficientProjectionPointData | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.CompactifiedProperTowerExchange | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.FiniteCoefficientVerdierData | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.OpenBaseChangeSquare | P2 | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | A5 | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | J1 | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.OpenFactorCoherenceData | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.OpenFactorExchangeRealization | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletionData | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.ProductSystemUniformRealizationDomain | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.ProjectionRefinementDescent | E2 | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.ScalarDirectImageMateCoherence | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.ScalarSixDirectImage | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.VerdierExchangeData | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed | Unrelated last-name match; public interface unchanged. |
| Sheaf.TraceFormula.FrobeniusProperPowerExchange | unclaimed | Unrelated last-name match; public interface unchanged. |

## Status

landed 20261025T164948-L-1144847 2026-10-25 (merge of deliver/Z6/Sheaf.Paper.ComponentOrdinaryPullbackSquare)

Validation note: the generic tensor equation equivalence was compiled independently
in scratchpad/TensorEquations.lean. It rewrites Functor.LaxMonoidal.comp_μ and comp_ε,
reassociates compositions, and constructs/destructs the two IsMonoidal fields.
The generic coherence definitions merely abstract functor arguments from the old
formulas, so their field propositions are definitionally equal to the originals.
The packet does not include the scratch probes.
