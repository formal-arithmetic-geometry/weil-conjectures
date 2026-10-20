# affineTraceCounit and the affine trace constructions

## Reason

Move the constructions into a module usable by intermediate affine-line lemmas without
an import cycle. The original module publicly re-exports it. Preserve existing signatures
and visibility. Replace the tower adjunction composite implementation with explicit counit
components to repair deterministic timeouts checking the successor equation. The short
one-line composites are abbreviations, so the kernel reduces these aliases before
the large scheme and derived-functor implementations when comparing components.
The right comparison stores explicit components, proved equal to the original iso.

## Old

In lean/Sheaf/AlgebraicGeometry/AffineSpaceTopTrace.lean:

```lean
/-- One affine-line left functor, on its specified standard compactification.
Source: blueprint sk-prop-an, Step 5(b) (blueprint: lem-amb-affine-space-top-trace). -/
@[implicit_reducible]
def affineTraceLineLeft (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    DerivedCategoryModule A (AffineSpace PUnit.{u + 1} S) ⥤ DerivedCategoryModule A S :=
  rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
    (affineTraceLineCompactification S)

/-- The right functor obtained by restricting the normalized projective-line right
functor to the standard affine chart. Source: blueprint sk-prop-an, Step 5(b)
(blueprint: lem-amb-affine-space-top-trace). -/
@[implicit_reducible]
def affineTraceLineRight (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) :
    DerivedCategoryModule A S ⥤ DerivedCategoryModule A (AffineSpace PUnit.{u + 1} S) :=
  ordinaryFiniteP1Right A N hA S ⋙ ordinaryFinitePullback A (ProjectiveLine.affineChart S)

/-- Compose the actual open adjunction with the actual normalized projective adjunction.
Source: blueprint sk-prop-an, Step 5(b) (blueprint: lem-amb-affine-space-top-trace). -/
def affineTraceLineAdjunction (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (D : OrdinaryFiniteP1Datum A N hA t S hS) :
    affineTraceLineLeft A S ⊣ affineTraceLineRight A N hA S :=
  ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
    (ProjectiveLine.affineChart S)).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (ProjectiveLine.affineChart S)).symm).comp D.adjunction

/-- The ordered unbounded left functor of the coordinate tower.
Source: blueprint sk-prop-an, Step 6 (blueprint: lem-amb-affine-space-top-trace). -/
def affineTraceLeft (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    (d : ℕ) → DerivedCategoryModule A (affineTraceTower S d) ⥤ DerivedCategoryModule A S
  | 0 => 𝟭 _
  | d + 1 => affineTraceLineLeft A (affineTraceTower S d) ⋙ affineTraceLeft A S d

/-- The ordered right functor: p* K(d)[2d] written as the iterated shifted-line twists.
Source: blueprint sk-prop-an, Step 6 (blueprint: lem-amb-affine-space-top-trace). -/
def affineTraceRight (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) :
    (d : ℕ) → DerivedCategoryModule A S ⥤ DerivedCategoryModule A (affineTraceTower S d)
  | 0 => 𝟭 _
  | d + 1 => affineTraceRight A N hA S d ⋙
      affineTraceLineRight A N hA (affineTraceTower S d)

/-- The literal composite adjunction, with the literal identity adjunction in dimension zero.
Source: blueprint sk-prop-an, Step 6 (blueprint: lem-amb-affine-space-top-trace). -/
def affineTraceAdjunction (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    (d : ℕ) → affineTraceLeft A S d ⊣ affineTraceRight A N hA S d
  | 0 => Adjunction.id
  | d + 1 =>
    (affineTraceLineAdjunction A N hA t (affineTraceTower S d)
      (affineTraceInvertible N S hS d)
      (@D (affineTraceTower S d) (affineTraceNoetherian S d)
        (affineTraceInvertible N S hS d))).comp
      (affineTraceAdjunction A N hA t D S hS d)

/-- The actual trace, the counit at the constant coefficient complex. Its source is
F_d applied to the coordinate-tower model of A(d)[2d].
Source: blueprint sk-prop-an, Steps 5(b), 6 (blueprint: lem-amb-affine-space-top-trace). -/
def affineTraceCounit (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :=
  (affineTraceAdjunction A N hA t D S hS d).counit.app (ordinaryFiniteUnit A S)

/-- The bounded-below version of the same ordered left functor.
Source: blueprint sk-prop-an, Step 6 (blueprint: lem-amb-affine-space-top-trace). -/
def affineTraceLeftPlus (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    (d : ℕ) → DerivedCategory.Plus
        (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
  | 0 => 𝟭 _
  | d + 1 => rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification (affineTraceTower S d)) ⋙ affineTraceLeftPlus A S d

/-- The canonical coherent comparison of the ordered tower with Rp_d! on D+.
Source: blueprint sk-prop-an, Step 6 (blueprint: lem-amb-affine-space-top-trace). -/
def affineTraceCompactSupportComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] : (d : ℕ) →
    affineTraceLeftPlus A S d ≅
      rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) (affineTraceProjection S d)
  | 0 => (rightDerivedLowerShriekPlusId A S).symm
  | d + 1 =>
    letI := affineTraceNoetherian S d
    let e₁ := rightDerivedLowerShriekOfCompactificationPlusIso A
      (f := AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
      (affineTraceLineCompactification (affineTraceTower S d))
      (HasCompactification.compactification
        (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d))
    let e₂ := affineTraceCompactSupportComparison A S d
    let e₃ := rightDerivedLowerShriekPlusCompIso A
      (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
      (affineTraceProjection S d)
    Functor.isoWhiskerRight e₁ (affineTraceLeftPlus A S d) ≪≫
      Functor.isoWhiskerLeft
        (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A)
          (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)) e₂ ≪≫ e₃

/-- The restriction of the unbounded tower to D+ is its bounded-below tower.
Source: blueprint sk-prop-an, Step 6 (blueprint: lem-amb-affine-space-top-trace). -/
def affineTracePlusCompatibility (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    (d : ℕ) → affineTraceLeftPlus A S d ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ affineTraceLeft A S d
  | 0 => Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm
  | d + 1 =>
    let L := rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification (affineTraceTower S d))
    let F := affineTraceLeftPlus A S d
    let l := affineTraceLineLeft A (affineTraceTower S d)
    let f := affineTraceLeft A S d
    let e := rightDerivedLowerShriekOfCompactificationPlusCompatibility (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification (affineTraceTower S d))
    let r := affineTracePlusCompatibility A S d
    Functor.associator L F DerivedCategory.Plus.ι ≪≫
      Functor.isoWhiskerLeft L r ≪≫
      (Functor.associator L DerivedCategory.Plus.ι f).symm ≪≫
      Functor.isoWhiskerRight e f ≪≫ Functor.associator DerivedCategory.Plus.ι l f

/-- Canonical proper exchange followed by open exchange and the coherent comparison
back to the standard compactification on the changed base.
Source: blueprint sk-prop-an, Step 5(b) (blueprint: lem-amb-affine-space-top-trace). -/
def affineTraceLineExchange (A : Type (u + 1)) [CommRing A] [Finite A]
    {S' S : Scheme.{u}} (f : S' ⟶ S)
    (M : DerivedCategoryModule A (AffineSpace PUnit.{u + 1} S)) :
    (ordinaryFinitePullback A f).obj ((affineTraceLineLeft A S).obj M) ⟶
      (affineTraceLineLeft A S').obj
        ((ordinaryFinitePullback A (AffineSpace.map PUnit.{u + 1} f)).obj M) :=
  let e₁ := rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} A)
    (AffineSpace.isPullback_map (n := PUnit.{u + 1}) f)
    (affineTraceLineCompactification S)
  let e₂ := rightDerivedLowerShriekOfCompactificationIso A
    ((affineTraceLineCompactification S).ofIsPullback
      (AffineSpace.isPullback_map (n := PUnit.{u + 1}) f))
    (affineTraceLineCompactification S')
  e₁.app M ≫ e₂.hom.app _

/-- The canonical exchange of the ordered coordinate tower, obtained by pasting the
proper/open exchanges of its coordinate steps. Source: blueprint sk-prop-an, Step 6
(blueprint: lem-amb-affine-space-top-trace). -/
def affineTraceExchange (A : Type (u + 1)) [CommRing A] [Finite A]
    {S' S : Scheme.{u}} (f : S' ⟶ S) : (d : ℕ) →
    (M : DerivedCategoryModule A (affineTraceTower S d)) →
    (ordinaryFinitePullback A f).obj ((affineTraceLeft A S d).obj M) ⟶
      (affineTraceLeft A S' d).obj
        ((ordinaryFinitePullback A (affineTraceMap f d)).obj M)
  | 0, M => 𝟙 ((ordinaryFinitePullback A f).obj M)
  | d + 1, M =>
    affineTraceExchange A f d ((affineTraceLineLeft A (affineTraceTower S d)).obj M) ≫
      (affineTraceLeft A S' d).map (affineTraceLineExchange A (affineTraceMap f d) M)

/-- The inverse-image comparison around the standard affine-chart square.
Source: blueprint sk-prop-an, Step 5(b) (blueprint: lem-amb-affine-space-top-trace). -/
def affineTraceOpenPullbackSquare (A : Type (u + 1)) [CommRing A]
    {S' S : Scheme.{u}} (f : S' ⟶ S) :
    ordinaryFinitePullback A (ProjectiveLine.affineChart S) ⋙
        ordinaryFinitePullback A (AffineSpace.map PUnit.{u + 1} f) ≅
      ordinaryFinitePullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) f) ⋙
        ordinaryFinitePullback A (ProjectiveLine.affineChart S') :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (AffineSpace.map PUnit.{u + 1} f) (ProjectiveLine.affineChart S)).symm ≪≫
  eqToIso (congrArg (ordinaryFinitePullback A) (affineTraceChart_isPullback f).w) ≪≫
  leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (ProjectiveLine.affineChart S')
    (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)

/-- Canonical pullback of the one-coordinate right functor, with the normalized
roots-of-unity Tate comparison. Source: blueprint sk-prop-an, Step 5(b)
(blueprint: lem-amb-affine-space-top-trace). -/
def affineTraceLineRightBaseChange (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S' S : Scheme.{u}} (f : S' ⟶ S) (hP : IsUnit (N : Γ(ProjectiveLine S, ⊤)))
    (K : DerivedCategoryModule A S) :
    (ordinaryFinitePullback A (AffineSpace.map PUnit.{u + 1} f)).obj
        ((affineTraceLineRight A N hA S).obj K) ≅
      (affineTraceLineRight A N hA S').obj ((ordinaryFinitePullback A f).obj K) :=
  (affineTraceOpenPullbackSquare A f).app ((ordinaryFiniteP1Right A N hA S).obj K) ≪≫
    (ordinaryFinitePullback A (ProjectiveLine.affineChart S')).mapIso
      (ordinaryFiniteP1RightBaseChange A N hA t f hP K)

/-- One pasting step for the canonical right-functor base-change comparison.
The last argument is the preceding coordinate comparison; no map is chosen here.
Source: blueprint sk-prop-an, Step 6 (blueprint: lem-amb-affine-space-top-trace). -/
def affineTraceRightBaseChangeStep (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S' S : Scheme.{u}} (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (K : DerivedCategoryModule A S)
    (e : (ordinaryFinitePullback A (affineTraceMap f d)).obj
        ((affineTraceRight A N hA S d).obj K) ≅
      (affineTraceRight A N hA S' d).obj ((ordinaryFinitePullback A f).obj K)) :
    (ordinaryFinitePullback A (AffineSpace.map PUnit.{u + 1} (affineTraceMap f d))).obj
        ((affineTraceLineRight A N hA (affineTraceTower S d)).obj
          ((affineTraceRight A N hA S d).obj K)) ≅
      (affineTraceLineRight A N hA (affineTraceTower S' d)).obj
        ((affineTraceRight A N hA S' d).obj ((ordinaryFinitePullback A f).obj K)) :=
  affineTraceLineRightBaseChange A N hA t (affineTraceMap f d)
    (affineTraceProjectiveInvertible N (affineTraceTower S d)
      (affineTraceInvertible N S hS d)) ((affineTraceRight A N hA S d).obj K) ≪≫
    (affineTraceLineRight A N hA (affineTraceTower S' d)).mapIso e

/-- The canonical right-functor base-change comparison, pasted coordinatewise.
Source: blueprint sk-prop-an, Step 6 (blueprint: lem-amb-affine-space-top-trace). -/
def affineTraceRightBaseChange (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S' S : Scheme.{u}} (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (K : DerivedCategoryModule A S) :
    (ordinaryFinitePullback A (affineTraceMap f d)).obj
        ((affineTraceRight A N hA S d).obj K) ≅
      (affineTraceRight A N hA S' d).obj ((ordinaryFinitePullback A f).obj K) :=
  Nat.rec (motive := fun e ↦
    (ordinaryFinitePullback A (affineTraceMap f e)).obj
        ((affineTraceRight A N hA S e).obj K) ≅
      (affineTraceRight A N hA S' e).obj ((ordinaryFinitePullback A f).obj K))
    (Iso.refl ((ordinaryFinitePullback A f).obj K))
    (fun e r ↦ affineTraceRightBaseChangeStep A N hA t f hS e K r) d

```

## New

The original module publicly re-exports the following constructions.

```lean
/-- Exact derived extension by zero for the standard chart, recorded once.
Source: the exact derived open extension
(blueprint: def-amb-affine-trace-construction). -/
def affineTraceOpenLeft (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    DerivedCategoryModule A (AffineSpace PUnit.{u + 1} S) ⥤
      DerivedCategoryModule A (ProjectiveLine S) :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} A)
    (ProjectiveLine.affineChart S)).mapDerivedCategory

/-- One affine-line left functor, on its specified standard compactification.
Source: blueprint sk-prop-an, Step 5(b) (blueprint: def-amb-affine-trace-construction). -/
abbrev affineTraceLineLeft (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    DerivedCategoryModule A (AffineSpace PUnit.{u + 1} S) ⥤ DerivedCategoryModule A S :=
  affineTraceOpenLeft A S ⋙ ordinaryFinitePushforward A (ProjectiveLine S ↘ S)

/-- The right functor obtained by restricting the normalized projective-line right
functor to the standard affine chart. Source: blueprint sk-prop-an, Step 5(b)
(blueprint: def-amb-affine-trace-construction). -/
abbrev affineTraceLineRight (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) :
    DerivedCategoryModule A S ⥤ DerivedCategoryModule A (AffineSpace PUnit.{u + 1} S) :=
  ordinaryFiniteP1Right A N hA S ⋙ ordinaryFinitePullback A (ProjectiveLine.affineChart S)

/-- The derived open adjunction with its ordinary inverse-image functor recorded once.
Source: the exact derived open adjunction
(blueprint: def-amb-affine-trace-construction). -/
def affineTraceOpenAdjunction (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    affineTraceOpenLeft A S ⊣ ordinaryFinitePullback A (ProjectiveLine.affineChart S) :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
    (ProjectiveLine.affineChart S)).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (ProjectiveLine.affineChart S)).symm

attribute [irreducible] affineTraceOpenAdjunction

/-- Ordered left composites for a family of categories.
Source: Mathlib adjunction composition (blueprint: def-amb-affine-trace-construction). -/
abbrev affineTraceLeftTower {C : ℕ → Type*} [∀ d, Category (C d)]
    (L : ∀ d, C (d + 1) ⥤ C d) : (d : ℕ) → C d ⥤ C 0 :=
  Nat.rec (motive := fun d ↦ C d ⥤ C 0) (𝟭 _) (fun d F ↦ L d ⋙ F)

/-- Ordered right composites for a family of categories.
Source: Mathlib adjunction composition (blueprint: def-amb-affine-trace-construction). -/
abbrev affineTraceRightTower {C : ℕ → Type*} [∀ d, Category (C d)]
    (R : ∀ d, C d ⥤ C (d + 1)) : (d : ℕ) → C 0 ⥤ C d :=
  Nat.rec (motive := fun d ↦ C 0 ⥤ C d) (𝟭 _) (fun d G ↦ G ⋙ R d)

/-- The ordered unbounded left functor of the coordinate tower.
Source: blueprint sk-prop-an, Step 6 (blueprint: def-amb-affine-trace-construction). -/
abbrev affineTraceLeft (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    (d : ℕ) → DerivedCategoryModule A (affineTraceTower S d) ⥤ DerivedCategoryModule A S :=
  affineTraceLeftTower (C := fun d ↦ DerivedCategoryModule A (affineTraceTower S d))
    (fun d ↦ affineTraceLineLeft A (affineTraceTower S d))

/-- The ordered right functor: p* K(d)[2d] written as the iterated shifted-line twists.
Source: blueprint sk-prop-an, Step 6 (blueprint: def-amb-affine-trace-construction). -/
abbrev affineTraceRight (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) :
    (d : ℕ) → DerivedCategoryModule A S ⥤ DerivedCategoryModule A (affineTraceTower S d) :=
  affineTraceRightTower (C := fun d ↦ DerivedCategoryModule A (affineTraceTower S d))
    (fun d ↦ affineTraceLineRight A N hA (affineTraceTower S d))


/-- Composite adjunction with its counit written componentwise.
This is Mathlib's composite, with the same unit and counit; the explicit components
avoid expanding the associator implementation in coordinate inductions.
Source: blueprint affine-space top trace, step 7
(blueprint: def-amb-affine-trace-construction). -/
def affineTraceComposeAdjunction
    {C : Type*} {E : Type*} {F : Type*}
    [Category C] [Category E] [Category F]
    {L : C ⥤ E} {R : E ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (a : L ⊣ R) (b : L' ⊣ R') : L ⋙ L' ⊣ R' ⋙ R := by
  let c : (R' ⋙ R) ⋙ (L ⋙ L') ⟶ 𝟭 F :=
    { app := fun X ↦ L'.map (a.counit.app (R'.obj X)) ≫ b.counit.app X
      naturality := fun X Y f ↦ by
        have ha := a.counit.naturality (R'.map f)
        have hb := b.counit.naturality f
        simp only [Functor.comp_map, Functor.id_map] at ha hb ⊢
        rw [← Category.assoc, ← L'.map_comp, ha, L'.map_comp,
          Category.assoc, hb, ← Category.assoc] }
  have h : c = (a.comp b).counit := by
    ext X
    exact (Adjunction.comp_counit_app a b X).symm
  exact
    { unit := (a.comp b).unit
      counit := c
      left_triangle_components := fun X ↦ by
        rw [h]
        exact (a.comp b).left_triangle_components X
      right_triangle_components := fun X ↦ by
        rw [h]
        exact (a.comp b).right_triangle_components X }

/-- Component formula for the explicit composite.
Source: Mathlib `Adjunction.comp_counit_app`
(blueprint: def-amb-affine-trace-construction). -/
theorem affineTraceComposeAdjunction_counit
    {C : Type*} {E : Type*} {F : Type*}
    [Category C] [Category E] [Category F]
    {L : C ⥤ E} {R : E ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (a : L ⊣ R) (b : L' ⊣ R') (X : F) :
    (affineTraceComposeAdjunction a b).counit.app X =
      L'.map (a.counit.app (R'.obj X)) ≫ b.counit.app X := by
  rfl

/-- The explicit-component presentation is the original composite adjunction.
Source: Mathlib `Adjunction.ext` and `Adjunction.comp_counit_app`
(blueprint: def-amb-affine-trace-construction). -/
theorem affineTraceComposeAdjunction_eq
    {C : Type*} {E : Type*} {F : Type*}
    [Category C] [Category E] [Category F]
    {L : C ⥤ E} {R : E ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (a : L ⊣ R) (b : L' ⊣ R') :
    affineTraceComposeAdjunction a b = a.comp b := by
  apply Adjunction.ext
  rfl

/-- Compose the actual open adjunction with the actual normalized projective adjunction.
Source: blueprint sk-prop-an, Step 5(b) (blueprint: def-amb-affine-trace-construction). -/
abbrev affineTraceLineAdjunction (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (D : OrdinaryFiniteP1Datum A N hA t S hS) :
    affineTraceLineLeft A S ⊣ affineTraceLineRight A N hA S :=
  affineTraceComposeAdjunction (affineTraceOpenAdjunction A S) D.adjunction

/-- The line counit in open/proper components.
Source: the explicit composite counit
(blueprint: def-amb-affine-trace-construction). -/
theorem affineTraceLineAdjunction_counit (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (D : OrdinaryFiniteP1Datum A N hA t S hS) (K : DerivedCategoryModule A S) :
    (affineTraceLineAdjunction A N hA t S hS D).counit.app K =
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).map
        ((affineTraceOpenAdjunction A S).counit.app
          ((ordinaryFiniteP1Right A N hA S).obj K)) ≫ D.adjunction.counit.app K := by
  unfold affineTraceLineAdjunction
  exact affineTraceComposeAdjunction_counit _ _ _

/-- Ordered composite adjunctions in a family of abstract categories.
Source: Mathlib adjunction composition (blueprint: def-amb-affine-trace-construction). -/
def affineTraceAdjunctionTower {C : ℕ → Type*} [∀ d, Category (C d)]
    {L : ∀ d, C (d + 1) ⥤ C d} {R : ∀ d, C d ⥤ C (d + 1)}
    (a : ∀ d, L d ⊣ R d) : (d : ℕ) →
      affineTraceLeftTower L d ⊣ affineTraceRightTower R d :=
  Nat.rec (motive := fun d ↦ affineTraceLeftTower L d ⊣ affineTraceRightTower R d)
    Adjunction.id (fun d b ↦ affineTraceComposeAdjunction (a d) b)

/-- Successor counit formula, checked before specializing the category instances.
Source: Mathlib `Adjunction.comp_counit_app`
(blueprint: def-amb-affine-trace-construction). -/
theorem affineTraceAdjunctionTower_counit_succ {C : ℕ → Type*} [∀ d, Category (C d)]
    {L : ∀ d, C (d + 1) ⥤ C d} {R : ∀ d, C d ⥤ C (d + 1)}
    (a : ∀ d, L d ⊣ R d) (d : ℕ) (K : C 0) :
    (affineTraceAdjunctionTower a (d + 1)).counit.app K =
      (affineTraceLeftTower L d).map
        ((a d).counit.app ((affineTraceRightTower R d).obj K)) ≫
      (affineTraceAdjunctionTower a d).counit.app K := by
  rfl

/-- Invertible coordinate counits give invertible composite counits.
Source: blueprint affine-space trace, step 7
(blueprint: def-amb-affine-trace-construction). -/
theorem affineTraceAdjunctionTower_counit_isIso {C : ℕ → Type*} [∀ d, Category (C d)]
    {L : ∀ d, C (d + 1) ⥤ C d} {R : ∀ d, C d ⥤ C (d + 1)}
    (a : ∀ d, L d ⊣ R d) (ha : ∀ d K, IsIso ((a d).counit.app K))
    (d : ℕ) (K : C 0) : IsIso ((affineTraceAdjunctionTower a d).counit.app K) := by
  induction d with
  | zero => change IsIso (𝟙 K); infer_instance
  | succ d ih =>
    rw [affineTraceAdjunctionTower_counit_succ]
    have := ha d ((affineTraceRightTower R d).obj K)
    infer_instance

/-- The literal composite adjunction, with the literal identity adjunction in dimension zero.
Source: blueprint sk-prop-an, Step 6 (blueprint: def-amb-affine-trace-construction). -/
def affineTraceAdjunction (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    (d : ℕ) → affineTraceLeft A S d ⊣ affineTraceRight A N hA S d
  := affineTraceAdjunctionTower
    (C := fun d ↦ DerivedCategoryModule A (affineTraceTower S d))
    (fun d ↦ affineTraceLineAdjunction A N hA t (affineTraceTower S d)
      (affineTraceInvertible N S hS d)
      (@D (affineTraceTower S d) (affineTraceNoetherian S d)
        (affineTraceInvertible N S hS d)))

attribute [irreducible] affineTraceAdjunction

/-- The actual trace, the counit at the constant coefficient complex. Its source is
F_d applied to the coordinate-tower model of A(d)[2d].
Source: blueprint sk-prop-an, Steps 5(b), 6 (blueprint: def-amb-affine-trace-construction). -/
def affineTraceCounit (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :=
  (affineTraceAdjunction A N hA t D S hS d).counit.app (ordinaryFiniteUnit A S)

/-- The bounded-below version of the same ordered left functor.
Source: blueprint sk-prop-an, Step 6 (blueprint: def-amb-affine-trace-construction). -/
def affineTraceLeftPlus (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    (d : ℕ) → DerivedCategory.Plus
        (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
  | 0 => 𝟭 _
  | d + 1 => rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification (affineTraceTower S d)) ⋙ affineTraceLeftPlus A S d

/-- The canonical coherent comparison of the ordered tower with Rp_d! on D+.
Source: blueprint sk-prop-an, Step 6 (blueprint: def-amb-affine-trace-construction). -/
def affineTraceCompactSupportComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] : (d : ℕ) →
    affineTraceLeftPlus A S d ≅
      rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) (affineTraceProjection S d)
  | 0 => (rightDerivedLowerShriekPlusId A S).symm
  | d + 1 =>
    letI := affineTraceNoetherian S d
    let e₁ := rightDerivedLowerShriekOfCompactificationPlusIso A
      (f := AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
      (affineTraceLineCompactification (affineTraceTower S d))
      (HasCompactification.compactification
        (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d))
    let e₂ := affineTraceCompactSupportComparison A S d
    let e₃ := rightDerivedLowerShriekPlusCompIso A
      (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
      (affineTraceProjection S d)
    Functor.isoWhiskerRight e₁ (affineTraceLeftPlus A S d) ≪≫
      Functor.isoWhiskerLeft
        (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A)
          (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)) e₂ ≪≫ e₃

/-- The restriction of the unbounded tower to D+ is its bounded-below tower.
Source: blueprint sk-prop-an, Step 6 (blueprint: def-amb-affine-trace-construction). -/
def affineTracePlusCompatibility (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    (d : ℕ) → affineTraceLeftPlus A S d ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ affineTraceLeft A S d
  | 0 => Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm
  | d + 1 =>
    let L := rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification (affineTraceTower S d))
    let F := affineTraceLeftPlus A S d
    let l := affineTraceLineLeft A (affineTraceTower S d)
    let f := affineTraceLeft A S d
    let e := rightDerivedLowerShriekOfCompactificationPlusCompatibility (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification (affineTraceTower S d))
    let r := affineTracePlusCompatibility A S d
    Functor.associator L F DerivedCategory.Plus.ι ≪≫
      Functor.isoWhiskerLeft L r ≪≫
      (Functor.associator L DerivedCategory.Plus.ι f).symm ≪≫
      Functor.isoWhiskerRight e f ≪≫ Functor.associator DerivedCategory.Plus.ι l f

/-- The natural transformation underlying the standard affine-line exchange.
It is the proper exchange followed by the open exchange and compactification comparison.
Source: blueprint sk-prop-an, Step 5(b) (blueprint: def-amb-affine-trace-construction). -/
def affineTraceLineExchangeTransformation (A : Type (u + 1)) [CommRing A] [Finite A]
    {S' S : Scheme.{u}} (f : S' ⟶ S) :
    affineTraceLineLeft A S ⋙ ordinaryFinitePullback A f ⟶
      ordinaryFinitePullback A (AffineSpace.map PUnit.{u + 1} f) ⋙
        affineTraceLineLeft A S' :=
  let e₁ := rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} A)
    (AffineSpace.isPullback_map (n := PUnit.{u + 1}) f)
    (affineTraceLineCompactification S)
  let e₂ := rightDerivedLowerShriekOfCompactificationIso A
    ((affineTraceLineCompactification S).ofIsPullback
      (AffineSpace.isPullback_map (n := PUnit.{u + 1}) f))
    (affineTraceLineCompactification S')
  e₁ ≫ Functor.whiskerLeft _ e₂.hom

attribute [irreducible] affineTraceLineExchangeTransformation

/-- Canonical proper exchange followed by open exchange and the coherent comparison
back to the standard compactification on the changed base.
Source: blueprint sk-prop-an, Step 5(b) (blueprint: def-amb-affine-trace-construction). -/
def affineTraceLineExchange (A : Type (u + 1)) [CommRing A] [Finite A]
    {S' S : Scheme.{u}} (f : S' ⟶ S)
    (M : DerivedCategoryModule A (AffineSpace PUnit.{u + 1} S)) :
    (ordinaryFinitePullback A f).obj ((affineTraceLineLeft A S).obj M) ⟶
      (affineTraceLineLeft A S').obj
        ((ordinaryFinitePullback A (AffineSpace.map PUnit.{u + 1} f)).obj M) :=
  (affineTraceLineExchangeTransformation A f).app M

attribute [irreducible] affineTraceLineExchange

/-- Packaging the line exchange preserves its original component map.
Source: blueprint sk-prop-an, Step 5(b) (blueprint: def-amb-affine-trace-construction). -/
theorem affineTraceLineExchange_eq (A : Type (u + 1)) [CommRing A] [Finite A]
    {S' S : Scheme.{u}} (f : S' ⟶ S)
    (M : DerivedCategoryModule A (AffineSpace PUnit.{u + 1} S)) :
    affineTraceLineExchange A f M =
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} A)
        (AffineSpace.isPullback_map (n := PUnit.{u + 1}) f)
        (affineTraceLineCompactification S)).app M ≫
      (rightDerivedLowerShriekOfCompactificationIso A
        ((affineTraceLineCompactification S).ofIsPullback
          (AffineSpace.isPullback_map (n := PUnit.{u + 1}) f))
        (affineTraceLineCompactification S')).hom.app _ := by
  unfold affineTraceLineExchange affineTraceLineExchangeTransformation
  rfl

/-- Paste exchange squares along ordered towers of abstract categories.
Source: blueprint affine-space trace, step 9
(blueprint: def-amb-affine-trace-construction). -/
def affineTraceExchangeTower {C C' : ℕ → Type*}
    [∀ d, Category (C d)] [∀ d, Category (C' d)]
    (L : ∀ d, C (d + 1) ⥤ C d) (L' : ∀ d, C' (d + 1) ⥤ C' d)
    (B : ∀ d, C d ⥤ C' d) (e : ∀ d, L d ⋙ B d ⟶ B (d + 1) ⋙ L' d) :
    (d : ℕ) → affineTraceLeftTower L d ⋙ B 0 ⟶ B d ⋙ affineTraceLeftTower L' d
  | 0 => (B 0).leftUnitor.hom ≫ (B 0).rightUnitor.inv
  | d + 1 =>
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (L d) (affineTraceExchangeTower L L' B e d) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (e d) (affineTraceLeftTower L' d) ≫
      (Functor.associator _ _ _).hom

/-- Component formula for a pasted exchange at dimension zero.
Source: identity natural transformation (blueprint: def-amb-affine-trace-construction). -/
theorem affineTraceExchangeTower_zero {C C' : ℕ → Type*}
    [∀ d, Category (C d)] [∀ d, Category (C' d)]
    (L : ∀ d, C (d + 1) ⥤ C d) (L' : ∀ d, C' (d + 1) ⥤ C' d)
    (B : ∀ d, C d ⥤ C' d) (e : ∀ d, L d ⋙ B d ⟶ B (d + 1) ⋙ L' d)
    (M : C 0) : (affineTraceExchangeTower L L' B e 0).app M = 𝟙 _ := by
  simp [affineTraceExchangeTower]

/-- Component formula for a pasted successor exchange.
Source: composition of natural transformations
(blueprint: def-amb-affine-trace-construction). -/
theorem affineTraceExchangeTower_succ {C C' : ℕ → Type*}
    [∀ d, Category (C d)] [∀ d, Category (C' d)]
    (L : ∀ d, C (d + 1) ⥤ C d) (L' : ∀ d, C' (d + 1) ⥤ C' d)
    (B : ∀ d, C d ⥤ C' d) (e : ∀ d, L d ⋙ B d ⟶ B (d + 1) ⋙ L' d)
    (d : ℕ) (M : C (d + 1)) :
    (affineTraceExchangeTower L L' B e (d + 1)).app M =
      (affineTraceExchangeTower L L' B e d).app ((L d).obj M) ≫
        (affineTraceLeftTower L' d).map ((e d).app M) := by
  simp [affineTraceExchangeTower]

/-- The canonical exchange of the ordered coordinate tower, obtained by pasting the
proper/open exchanges of its coordinate steps. Source: blueprint sk-prop-an, Step 6
(blueprint: def-amb-affine-trace-construction). -/
def affineTraceExchange (A : Type (u + 1)) [CommRing A] [Finite A]
    {S' S : Scheme.{u}} (f : S' ⟶ S) (d : ℕ)
    (M : DerivedCategoryModule A (affineTraceTower S d)) :
    (ordinaryFinitePullback A f).obj ((affineTraceLeft A S d).obj M) ⟶
      (affineTraceLeft A S' d).obj
        ((ordinaryFinitePullback A (affineTraceMap f d)).obj M) :=
  (affineTraceExchangeTower
    (C := fun d ↦ DerivedCategoryModule A (affineTraceTower S d))
    (C' := fun d ↦ DerivedCategoryModule A (affineTraceTower S' d))
    (fun d ↦ affineTraceLineLeft A (affineTraceTower S d))
    (fun d ↦ affineTraceLineLeft A (affineTraceTower S' d))
    (fun d ↦ ordinaryFinitePullback A (affineTraceMap f d))
    (fun d ↦ affineTraceLineExchangeTransformation A (affineTraceMap f d)) d).app M

/-- The inverse-image comparison around the standard affine-chart square.
Source: blueprint sk-prop-an, Step 5(b) (blueprint: def-amb-affine-trace-construction). -/
def affineTraceOpenPullbackSquare (A : Type (u + 1)) [CommRing A]
    {S' S : Scheme.{u}} (f : S' ⟶ S) :
    ordinaryFinitePullback A (ProjectiveLine.affineChart S) ⋙
        ordinaryFinitePullback A (AffineSpace.map PUnit.{u + 1} f) ≅
      ordinaryFinitePullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) f) ⋙
        ordinaryFinitePullback A (ProjectiveLine.affineChart S') :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (AffineSpace.map PUnit.{u + 1} f) (ProjectiveLine.affineChart S)).symm ≪≫
  eqToIso (congrArg (ordinaryFinitePullback A) (affineTraceChart_isPullback f).w) ≪≫
  leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (ProjectiveLine.affineChart S')
    (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)

/-- A square comparison followed by inverse image of an object comparison.
Source: composition of natural and object isomorphisms
(blueprint: def-amb-affine-trace-construction). -/
def affineTraceRightSquareIso
    {D E D' E' : Type*} [Category D] [Category E] [Category D'] [Category E']
    {U : D ⥤ E} {B2 : E ⥤ E'} {B1 : D ⥤ D'} {U' : D' ⥤ E'}
    (s : U ⋙ B2 ≅ B1 ⋙ U') (M : D) {M' : D'} (c : B1.obj M ≅ M') :
    B2.obj (U.obj M) ≅ U'.obj M' where
  hom := s.hom.app M ≫ U'.map c.hom
  inv := U'.map c.inv ≫ s.inv.app M
  hom_inv_id := by simp [Category.assoc]
  inv_hom_id := by simp [Category.assoc]

/-- The explicit square comparison is the usual composite isomorphism.
Source: functoriality of isomorphisms
(blueprint: def-amb-affine-trace-construction). -/
theorem affineTraceRightSquareIso_eq
    {D E D' E' : Type*} [Category D] [Category E] [Category D'] [Category E']
    {U : D ⥤ E} {B2 : E ⥤ E'} {B1 : D ⥤ D'} {U' : D' ⥤ E'}
    (s : U ⋙ B2 ≅ B1 ⋙ U') (M : D) {M' : D'} (c : B1.obj M ≅ M') :
    affineTraceRightSquareIso s M c = s.app M ≪≫ U'.mapIso c := by
  apply Iso.ext
  rfl

/-- The same square comparison with the composite right functors in its interface.
Keeping the composite functors avoids comparing inverse-image objects with different
source categories after specialization to schemes.
Source: composition of the two right functors
(blueprint: def-amb-affine-trace-construction). -/
def affineTraceCompositeRightSquareIso
    {C D E C' D' E' : Type*} [Category C] [Category D] [Category E]
    [Category C'] [Category D'] [Category E']
    {R : C ⥤ D} {R' : C' ⥤ D'} {B : C ⥤ C'}
    {U : D ⥤ E} {B2 : E ⥤ E'} {B1 : D ⥤ D'} {U' : D' ⥤ E'}
    (s : U ⋙ B2 ≅ B1 ⋙ U') (K : C)
    (c : B1.obj (R.obj K) ≅ R'.obj (B.obj K)) :
    B2.obj ((R ⋙ U).obj K) ≅ (R' ⋙ U').obj (B.obj K) :=
  affineTraceRightSquareIso s (R.obj K) c

/-- Recording the composite right functors preserves the square isomorphism.
Source: the component construction above
(blueprint: def-amb-affine-trace-construction). -/
theorem affineTraceCompositeRightSquareIso_eq
    {C D E C' D' E' : Type*} [Category C] [Category D] [Category E]
    [Category C'] [Category D'] [Category E']
    {R : C ⥤ D} {R' : C' ⥤ D'} {B : C ⥤ C'}
    {U : D ⥤ E} {B2 : E ⥤ E'} {B1 : D ⥤ D'} {U' : D' ⥤ E'}
    (s : U ⋙ B2 ≅ B1 ⋙ U') (K : C)
    (c : B1.obj (R.obj K) ≅ R'.obj (B.obj K)) :
    affineTraceCompositeRightSquareIso s K c = affineTraceRightSquareIso s (R.obj K) c := by
  rfl

/-- Canonical pullback of the one-coordinate right functor, with the normalized
roots-of-unity Tate comparison. Source: blueprint sk-prop-an, Step 5(b)
(blueprint: def-amb-affine-trace-construction). -/
abbrev affineTraceLineRightBaseChange (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S' S : Scheme.{u}} (f : S' ⟶ S) (hP : IsUnit (N : Γ(ProjectiveLine S, ⊤)))
    (K : DerivedCategoryModule A S) :
    (ordinaryFinitePullback A (AffineSpace.map PUnit.{u + 1} f)).obj
        ((affineTraceLineRight A N hA S).obj K) ≅
      (affineTraceLineRight A N hA S').obj ((ordinaryFinitePullback A f).obj K) :=
  affineTraceCompositeRightSquareIso
    (R := ordinaryFiniteP1Right A N hA S) (R' := ordinaryFiniteP1Right A N hA S')
    (B := ordinaryFinitePullback A f) (affineTraceOpenPullbackSquare A f) K
    (ordinaryFiniteP1RightBaseChange A N hA t f hP K)

/-- One pasting step for the canonical right-functor base-change comparison.
The last argument is the preceding coordinate comparison; no map is chosen here.
Source: blueprint sk-prop-an, Step 6 (blueprint: def-amb-affine-trace-construction). -/
def affineTraceRightBaseChangeStep (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S' S : Scheme.{u}} (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (K : DerivedCategoryModule A S)
    (e : (ordinaryFinitePullback A (affineTraceMap f d)).obj
        ((affineTraceRight A N hA S d).obj K) ≅
      (affineTraceRight A N hA S' d).obj ((ordinaryFinitePullback A f).obj K)) :
    (ordinaryFinitePullback A (AffineSpace.map PUnit.{u + 1} (affineTraceMap f d))).obj
        ((affineTraceLineRight A N hA (affineTraceTower S d)).obj
          ((affineTraceRight A N hA S d).obj K)) ≅
      (affineTraceLineRight A N hA (affineTraceTower S' d)).obj
        ((affineTraceRight A N hA S' d).obj ((ordinaryFinitePullback A f).obj K)) :=
  affineTraceLineRightBaseChange A N hA t (affineTraceMap f d)
    (affineTraceProjectiveInvertible N (affineTraceTower S d)
      (affineTraceInvertible N S hS d)) ((affineTraceRight A N hA S d).obj K) ≪≫
    (affineTraceLineRight A N hA (affineTraceTower S' d)).mapIso e

/-- Paste right-functor comparisons along an ordered tower.
Source: blueprint affine-space trace, step 9
(blueprint: def-amb-affine-trace-construction). -/
def affineTraceRightExchangeTower {C C' : ℕ → Type*}
    [∀ d, Category (C d)] [∀ d, Category (C' d)]
    (R : ∀ d, C d ⥤ C (d + 1)) (R' : ∀ d, C' d ⥤ C' (d + 1))
    (B : ∀ d, C d ⥤ C' d)
    (r : ∀ d K, (B (d + 1)).obj ((R d).obj K) ≅ (R' d).obj ((B d).obj K)) :
    (d : ℕ) → (K : C 0) →
      (B d).obj ((affineTraceRightTower R d).obj K) ≅
        (affineTraceRightTower R' d).obj ((B 0).obj K)
  | 0, _ => Iso.refl _
  | d + 1, K => r d _ ≪≫ (R' d).mapIso (affineTraceRightExchangeTower R R' B r d K)

/-- The canonical right-functor base-change comparison, pasted coordinatewise.
Source: blueprint sk-prop-an, Step 6 (blueprint: def-amb-affine-trace-construction). -/
def affineTraceRightBaseChange (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S' S : Scheme.{u}} (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (K : DerivedCategoryModule A S) :
    (ordinaryFinitePullback A (affineTraceMap f d)).obj
        ((affineTraceRight A N hA S d).obj K) ≅
      (affineTraceRight A N hA S' d).obj ((ordinaryFinitePullback A f).obj K) :=
  affineTraceRightExchangeTower
    (C := fun d ↦ DerivedCategoryModule A (affineTraceTower S d))
    (C' := fun d ↦ DerivedCategoryModule A (affineTraceTower S' d))
    (fun d ↦ affineTraceLineRight A N hA (affineTraceTower S d))
    (fun d ↦ affineTraceLineRight A N hA (affineTraceTower S' d))
    (fun d ↦ ordinaryFinitePullback A (affineTraceMap f d))
    (fun d K ↦ affineTraceLineRightBaseChange A N hA t (affineTraceMap f d)
      (affineTraceProjectiveInvertible N (affineTraceTower S d)
        (affineTraceInvertible N S hS d)) K) d K

/-- Recursion equation for the coordinate adjunction.
Source: blueprint sk-prop-an, Step 6 (blueprint: def-amb-affine-trace-construction). -/
theorem affineTraceAdjunction_succ (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    affineTraceAdjunction A N hA t D S hS (d + 1) =
      affineTraceComposeAdjunction
        (affineTraceLineAdjunction A N hA t (affineTraceTower S d)
          (affineTraceInvertible N S hS d) (@D _ (affineTraceNoetherian S d) _))
        (affineTraceAdjunction A N hA t D S hS d) := by
  unfold affineTraceAdjunction affineTraceAdjunctionTower
  rfl
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineLinearTraceAction | unclaimed | unchanged; same signatures and maps; compiled unchanged in the complete linear-action chain |
| Sheaf.AlgebraicGeometry.AffineLinearUniversalAction | unclaimed | unchanged; same signatures and maps; compiled unchanged in the complete linear-action chain |
| Sheaf.AlgebraicGeometry.AffineLinearActionFamily | unclaimed | unchanged; same signatures and maps; compiled unchanged in the complete linear-action chain |
| Sheaf.AlgebraicGeometry.AffineLinearActionRigidity | unclaimed | unchanged; same signatures and maps; compiled unchanged in the complete linear-action chain |
| Sheaf.AlgebraicGeometry.AffineLinearExchangeCoherence | unclaimed | unchanged; same signatures and maps; compiled unchanged in the complete linear-action chain |
| Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance | G6 | unchanged; same signatures and maps; consumer checks described below |
| Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace | unclaimed | unchanged; same signatures and maps; consumer checks described below |
| Sheaf.AlgebraicGeometry.VectorBundleIntegration | F7 | unchanged; same signatures and maps; consumer checks described below |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | unchanged; same signatures and maps; consumer checks described below |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | unchanged; same signatures and maps; consumer checks described below |
| Sheaf.Paper.FiniteRingSectionDeformation | G9 | unchanged; same signatures and maps; consumer checks described below |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | A4 | unchanged; same signatures and maps; consumer checks described below |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | unchanged; same signatures and maps; consumer checks described below |
| Sheaf.Paper.NoetherianPrimePowerSmoothDuality | unclaimed | unchanged; same signatures and maps; consumer checks described below |
| Sheaf.Paper.VectorBundlePurity | S1 | unchanged; same signatures and maps; consumer checks described below |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | D6 | unchanged; same signatures and maps; consumer checks described below |
| Sheaf.SecSmoothPurity.ReductionExceptional | G8 | unchanged; same signatures and maps; consumer checks described below |
| Sheaf.SixFunctors.FiniteDualizing | M6 | unchanged; same signatures and maps; consumer checks described below |
| Sheaf.Targets.VectorBundlePurity | F6 | unchanged; same signatures and maps; consumer checks described below |
| Sheaf.Paper.PurityDiagonalDualizingObject | G3 | unchanged; same signatures and maps; consumer checks described below |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | K9 | unchanged; same signatures and maps; consumer checks described below |

All existing declaration types are preserved, including the dependent function type
of affineTraceExchange (its binders were moved before the colon without changing its type).
The original public interface is re-exported through AffineTraceConstruction.
The new generic adjunction and right-square presentations have proved equality to
the original compositions. Targets using these definitions require the independent
definition review.

The initial seventeen-consumer snapshot was checked against unchanged sources;
thirteen compiled in the current session. During validation the shared repository
withdrew FiniteExceptionalSystemAdjunction and refactored linear trace invariance.
The current consumer snapshot and its compile limitations are recorded in report.md.
No held module is adapted. A timeout or an unrelated import-artifact conflict is not
reported as a successful consumer check.

## Status

landed 20261020T051303-L-1621396 2026-10-20 (merge of deliver/G1/Sheaf.AlgebraicGeometry.AffineSpaceTopTrace)
