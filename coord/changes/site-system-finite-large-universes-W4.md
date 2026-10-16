# CategoryTheory.SiteSystemPairs.diagram, finiteEquivalencePrecoverage, continuous_of_finite_pullbacks

## Reason

The assigned affine site has objects in `Type (u + 1)` and homs in `Type u`.
The existing pair construction and finite-cover APIs tied these universes together.
Their arguments do not need that restriction. The finite-cover APIs also required
unrestricted composition/base change even though their finite conclusions need only
the finite axioms. Generalize these unclaimed modules and prove the finite instances
and natural-isomorphism transport directly. The old small-category specialization
and all existing conclusions are unchanged. No Challenge signature changes, and the
underlying definitions at all previous specializations are unchanged.

The item itself retains its exact original theorem signature and its one original
sorry. Its final covering-reflection clause is disputed; see report.md. The new
module AffineEtaleFiniteColimitConstruction proves the complete finite-family construction
without new sorries.

## Old

### Sheaf.CategoryTheory.SiteSystemStrictificationCategory

```lean
universe u v w

variable {I : Type u} [Preorder I] (C : I → Cat.{u, u})

structure Obj (i : I)

variable (U : ∀ (i j : I), i ≤ j → C i ⥤ C j)

abbrev evalObj (i : I) (X : Obj C i) : C i

abbrev Fiber (i : I)

abbrev eval (i : I) : Fiber C U i ⥤ C i

def inclusion (i : I) : C i ⥤ Fiber C U i

variable (gamma : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k),
  U i j h ⋙ U j k h' ≅ U i k (h.trans h'))

def transition (i j : I) (h : i ≤ j) : Fiber C U i ⥤ Fiber C U j

def comparison (i j : I) (h : i ≤ j) :
    transition C U gamma i j h ⋙ eval C U j ≅ eval C U i ⋙ U i j h

variable (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i))

theorem inclusion_eval (i : I) : inclusion C U i ⋙ eval C U i = U i i le_rfl

theorem eval_isEquivalence
    (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i)) (i : I) : (eval C U i).IsEquivalence

theorem inclusion_isEquivalence
    (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i)) (i : I) : (inclusion C U i).IsEquivalence

private theorem normalized_map
    {A B E : Type u} [SmallCategory A] [SmallCategory B] [SmallCategory E]
    (G : E ⥤ E) (hG : G = 𝟭 E) (K : A ⥤ E) (L : B ⥤ E)
    (a : K ⋙ G ≅ K) (b : L ⋙ G ≅ L)
    (ha : HEq a (Iso.refl K)) (hb : HEq b (Iso.refl L))
    (X : A) (Y : B) (f : K.obj X ⟶ L.obj Y) :
    a.inv.app X ≫ G.map f ≫ b.hom.app Y = f

theorem transition_id (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i))
    (hgammaRight : ∀ (i k : I) (h : i ≤ k),
      HEq (gamma i k k h le_rfl) (Iso.refl (U i k h))) (i : I) :
    transition C U gamma i i le_rfl = 𝟭 (Fiber C U i)

theorem transition_comp
    (hgamma : ∀ (i j k l : I) (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ l) (X : C i),
      (gamma j k l h' h'').hom.app ((U i j h).obj X) ≫
          (gamma i j l h (h'.trans h'')).hom.app X =
        (U k l h'').map ((gamma i j k h h').hom.app X) ≫
          (gamma i k l (h.trans h') h'').hom.app X)
    (i j k : I) (h : i ≤ j) (h' : j ≤ k) :
    transition C U gamma i j h ⋙ transition C U gamma j k h' =
      transition C U gamma i k (h.trans h')

def diagram
    (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i))
    (hgammaRight : ∀ (i k : I) (h : i ≤ k),
      HEq (gamma i k k h le_rfl) (Iso.refl (U i k h)))
    (hgamma : ∀ (i j k l : I) (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ l) (X : C i),
      (gamma j k l h' h'').hom.app ((U i j h).obj X) ≫
          (gamma i j l h (h'.trans h'')).hom.app X =
        (U k l h'').map ((gamma i j k h h').hom.app X) ≫
          (gamma i k l (h.trans h') h'').hom.app X) : I ⥤ Cat.{u, u}

variable (D : Type v) [Category.{w} D] (v : ∀ i : I, C i ⥤ D)
  (delta : ∀ (i j : I) (h : i ≤ j), U i j h ⋙ v j ≅ v i)

def coefficients (i : I) : Fiber C U i ⥤ D

private theorem normalized_natiso_map
    {A : Type u} [SmallCategory A] {E : Type v} [Category.{w} E]
    (G H : A ⥤ E) (hG : G = H) (a : G ≅ H) (ha : HEq a (Iso.refl H))
    {X Y : A} (f : X ⟶ Y) : a.inv.app X ≫ G.map f ≫ a.hom.app Y = H.map f

theorem inclusion_coefficients
    (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i))
    (hdeltaId : ∀ i : I, HEq (delta i i le_rfl) (Iso.refl (v i))) (i : I) :
    inclusion C U i ⋙ coefficients C U D v delta i = v i

theorem transition_coefficients
    (hdelta : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k) (X : C i),
      (v k).map ((gamma i j k h h').hom.app X) ≫
          (delta i k (h.trans h')).hom.app X =
        (delta j k h').hom.app ((U i j h).obj X) ≫ (delta i j h).hom.app X)
    (i j : I) (h : i ≤ j) :
    transition C U gamma i j h ⋙ coefficients C U D v delta j =
      coefficients C U D v delta i

def theta
    (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i))
    (hgammaLeft : ∀ (i k : I) (h : i ≤ k),
      HEq (gamma i i k le_rfl h) (Iso.refl (U i k h)))
    (i j : I) (h : i ≤ j) :
    inclusion C U i ⋙ transition C U gamma i j h ≅ U i j h ⋙ inclusion C U j

private theorem normalized_coefficient_identity
    {A : Type u} [SmallCategory A] {E : Type v} [Category.{w} E]
    (G : A ⥤ A) (hG : G = 𝟭 A) (H : A ⥤ E) (a : G ⋙ H ≅ H)
    (ha : HEq a (Iso.refl H)) (X : A) :
    H.map ((eqToIso hG).inv.app X) ≫ a.hom.app X = 𝟙 (H.obj X)

theorem theta_coefficients
    (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i))
    (hgammaLeft : ∀ (i k : I) (h : i ≤ k),
      HEq (gamma i i k le_rfl h) (Iso.refl (U i k h)))
    (hdeltaId : ∀ i : I, HEq (delta i i le_rfl) (Iso.refl (v i)))
    (i j : I) (h : i ≤ j) (X : C i) :
    Arrow.mk ((coefficients C U D v delta j).map
      ((theta C U gamma hUid hgammaLeft i j h).hom.app X)) =
        Arrow.mk ((delta i j h).inv.app X)
```

### Sheaf.CategoryTheory.SiteSystemFiniteCoverings

```lean
universe u

def finiteEquivalencePrecoverage {A B : Type u} [SmallCategory A] [SmallCategory B]
    (p : A ⥤ B) (P : Precoverage B) : Precoverage A

variable {A B : Type u} [SmallCategory A] [SmallCategory B]
  (p : A ⥤ B) (P : Precoverage B)

instance [P.HasIsos] : (finiteEquivalencePrecoverage p P).HasIsos

instance [P.IsStableUnderComposition] :
    (finiteEquivalencePrecoverage p P).IsStableUnderFiniteComposition

instance [p.IsEquivalence] [P.IsStableUnderBaseChange] :
    (finiteEquivalencePrecoverage p P).IsStableUnderFiniteBaseChange

instance [p.IsEquivalence] [P.HasPullbacks] :
    (finiteEquivalencePrecoverage p P).HasPullbacks

theorem finiteEquivalencePrecoverage_finite (X : A) (R : Presieve X)
    (hR : R ∈ finiteEquivalencePrecoverage p P X) : Finite R.uncurry

private theorem presieve_eq_ofArrows (X : A) (R : Presieve X) :
    R = Presieve.ofArrows (fun i : R.uncurry ↦ i.val.1) (fun i ↦ i.val.2)

private theorem finite_map (X : A) (R : Presieve X) (hf : R.uncurry.Finite) :
    (R.map p).uncurry.Finite

private theorem covering_map_iso
    [P.HasIsos] [P.IsStableUnderComposition] [P.IsStableUnderBaseChange] [P.HasPullbacks]
    (q : A ⥤ B) (a : p ≅ q) (X : A) (R : Presieve X) :
    R.map p ∈ P (p.obj X) ↔ R.map q ∈ P (q.obj X)

theorem finiteEquivalencePrecoverage_inclusion
    (e : B ⥤ A) (hep : e ⋙ p = 𝟭 B)
    (hfinite : ∀ (X : B) (R : Presieve X), R ∈ P X → Finite R.uncurry)
    (X : B) (R : Presieve X) :
    R ∈ P X ↔ R.map e ∈ finiteEquivalencePrecoverage p P (e.obj X)

theorem finiteEquivalencePrecoverage_lift
    [P.HasIsos] [P.IsStableUnderComposition] [P.IsStableUnderBaseChange] [P.HasPullbacks]
    (e : B ⥤ A) [e.IsEquivalence] (hep : e ⋙ p = 𝟭 B)
    (X : A) (K : Type u) (Y : K → A) (f : ∀ k, Y k ⟶ X)
    (hR : Presieve.ofArrows Y f ∈ finiteEquivalencePrecoverage p P X) :
    ∃ (Z : B) (T : K → B) (g : ∀ k, T k ⟶ Z)
      (t : e.obj Z ≅ X) (s : ∀ k, e.obj (T k) ≅ Y k),
      Presieve.ofArrows T g ∈ P Z ∧ ∀ k, e.map (g k) ≫ t.hom = (s k).hom ≫ f k

theorem finiteEquivalencePrecoverage_transition
    {A' B' : Type u} [SmallCategory A'] [SmallCategory B']
    (p' : A' ⥤ B') (P' : Precoverage B')
    [P'.HasIsos] [P'.IsStableUnderComposition] [P'.IsStableUnderBaseChange]
    [P'.HasPullbacks]
    (U : B ⥤ B')
    (hcover : ∀ (X : B) (R : Presieve X), R ∈ P X → R.map U ∈ P' (U.obj X))
    (T : A ⥤ A') (a : T ⋙ p' ≅ p ⋙ U) (X : A) (R : Presieve X)
    (hR : R ∈ finiteEquivalencePrecoverage p P X) :
    R.map T ∈ finiteEquivalencePrecoverage p' P' (T.obj X)

theorem finiteEquivalencePrecoverage_transition_pullback
    [p.IsEquivalence]
    {A' B' : Type u} [SmallCategory A'] [SmallCategory B']
    (p' : A' ⥤ B') [p'.IsEquivalence] (U : B ⥤ B')
    (hpullback : ∀ (X Y Z : B) (R : Presieve X), R ∈ P X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) U)
    (T : A ⥤ A') (a : T ⋙ p' ≅ p ⋙ U)
    (X Y Z : A) (R : Presieve X) (hR : R ∈ finiteEquivalencePrecoverage p P X)
    (f : Y ⟶ X) (g : Z ⟶ X) (hf : R f) : PreservesLimit (cospan f g) T
```

### Sheaf.CategoryTheory.SiteSystemFiniteSheafTransport

```lean
universe u

private theorem finite_pullback_cover
    {C : Type u} [SmallCategory C] (P : Precoverage C)
    [P.IsStableUnderFiniteBaseChange] [P.HasPullbacks]
    (hfinite : ∀ (X : C) (R : Presieve X), R ∈ P X → Finite R.uncurry)
    {X Y : C} (R : Presieve X) (hR : R ∈ P X) (g : Y ⟶ X) :
    have

theorem continuous_of_finite_pullbacks
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (U : C ⥤ D) (P : Precoverage C) (Q : Precoverage D)
    [P.IsStableUnderFiniteBaseChange] [P.HasPullbacks]
    (hfinite : ∀ (X : C) (R : Presieve X), R ∈ P X → Finite R.uncurry)
    (hcover : ∀ (X : C) (R : Presieve X), R ∈ P X → R.map U ∈ Q (U.obj X))
    (hpres : ∀ (X Y Z : C) (R : Presieve X), R ∈ P X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) U) :
    U.IsContinuous P.toGrothendieck Q.toGrothendieck

theorem continuous_equivalence_pullback_exact
    {A B : Type u} [SmallCategory A] [SmallCategory B]
    (JA : GrothendieckTopology A) (JB : GrothendieckTopology B)
    (p : A ⥤ B) (e : B ⥤ A)
    (eta : 𝟭 A ≅ p ⋙ e) (epsilon : e ⋙ p ≅ 𝟭 B)
    [p.IsContinuous JA JB] [e.IsContinuous JB JA] :
    PreservesFiniteLimits (sheafPullback p (Type u) JA JB) ∧
    PreservesFiniteColimits (sheafPullback p (Type u) JA JB)

theorem continuous_composite_pullback_exact
    {A B C : Type u} [SmallCategory A] [SmallCategory B] [SmallCategory C]
    (JA : GrothendieckTopology A) (JB : GrothendieckTopology B)
    (JC : GrothendieckTopology C) (p : A ⥤ B) (q : B ⥤ C)
    [p.IsContinuous JA JB] [q.IsContinuous JB JC]
    [PreservesFiniteLimits (sheafPullback p (Type u) JA JB)]
    [PreservesFiniteColimits (sheafPullback p (Type u) JA JB)]
    [PreservesFiniteLimits (sheafPullback q (Type u) JB JC)]
    [PreservesFiniteColimits (sheafPullback q (Type u) JB JC)] :
    have : (p ⋙ q).IsContinuous JA JC

theorem finiteEquivalencePrecoverage_sheaf_equivalence
    {A B : Type u} [SmallCategory A] [SmallCategory B]
    (p : A ⥤ B) [p.IsEquivalence] (P : Precoverage B)
    [P.HasIsos] [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]
    [P.HasPullbacks] (e : B ⥤ A) [e.IsEquivalence] (hep : e ⋙ p = 𝟭 B)
    (hfinite : ∀ (X : B) (R : Presieve X), R ∈ P X → Finite R.uncurry) :
    ∃ (_ : p.IsContinuous (finiteEquivalencePrecoverage p P).toGrothendieck
        P.toGrothendieck),
      ∃ (_ : e.IsContinuous P.toGrothendieck
          (finiteEquivalencePrecoverage p P).toGrothendieck),
        (PreservesFiniteLimits (sheafPullback p (Type u)
          (finiteEquivalencePrecoverage p P).toGrothendieck P.toGrothendieck) ∧
        PreservesFiniteColimits (sheafPullback p (Type u)
          (finiteEquivalencePrecoverage p P).toGrothendieck P.toGrothendieck)) ∧
        (PreservesFiniteLimits (sheafPullback e (Type u) P.toGrothendieck
          (finiteEquivalencePrecoverage p P).toGrothendieck) ∧
        PreservesFiniteColimits (sheafPullback e (Type u) P.toGrothendieck
          (finiteEquivalencePrecoverage p P).toGrothendieck))

theorem continuous_transport_pullback_exact
    {A B C D : Type u}
    [SmallCategory A] [SmallCategory B] [SmallCategory C] [SmallCategory D]
    (JA : GrothendieckTopology A) (JB : GrothendieckTopology B)
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (p : A ⥤ C) (U : C ⥤ D) (e : D ⥤ B) (T : A ⥤ B)
    [p.IsContinuous JA JC] [U.IsContinuous JC JD] [e.IsContinuous JD JB]
    [T.IsContinuous JA JB]
    [PreservesFiniteLimits (sheafPullback p (Type u) JA JC)]
    [PreservesFiniteColimits (sheafPullback p (Type u) JA JC)]
    [PreservesFiniteLimits (sheafPullback U (Type u) JC JD)]
    [PreservesFiniteColimits (sheafPullback U (Type u) JC JD)]
    [PreservesFiniteLimits (sheafPullback e (Type u) JD JB)]
    [PreservesFiniteColimits (sheafPullback e (Type u) JD JB)]
    (theta : T ≅ (p ⋙ U) ⋙ e) :
    PreservesFiniteLimits (sheafPullback T (Type u) JA JB) ∧
    PreservesFiniteColimits (sheafPullback T (Type u) JA JB)
```

## New

### Sheaf.CategoryTheory.SiteSystemStrictificationCategory

```lean
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

variable {I : Type u} [Preorder I] (C : I → Cat.{v₁, u₁})

structure Obj (i : I)

variable (U : ∀ (i j : I), i ≤ j → C i ⥤ C j)

abbrev evalObj (i : I) (X : Obj C i) : C i

abbrev Fiber (i : I)

abbrev eval (i : I) : Fiber C U i ⥤ C i

def inclusion (i : I) : C i ⥤ Fiber C U i

variable (gamma : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k),
  U i j h ⋙ U j k h' ≅ U i k (h.trans h'))

def transition (i j : I) (h : i ≤ j) : Fiber C U i ⥤ Fiber C U j

def comparison (i j : I) (h : i ≤ j) :
    transition C U gamma i j h ⋙ eval C U j ≅ eval C U i ⋙ U i j h

variable (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i))

theorem inclusion_eval (i : I) : inclusion C U i ⋙ eval C U i = U i i le_rfl

theorem eval_isEquivalence
    (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i)) (i : I) : (eval C U i).IsEquivalence

theorem inclusion_isEquivalence
    (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i)) (i : I) : (inclusion C U i).IsEquivalence

private theorem normalized_map
    {A : Type u₁} {B : Type u₂} {E : Type u₃}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} E]
    (G : E ⥤ E) (hG : G = 𝟭 E) (K : A ⥤ E) (L : B ⥤ E)
    (a : K ⋙ G ≅ K) (b : L ⋙ G ≅ L)
    (ha : HEq a (Iso.refl K)) (hb : HEq b (Iso.refl L))
    (X : A) (Y : B) (f : K.obj X ⟶ L.obj Y) :
    a.inv.app X ≫ G.map f ≫ b.hom.app Y = f

theorem transition_id (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i))
    (hgammaRight : ∀ (i k : I) (h : i ≤ k),
      HEq (gamma i k k h le_rfl) (Iso.refl (U i k h))) (i : I) :
    transition C U gamma i i le_rfl = 𝟭 (Fiber C U i)

theorem transition_comp
    (hgamma : ∀ (i j k l : I) (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ l) (X : C i),
      (gamma j k l h' h'').hom.app ((U i j h).obj X) ≫
          (gamma i j l h (h'.trans h'')).hom.app X =
        (U k l h'').map ((gamma i j k h h').hom.app X) ≫
          (gamma i k l (h.trans h') h'').hom.app X)
    (i j k : I) (h : i ≤ j) (h' : j ≤ k) :
    transition C U gamma i j h ⋙ transition C U gamma j k h' =
      transition C U gamma i k (h.trans h')

def diagram
    (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i))
    (hgammaRight : ∀ (i k : I) (h : i ≤ k),
      HEq (gamma i k k h le_rfl) (Iso.refl (U i k h)))
    (hgamma : ∀ (i j k l : I) (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ l) (X : C i),
      (gamma j k l h' h'').hom.app ((U i j h).obj X) ≫
          (gamma i j l h (h'.trans h'')).hom.app X =
        (U k l h'').map ((gamma i j k h h').hom.app X) ≫
          (gamma i k l (h.trans h') h'').hom.app X) : I ⥤ Cat.{v₁, max u u₁}

variable (D : Type v) [Category.{w} D] (v : ∀ i : I, C i ⥤ D)
  (delta : ∀ (i j : I) (h : i ≤ j), U i j h ⋙ v j ≅ v i)

def coefficients (i : I) : Fiber C U i ⥤ D

private theorem normalized_natiso_map
    {A : Type u₁} [Category.{v₁} A] {E : Type v} [Category.{w} E]
    (G H : A ⥤ E) (hG : G = H) (a : G ≅ H) (ha : HEq a (Iso.refl H))
    {X Y : A} (f : X ⟶ Y) : a.inv.app X ≫ G.map f ≫ a.hom.app Y = H.map f

theorem inclusion_coefficients
    (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i))
    (hdeltaId : ∀ i : I, HEq (delta i i le_rfl) (Iso.refl (v i))) (i : I) :
    inclusion C U i ⋙ coefficients C U D v delta i = v i

theorem transition_coefficients
    (hdelta : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k) (X : C i),
      (v k).map ((gamma i j k h h').hom.app X) ≫
          (delta i k (h.trans h')).hom.app X =
        (delta j k h').hom.app ((U i j h).obj X) ≫ (delta i j h).hom.app X)
    (i j : I) (h : i ≤ j) :
    transition C U gamma i j h ⋙ coefficients C U D v delta j =
      coefficients C U D v delta i

def theta
    (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i))
    (hgammaLeft : ∀ (i k : I) (h : i ≤ k),
      HEq (gamma i i k le_rfl h) (Iso.refl (U i k h)))
    (i j : I) (h : i ≤ j) :
    inclusion C U i ⋙ transition C U gamma i j h ≅ U i j h ⋙ inclusion C U j

private theorem normalized_coefficient_identity
    {A : Type u₁} [Category.{v₁} A] {E : Type v} [Category.{w} E]
    (G : A ⥤ A) (hG : G = 𝟭 A) (H : A ⥤ E) (a : G ⋙ H ≅ H)
    (ha : HEq a (Iso.refl H)) (X : A) :
    H.map ((eqToIso hG).inv.app X) ≫ a.hom.app X = 𝟙 (H.obj X)

theorem theta_coefficients
    (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i))
    (hgammaLeft : ∀ (i k : I) (h : i ≤ k),
      HEq (gamma i i k le_rfl h) (Iso.refl (U i k h)))
    (hdeltaId : ∀ i : I, HEq (delta i i le_rfl) (Iso.refl (v i)))
    (i j : I) (h : i ≤ j) (X : C i) :
    Arrow.mk ((coefficients C U D v delta j).map
      ((theta C U gamma hUid hgammaLeft i j h).hom.app X)) =
        Arrow.mk ((delta i j h).inv.app X)
```

### Sheaf.CategoryTheory.SiteSystemFiniteCoverings

```lean
universe u v

def finiteEquivalencePrecoverage {A B : Type u} [Category.{v} A] [Category.{v} B]
    (p : A ⥤ B) (P : Precoverage B) : Precoverage A

variable {A B : Type u} [Category.{v} A] [Category.{v} B]
  (p : A ⥤ B) (P : Precoverage B)

instance [P.HasIsos] : (finiteEquivalencePrecoverage p P).HasIsos

instance [P.IsStableUnderFiniteComposition] :
    (finiteEquivalencePrecoverage p P).IsStableUnderFiniteComposition

instance [p.IsEquivalence] [P.IsStableUnderFiniteBaseChange] :
    (finiteEquivalencePrecoverage p P).IsStableUnderFiniteBaseChange

instance [p.IsEquivalence] [P.HasPullbacks] :
    (finiteEquivalencePrecoverage p P).HasPullbacks

theorem finiteEquivalencePrecoverage_finite (X : A) (R : Presieve X)
    (hR : R ∈ finiteEquivalencePrecoverage p P X) : Finite R.uncurry

private theorem presieve_eq_ofArrows (X : A) (R : Presieve X) :
    R = Presieve.ofArrows (fun i : R.uncurry ↦ i.val.1) (fun i ↦ i.val.2)

private theorem finite_map (X : A) (R : Presieve X) (hf : R.uncurry.Finite) :
    (R.map p).uncurry.Finite

private theorem covering_map_iso
    [P.IsStableUnderFiniteBaseChange]
    (q : A ⥤ B) (a : p ≅ q) (X : A) (R : Presieve X) (hfin : Finite R.uncurry) :
    R.map p ∈ P (p.obj X) ↔ R.map q ∈ P (q.obj X)

theorem finiteEquivalencePrecoverage_inclusion
    (e : B ⥤ A) (hep : e ⋙ p = 𝟭 B)
    (hfinite : ∀ (X : B) (R : Presieve X), R ∈ P X → Finite R.uncurry)
    (X : B) (R : Presieve X) :
    R ∈ P X ↔ R.map e ∈ finiteEquivalencePrecoverage p P (e.obj X)

theorem finiteEquivalencePrecoverage_lift
    [P.HasIsos] [P.IsStableUnderFiniteComposition] [P.IsStableUnderFiniteBaseChange]
    [P.HasPullbacks]
    (e : B ⥤ A) [e.IsEquivalence] (hep : e ⋙ p = 𝟭 B)
    (X : A) (K : Type (max u v)) (Y : K → A) (f : ∀ k, Y k ⟶ X)
    (hR : Presieve.ofArrows Y f ∈ finiteEquivalencePrecoverage p P X) :
    ∃ (Z : B) (T : K → B) (g : ∀ k, T k ⟶ Z)
      (t : e.obj Z ≅ X) (s : ∀ k, e.obj (T k) ≅ Y k),
      Presieve.ofArrows T g ∈ P Z ∧ ∀ k, e.map (g k) ≫ t.hom = (s k).hom ≫ f k

theorem finiteEquivalencePrecoverage_transition
    {A' B' : Type u} [Category.{v} A'] [Category.{v} B']
    (p' : A' ⥤ B') (P' : Precoverage B')
    [P'.HasIsos] [P'.IsStableUnderFiniteComposition] [P'.IsStableUnderFiniteBaseChange]
    [P'.HasPullbacks]
    (U : B ⥤ B')
    (hcover : ∀ (X : B) (R : Presieve X), R ∈ P X → R.map U ∈ P' (U.obj X))
    (T : A ⥤ A') (a : T ⋙ p' ≅ p ⋙ U) (X : A) (R : Presieve X)
    (hR : R ∈ finiteEquivalencePrecoverage p P X) :
    R.map T ∈ finiteEquivalencePrecoverage p' P' (T.obj X)

theorem finiteEquivalencePrecoverage_transition_pullback
    [p.IsEquivalence]
    {A' B' : Type u} [Category.{v} A'] [Category.{v} B']
    (p' : A' ⥤ B') [p'.IsEquivalence] (U : B ⥤ B')
    (hpullback : ∀ (X Y Z : B) (R : Presieve X), R ∈ P X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) U)
    (T : A ⥤ A') (a : T ⋙ p' ≅ p ⋙ U)
    (X Y Z : A) (R : Presieve X) (hR : R ∈ finiteEquivalencePrecoverage p P X)
    (f : Y ⟶ X) (g : Z ⟶ X) (hf : R f) : PreservesLimit (cospan f g) T
```

### Sheaf.CategoryTheory.SiteSystemFiniteSheafTransport

```lean
universe u v

private theorem finite_pullback_cover
    {C : Type u} [Category.{v} C] (P : Precoverage C)
    [P.IsStableUnderFiniteBaseChange] [P.HasPullbacks]
    (hfinite : ∀ (X : C) (R : Presieve X), R ∈ P X → Finite R.uncurry)
    {X Y : C} (R : Presieve X) (hR : R ∈ P X) (g : Y ⟶ X) :
    have

theorem continuous_of_finite_pullbacks
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (U : C ⥤ D) (P : Precoverage C) (Q : Precoverage D)
    [P.IsStableUnderFiniteBaseChange] [P.HasPullbacks]
    (hfinite : ∀ (X : C) (R : Presieve X), R ∈ P X → Finite R.uncurry)
    (hcover : ∀ (X : C) (R : Presieve X), R ∈ P X → R.map U ∈ Q (U.obj X))
    (hpres : ∀ (X Y Z : C) (R : Presieve X), R ∈ P X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) U) :
    U.IsContinuous P.toGrothendieck Q.toGrothendieck

theorem continuous_equivalence_pullback_exact
    {A B : Type u} [SmallCategory A] [SmallCategory B]
    (JA : GrothendieckTopology A) (JB : GrothendieckTopology B)
    (p : A ⥤ B) (e : B ⥤ A)
    (eta : 𝟭 A ≅ p ⋙ e) (epsilon : e ⋙ p ≅ 𝟭 B)
    [p.IsContinuous JA JB] [e.IsContinuous JB JA] :
    PreservesFiniteLimits (sheafPullback p (Type u) JA JB) ∧
    PreservesFiniteColimits (sheafPullback p (Type u) JA JB)

theorem continuous_composite_pullback_exact
    {A B C : Type u} [SmallCategory A] [SmallCategory B] [SmallCategory C]
    (JA : GrothendieckTopology A) (JB : GrothendieckTopology B)
    (JC : GrothendieckTopology C) (p : A ⥤ B) (q : B ⥤ C)
    [p.IsContinuous JA JB] [q.IsContinuous JB JC]
    [PreservesFiniteLimits (sheafPullback p (Type u) JA JB)]
    [PreservesFiniteColimits (sheafPullback p (Type u) JA JB)]
    [PreservesFiniteLimits (sheafPullback q (Type u) JB JC)]
    [PreservesFiniteColimits (sheafPullback q (Type u) JB JC)] :
    have : (p ⋙ q).IsContinuous JA JC

theorem finiteEquivalencePrecoverage_sheaf_equivalence
    {A B : Type u} [SmallCategory A] [SmallCategory B]
    (p : A ⥤ B) [p.IsEquivalence] (P : Precoverage B)
    [P.HasIsos] [P.IsStableUnderFiniteComposition] [P.IsStableUnderFiniteBaseChange]
    [P.HasPullbacks] (e : B ⥤ A) [e.IsEquivalence] (hep : e ⋙ p = 𝟭 B)
    (hfinite : ∀ (X : B) (R : Presieve X), R ∈ P X → Finite R.uncurry) :
    ∃ (_ : p.IsContinuous (finiteEquivalencePrecoverage p P).toGrothendieck
        P.toGrothendieck),
      ∃ (_ : e.IsContinuous P.toGrothendieck
          (finiteEquivalencePrecoverage p P).toGrothendieck),
        (PreservesFiniteLimits (sheafPullback p (Type u)
          (finiteEquivalencePrecoverage p P).toGrothendieck P.toGrothendieck) ∧
        PreservesFiniteColimits (sheafPullback p (Type u)
          (finiteEquivalencePrecoverage p P).toGrothendieck P.toGrothendieck)) ∧
        (PreservesFiniteLimits (sheafPullback e (Type u) P.toGrothendieck
          (finiteEquivalencePrecoverage p P).toGrothendieck) ∧
        PreservesFiniteColimits (sheafPullback e (Type u) P.toGrothendieck
          (finiteEquivalencePrecoverage p P).toGrothendieck))

theorem continuous_transport_pullback_exact
    {A B C D : Type u}
    [SmallCategory A] [SmallCategory B] [SmallCategory C] [SmallCategory D]
    (JA : GrothendieckTopology A) (JB : GrothendieckTopology B)
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (p : A ⥤ C) (U : C ⥤ D) (e : D ⥤ B) (T : A ⥤ B)
    [p.IsContinuous JA JC] [U.IsContinuous JC JD] [e.IsContinuous JD JB]
    [T.IsContinuous JA JB]
    [PreservesFiniteLimits (sheafPullback p (Type u) JA JC)]
    [PreservesFiniteColimits (sheafPullback p (Type u) JA JC)]
    [PreservesFiniteLimits (sheafPullback U (Type u) JC JD)]
    [PreservesFiniteColimits (sheafPullback U (Type u) JC JD)]
    [PreservesFiniteLimits (sheafPullback e (Type u) JD JB)]
    [PreservesFiniteColimits (sheafPullback e (Type u) JD JB)]
    (theta : T ≅ (p ⋙ U) ⋙ e) :
    PreservesFiniteLimits (sheafPullback T (Type u) JA JB) ∧
    PreservesFiniteColimits (sheafPullback T (Type u) JA JB)
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineEtaleFiniteColimitConstruction | unclaimed (new module by W4) | Uses the generalized universes and finite site axioms; fully proved. |
| Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| Sheaf.AlgebraicGeometry.AffineComparisonInjectiveVanishing | V3 | Unchanged signature and source; generalized APIs preserve its old specialization. |
| Sheaf.AlgebraicGeometry.AffineEtaleColimitPresentationFinite | W4 | Assigned item; new private proofs use the larger-universe finite APIs. |
| Sheaf.AlgebraicGeometry.AffineEtaleSiteColimitStatement | W3 | Unchanged signature and source; generalized APIs preserve its old specialization. |
| Sheaf.AlgebraicGeometry.ComparisonDirectImage | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| Sheaf.AlgebraicGeometry.ProEtaleFunctionsQuotientSections | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel | T4 | Unchanged signature and source; generalized APIs preserve its old specialization. |
| Sheaf.CategoryTheory.SiteSystemFiniteCoverings | unclaimed | Interface generalized; all proofs compile. |
| Sheaf.CategoryTheory.SiteSystemFiniteSheafTransport | unclaimed | Interface generalized; all proofs compile. |
| Sheaf.CategoryTheory.SiteSystemStrictification | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| Sheaf.CategoryTheory.SiteSystemStrictificationCategory | unclaimed | Interface generalized; all proofs compile. |
| Sheaf.CategoryTheory.SiteSystemStrictificationData | unclaimed | Direct consumer; unchanged original source compiled against the overlay. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | C2 | Unchanged signature and source; generalized APIs preserve its old specialization. |
| Sheaf.Paper.ProEtaleLisseOrigin | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| TargetsCheck | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexInternalHom | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexTensorHom | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.AmbientCounterexample | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.AmbientCounterexampleCoproducts | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Comparison | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Comparison.Counterexample | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic | V2 | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Derived.AlgClosedField | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Comparison | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ComparisonMonoidal | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Constructible | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Derived.DualPerfect | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Duality | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Finiteness | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Derived.FlatModel | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Derived.HomComparison | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationConstructible | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationFiniteTor | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekBaseChange | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekComparison | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekIndependence | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerStarProjectionComparison | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Derived.OpenCover | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ProjectionFormula | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ProjectionFormulaExtendScalars | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ScalarExtension | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Shift | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Stability | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitude | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitudeResidue | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriek | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.Derived.WeilComplex | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtension | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Additivity | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Adic | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobenius | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobeniusLift | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobeniusTrace | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicRange | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicSystem | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AffineLine | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AffineReduction | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Correspondence | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Curve | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Defs | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.FiniteModel | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.FixedPoints | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Frobenius | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.GlobalOperator | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Iterate | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.KernelPushforward | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.LocalFrobenius | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Localization | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Main | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ModelRestriction | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Pairing | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Perfectness | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperCurve | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperPushforward | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.PushforwardFibres | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.PushforwardStep | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.RelativeAffineLine | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceClass | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceFormulaHolds | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceMap | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.SixFunctors.ProEtale.WeaklyContractibleCohomology | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.Statement | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.WeilSheaf.Localization | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Unchanged signature and source; generalized APIs preserve its old specialization. |

The uses search found actual mentions only in the three changed utility modules and
SiteSystemStrictificationData; the other rows are transitive importers. No forced
adaptation of a held module is included.

## Status

landed 20261016T054839-L-158286 2026-10-16 (merge of deliver/W4/Sheaf.AlgebraicGeometry.AffineEtaleColimitPresentationFinite)
