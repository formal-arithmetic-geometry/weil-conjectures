# AlgebraicGeometry.Scheme.FrobeniusStalkTrivializationNormalized

## Reason

The explicit nested normalization predicate repeats concrete stalk, pullback and derived
expressions at the identity point of `Spec k`. Kernel conversions in the complete proof
exceeded the fixed 60-second single-file limit. Factor the germ, map, derived, site, unit, composition and naturality formulas
into public predicates with arbitrary map and point parameters. Their bodies are exactly
the original formulas. Use named proved point-equality lemmas in equality transports.
The two reparametrization compatibility clauses now write `𝟙 _ ≫ z` explicitly, the
point already indexing their comparison source. This is the same point as `z`.
The original theorem signature, quantifiers, boundedness hypotheses,
normalization equations and chosen data are preserved. One logical regrouping separates
`(∃ w, naturality w) ∧ derived` from `∃ w, naturality w ∧ derived`; the derived clause
does not depend on `w`, so the two are equivalent. Equality-proof transports are
unchanged by proof irrelevance. No data comes from a new existence
claim. This definition repair reopens the target-definition review, as required.

## Old

```lean
def FrobeniusStalkTrivializationNormalized
    (p : ℕ) (hp : Nat.Prime p) (k : Type u) [Field k] [IsAlgClosed k]
    (hs : (Spec (.of k)).IsCharacteristic p) (X : Scheme.{u})
    (hX : X.IsCharacteristic p) (z : Spec (.of k) ⟶ X)
    (A : Type u) [CommRing A] [Finite A] : Prop :=
  ∀ b : ℕ,
    ∃ (δ : k ≃+* k),
      (∀ x : k, δ x = x ^ p ^ b) ∧
      ∃ (_hδS : Spec.map (CommRingCat.ofHom δ.toRingHom) =
          (Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b),
      ∃ (_hz : Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z =
          z ≫ X.iterateFrobenius hp (hX.2 ⊤) b),
        ∃ (rS : 𝟭 (Spec (.of k)).ProEt ≅ proEtaleBaseChange
            ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b))
          (rX : 𝟭 X.ProEt ≅ proEtaleBaseChange
            (X.iterateFrobenius hp (hX.2 ⊤) b))
          (tauS : proEtaleConstantRingPullback A
            ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b) ≅ 𝟭 _)
          (tauX : proEtaleConstantRingPullback A
            (X.iterateFrobenius hp (hX.2 ⊤) b) ≅ 𝟭 _),
          (∀ (V : (Spec (.of k)).ProEt),
            ∃ hV : (p : Γ(V.left, ⊤)) = 0,
              (rS.hom.app V).left ≫ pullback.fst V.hom
                  ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b) =
                V.left.iterateFrobenius hp hV b) ∧
          (∀ (V : X.ProEt),
            ∃ hV : (p : Γ(V.left, ⊤)) = 0,
              (rX.hom.app V).left ≫ pullback.fst V.hom
                  (X.iterateFrobenius hp (hX.2 ⊤) b) =
                V.left.iterateFrobenius hp hV b) ∧
          (∀ (M : proEtaleRingModules (Spec (.of k))
                (proEtaleConstantRing (Spec (.of k)) A))
            (V : (Spec (.of k)).ProEt)
            (m : M.val.obj (op V)),
            ((proEtaleConstantRingAdjunction A
                ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b)).unit.app M ≫
              (proEtaleConstantRingPushforward A
                ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b)).map
                (tauS.hom.app M)).val.app (op V) m =
              M.val.map (rS.inv.app V).op m) ∧
          (∀ (M : proEtaleRingModules X (proEtaleConstantRing X A))
            (V : X.ProEt) (m : M.val.obj (op V)),
            ((proEtaleConstantRingAdjunction A
                (X.iterateFrobenius hp (hX.2 ⊤) b)).unit.app M ≫
              (proEtaleConstantRingPushforward A
                (X.iterateFrobenius hp (hX.2 ⊤) b)).map
                (tauX.hom.app M)).val.app (op V) m =
              M.val.map (rX.inv.app V).op m) ∧
          (∀ (M : proEtaleRingModules X (proEtaleConstantRing X A))
              (N : ProEtaleGeometricNeighbourhood
                (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z))
              (a : M.val.obj (op N.right)),
            (eqToHom (congrArg (fun w => (finiteCoefficientModuleStalkFunctor w A).obj M)
                _hz) ≫
              (proEtalePullbackStalkComparison A
                (X.iterateFrobenius hp (hX.2 ⊤) b) z).inv.app M ≫
              (finiteCoefficientModuleStalkFunctor z A).map (tauX.hom.app M))
                (proEtaleCoefficientModuleGerm
                  (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z) A M N a) =
            eqToHom (congrArg (fun w => (finiteCoefficientModuleStalkFunctor w A).obj M)
                (by
                  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
                  simp : Spec.map (CommRingCat.ofHom δ.symm.toRingHom) ≫
                    Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z = z))
              ((proEtaleStalkReparam A
                (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z) δ.symm).hom.app M
                (proEtaleCoefficientModuleGerm
                  (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z) A M N a))) ∧
          (∀ (M : proEtaleRingModules X
              (proEtaleConstantRing X A)),
            (proEtalePullbackStalkComparison A z (𝟙 _)).hom.app M ≫
              (proEtaleStalkReparam A z δ).hom.app M =
            (proEtaleStalkReparam A (𝟙 (Spec (.of k))) δ).hom.app
                ((proEtaleConstantRingPullback A z).obj M) ≫
              (proEtalePullbackStalkComparison A z
                (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ 𝟙 _)).hom.app M ≫
              eqToHom (congrArg (fun w =>
                  (finiteCoefficientModuleStalkFunctor w A).obj M)
                (Category.assoc (Spec.map (CommRingCat.ofHom δ.toRingHom))
                  (𝟙 (Spec (.of k))) z))) ∧
          (∀ (H : CochainComplex (proEtaleRingModules X
              (proEtaleConstantRing X A)) ℤ),
            (∃ a₀ b₀ : ℤ, ∀ n : ℤ, n < a₀ ∨ b₀ < n → IsZero (H.X n)) →
            (proEtaleDerivedPullbackStalkComparison A z (𝟙 _)).hom.app
                (DerivedCategory.Q.obj H) ≫
              (proEtaleDerivedStalkReparam A z δ).hom.app
                (DerivedCategory.Q.obj H) =
            (proEtaleDerivedStalkReparam A (𝟙 (Spec (.of k))) δ).hom.app
                ((proEtaleConstantRingDerivedPullback A z).obj
                  (DerivedCategory.Q.obj H)) ≫
              (proEtaleDerivedPullbackStalkComparison A z
                (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ 𝟙 _)).hom.app
                (DerivedCategory.Q.obj H) ≫
              eqToHom (congrArg (fun w =>
                  (proEtaleFiniteCoefficientDerivedStalk A w).obj
                    (DerivedCategory.Q.obj H))
                (Category.assoc (Spec.map (CommRingCat.ofHom δ.toRingHom))
                  (𝟙 (Spec (.of k))) z))) ∧
          (∀ (M : proEtaleRingModules (Spec (.of k))
              (proEtaleConstantRing (Spec (.of k)) A))
              (N : ProEtaleGeometricNeighbourhood
                (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ 𝟙 (Spec (.of k))))
              (a : M.val.obj (op N.right)),
            (eqToHom (congrArg (fun w =>
                (finiteCoefficientModuleStalkFunctor w A).obj M)
              (by rw [_hδS, Category.comp_id, Category.id_comp])) ≫
              (proEtalePullbackStalkComparison A
                ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b) (𝟙 _)).inv.app M ≫
              (finiteCoefficientModuleStalkFunctor (𝟙 (Spec (.of k))) A).map
                (tauS.hom.app M))
                (proEtaleCoefficientModuleGerm
                  (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫
                    𝟙 (Spec (.of k))) A M N a) =
            eqToHom (congrArg (fun w =>
                (finiteCoefficientModuleStalkFunctor w A).obj M)
              (by
                rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
                simp : Spec.map (CommRingCat.ofHom δ.symm.toRingHom) ≫
                  Spec.map (CommRingCat.ofHom δ.toRingHom) ≫
                    𝟙 (Spec (.of k)) = 𝟙 (Spec (.of k))))
              ((proEtaleStalkReparam A
                (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫
                  𝟙 (Spec (.of k))) δ.symm).hom.app M
                (proEtaleCoefficientModuleGerm
                  (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫
                    𝟙 (Spec (.of k))) A M N a))) ∧
          (∀ (M : proEtaleRingModules (Spec (.of k))
              (proEtaleConstantRing (Spec (.of k)) A)),
            eqToHom (congrArg (fun w =>
                (finiteCoefficientModuleStalkFunctor w A).obj M)
              (by rw [_hδS, Category.comp_id, Category.id_comp])) ≫
              (proEtalePullbackStalkComparison A
                ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b) (𝟙 _)).inv.app M ≫
              (finiteCoefficientModuleStalkFunctor (𝟙 (Spec (.of k))) A).map
                (tauS.hom.app M) =
            (proEtaleStalkReparam A
              (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ 𝟙 (Spec (.of k))) δ.symm).hom.app M ≫
              eqToHom (congrArg (fun w =>
                  (finiteCoefficientModuleStalkFunctor w A).obj M)
                (by
                  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
                  simp : Spec.map (CommRingCat.ofHom δ.symm.toRingHom) ≫
                    Spec.map (CommRingCat.ofHom δ.toRingHom) ≫
                      𝟙 (Spec (.of k)) = 𝟙 (Spec (.of k))))) ∧
          (∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)),
            eqToHom (congrArg (fun w => (finiteCoefficientModuleStalkFunctor w A).obj M)
                _hz) ≫
              (proEtalePullbackStalkComparison A
                (X.iterateFrobenius hp (hX.2 ⊤) b) z).inv.app M ≫
              (finiteCoefficientModuleStalkFunctor z A).map (tauX.hom.app M) =
            (proEtaleStalkReparam A (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z)
              δ.symm).hom.app M ≫
              eqToHom (congrArg (fun w => (finiteCoefficientModuleStalkFunctor w A).obj M)
                (by
                  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
                  simp : Spec.map (CommRingCat.ofHom δ.symm.toRingHom) ≫
                    Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z = z))) ∧
          (∀ (H : CochainComplex (proEtaleRingModules (Spec (.of k))
              (proEtaleConstantRing (Spec (.of k)) A)) ℤ),
            (∃ a₀ b₀ : ℤ, ∀ n : ℤ, n < a₀ ∨ b₀ < n → IsZero (H.X n)) →
            eqToHom (congrArg (fun w =>
                (proEtaleFiniteCoefficientDerivedStalk A w).obj
                  (DerivedCategory.Q.obj H))
              (by rw [_hδS, Category.comp_id, Category.id_comp])) ≫
              (proEtaleDerivedPullbackStalkComparison A
                ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b) (𝟙 _)).inv.app
                (DerivedCategory.Q.obj H) ≫
              (proEtaleFiniteCoefficientDerivedStalk A (𝟙 (Spec (.of k)))).map
                ((proEtaleFrobeniusDerivedIso A tauS).hom.app
                  (DerivedCategory.Q.obj H)) =
            (proEtaleDerivedStalkReparam A
              (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫
                𝟙 (Spec (.of k))) δ.symm).hom.app
              (DerivedCategory.Q.obj H) ≫
              eqToHom (congrArg (fun w =>
                  (proEtaleFiniteCoefficientDerivedStalk A w).obj
                    (DerivedCategory.Q.obj H))
                (by
                  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
                  simp : Spec.map (CommRingCat.ofHom δ.symm.toRingHom) ≫
                    Spec.map (CommRingCat.ofHom δ.toRingHom) ≫
                      𝟙 (Spec (.of k)) = 𝟙 (Spec (.of k))))) ∧
          ∃ (comp : ∀ {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W),
              proEtaleConstantRingPullback A (f ≫ g) ≅
                proEtaleConstantRingPullback A g ⋙
                  proEtaleConstantRingPullback A f),
            (∀ {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W)
                (M : proEtaleRingModules Y (proEtaleConstantRing Y A))
                (V : W.ProEt)
                (m : ((proEtaleConstantRingPushforward A f ⋙
                  proEtaleConstantRingPushforward A g).obj M).val.obj (op V)),
              ((conjugateIsoEquiv
                ((proEtaleConstantRingAdjunction A g).comp
                  (proEtaleConstantRingAdjunction A f))
                (proEtaleConstantRingAdjunction A (f ≫ g))
                (comp f g)).hom.app M).val.app (op V) m =
                M.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app V).op m) ∧
            ∃ (w : (Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b ≫ z =
                z ≫ X.iterateFrobenius hp (hX.2 ⊤) b),
              (proEtaleFrobeniusDerivedComp A z
                (X.iterateFrobenius hp (hX.2 ⊤) b)
                (comp z (X.iterateFrobenius hp (hX.2 ⊤) b))).inv ≫
                eqToHom (congrArg (proEtaleConstantRingDerivedPullback A) w.symm) ≫
                (proEtaleFrobeniusDerivedComp A
                  ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b) z
                  (comp ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b) z)).hom ≫
                Functor.whiskerLeft
                  (proEtaleConstantRingDerivedPullback A z)
                  (proEtaleFrobeniusDerivedIso A tauS).hom ≫
                (Functor.rightUnitor _).hom =
              Functor.whiskerRight
                (proEtaleFrobeniusDerivedIso A tauX).hom
                (proEtaleConstantRingDerivedPullback A z) ≫
                (Functor.leftUnitor _).hom ∧
          (∀ (H : CochainComplex (proEtaleRingModules X
              (proEtaleConstantRing X A)) ℤ),
            (∃ a₀ b₀ : ℤ, ∀ n : ℤ, n < a₀ ∨ b₀ < n → IsZero (H.X n)) →
            eqToHom (congrArg (fun w => (proEtaleFiniteCoefficientDerivedStalk A w).obj
                (DerivedCategory.Q.obj H)) _hz) ≫
              (proEtaleDerivedPullbackStalkComparison A
                (X.iterateFrobenius hp (hX.2 ⊤) b) z).inv.app (DerivedCategory.Q.obj H) ≫
              (proEtaleFiniteCoefficientDerivedStalk A z).map
                ((proEtaleFrobeniusDerivedIso A tauX).hom.app (DerivedCategory.Q.obj H)) =
            (proEtaleDerivedStalkReparam A
              (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z) δ.symm).hom.app
                (DerivedCategory.Q.obj H) ≫
              eqToHom (congrArg (fun w => (proEtaleFiniteCoefficientDerivedStalk A w).obj
                (DerivedCategory.Q.obj H))
                (by
                  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
                  simp : Spec.map (CommRingCat.ofHom δ.symm.toRingHom) ≫
                    Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z = z)))
```

## New

The following proved point-equality lemmas and explicit predicates precede the repaired
definition in the same module:

```lean
/-- Cancellation of the inverse field reparametrization on a geometric point.
Source: Stacks Tag 0F6W (blueprint: lem-trf-frobenius-stalk-trivialization-normalization). -/
theorem frobeniusNormalization_inverse_point {k : Type u} [Field k] (δ : k ≃+* k)
    {T : Scheme.{u}} (x : Spec (.of k) ⟶ T) :
    Spec.map (CommRingCat.ofHom δ.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ x = x := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  simp

/-- Identity-point form of a specified scheme-map equality.
Source: Stacks Tag 0F6W (blueprint: lem-trf-frobenius-stalk-trivialization-normalization). -/
theorem frobeniusNormalization_identity_point {S : Scheme.{u}}
    {f g : S ⟶ S} (h : f = g) : f ≫ 𝟙 S = 𝟙 S ≫ g := by
  simpa only [Category.comp_id, Category.id_comp] using h

/-- The projection formula specifying the relative-Frobenius site isomorphism.
Source: Stacks Tag 0F6W (blueprint: lem-trf-frobenius-stalk-trivialization-normalization). -/
def FrobeniusNormalizationSite (p : ℕ) (hp : p.Prime) (b : ℕ)
    {T : Scheme.{u}} (f : T ⟶ T) (r : 𝟭 T.ProEt ≅ proEtaleBaseChange f) : Prop :=
  ∀ V : T.ProEt, ∃ hV : (p : Γ(V.left, ⊤)) = 0,
    (r.hom.app V).left ≫ pullback.fst V.hom f = V.left.iterateFrobenius hp hV b

/-- The sectionwise adjunction-unit equation specifying the module trivialization.
Source: Stacks Tag 0F6W (blueprint: lem-trf-frobenius-stalk-trivialization-normalization). -/
def FrobeniusNormalizationUnit {T : Scheme.{u}} (f : T ⟶ T)
    (A : Type u) [CommRing A] (r : 𝟭 T.ProEt ≅ proEtaleBaseChange f)
    (tau : proEtaleConstantRingPullback A f ≅ 𝟭 _) : Prop :=
  ∀ (M : proEtaleRingModules T (proEtaleConstantRing T A))
    (V : T.ProEt) (a : M.val.obj (op V)),
    ((proEtaleConstantRingAdjunction A f).unit.app M ≫
      (proEtaleConstantRingPushforward A f).map (tau.hom.app M)).val.app (op V) a =
        M.val.map (r.inv.app V).op a

set_option backward.isDefEq.respectTransparency.types false in
/-- The germs clause of inverse-Frobenius normalization, with the map and point
kept as parameters to avoid expanding their constructions during type comparison.
Source: Stacks Tag 0F6W (blueprint: lem-trf-frobenius-stalk-trivialization-normalization). -/
def FrobeniusNormalizationGerms
    {k : Type u} [Field k] [IsAlgClosed k] {T : Scheme.{u}}
    (f : T ⟶ T) (x y : Spec (.of k) ⟶ T) (A : Type u) [CommRing A] [Finite A]
    (α : k ≃+* k) (hx : y = x ≫ f)
    (hα : Spec.map (CommRingCat.ofHom α.toRingHom) ≫ y = x)
    (tau : proEtaleConstantRingPullback A f ≅ 𝟭 _) : Prop :=
  ∀ (M : proEtaleRingModules T (proEtaleConstantRing T A))
    (N : ProEtaleGeometricNeighbourhood
      y)
    (a : M.val.obj (op N.right)),
  (eqToHom (congrArg (fun w => (finiteCoefficientModuleStalkFunctor w A).obj M)
      hx) ≫
    (proEtalePullbackStalkComparison A
      f x).inv.app M ≫
    (finiteCoefficientModuleStalkFunctor x A).map (tau.hom.app M))
      (proEtaleCoefficientModuleGerm
        y A M N a) =
  eqToHom (congrArg (fun w => (finiteCoefficientModuleStalkFunctor w A).obj M)
      hα)
    ((proEtaleStalkReparam A
      y α).hom.app M
      (proEtaleCoefficientModuleGerm
        y A M N a))

set_option backward.isDefEq.respectTransparency.types false in
/-- The maps clause of inverse-Frobenius normalization, with the map and point
kept as parameters to avoid expanding their constructions during type comparison.
Source: Stacks Tag 0F6W (blueprint: lem-trf-frobenius-stalk-trivialization-normalization). -/
def FrobeniusNormalizationMaps
    {k : Type u} [Field k] [IsAlgClosed k] {T : Scheme.{u}}
    (f : T ⟶ T) (x y : Spec (.of k) ⟶ T) (A : Type u) [CommRing A] [Finite A]
    (α : k ≃+* k) (hx : y = x ≫ f)
    (hα : Spec.map (CommRingCat.ofHom α.toRingHom) ≫ y = x)
    (tau : proEtaleConstantRingPullback A f ≅ 𝟭 _) : Prop :=
  ∀ (M : proEtaleRingModules T (proEtaleConstantRing T A)),
  eqToHom (congrArg (fun w => (finiteCoefficientModuleStalkFunctor w A).obj M)
      hx) ≫
    (proEtalePullbackStalkComparison A
      f x).inv.app M ≫
    (finiteCoefficientModuleStalkFunctor x A).map (tau.hom.app M) =
  (proEtaleStalkReparam A y
    α).hom.app M ≫
    eqToHom (congrArg (fun w => (finiteCoefficientModuleStalkFunctor w A).obj M)
      hα)

set_option backward.isDefEq.respectTransparency.types false in
/-- The derived clause of inverse-Frobenius normalization, with the map and point
kept as parameters to avoid expanding their constructions during type comparison.
Source: Stacks Tag 0F6W (blueprint: lem-trf-frobenius-stalk-trivialization-normalization). -/
def FrobeniusNormalizationDerived
    {k : Type u} [Field k] [IsAlgClosed k] {T : Scheme.{u}}
    (f : T ⟶ T) (x y : Spec (.of k) ⟶ T) (A : Type u) [CommRing A] [Finite A]
    (α : k ≃+* k) (hx : y = x ≫ f)
    (hα : Spec.map (CommRingCat.ofHom α.toRingHom) ≫ y = x)
    (tau : proEtaleConstantRingPullback A f ≅ 𝟭 _) : Prop :=
  ∀ (H : CochainComplex (proEtaleRingModules T
    (proEtaleConstantRing T A)) ℤ),
  (∃ a₀ b₀ : ℤ, ∀ n : ℤ, n < a₀ ∨ b₀ < n → IsZero (H.X n)) →
  eqToHom (congrArg (fun w => (proEtaleFiniteCoefficientDerivedStalk A w).obj
      (DerivedCategory.Q.obj H)) hx) ≫
    (proEtaleDerivedPullbackStalkComparison A
      f x).inv.app (DerivedCategory.Q.obj H) ≫
    (proEtaleFiniteCoefficientDerivedStalk A x).map
      ((proEtaleFrobeniusDerivedIso A tau).hom.app (DerivedCategory.Q.obj H)) =
  (proEtaleDerivedStalkReparam A
    y α).hom.app
      (DerivedCategory.Q.obj H) ≫
    eqToHom (congrArg (fun w => (proEtaleFiniteCoefficientDerivedStalk A w).obj
      (DerivedCategory.Q.obj H))
      hα)

set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback compatibility with field reparametrization in the normalization formula.
Source: Stacks Tag 0F6W (blueprint: lem-trf-frobenius-stalk-trivialization-normalization). -/
def FrobeniusNormalizationReparametrization
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (z : Spec (.of k) ⟶ X) (A : Type u) [CommRing A] [Finite A]
    (δ : k ≃+* k) : Prop :=
  ∀ (M : proEtaleRingModules X
    (proEtaleConstantRing X A)),
  (proEtalePullbackStalkComparison A z (𝟙 _)).hom.app M ≫
    (proEtaleStalkReparam A (𝟙 _ ≫ z) δ).hom.app M =
  (proEtaleStalkReparam A (𝟙 (Spec (.of k))) δ).hom.app
      ((proEtaleConstantRingPullback A z).obj M) ≫
    (proEtalePullbackStalkComparison A z
      (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ 𝟙 _)).hom.app M ≫
    eqToHom (congrArg (fun w =>
        (finiteCoefficientModuleStalkFunctor w A).obj M)
      (Category.assoc (Spec.map (CommRingCat.ofHom δ.toRingHom))
        (𝟙 (Spec (.of k))) z))

set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback compatibility with field reparametrization in the normalization formula.
Source: Stacks Tag 0F6W (blueprint: lem-trf-frobenius-stalk-trivialization-normalization). -/
def FrobeniusNormalizationDerivedReparametrization
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (z : Spec (.of k) ⟶ X) (A : Type u) [CommRing A] [Finite A]
    (δ : k ≃+* k) : Prop :=
  ∀ (H : CochainComplex (proEtaleRingModules X
    (proEtaleConstantRing X A)) ℤ),
  (∃ a₀ b₀ : ℤ, ∀ n : ℤ, n < a₀ ∨ b₀ < n → IsZero (H.X n)) →
  (proEtaleDerivedPullbackStalkComparison A z (𝟙 _)).hom.app
      (DerivedCategory.Q.obj H) ≫
    (proEtaleDerivedStalkReparam A (𝟙 _ ≫ z) δ).hom.app
      (DerivedCategory.Q.obj H) =
  (proEtaleDerivedStalkReparam A (𝟙 (Spec (.of k))) δ).hom.app
      ((proEtaleConstantRingDerivedPullback A z).obj
        (DerivedCategory.Q.obj H)) ≫
    (proEtaleDerivedPullbackStalkComparison A z
      (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ 𝟙 _)).hom.app
      (DerivedCategory.Q.obj H) ≫
    eqToHom (congrArg (fun w =>
        (proEtaleFiniteCoefficientDerivedStalk A w).obj
          (DerivedCategory.Q.obj H))
      (Category.assoc (Spec.map (CommRingCat.ofHom δ.toRingHom))
        (𝟙 (Spec (.of k))) z))

/-- The unit-normalized pullback composition comparison used in normalization.
Source: Stacks Tag 0F6W (blueprint: lem-trf-frobenius-stalk-trivialization-normalization). -/
def FrobeniusNormalizationComposition (A : Type u) [CommRing A]
    (comp : ∀ {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W),
      proEtaleConstantRingPullback A (f ≫ g) ≅
        proEtaleConstantRingPullback A g ⋙ proEtaleConstantRingPullback A f) : Prop :=
  ∀ {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W)
                (M : proEtaleRingModules Y (proEtaleConstantRing Y A))
                (V : W.ProEt)
                (m : ((proEtaleConstantRingPushforward A f ⋙
                  proEtaleConstantRingPushforward A g).obj M).val.obj (op V)),
              ((conjugateIsoEquiv
                ((proEtaleConstantRingAdjunction A g).comp
                  (proEtaleConstantRingAdjunction A f))
                (proEtaleConstantRingAdjunction A (f ≫ g))
                (comp f g)).hom.app M).val.app (op V) m =
                M.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app V).op m

/-- The derived naturality equation for the specified Frobenius trivializations.
Source: Stacks Tag 0F6W (blueprint: lem-trf-frobenius-stalk-trivialization-normalization). -/
def FrobeniusNormalizationNaturality (A : Type u) [CommRing A]
    (comp : ∀ {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W),
      proEtaleConstantRingPullback A (f ≫ g) ≅
        proEtaleConstantRingPullback A g ⋙ proEtaleConstantRingPullback A f)
    {T X : Scheme.{u}} (t : T ⟶ X) (f : T ⟶ T) (g : X ⟶ X)
    (tauT : proEtaleConstantRingPullback A f ≅ 𝟭 _)
    (tauX : proEtaleConstantRingPullback A g ≅ 𝟭 _) : Prop :=
  ∃ (w : f ≫ t =
                t ≫ g),
              (proEtaleFrobeniusDerivedComp A t
                g
                (comp t g)).inv ≫
                eqToHom (congrArg (proEtaleConstantRingDerivedPullback A) w.symm) ≫
                (proEtaleFrobeniusDerivedComp A
                  f t
                  (comp f t)).hom ≫
                Functor.whiskerLeft
                  (proEtaleConstantRingDerivedPullback A t)
                  (proEtaleFrobeniusDerivedIso A tauT).hom ≫
                (Functor.rightUnitor _).hom =
              Functor.whiskerRight
                (proEtaleFrobeniusDerivedIso A tauX).hom
                (proEtaleConstantRingDerivedPullback A t) ≫
                (Functor.leftUnitor _).hom

def FrobeniusStalkTrivializationNormalized
    (p : ℕ) (hp : Nat.Prime p) (k : Type u) [Field k] [IsAlgClosed k]
    (hs : (Spec (.of k)).IsCharacteristic p) (X : Scheme.{u})
    (hX : X.IsCharacteristic p) (z : Spec (.of k) ⟶ X)
    (A : Type u) [CommRing A] [Finite A] : Prop :=
  ∀ b : ℕ,
    ∃ (δ : k ≃+* k),
      (∀ x : k, δ x = x ^ p ^ b) ∧
      ∃ (_hδS : Spec.map (CommRingCat.ofHom δ.toRingHom) =
          (Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b),
      ∃ (_hz : Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z =
          z ≫ X.iterateFrobenius hp (hX.2 ⊤) b),
        ∃ (rS : 𝟭 (Spec (.of k)).ProEt ≅ proEtaleBaseChange
            ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b))
          (rX : 𝟭 X.ProEt ≅ proEtaleBaseChange
            (X.iterateFrobenius hp (hX.2 ⊤) b))
          (tauS : proEtaleConstantRingPullback A
            ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b) ≅ 𝟭 _)
          (tauX : proEtaleConstantRingPullback A
            (X.iterateFrobenius hp (hX.2 ⊤) b) ≅ 𝟭 _),
          FrobeniusNormalizationSite p hp b
            ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b) rS ∧
          FrobeniusNormalizationSite p hp b (X.iterateFrobenius hp (hX.2 ⊤) b) rX ∧
          FrobeniusNormalizationUnit ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b) A rS tauS ∧
          FrobeniusNormalizationUnit (X.iterateFrobenius hp (hX.2 ⊤) b) A rX tauX ∧
          FrobeniusNormalizationGerms (X.iterateFrobenius hp (hX.2 ⊤) b) z
      (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z) A δ.symm _hz
      (frobeniusNormalization_inverse_point δ z) tauX ∧
          FrobeniusNormalizationReparametrization z A δ ∧
          FrobeniusNormalizationDerivedReparametrization z A δ ∧
          FrobeniusNormalizationGerms ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b) (𝟙 _)
            (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ 𝟙 _) A δ.symm
            (frobeniusNormalization_identity_point _hδS)
            (frobeniusNormalization_inverse_point δ (𝟙 _)) tauS ∧
          FrobeniusNormalizationMaps ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b) (𝟙 _)
            (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ 𝟙 _) A δ.symm
            (frobeniusNormalization_identity_point _hδS)
            (frobeniusNormalization_inverse_point δ (𝟙 _)) tauS ∧
          FrobeniusNormalizationMaps (X.iterateFrobenius hp (hX.2 ⊤) b) z
      (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z) A δ.symm _hz
      (frobeniusNormalization_inverse_point δ z) tauX ∧
          FrobeniusNormalizationDerived ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b) (𝟙 _)
            (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ 𝟙 _) A δ.symm
            (frobeniusNormalization_identity_point _hδS)
            (frobeniusNormalization_inverse_point δ (𝟙 _)) tauS ∧
          ∃ (comp : ∀ {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W),
              proEtaleConstantRingPullback A (f ≫ g) ≅
                proEtaleConstantRingPullback A g ⋙
                  proEtaleConstantRingPullback A f),
            FrobeniusNormalizationComposition A comp ∧
            FrobeniusNormalizationNaturality A comp z
              ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b)
              (X.iterateFrobenius hp (hX.2 ⊤) b) tauS tauX ∧
          FrobeniusNormalizationDerived (X.iterateFrobenius hp (hX.2 ⊤) b) z
      (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z) A δ.symm _hz
      (frobeniusNormalization_inverse_point δ z) tauX
```

## Users

`tools/downstream.py ... --uses FrobeniusStalkTrivializationNormalized` reports one
importing module and no use of this definition outside its own module. No consumer
signature or proof adaptation is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FrobeniusStalkTrivializationNormalization | W7 | Definition factored and sole theorem proved; unchanged theorem signature. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed; no adaptation | Imports this module but never unfolds or names the predicate; statement unchanged. |

The item compiled cleanly in 27.5 seconds. A fresh compile set of the exact current
item and unchanged consumer passed (54.6 and 30.4 seconds). The whole-definition `rfl` check fails because of the logically equivalent regrouping
of the naturality witness described above. An explicit bidirectional tuple reconstruction
check exceeded the 60-second limit.
The independent reader should check the explicit clause expansions in this record,
especially the identity-point source of the two compatibility equations.

## Status

landed 20261020T131225-L-1262738 2026-10-20 (merge of deliver/W7/Sheaf.AlgebraicGeometry.FrobeniusStalkTrivializationNormalization)
