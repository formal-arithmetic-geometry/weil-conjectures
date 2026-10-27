# SheafOfModules.SequenceProjection.sequenceTensorAugmentationUnit

## Reason

The fully expanded eleven-clause normalization conjunction repeatedly compares
large concrete category and localization instances in the kernel. The proof
checked with only the permitted axioms but exceeded the per-file compile limit.
Factor exactly that conjunction, in exactly its original right-associated order,
followed by the existing augmentation clause, into the public predicate
`augmentedDerivedLimitProperties`. Its body is copied from the original equations;
no hypothesis, witness, equation or quantifier is added, removed or weakened.
The new statement unfolds definitionally to the original one. This follows the
existing `derivedLimitProperties` factorization in
`SequencePushforwardLimitProjections`.

The predicate contains real proposition data, no choice and no postponed proof.
No target statement or existing definition changes. Local reducibility attributes
are not exported. There are no existing Lean importers to adapt.

## Old

```lean
theorem sequenceTensorAugmentationUnit
    (A : Sheaf J CommRingCat.{w}) (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B)
    [HasDerivedCategory.{d} (Modules A)] [HasDerivedCategory.{d} (StrictRingSystem B)]
    [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ Modules A)]
    [∀ n : ℕ, HasDerivedCategory.{d} (systemLevel B n)] :
    ∃ (G : Modules A ⥤ StrictRingSystem B) (F : StrictRingSystem B ⥤ Modules A)
      (_ : G.Additive) (_ : F.Additive)
      (e : ∀ (M : Modules A) (n : ℕ),
        (G.obj M).level n ≅ changeOfRings (α.app (op n)) M)
      (π : ∀ (N : StrictRingSystem B) (n : ℕ),
        F.obj N ⟶ (restriction A B α n).obj (N.level n))
      (adj : G ⊣ F),
      (∀ {M M' : Modules A} (f : M ⟶ M') (n : ℕ),
        (G.map f).app n ≫ (e M' n).hom =
          (e M n).hom ≫ changeOfRingsHom (α.app (op n)) M f) ∧
      (∀ (M : Modules A) {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ)
        (b : (B.obj (op n)).obj.obj U) (x : M.val.obj U),
        ((G.obj M).transition h).val.app U
            ((e M n).inv.val.app U (tensorSection (α.app (op n)) M U b x)) =
          (e M m).inv.val.app U (tensorSection (α.app (op m)) M U
            ((B.map (homOfLE h).op).hom.app U b) x)) ∧
      (∀ {N N' : StrictRingSystem B} (f : N ⟶ N') (n : ℕ),
        F.map f ≫ π N' n = π N n ≫ (restriction A B α n).map (f.app n)) ∧
      (∀ (N : StrictRingSystem B) {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ)
        (x : (F.obj N).val.obj U),
        (π N m).val.app U x =
          (N.transition h).val.app U ((π N n).val.app U x)) ∧
      (∀ (M : Modules A) (N : StrictRingSystem B)
        (f : ∀ n : ℕ, M ⟶ (restriction A B α n).obj (N.level n)),
        (∀ {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ) (x : M.val.obj U),
          (f m).val.app U x = (N.transition h).val.app U ((f n).val.app U x)) →
        ∃! h : M ⟶ F.obj N, ∀ n : ℕ, h ≫ π N n = f n) ∧
      (∀ (M : Modules A) (N : StrictRingSystem B) (h : M ⟶ F.obj N)
        (n : ℕ) (U : Cᵒᵖ) (b : (B.obj (op n)).obj.obj U) (x : M.val.obj U),
        (((adj.homEquiv M N).symm h).app n).val.app U
            ((e M n).inv.val.app U (tensorSection (α.app (op n)) M U b x)) =
          @SMul.smul ((B.obj (op n)).obj.obj U) ((N.level n).val.obj U) inferInstance b
            ((π N n).val.app U (h.val.app U x))) ∧
      ∃ (L : DerivedCategory.{d} (Modules A) ⥤ DerivedCategory.{d} (StrictRingSystem B))
        (R : DerivedCategory.{d} (StrictRingSystem B) ⥤ DerivedCategory.{d} (Modules A))
        (ε : DerivedCategory.Q ⋙ L ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
        (η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
        (derivedAdj : L ⊣ R),
        L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso (Modules A) (.up ℤ)) ∧
        R.IsRightDerivedFunctor η
          (HomologicalComplex.quasiIso (StrictRingSystem B) (.up ℤ)) ∧
        (∀ (Q : CochainComplex (Modules A) ℤ), Q.IsKFlatIndependentCoefficients →
          (∀ i : ℤ, (Q.X i).IsFlatOnSite) → IsIso (ε.app Q)) ∧
        (∀ (I : CochainComplex (StrictRingSystem B) ℤ), I.IsKInjective →
          IsIso (η.app I)) ∧
        (∀ (P Q : CochainComplex (Modules A) ℤ) (q : Q ⟶ P),
          Q.IsKFlatIndependentCoefficients → (∀ i : ℤ, (Q.X i).IsFlatOnSite) →
          QuasiIso q →
          ∃ c : L.obj (DerivedCategory.Q.obj P) ≅
            DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj Q),
            L.map (DerivedCategory.Q.map q) ≫ c.hom = ε.app Q) ∧
        (∀ (Q : CochainComplex (Modules A) ℤ)
          (I : CochainComplex (StrictRingSystem B) ℤ)
          (f : (G.mapHomologicalComplex (.up ℤ)).obj Q ⟶ I),
          derivedAdj.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
              (ε.app Q ≫ DerivedCategory.Q.map f) =
            DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv Q I f) ≫
              η.app I) ∧
        ∃ (U0 : StrictRingSystem B ⥤ (ℕᵒᵖ ⥤ Modules A))
          (_ : U0.Additive) (_ : PreservesFiniteLimits U0)
          (_ : PreservesFiniteColimits U0)
          (uObj : ∀ (N : StrictRingSystem B) (n : ℕ),
            (U0.obj N).obj (op n) = (restriction A B α n).obj (N.level n))
          (uEval : ∀ n : ℕ,
            U0 ⋙ (CategoryTheory.evaluation ℕᵒᵖ (Modules A)).obj (op n) ≅
              systemEvaluation B n ⋙ restriction A B α n)
          (πOrd : ∀ n : ℕ, F ⟶ systemEvaluation B n ⋙ restriction A B α n)
          (fLim : F ≅ U0 ⋙ (lim : (ℕᵒᵖ ⥤ Modules A) ⥤ Modules A))
          (RL : DerivedCategory.{d} (ℕᵒᵖ ⥤ Modules A) ⥤ DerivedCategory.{d} (Modules A))
          (etaLim : (lim : (ℕᵒᵖ ⥤ Modules A) ⥤ Modules A).mapHomologicalComplex (.up ℤ) ⋙
            DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RL)
          (piLim : ∀ n : ℕ, RL ⟶
            ((CategoryTheory.evaluation ℕᵒᵖ (Modules A)).obj (op n)).mapDerivedCategory)
          (xi : ∀ n : ℕ,
            U0.mapDerivedCategory ⋙
                ((CategoryTheory.evaluation ℕᵒᵖ (Modules A)).obj (op n)).mapDerivedCategory ≅
              (systemEvaluation B n).mapDerivedCategory ⋙
                (restriction A B α n).mapDerivedCategory)
          (c : R ≅ U0.mapDerivedCategory ⋙ RL)
          (levelAdj : ∀ n : ℕ, G ⋙ systemEvaluation B n ⊣ restriction A B α n)
          (derivedLevelAdj : ∀ n : ℕ,
            L ⋙ (systemEvaluation B n).mapDerivedCategory ⊣
              (restriction A B α n).mapDerivedCategory),
          (∀ {N N' : StrictRingSystem B} (f : N ⟶ N') (n : ℕ),
            (U0.map f).app (op n) ≫ eqToHom (uObj N' n) =
              eqToHom (uObj N n) ≫ (restriction A B α n).map (f.app n)) ∧
          (∀ (N : StrictRingSystem B) {m n : ℕ} (h : m ≤ n)
            (V : Cᵒᵖ) (x : (N.level n).val.obj V),
            ((U0.obj N).map (homOfLE h).op).val.app V
                ((eqToHom (uObj N n).symm).val.app V x) =
              (eqToHom (uObj N m).symm).val.app V ((N.transition h).val.app V x)) ∧
          (∀ (N : StrictRingSystem B) (n : ℕ),
            (uEval n).hom.app N = eqToHom (uObj N n)) ∧
          (∀ (N : StrictRingSystem B) (n : ℕ), (πOrd n).app N = π N n) ∧
          (∀ (N : StrictRingSystem B) (n : ℕ),
            fLim.hom.app N ≫ limit.π (U0.obj N) (op n) ≫ (uEval n).hom.app N = π N n) ∧
          RL.IsRightDerivedFunctor etaLim
            (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ Modules A) (.up ℤ)) ∧
          (∀ (T : CochainComplex (ℕᵒᵖ ⥤ Modules A) ℤ), T.IsKInjective →
            IsIso (etaLim.app T)) ∧
          (∀ (T : CochainComplex (ℕᵒᵖ ⥤ Modules A) ℤ) (n : ℕ),
            etaLim.app T ≫ (piLim n).app (DerivedCategory.Q.obj T) ≫
                ((CategoryTheory.evaluation ℕᵒᵖ (Modules A)).obj
                  (op n)).mapDerivedCategoryFactors.hom.app T =
              DerivedCategory.Q.map
                ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app T)) ∧
          (∀ (I : CochainComplex (StrictRingSystem B) ℤ) (n : ℕ),
            (xi n).hom.app (DerivedCategory.Q.obj I) ≫
                (restriction A B α n).mapDerivedCategory.map
                  ((systemEvaluation B n).mapDerivedCategoryFactors.hom.app I) ≫
                (restriction A B α n).mapDerivedCategoryFactors.hom.app
                  (((systemEvaluation B n).mapHomologicalComplex (.up ℤ)).obj I) =
              ((CategoryTheory.evaluation ℕᵒᵖ (Modules A)).obj (op n)).mapDerivedCategory.map
                  (U0.mapDerivedCategoryFactors.hom.app I) ≫
                ((CategoryTheory.evaluation ℕᵒᵖ (Modules A)).obj
                  (op n)).mapDerivedCategoryFactors.hom.app
                  ((U0.mapHomologicalComplex (.up ℤ)).obj I) ≫
                DerivedCategory.Q.map
                  ((NatIso.mapHomologicalComplex (uEval n) (.up ℤ)).hom.app I)) ∧
          (∀ (I : CochainComplex (StrictRingSystem B) ℤ), I.IsKInjective →
            ∀ (T : CochainComplex (ℕᵒᵖ ⥤ Modules A) ℤ), T.IsKInjective →
            ∀ (j : (U0.mapHomologicalComplex (.up ℤ)).obj I ⟶ T) [QuasiIso j],
            QuasiIso (((lim : (ℕᵒᵖ ⥤ Modules A) ⥤ Modules A).mapHomologicalComplex
              (.up ℤ)).map j) ∧
            η.app I ≫ c.hom.app (DerivedCategory.Q.obj I) ≫
                RL.map (U0.mapDerivedCategoryFactors.hom.app I) =
              DerivedCategory.Q.map ((NatIso.mapHomologicalComplex fLim (.up ℤ)).hom.app I) ≫
                DerivedCategory.Q.map
                  (((lim : (ℕᵒᵖ ⥤ Modules A) ⥤ Modules A).mapHomologicalComplex
                    (.up ℤ)).map j) ≫
                etaLim.app T ≫ RL.map (inv (DerivedCategory.Q.map j))) ∧
          (∀ (I : CochainComplex (StrictRingSystem B) ℤ) (n : ℕ),
            η.app I ≫ c.hom.app (DerivedCategory.Q.obj I) ≫
                (piLim n).app (U0.mapDerivedCategory.obj (DerivedCategory.Q.obj I)) ≫
                (xi n).hom.app (DerivedCategory.Q.obj I) ≫
                (restriction A B α n).mapDerivedCategory.map
                  ((systemEvaluation B n).mapDerivedCategoryFactors.hom.app I) ≫
                (restriction A B α n).mapDerivedCategoryFactors.hom.app
                  (((systemEvaluation B n).mapHomologicalComplex (.up ℤ)).obj I) =
              DerivedCategory.Q.map
                ((NatTrans.mapHomologicalComplex (πOrd n) (.up ℤ)).app I)) ∧
          (∀ (n : ℕ) (M : Modules A) (K : systemLevel B n)
            (h : M ⟶ (restriction A B α n).obj K) (V : Cᵒᵖ)
            (b : (B.obj (op n)).obj.obj V) (x : M.val.obj V),
            (((levelAdj n).homEquiv M K).symm h).val.app V
                ((e M n).inv.val.app V (tensorSection (α.app (op n)) M V b x)) =
              @SMul.smul ((B.obj (op n)).obj.obj V) (K.val.obj V) inferInstance b
                (h.val.app V x)) ∧
          (∀ (n : ℕ) (Q : CochainComplex (Modules A) ℤ)
            (K : CochainComplex (systemLevel B n) ℤ)
            (f : ((G ⋙ systemEvaluation B n).mapHomologicalComplex (.up ℤ)).obj Q ⟶ K),
            (derivedLevelAdj n).homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj K)
                ((systemEvaluation B n).mapDerivedCategory.map (ε.app Q) ≫
                  (systemEvaluation B n).mapDerivedCategoryFactors.hom.app
                    ((G.mapHomologicalComplex (.up ℤ)).obj Q) ≫ DerivedCategory.Q.map f) =
              DerivedCategory.Q.map
                  (((levelAdj n).mapHomologicalComplex (.up ℤ)).homEquiv Q K f) ≫
                (restriction A B α n).mapDerivedCategoryFactors.inv.app K) ∧
          (∀ (P : DerivedCategory.{d} (Modules A)) (n : ℕ),
            (derivedAdj.ofNatIsoRight c).unit.app P ≫
                (piLim n).app (U0.mapDerivedCategory.obj (L.obj P)) ≫
                (xi n).hom.app (L.obj P) = (derivedLevelAdj n).unit.app P) ∧
          (∀ (N : DerivedCategory.{d} (StrictRingSystem B)) (n : ℕ),
            (systemEvaluation B n).mapDerivedCategory.map
                ((derivedAdj.ofNatIsoRight c).counit.app N) =
              ((derivedLevelAdj n).homEquiv
                ((U0.mapDerivedCategory ⋙ RL).obj N)
                ((systemEvaluation B n).mapDerivedCategory.obj N)).symm
                  ((piLim n).app (U0.mapDerivedCategory.obj N) ≫ (xi n).hom.app N)) ∧
          (∀ (P : DerivedCategory.{d} (Modules A))
            (N : DerivedCategory.{d} (StrictRingSystem B))
            (h : P ⟶ (U0.mapDerivedCategory ⋙ RL).obj N) (n : ℕ),
            (systemEvaluation B n).mapDerivedCategory.map
                (((derivedAdj.ofNatIsoRight c).homEquiv P N).symm h) =
              (L ⋙ (systemEvaluation B n).mapDerivedCategory).map h ≫
                (systemEvaluation B n).mapDerivedCategory.map
                  ((derivedAdj.ofNatIsoRight c).counit.app N)) ∧
          (∀ (P : DerivedCategory.{d} (Modules A)),
            L.map ((derivedAdj.ofNatIsoRight c).unit.app P) ≫
              (derivedAdj.ofNatIsoRight c).counit.app (L.obj P) = 𝟙 (L.obj P)) ∧
          (∀ (N : DerivedCategory.{d} (StrictRingSystem B)),
            (derivedAdj.ofNatIsoRight c).unit.app ((U0.mapDerivedCategory ⋙ RL).obj N) ≫
              (U0.mapDerivedCategory ⋙ RL).map ((derivedAdj.ofNatIsoRight c).counit.app N) =
                𝟙 ((U0.mapDerivedCategory ⋙ RL).obj N)) ∧
          ∃ (beta : (Functor.const ℕᵒᵖ : Modules A ⥤ ℕᵒᵖ ⥤ Modules A) ⟶ G ⋙ U0)
            (towerAdj :
              (Functor.const ℕᵒᵖ : Modules A ⥤ ℕᵒᵖ ⥤ Modules A).mapDerivedCategory ⊣ RL)
            (augmentation :
              (Functor.const ℕᵒᵖ : Modules A ⥤ ℕᵒᵖ ⥤ Modules A).mapDerivedCategory ⟶
                L ⋙ U0.mapDerivedCategory),
            (∀ (M : Modules A) (n : ℕ) (V : Cᵒᵖ) (x : M.val.obj V),
              (eqToHom (uObj (G.obj M) n)).val.app V
                  (((beta.app M).app (op n)).val.app V x) =
                (e M n).inv.val.app V (tensorSection (α.app (op n)) M V 1 x)) ∧
            (∀ Q : CochainComplex (Modules A) ℤ,
              towerAdj.unit.app (DerivedCategory.Q.obj Q) ≫
                  RL.map ((Functor.const ℕᵒᵖ :
                    Modules A ⥤ ℕᵒᵖ ⥤ Modules A).mapDerivedCategoryFactors.hom.app Q) =
                DerivedCategory.Q.map
                    (((constLimAdj :
                      (Functor.const ℕᵒᵖ :
                        Modules A ⥤ ℕᵒᵖ ⥤ Modules A) ⊣
                          lim).mapHomologicalComplex (.up ℤ)).unit.app Q) ≫
                  etaLim.app (((Functor.const ℕᵒᵖ :
                    Modules A ⥤ ℕᵒᵖ ⥤ Modules A).mapHomologicalComplex (.up ℤ)).obj Q)) ∧
            (∀ (P : DerivedCategory.{d} (Modules A)),
              (derivedAdj.ofNatIsoRight c).unit.app P =
                towerAdj.unit.app P ≫ RL.map (augmentation.app P)) ∧
            (∀ (Q : CochainComplex (Modules A) ℤ),
              Q.IsKFlatIndependentCoefficients → (∀ i : ℤ, (Q.X i).IsFlatOnSite) →
              (augmentation.app (DerivedCategory.Q.obj Q) ≫
                  U0.mapDerivedCategory.map (ε.app Q) ≫
                  U0.mapDerivedCategoryFactors.hom.app
                    ((G.mapHomologicalComplex (.up ℤ)).obj Q) =
                (Functor.const ℕᵒᵖ :
                  Modules A ⥤ ℕᵒᵖ ⥤ Modules A).mapDerivedCategoryFactors.hom.app Q ≫
                  DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex beta (.up ℤ)).app Q)) ∧
              ((derivedAdj.ofNatIsoRight c).unit.app (DerivedCategory.Q.obj Q) ≫
                  RL.map (U0.mapDerivedCategory.map (ε.app Q) ≫
                    U0.mapDerivedCategoryFactors.hom.app
                      ((G.mapHomologicalComplex (.up ℤ)).obj Q)) =
                DerivedCategory.Q.map
                    (((constLimAdj :
                      (Functor.const ℕᵒᵖ :
                        Modules A ⥤ ℕᵒᵖ ⥤ Modules A) ⊣
                          lim).mapHomologicalComplex (.up ℤ)).homEquiv Q
                      ((U0.mapHomologicalComplex (.up ℤ)).obj
                        ((G.mapHomologicalComplex (.up ℤ)).obj Q))
                      ((NatTrans.mapHomologicalComplex beta (.up ℤ)).app Q)) ≫
                  etaLim.app ((U0.mapHomologicalComplex (.up ℤ)).obj
                    ((G.mapHomologicalComplex (.up ℤ)).obj Q))))
```

## New

```lean
def augmentedDerivedLimitProperties
    {D E T : Type*} {K : ℕ → Type*}
    [Category D] [Category E] [Category T] [∀ n, Category (K n)]
    [Abelian D] [Abelian E] [Abelian T] [∀ n, Abelian (K n)]
    [HasDerivedCategory.{d} D] [HasDerivedCategory.{d} E] [HasDerivedCategory.{d} T]
    [∀ n : ℕ, HasDerivedCategory.{d} (K n)]
    (G : D ⥤ E) (F : E ⥤ D) [G.Additive] [F.Additive]
    (U0 : E ⥤ T) (H : T ⥤ D) [U0.Additive] [H.PreservesZeroMorphisms]
    [PreservesFiniteLimits U0] [PreservesFiniteColimits U0]
    (W : ℕ → (T ⥤ D)) (V : ∀ n, E ⥤ K n) (S : ∀ n, K n ⥤ D)
    [∀ n, (W n).Additive] [∀ n, (V n).Additive] [∀ n, (S n).Additive]
    [∀ n, PreservesFiniteLimits (W n)] [∀ n, PreservesFiniteColimits (W n)]
    [∀ n, PreservesFiniteLimits (V n)] [∀ n, PreservesFiniteColimits (V n)]
    [∀ n, PreservesFiniteLimits (S n)] [∀ n, PreservesFiniteColimits (S n)]
    (uEval : ∀ n, U0 ⋙ W n ≅ V n ⋙ S n)
    (πOrd : ∀ n, F ⟶ V n ⋙ S n) (fLim : F ≅ U0 ⋙ H) (pOrd : ∀ n, H ⟶ W n)
    (L : DerivedCategory.{d} D ⥤ DerivedCategory.{d} E)
    (R : DerivedCategory.{d} E ⥤ DerivedCategory.{d} D)
    (ε : DerivedCategory.Q ⋙ L ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
    (dAdj : L ⊣ R)
    (RL : DerivedCategory.{d} T ⥤ DerivedCategory.{d} D)
    (etaLim : H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RL)
    (LevelProperty : (∀ n, G ⋙ V n ⊣ S n) → Prop)
    (piLim : ∀ n, RL ⟶ (W n).mapDerivedCategory)
      (xi : ∀ n, U0.mapDerivedCategory ⋙ (W n).mapDerivedCategory ≅
        (V n).mapDerivedCategory ⋙ (S n).mapDerivedCategory)
      (c : R ≅ U0.mapDerivedCategory ⋙ RL)
      (levelAdj : ∀ n, G ⋙ V n ⊣ S n)
      (derivedLevelAdj : ∀ n,
        L ⋙ (V n).mapDerivedCategory ⊣ (S n).mapDerivedCategory)
    (Extra : Prop) : Prop :=
    (∀ (T : CochainComplex T ℤ) (n : ℕ),
      etaLim.app T ≫ (piLim n).app (DerivedCategory.Q.obj T) ≫
          (W n).mapDerivedCategoryFactors.hom.app T =
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (pOrd n) (.up ℤ)).app T)) ∧
    (∀ (I : CochainComplex E ℤ) (n : ℕ),
      (xi n).hom.app (DerivedCategory.Q.obj I) ≫
          (S n).mapDerivedCategory.map
            ((V n).mapDerivedCategoryFactors.hom.app I) ≫
          (S n).mapDerivedCategoryFactors.hom.app
            (((V n).mapHomologicalComplex (.up ℤ)).obj I) =
        (W n).mapDerivedCategory.map
            (U0.mapDerivedCategoryFactors.hom.app I) ≫
          (W n).mapDerivedCategoryFactors.hom.app
            ((U0.mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (uEval n) (.up ℤ)).hom.app I)) ∧
    (∀ (I : CochainComplex E ℤ), I.IsKInjective →
      ∀ (T : CochainComplex T ℤ), T.IsKInjective →
      ∀ (j : (U0.mapHomologicalComplex (.up ℤ)).obj I ⟶ T) [QuasiIso j],
      QuasiIso ((H.mapHomologicalComplex
        (.up ℤ)).map j) ∧
      η.app I ≫ c.hom.app (DerivedCategory.Q.obj I) ≫
          RL.map (U0.mapDerivedCategoryFactors.hom.app I) =
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex fLim (.up ℤ)).hom.app I) ≫
          DerivedCategory.Q.map
            ((H.mapHomologicalComplex
              (.up ℤ)).map j) ≫
          etaLim.app T ≫ RL.map (inv (DerivedCategory.Q.map j))) ∧
    (∀ (I : CochainComplex E ℤ) (n : ℕ),
      η.app I ≫ c.hom.app (DerivedCategory.Q.obj I) ≫
          (piLim n).app (U0.mapDerivedCategory.obj (DerivedCategory.Q.obj I)) ≫
          (xi n).hom.app (DerivedCategory.Q.obj I) ≫
          (S n).mapDerivedCategory.map
            ((V n).mapDerivedCategoryFactors.hom.app I) ≫
          (S n).mapDerivedCategoryFactors.hom.app
            (((V n).mapHomologicalComplex (.up ℤ)).obj I) =
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (πOrd n) (.up ℤ)).app I)) ∧
    LevelProperty levelAdj ∧
    (∀ (n : ℕ) (Q : CochainComplex D ℤ)
      (K : CochainComplex (K n) ℤ)
      (f : ((G ⋙ V n).mapHomologicalComplex (.up ℤ)).obj Q ⟶ K),
      (derivedLevelAdj n).homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj K)
          ((V n).mapDerivedCategory.map (ε.app Q) ≫
            (V n).mapDerivedCategoryFactors.hom.app
              ((G.mapHomologicalComplex (.up ℤ)).obj Q) ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map
            (((levelAdj n).mapHomologicalComplex (.up ℤ)).homEquiv Q K f) ≫
          (S n).mapDerivedCategoryFactors.inv.app K) ∧
    (∀ (P : DerivedCategory.{d} D) (n : ℕ),
      (dAdj.ofNatIsoRight c).unit.app P ≫
          (piLim n).app (U0.mapDerivedCategory.obj (L.obj P)) ≫
          (xi n).hom.app (L.obj P) = (derivedLevelAdj n).unit.app P) ∧
    (∀ (N : DerivedCategory.{d} E) (n : ℕ),
      (V n).mapDerivedCategory.map
          ((dAdj.ofNatIsoRight c).counit.app N) =
        ((derivedLevelAdj n).homEquiv
          ((U0.mapDerivedCategory ⋙ RL).obj N)
          ((V n).mapDerivedCategory.obj N)).symm
            ((piLim n).app (U0.mapDerivedCategory.obj N) ≫ (xi n).hom.app N)) ∧
    (∀ (P : DerivedCategory.{d} D)
      (N : DerivedCategory.{d} E)
      (h : P ⟶ (U0.mapDerivedCategory ⋙ RL).obj N) (n : ℕ),
      (V n).mapDerivedCategory.map
          (((dAdj.ofNatIsoRight c).homEquiv P N).symm h) =
        (L ⋙ (V n).mapDerivedCategory).map h ≫
          (V n).mapDerivedCategory.map
            ((dAdj.ofNatIsoRight c).counit.app N)) ∧
    (∀ (P : DerivedCategory.{d} D),
      L.map ((dAdj.ofNatIsoRight c).unit.app P) ≫
        (dAdj.ofNatIsoRight c).counit.app (L.obj P) = 𝟙 (L.obj P)) ∧
    (∀ (N : DerivedCategory.{d} E),
      (dAdj.ofNatIsoRight c).unit.app ((U0.mapDerivedCategory ⋙ RL).obj N) ≫
        (U0.mapDerivedCategory ⋙ RL).map ((dAdj.ofNatIsoRight c).counit.app N) =
          𝟙 ((U0.mapDerivedCategory ⋙ RL).obj N)) ∧ Extra

theorem sequenceTensorAugmentationUnit
    (A : Sheaf J CommRingCat.{w}) (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B)
    [HasDerivedCategory.{d} (Modules A)] [HasDerivedCategory.{d} (StrictRingSystem B)]
    [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ Modules A)]
    [∀ n : ℕ, HasDerivedCategory.{d} (systemLevel B n)] :
    ∃ (G : Modules A ⥤ StrictRingSystem B) (F : StrictRingSystem B ⥤ Modules A)
      (_ : G.Additive) (_ : F.Additive)
      (e : ∀ (M : Modules A) (n : ℕ),
        (G.obj M).level n ≅ changeOfRings (α.app (op n)) M)
      (π : ∀ (N : StrictRingSystem B) (n : ℕ),
        F.obj N ⟶ (restriction A B α n).obj (N.level n))
      (adj : G ⊣ F),
      (∀ {M M' : Modules A} (f : M ⟶ M') (n : ℕ),
        (G.map f).app n ≫ (e M' n).hom =
          (e M n).hom ≫ changeOfRingsHom (α.app (op n)) M f) ∧
      (∀ (M : Modules A) {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ)
        (b : (B.obj (op n)).obj.obj U) (x : M.val.obj U),
        ((G.obj M).transition h).val.app U
            ((e M n).inv.val.app U (tensorSection (α.app (op n)) M U b x)) =
          (e M m).inv.val.app U (tensorSection (α.app (op m)) M U
            ((B.map (homOfLE h).op).hom.app U b) x)) ∧
      (∀ {N N' : StrictRingSystem B} (f : N ⟶ N') (n : ℕ),
        F.map f ≫ π N' n = π N n ≫ (restriction A B α n).map (f.app n)) ∧
      (∀ (N : StrictRingSystem B) {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ)
        (x : (F.obj N).val.obj U),
        (π N m).val.app U x =
          (N.transition h).val.app U ((π N n).val.app U x)) ∧
      (∀ (M : Modules A) (N : StrictRingSystem B)
        (f : ∀ n : ℕ, M ⟶ (restriction A B α n).obj (N.level n)),
        (∀ {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ) (x : M.val.obj U),
          (f m).val.app U x = (N.transition h).val.app U ((f n).val.app U x)) →
        ∃! h : M ⟶ F.obj N, ∀ n : ℕ, h ≫ π N n = f n) ∧
      (∀ (M : Modules A) (N : StrictRingSystem B) (h : M ⟶ F.obj N)
        (n : ℕ) (U : Cᵒᵖ) (b : (B.obj (op n)).obj.obj U) (x : M.val.obj U),
        (((adj.homEquiv M N).symm h).app n).val.app U
            ((e M n).inv.val.app U (tensorSection (α.app (op n)) M U b x)) =
          @SMul.smul ((B.obj (op n)).obj.obj U) ((N.level n).val.obj U) inferInstance b
            ((π N n).val.app U (h.val.app U x))) ∧
      ∃ (L : DerivedCategory.{d} (Modules A) ⥤ DerivedCategory.{d} (StrictRingSystem B))
        (R : DerivedCategory.{d} (StrictRingSystem B) ⥤ DerivedCategory.{d} (Modules A))
        (ε : DerivedCategory.Q ⋙ L ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
        (η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
        (derivedAdj : L ⊣ R),
        L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso (Modules A) (.up ℤ)) ∧
        R.IsRightDerivedFunctor η
          (HomologicalComplex.quasiIso (StrictRingSystem B) (.up ℤ)) ∧
        (∀ (Q : CochainComplex (Modules A) ℤ), Q.IsKFlatIndependentCoefficients →
          (∀ i : ℤ, (Q.X i).IsFlatOnSite) → IsIso (ε.app Q)) ∧
        (∀ (I : CochainComplex (StrictRingSystem B) ℤ), I.IsKInjective →
          IsIso (η.app I)) ∧
        (∀ (P Q : CochainComplex (Modules A) ℤ) (q : Q ⟶ P),
          Q.IsKFlatIndependentCoefficients → (∀ i : ℤ, (Q.X i).IsFlatOnSite) →
          QuasiIso q →
          ∃ c : L.obj (DerivedCategory.Q.obj P) ≅
            DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj Q),
            L.map (DerivedCategory.Q.map q) ≫ c.hom = ε.app Q) ∧
        (∀ (Q : CochainComplex (Modules A) ℤ)
          (I : CochainComplex (StrictRingSystem B) ℤ)
          (f : (G.mapHomologicalComplex (.up ℤ)).obj Q ⟶ I),
          derivedAdj.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
              (ε.app Q ≫ DerivedCategory.Q.map f) =
            DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv Q I f) ≫
              η.app I) ∧
        ∃ (U0 : StrictRingSystem B ⥤ (ℕᵒᵖ ⥤ Modules A))
          (_ : U0.Additive) (_ : PreservesFiniteLimits U0)
          (_ : PreservesFiniteColimits U0)
          (uObj : ∀ (N : StrictRingSystem B) (n : ℕ),
            (U0.obj N).obj (op n) = (restriction A B α n).obj (N.level n))
          (uEval : ∀ n : ℕ,
            U0 ⋙ (CategoryTheory.evaluation ℕᵒᵖ (Modules A)).obj (op n) ≅
              systemEvaluation B n ⋙ restriction A B α n)
          (πOrd : ∀ n : ℕ, F ⟶ systemEvaluation B n ⋙ restriction A B α n)
          (fLim : F ≅ U0 ⋙ (lim : (ℕᵒᵖ ⥤ Modules A) ⥤ Modules A))
          (RL : DerivedCategory.{d} (ℕᵒᵖ ⥤ Modules A) ⥤ DerivedCategory.{d} (Modules A))
          (etaLim : (lim : (ℕᵒᵖ ⥤ Modules A) ⥤ Modules A).mapHomologicalComplex (.up ℤ) ⋙
            DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RL)
          (piLim : ∀ n : ℕ, RL ⟶
            ((CategoryTheory.evaluation ℕᵒᵖ (Modules A)).obj (op n)).mapDerivedCategory)
          (xi : ∀ n : ℕ,
            U0.mapDerivedCategory ⋙
                ((CategoryTheory.evaluation ℕᵒᵖ (Modules A)).obj (op n)).mapDerivedCategory ≅
              (systemEvaluation B n).mapDerivedCategory ⋙
                (restriction A B α n).mapDerivedCategory)
          (c : R ≅ U0.mapDerivedCategory ⋙ RL)
          (levelAdj : ∀ n : ℕ, G ⋙ systemEvaluation B n ⊣ restriction A B α n)
          (derivedLevelAdj : ∀ n : ℕ,
            L ⋙ (systemEvaluation B n).mapDerivedCategory ⊣
              (restriction A B α n).mapDerivedCategory),
          (∀ {N N' : StrictRingSystem B} (f : N ⟶ N') (n : ℕ),
            (U0.map f).app (op n) ≫ eqToHom (uObj N' n) =
              eqToHom (uObj N n) ≫ (restriction A B α n).map (f.app n)) ∧
          (∀ (N : StrictRingSystem B) {m n : ℕ} (h : m ≤ n)
            (V : Cᵒᵖ) (x : (N.level n).val.obj V),
            ((U0.obj N).map (homOfLE h).op).val.app V
                ((eqToHom (uObj N n).symm).val.app V x) =
              (eqToHom (uObj N m).symm).val.app V ((N.transition h).val.app V x)) ∧
          (∀ (N : StrictRingSystem B) (n : ℕ),
            (uEval n).hom.app N = eqToHom (uObj N n)) ∧
          (∀ (N : StrictRingSystem B) (n : ℕ), (πOrd n).app N = π N n) ∧
          (∀ (N : StrictRingSystem B) (n : ℕ),
            fLim.hom.app N ≫ limit.π (U0.obj N) (op n) ≫ (uEval n).hom.app N = π N n) ∧
          RL.IsRightDerivedFunctor etaLim
            (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ Modules A) (.up ℤ)) ∧
          (∀ (T : CochainComplex (ℕᵒᵖ ⥤ Modules A) ℤ), T.IsKInjective →
            IsIso (etaLim.app T)) ∧
          augmentedDerivedLimitProperties G F U0 (lim : (ℕᵒᵖ ⥤ Modules A) ⥤ Modules A)
            (fun n ↦ (CategoryTheory.evaluation ℕᵒᵖ (Modules A)).obj (op n))
            (systemEvaluation B) (restriction A B α) uEval πOrd fLim
            (fun n ↦ lim.π (op n)) L R ε η derivedAdj RL etaLim
            (fun levelAdj ↦ ∀ (n : ℕ) (M : Modules A) (K : systemLevel B n)
            (h : M ⟶ (restriction A B α n).obj K) (V : Cᵒᵖ)
            (b : (B.obj (op n)).obj.obj V) (x : M.val.obj V),
            (((levelAdj n).homEquiv M K).symm h).val.app V
                ((e M n).inv.val.app V (tensorSection (α.app (op n)) M V b x)) =
              @SMul.smul ((B.obj (op n)).obj.obj V) (K.val.obj V)
                (by
                  set_option backward.isDefEq.respectTransparency.types false in
                    exact inferInstance) b
                (h.val.app V x))
            piLim xi c levelAdj derivedLevelAdj
          (∃ (beta : (Functor.const ℕᵒᵖ : Modules A ⥤ ℕᵒᵖ ⥤ Modules A) ⟶ G ⋙ U0)
            (towerAdj :
              (Functor.const ℕᵒᵖ : Modules A ⥤ ℕᵒᵖ ⥤ Modules A).mapDerivedCategory ⊣ RL)
            (augmentation :
              (Functor.const ℕᵒᵖ : Modules A ⥤ ℕᵒᵖ ⥤ Modules A).mapDerivedCategory ⟶
                L ⋙ U0.mapDerivedCategory),
            (∀ (M : Modules A) (n : ℕ) (V : Cᵒᵖ) (x : M.val.obj V),
              (eqToHom (uObj (G.obj M) n)).val.app V
                  (((beta.app M).app (op n)).val.app V x) =
                (e M n).inv.val.app V (tensorSection (α.app (op n)) M V 1 x)) ∧
            (∀ Q : CochainComplex (Modules A) ℤ,
              towerAdj.unit.app (DerivedCategory.Q.obj Q) ≫
                  RL.map ((Functor.const ℕᵒᵖ :
                    Modules A ⥤ ℕᵒᵖ ⥤ Modules A).mapDerivedCategoryFactors.hom.app Q) =
                DerivedCategory.Q.map
                    (((constLimAdj :
                      (Functor.const ℕᵒᵖ :
                        Modules A ⥤ ℕᵒᵖ ⥤ Modules A) ⊣
                          lim).mapHomologicalComplex (.up ℤ)).unit.app Q) ≫
                  etaLim.app (((Functor.const ℕᵒᵖ :
                    Modules A ⥤ ℕᵒᵖ ⥤ Modules A).mapHomologicalComplex (.up ℤ)).obj Q)) ∧
            (∀ (P : DerivedCategory.{d} (Modules A)),
              (derivedAdj.ofNatIsoRight c).unit.app P =
                towerAdj.unit.app P ≫ RL.map (augmentation.app P)) ∧
            (∀ (Q : CochainComplex (Modules A) ℤ),
              Q.IsKFlatIndependentCoefficients → (∀ i : ℤ, (Q.X i).IsFlatOnSite) →
              (augmentation.app (DerivedCategory.Q.obj Q) ≫
                  U0.mapDerivedCategory.map (ε.app Q) ≫
                  U0.mapDerivedCategoryFactors.hom.app
                    ((G.mapHomologicalComplex (.up ℤ)).obj Q) =
                (Functor.const ℕᵒᵖ :
                  Modules A ⥤ ℕᵒᵖ ⥤ Modules A).mapDerivedCategoryFactors.hom.app Q ≫
                  DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex beta (.up ℤ)).app Q)) ∧
              ((derivedAdj.ofNatIsoRight c).unit.app (DerivedCategory.Q.obj Q) ≫
                  RL.map (U0.mapDerivedCategory.map (ε.app Q) ≫
                    U0.mapDerivedCategoryFactors.hom.app
                      ((G.mapHomologicalComplex (.up ℤ)).obj Q)) =
                DerivedCategory.Q.map
                    (((constLimAdj :
                      (Functor.const ℕᵒᵖ :
                        Modules A ⥤ ℕᵒᵖ ⥤ Modules A) ⊣
                          lim).mapHomologicalComplex (.up ℤ)).homEquiv Q
                      ((U0.mapHomologicalComplex (.up ℤ)).obj
                        ((G.mapHomologicalComplex (.up ℤ)).obj Q))
                      ((NatTrans.mapHomologicalComplex beta (.up ℤ)).app Q)) ≫
                  etaLim.app ((U0.mapHomologicalComplex (.up ℤ)).obj
                    ((G.mapHomologicalComplex (.up ℤ)).obj Q)))))
```

## Users

`python3 tools/downstream.py Sheaf.CategoryTheory.SequenceTensorAugmentationUnit
--uses sequenceTensorAugmentationUnit` reports zero downstream modules and only
the declaration's own module as a textual use. A direct import search also finds
no importers. DAG parents with unfinished proofs retain exactly the same
mathematical statement; unfolding the predicate recovers all original clauses.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.SequenceTensorAugmentationUnit | A6 | Definitionally equal statement factorization; complete proof supplied. |

A temporary client with the full original signature proves it by direct application
of the factored theorem, with no conversion lemma or extra hypothesis. It compiles
in 20.3 s and depends only on `propext`, `Classical.choice` and `Quot.sound`.
The clean item compiles in 46.4 s. The temporary client is not part of the delivery.

## Status

landed 20261026T222545-L-667952 2026-10-26 (merge of deliver/A6/Sheaf.CategoryTheory.SequenceTensorAugmentationUnit)
