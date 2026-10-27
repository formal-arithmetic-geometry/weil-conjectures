# SheafOfModules.LocalizedStrictTensor.DerivedNormalized

## Reason

Factor the identical representative descent and evaluation equations and exact-square localization
construction into shared definitions. Applying generic counit descent and evaluation
pasting to the old expanded scalar normalization caused expensive definitional
comparison, reaching the single-file compilation limit. Named equations preserve
the exact formulas while keeping the comparison at their parameters. The exact
square constructor is irreducible after its concrete construction; its normalization
is proved by explicitly unfolding it in the private proof API.

No mathematical hypothesis, equation, universe, existing declaration signature,
or target text changes. In particular, the scalar normalization still quantifies
over every flat-term K-flat representative and uses the same chain map. These
definitions occur under target dependencies, so their meaning is open to statement
review again; the old and new formulas agree by unfolding the shared definitions.

The coefficient family now states `obj S := reduction R S` explicitly. Its maps,
identity and composition laws are the previous composed functor's maps and laws.
This is definitionally the same functor after unfolding; it prevents comparisons
of its objects from expanding the tensor construction repeatedly.

## Old

```lean
def reductionFamily : AlgebraTowers.{c, v, r} R ⥤
    Modules.{c, v, r} R ⥤ (ℕᵒᵖ ⥤ Modules.{c, v, r} R) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (algebraModules.{c, v, r} R) ⋙
    (curriedTensor (ℕᵒᵖ ⥤ Modules.{c, v, r} R)).flip ⋙
      (Functor.whiskeringLeft (Modules.{c, v, r} R)
        (ℕᵒᵖ ⥤ Modules.{c, v, r} R) (ℕᵒᵖ ⥤ Modules.{c, v, r} R)).obj
          (Functor.const ℕᵒᵖ)
```

```lean
def DerivedNormalized
    (m : ReductionModel.{c, v, r} R)
    (mV : ReductionModel.{max c v, v, r} (R.over V))
    (S : AlgebraTowers.{c, v, r} R)
    (η : localizedSystemExtension.{c, v, r} R V ⋙ reduction.{c, v, r} R S ≅
      reduction.{max c v, v, r} (R.over V) (S ⋙ sliceAlgebras.{c, v, r} R V) ⋙
        towerExtension.{c, v, r} R V)
    (ρ : (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory ⋙ m.F.obj S ≅
      mV.F.obj (S ⋙ sliceAlgebras.{c, v, r} R V) ⋙
        (towerExtension.{c, v, r} R V).mapDerivedCategory) : Prop :=
  ∀ (P : CochainComplex (Modules.{max c v, v, r} (R.over V)) ℤ),
    Resolving.{max c v, v, r} (R.over V) P →
      (m.F.obj S).map
        ((localizedSystemExtension.{c, v, r} R V).mapDerivedCategoryFactors.hom.app P) ≫
      (m.ε S).app
        (((localizedSystemExtension.{c, v, r} R V).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((comparisonOnComplexes.{c, v, r} R V S η).hom.app P) =
      ρ.hom.app (DerivedCategory.Q.obj P) ≫
      (towerExtension.{c, v, r} R V).mapDerivedCategory.map
        ((mV.ε (S ⋙ sliceAlgebras.{c, v, r} R V)).app P) ≫
      (towerExtension.{c, v, r} R V).mapDerivedCategoryFactors.hom.app
        (((reduction.{max c v, v, r} (R.over V)
          (S ⋙ sliceAlgebras.{c, v, r} R V)).mapHomologicalComplex (.up ℤ)).obj P)
```

```lean
structure EvaluationModel (m : ReductionModel.{c, v, r} R)
    (S : AlgebraTowers.{c, v, r} R) (n : ℕᵒᵖ) where
  /-- The existing, genuinely coefficient-linear derived extension. -/
  scalar : ScalarModel.{c, v, r} R (S.obj n)
  /-- The canonical ordinary identification of underlying tensor with scalar extension. -/
  ordinary : reduction.{c, v, r} R S ⋙ evaluation.{c, v, r} R n ≅
    scalar.E ⋙ scalars.{c, v, r} R (S.obj n)
  /-- Its pure-tensor formula fixes the ordinary comparison. -/
  ordinary_normalized : EvaluationOrdinaryNormalized.{c, v, r} R S n scalar ordinary
  /-- Evaluation after localization, identified with scalar restriction of extension. -/
  derived : m.F.obj S ⋙ (evaluation.{c, v, r} R n).mapDerivedCategory ≅
    scalar.T ⋙ (scalars.{c, v, r} R (S.obj n)).mapDerivedCategory
  /-- The identification uses the universal computation counits, not a chosen resolution. -/
  normalized : ∀ (P : CochainComplex (Modules.{c, v, r} R) ℤ),
    Resolving.{c, v, r} R P →
    (evaluation.{c, v, r} R n).mapDerivedCategory.map ((m.ε S).app P) ≫
      (evaluation.{c, v, r} R n).mapDerivedCategoryFactors.hom.app
        (((reduction.{c, v, r} R S).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P) =
    derived.hom.app (DerivedCategory.Q.obj P) ≫
      (scalars.{c, v, r} R (S.obj n)).mapDerivedCategory.map (scalar.ε.app P) ≫
      (scalars.{c, v, r} R (S.obj n)).mapDerivedCategoryFactors.hom.app
        ((scalar.E.mapHomologicalComplex (.up ℤ)).obj P)
```

```lean
def evaluationExtensionDerived (n : ℕᵒᵖ) :
    (towerExtension.{c, v, r} R V).mapDerivedCategory ⋙
      (evaluation.{c, v, r} R n).mapDerivedCategory ≅
    (evaluation.{max c v, v, r} (R.over V) n).mapDerivedCategory ⋙
      (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory :=
  letI := localizedSystemExtensionAdditive.{c, v, r} R V
  letI := localizedSystemExtensionLimits.{c, v, r} R V
  letI := localizedSystemExtensionColimits.{c, v, r} R V
  (Functor.mapDerivedCategoryCompIso (towerExtension.{c, v, r} R V)
    (evaluation.{c, v, r} R n)).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl) :
          towerExtension.{c, v, r} R V ⋙ evaluation.{c, v, r} R n ≅
            evaluation.{max c v, v, r} (R.over V) n ⋙
              localizedSystemExtension.{c, v, r} R V) ≪≫
        Functor.mapDerivedCategoryCompIso (evaluation.{max c v, v, r} (R.over V) n)
          (localizedSystemExtension.{c, v, r} R V)
```

```lean
def scalarExtensionDerived (A : Under R)
    (θ : scalars.{max c v, v, r} (R.over V) ((sliceAlgebras.{c, v, r} R V).obj A) ⋙
        localizedSystemExtension.{c, v, r} R V ≅
      localizedSystemExtension.{c, v, r} A.right V ⋙ scalars.{c, v, r} R A) :
    (scalars.{max c v, v, r} (R.over V)
      ((sliceAlgebras.{c, v, r} R V).obj A)).mapDerivedCategory ⋙
        (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory ≅
      (localizedSystemExtension.{c, v, r} A.right V).mapDerivedCategory ⋙
        (scalars.{c, v, r} R A).mapDerivedCategory :=
  letI := localizedSystemExtensionAdditive.{c, v, r} R V
  letI := localizedSystemExtensionLimits.{c, v, r} R V
  letI := localizedSystemExtensionColimits.{c, v, r} R V
  letI := localizedSystemExtensionAdditive.{c, v, r} A.right V
  letI := localizedSystemExtensionLimits.{c, v, r} A.right V
  letI := localizedSystemExtensionColimits.{c, v, r} A.right V
  (Functor.mapDerivedCategoryCompIso
    (scalars.{max c v, v, r} (R.over V) ((sliceAlgebras.{c, v, r} R V).obj A))
    (localizedSystemExtension.{c, v, r} R V)).symm ≪≫
      Functor.mapDerivedCategoryNatIso θ ≪≫
        Functor.mapDerivedCategoryCompIso (localizedSystemExtension.{c, v, r} A.right V)
          (scalars.{c, v, r} R A)
```

## New

```lean
def reductionFamily : AlgebraTowers.{c, v, r} R ⥤
    Modules.{c, v, r} R ⥤ (ℕᵒᵖ ⥤ Modules.{c, v, r} R) :=
  let F := (Functor.whiskeringRight ℕᵒᵖ _ _).obj (algebraModules.{c, v, r} R) ⋙
    (curriedTensor (ℕᵒᵖ ⥤ Modules.{c, v, r} R)).flip ⋙
      (Functor.whiskeringLeft (Modules.{c, v, r} R)
        (ℕᵒᵖ ⥤ Modules.{c, v, r} R) (ℕᵒᵖ ⥤ Modules.{c, v, r} R)).obj
          (Functor.const ℕᵒᵖ)
  { obj S := reduction.{c, v, r} R S
    map := F.map
    map_id := F.map_id
    map_comp := F.map_comp }
```

```lean
def ExactDescentEquation
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (N : C ⥤ D) [N.Additive] [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    (E : B ⥤ D) [E.Additive] (F : A ⥤ C) [F.Additive]
    (T : DerivedCategory B ⥤ DerivedCategory D)
    (U : DerivedCategory A ⥤ DerivedCategory C)
    (ε : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (δ : DerivedCategory.Q ⋙ U ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (η : L ⋙ E ≅ F ⋙ N)
    (ρ : L.mapDerivedCategory ⋙ T ≅ U ⋙ N.mapDerivedCategory)
    (P : CochainComplex A ℤ) : Prop :=
  T.map (L.mapDerivedCategoryFactors.hom.app P) ≫
    ε.app ((L.mapHomologicalComplex (.up ℤ)).obj P) ≫
    DerivedCategory.Q.map ((NatIso.mapHomologicalComplex η (.up ℤ)).hom.app P) =
  ρ.hom.app (DerivedCategory.Q.obj P) ≫ N.mapDerivedCategory.map (δ.app P) ≫
    N.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P)
```

```lean
def NormalizedExactDescent
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (N : C ⥤ D) [N.Additive] [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    (E : B ⥤ D) [E.Additive] (F : A ⥤ C) [F.Additive]
    (T : DerivedCategory B ⥤ DerivedCategory D)
    (U : DerivedCategory A ⥤ DerivedCategory C)
    (ε : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (δ : DerivedCategory.Q ⋙ U ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (good : CochainComplex A ℤ → Prop) (η : L ⋙ E ≅ F ⋙ N)
    (ρ : L.mapDerivedCategory ⋙ T ≅ U ⋙ N.mapDerivedCategory) : Prop :=
  ∀ P, good P → ExactDescentEquation L N E F T U ε δ η ρ P
```

```lean
def DerivedNormalized
    (m : ReductionModel.{c, v, r} R)
    (mV : ReductionModel.{max c v, v, r} (R.over V))
    (S : AlgebraTowers.{c, v, r} R)
    (η : localizedSystemExtension.{c, v, r} R V ⋙ reduction.{c, v, r} R S ≅
      reduction.{max c v, v, r} (R.over V) (S ⋙ sliceAlgebras.{c, v, r} R V) ⋙
        towerExtension.{c, v, r} R V)
    (ρ : (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory ⋙ m.F.obj S ≅
      mV.F.obj (S ⋙ sliceAlgebras.{c, v, r} R V) ⋙
        (towerExtension.{c, v, r} R V).mapDerivedCategory) : Prop :=
  letI := reduction_additive.{c, v, r} R S
  letI := reduction_additive.{max c v, v, r} (R.over V)
    (S ⋙ sliceAlgebras.{c, v, r} R V)
  letI := localizedSystemExtensionAdditive.{c, v, r} R V
  letI := localizedSystemExtensionLimits.{c, v, r} R V
  letI := localizedSystemExtensionColimits.{c, v, r} R V
  NormalizedExactDescent (localizedSystemExtension.{c, v, r} R V)
    (towerExtension.{c, v, r} R V) (reduction.{c, v, r} R S)
    (reduction.{max c v, v, r} (R.over V) (S ⋙ sliceAlgebras.{c, v, r} R V))
    (m.F.obj S) (mV.F.obj (S ⋙ sliceAlgebras.{c, v, r} R V))
    (m.ε S) (mV.ε _) (Resolving.{max c v, v, r} (R.over V)) η ρ
```

```lean
def EvaluatedDescentEquation
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (E : A ⥤ B) [E.Additive] (F : A ⥤ C) [F.Additive]
    (H : B ⥤ D) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (N : C ⥤ D) [N.Additive] [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    (T : DerivedCategory A ⥤ DerivedCategory B)
    (U : DerivedCategory A ⥤ DerivedCategory C)
    (ε : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (δ : DerivedCategory.Q ⋙ U ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (η : E ⋙ H ≅ F ⋙ N)
    (ρ : T ⋙ H.mapDerivedCategory ≅ U ⋙ N.mapDerivedCategory)
    (P : CochainComplex A ℤ) : Prop :=
  H.mapDerivedCategory.map (ε.app P) ≫
    H.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
    DerivedCategory.Q.map ((NatIso.mapHomologicalComplex η (.up ℤ)).hom.app P) =
  ρ.hom.app (DerivedCategory.Q.obj P) ≫ N.mapDerivedCategory.map (δ.app P) ≫
    N.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P)
```

```lean
structure EvaluationModel (m : ReductionModel.{c, v, r} R)
    (S : AlgebraTowers.{c, v, r} R) (n : ℕᵒᵖ) where
  /-- The existing, genuinely coefficient-linear derived extension. -/
  scalar : ScalarModel.{c, v, r} R (S.obj n)
  /-- The canonical ordinary identification of underlying tensor with scalar extension. -/
  ordinary : reduction.{c, v, r} R S ⋙ evaluation.{c, v, r} R n ≅
    scalar.E ⋙ scalars.{c, v, r} R (S.obj n)
  /-- Its pure-tensor formula fixes the ordinary comparison. -/
  ordinary_normalized : EvaluationOrdinaryNormalized.{c, v, r} R S n scalar ordinary
  /-- Evaluation after localization, identified with scalar restriction of extension. -/
  derived : m.F.obj S ⋙ (evaluation.{c, v, r} R n).mapDerivedCategory ≅
    scalar.T ⋙ (scalars.{c, v, r} R (S.obj n)).mapDerivedCategory
  /-- The identification uses the universal computation counits, not a chosen resolution. -/
  normalized : ∀ (P : CochainComplex (Modules.{c, v, r} R) ℤ),
    Resolving.{c, v, r} R P →
    EvaluatedDescentEquation (reduction.{c, v, r} R S) scalar.E
      (evaluation.{c, v, r} R n) (scalars.{c, v, r} R (S.obj n))
      (m.F.obj S) scalar.T (m.ε S) scalar.ε ordinary derived P
```

```lean
def exactDerivedSquare
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : B ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (H : A ⥤ C) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (I : C ⥤ D) [I.Additive] [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (η : F ⋙ G ≅ H ⋙ I) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      H.mapDerivedCategory ⋙ I.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso F G).symm ≪≫
    Functor.mapDerivedCategoryNatIso η ≪≫ Functor.mapDerivedCategoryCompIso H I
```

```lean
def evaluationExtensionDerived (n : ℕᵒᵖ) :
    (towerExtension.{c, v, r} R V).mapDerivedCategory ⋙
      (evaluation.{c, v, r} R n).mapDerivedCategory ≅
    (evaluation.{max c v, v, r} (R.over V) n).mapDerivedCategory ⋙
      (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory :=
  letI := localizedSystemExtensionAdditive.{c, v, r} R V
  letI := localizedSystemExtensionLimits.{c, v, r} R V
  letI := localizedSystemExtensionColimits.{c, v, r} R V
  exactDerivedSquare (towerExtension.{c, v, r} R V) (evaluation.{c, v, r} R n)
    (evaluation.{max c v, v, r} (R.over V) n) (localizedSystemExtension.{c, v, r} R V)
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl))
```

```lean
def scalarExtensionDerived (A : Under R)
    (θ : scalars.{max c v, v, r} (R.over V) ((sliceAlgebras.{c, v, r} R V).obj A) ⋙
        localizedSystemExtension.{c, v, r} R V ≅
      localizedSystemExtension.{c, v, r} A.right V ⋙ scalars.{c, v, r} R A) :
    (scalars.{max c v, v, r} (R.over V)
      ((sliceAlgebras.{c, v, r} R V).obj A)).mapDerivedCategory ⋙
        (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory ≅
      (localizedSystemExtension.{c, v, r} A.right V).mapDerivedCategory ⋙
        (scalars.{c, v, r} R A).mapDerivedCategory :=
  letI := localizedSystemExtensionAdditive.{c, v, r} R V
  letI := localizedSystemExtensionLimits.{c, v, r} R V
  letI := localizedSystemExtensionColimits.{c, v, r} R V
  letI := localizedSystemExtensionAdditive.{c, v, r} A.right V
  letI := localizedSystemExtensionLimits.{c, v, r} A.right V
  letI := localizedSystemExtensionColimits.{c, v, r} A.right V
  exactDerivedSquare
    (scalars.{max c v, v, r} (R.over V) ((sliceAlgebras.{c, v, r} R V).obj A))
    (localizedSystemExtension.{c, v, r} R V)
    (localizedSystemExtension.{c, v, r} A.right V) (scalars.{c, v, r} R A) θ
```

The local scalar-evaluation interface adaptation is recorded in
`U1-localized-strict-linear-normalization.md`. All data are concrete constructions;
no witness or proof hole is introduced.

The same evaluation square is shared by the linear evaluation record:

```lean
def DerivedEvaluationSquare
    {A B C D E F : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (N : C ⥤ D) [N.Additive] [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    (H : D ⥤ B) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (H' : C ⥤ A) [H'.Additive] [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
    (M : E ⥤ F) [M.Additive] [PreservesFiniteLimits M] [PreservesFiniteColimits M]
    (U : F ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (U' : E ⥤ A) [U'.Additive] [PreservesFiniteLimits U'] [PreservesFiniteColimits U']
    (T : DerivedCategory B ⥤ DerivedCategory D)
    (T' : DerivedCategory A ⥤ DerivedCategory C)
    (W : DerivedCategory B ⥤ DerivedCategory F)
    (W' : DerivedCategory A ⥤ DerivedCategory E)
    (κ : N ⋙ H ≅ H' ⋙ L) (θ : U' ⋙ L ≅ M ⋙ U)
    (ρ : L.mapDerivedCategory ⋙ T ≅ T' ⋙ N.mapDerivedCategory)
    (pd : T ⋙ H.mapDerivedCategory ≅ W ⋙ U.mapDerivedCategory)
    (qd : T' ⋙ H'.mapDerivedCategory ≅ W' ⋙ U'.mapDerivedCategory)
    (β : L.mapDerivedCategory ⋙ W ≅ W' ⋙ M.mapDerivedCategory) : Prop :=
  ∀ K : DerivedCategory A,
    H.mapDerivedCategory.map (ρ.hom.app K) ≫
      (exactDerivedSquare N H H' L κ).hom.app (T'.obj K) ≫
      L.mapDerivedCategory.map (qd.hom.app K) ≫
      (exactDerivedSquare U' L M U θ).hom.app (W'.obj K) =
    pd.hom.app (L.mapDerivedCategory.obj K) ≫
      U.mapDerivedCategory.map (β.hom.app K)
```

## Users

The table includes every downstream module printed by `tools/downstream.py`, and
all direct uses of each changed declaration. The `--uses` results are:
reductionFamily: Data, Descent, StrictTensorDerivedData, SliceTensorGeneratorCoherence;
DerivedNormalized: Data, Descent; EvaluationModel: Data, LinearEvaluation;
evaluationExtensionDerived: Data,
LinearEvaluation; scalarExtensionDerived: Data, LinearEvaluation,
CoefficientLinearProjectionDescent.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.CoefficientLinearProjectionDescent | unclaimed | No adaptation; signatures and meaning unchanged. |
| Sheaf.Algebra.Homology.LocalizedStrictTensorData | unclaimed | Definition refactor; compiled. |
| Sheaf.Algebra.Homology.LocalizedStrictTensorDescent | U1 | Proof supplied using shared equations. |
| Sheaf.Algebra.Homology.LocalizedStrictTensorLinearEvaluation | unclaimed | Equivalent normalization presentation; compiled. |
| Sheaf.Algebra.Homology.OpenTensorScalarUnitAugmentation | unclaimed | No adaptation; signatures and meaning unchanged. |
| Sheaf.Algebra.Homology.OpenTotalTensorCoefficientCoherence | unclaimed | No adaptation; signatures and meaning unchanged. |
| Sheaf.Algebra.Homology.OpenTotalTensorCoefficientData | unclaimed | No adaptation; signatures and meaning unchanged. |
| Sheaf.Algebra.Homology.OpenTotalTensorCoefficientInterchange | unclaimed | No adaptation; signatures and meaning unchanged. |
| Sheaf.Algebra.Homology.OpenTotalTensorCoefficientNormalization | unclaimed | No adaptation; signatures and meaning unchanged. |
| Sheaf.Algebra.Homology.StrictCoefficientAugmentationHomotopicality | unclaimed | No adaptation; signatures and meaning unchanged. |
| Sheaf.Algebra.Homology.StrictTensorDerivedData | unclaimed | No adaptation; signatures and meaning unchanged. |
| Sheaf.Algebra.Homology.StrictTensorModelEvaluation | unclaimed | No adaptation; signatures and meaning unchanged. |
| Sheaf.Algebra.Homology.StrictTensorOrdinaryData | unclaimed | No adaptation; signatures and meaning unchanged. |
| Sheaf.CategoryTheory.SliceTensorGeneratorCoherence | unclaimed | No adaptation; signatures and meaning unchanged. |
| Sheaf.Paper.CompletedSupportIntermediateTower | unclaimed | No adaptation; signatures and meaning unchanged. |

## Status

landed 20261024T191322-L-305932 2026-10-24 (merge of deliver/U1/Sheaf.Algebra.Homology.LocalizedStrictTensorDescent)
