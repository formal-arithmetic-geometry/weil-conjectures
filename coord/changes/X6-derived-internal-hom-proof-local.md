# Sheaf.Paper.DerivedInternalHomFilteredColimit proof-local commands

## Reason

Stage-3 X6 proves the two remaining holes from existing declarations. The static
interface check requests this record because the proof adds local sections, local
attributes and private helpers and removes old private helper declarations.
Every existing public declaration signature, public definition body and public
import is unchanged. No target meaning changes and no consumer adaptation is needed.

The old scalar-evaluation construction duplicates the existing normalized strict
scalar-chain API. Reuse its sigma, sigma_unique and sigma_natural; the normalization
bridge identifies these with the existing comparison. Removing that duplicate
construction and preventing proof-local tensor/comparison unfolding keeps the
complete single module within its compile limit. No source-library file is edited.

## Old

The original proof imports were:

```lean
import Sheaf.Paper.InternalHomFiniteFreeStage
import Sheaf.Paper.InternalHomFilteredContinuity
```

The following private signatures are removed. They were implementation helpers,
not public declarations or DAG statements. Their original types are recorded verbatim:

```lean
private theorem extensionPresheafUnit_locallySurjective
    {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings (J := J) φ M)
    (M : Modules.{u, v, r} J R) :
    Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map
      (extensionPresheafUnit.{u, v, r} J φ E h M))
```

```lean
private theorem extensionUnit_exists {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings (J := J) φ M)
    (hmap : ∀ {M N : Modules.{u, v, r} J R} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom (J := J) φ M f ≫ eqToHom (h N).symm)
    [E.Additive] :
    ∃ η : 𝟭 (Modules.{u, v, r} J R) ⟶ E ⋙ SheafOfModules.restrictScalars.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).map φ),
      ∀ (M : Modules.{u, v, r} J R) (U : Cᵒᵖ) (x : M.val.obj U),
        (η.app M).val.app U x = extensionGenerator.{u, v, r} J φ E h M U 1 x
```

```lean
private theorem extensionGenerator_map {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings (J := J) φ M)
    (hmap : ∀ {M N : Modules.{u, v, r} J R} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom (J := J) φ M f ≫ eqToHom (h N).symm)
    [E.Additive] {M N : Modules.{u, v, r} J R} (f : M ⟶ N)
    (U : Cᵒᵖ) (x : M.val.obj U) :
    (E.map f).val.app U (extensionGenerator.{u, v, r} J φ E h M U 1 x) =
      extensionGenerator.{u, v, r} J φ E h N U 1 (f.val.app U x)
```

```lean
private theorem extensionGenerator_restrict {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings (J := J) φ M)
    (hmap : ∀ {M N : Modules.{u, v, r} J R} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom (J := J) φ M f ≫ eqToHom (h N).symm)
    [E.Additive] (M : Modules.{u, v, r} J R) {U V : Cᵒᵖ} (i : U ⟶ V)
    (x : M.val.obj U) :
    (E.obj M).val.map i (extensionGenerator.{u, v, r} J φ E h M U 1 x) =
      extensionGenerator.{u, v, r} J φ E h M V 1 (M.val.map i x)
```

```lean
private theorem restricted_hom_ext (R : Sheaf J CommRingCat.{max u v r})
    (A : PresheafOfModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R).obj)
    (M N : Modules.{u, v, r} J R)
    (η : A ⟶ (PresheafOfModules.restrictScalars (𝟙
      ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R).obj)).obj
        M.val)
    [Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map η)]
    (U : C) (a b : (PresheafOfModules.restrictOver R.obj U).obj M.val ⟶
      (PresheafOfModules.restrictOver R.obj U).obj N.val)
    (hab : ∀ (W : (Over U)ᵒᵖ) (x : A.obj (op W.unop.left)),
      a.app W (η.app (op W.unop.left) x) = b.app W (η.app (op W.unop.left) x)) :
    a = b
```

```lean
private theorem extension_local_ext {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings (J := J) φ M)
    (M : Modules.{u, v, r} J R) (N : Modules.{u, v, r} J S) (U : C)
    (a b : (PresheafOfModules.restrictOver S.obj U).obj (E.obj M).val ⟶
      (PresheafOfModules.restrictOver S.obj U).obj N.val)
    (hab : ∀ (W : (Over U)ᵒᵖ) (x : M.val.obj (op W.unop.left)),
      a.app W (extensionGenerator.{u, v, r} J φ E h M (op W.unop.left) 1 x) =
        b.app W (extensionGenerator.{u, v, r} J φ E h M (op W.unop.left) 1 x)) : a = b
```

```lean
private theorem extension_hom_ext {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings (J := J) φ M)
    (M : Modules.{u, v, r} J R) (N : Modules.{u, v, r} J S)
    (a b : E.obj M ⟶ N)
    (hab : ∀ (U : Cᵒᵖ) (x : M.val.obj U),
      a.val.app U (extensionGenerator.{u, v, r} J φ E h M U 1 x) =
        b.val.app U (extensionGenerator.{u, v, r} J φ E h M U 1 x)) : a = b
```

```lean
private theorem extension_to_homObj_ext {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings (J := J) φ M)
    (hmap : ∀ {M N : Modules.{u, v, r} J R} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom (J := J) φ M f ≫ eqToHom (h N).symm)
    [E.Additive] (M N : Modules.{u, v, r} J R) (V : Modules.{u, v, r} J S)
    (a b : E.obj M ⟶ SheafOfModules.homObj (J := J) (R := S) (E.obj N) V)
    (hab : ∀ (U : Cᵒᵖ) (z : M.val.obj U) (x : N.val.obj U),
      ((a.val.app U (extensionGenerator.{u, v, r} J φ E h M U 1 z)).app
        (op (Over.mk (𝟙 U.unop)))).hom
          (extensionGenerator.{u, v, r} J φ E h N U 1 x) =
      ((b.val.app U (extensionGenerator.{u, v, r} J φ E h M U 1 z)).app
        (op (Over.mk (𝟙 U.unop)))).hom
          (extensionGenerator.{u, v, r} J φ E h N U 1 x)) : a = b
```

```lean
private theorem scalar_hom_ext {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings (J := J) φ M)
    (hmap : ∀ {M N : Modules.{u, v, r} J R} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom (J := J) φ M f ≫ eqToHom (h N).symm)
    [E.Additive] (M : Modules.{u, v, r} J R)
    (P : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (Q : CochainComplex (Modules.{u, v, r} J S) ℤ) (n : ℤ)
    (a b : E.obj M ⟶
      (homComplex (J := J) (R := S) ((E.mapHomologicalComplex (.up ℤ)).obj P) Q).X n)
    (hab : ∀ (p q : ℤ) (hpq : p + n = q) (U : Cᵒᵖ)
      (z : M.val.obj U) (x : (P.X p).val.obj U),
      homValue.{u, v, r} J S
          ((E.mapHomologicalComplex (.up ℤ)).obj P) Q n p q hpq U
          (a.val.app U (extensionGenerator.{u, v, r} J φ E h M U 1 z))
          (extensionGenerator.{u, v, r} J φ E h (P.X p) U 1 x) =
        homValue.{u, v, r} J S
          ((E.mapHomologicalComplex (.up ℤ)).obj P) Q n p q hpq U
          (b.val.app U (extensionGenerator.{u, v, r} J φ E h M U 1 z))
          (extensionGenerator.{u, v, r} J φ E h (P.X p) U 1 x)) : a = b
```

```lean
private theorem homObjMap_evaluate (R : Sheaf J CommRingCat.{max u v r})
    {M M' N N' : Modules.{u, v, r} J R} (f : M' ⟶ M) (g : N ⟶ N')
    (U : Cᵒᵖ) (z : (SheafOfModules.homObj (J := J) (R := R) M N).val.obj U)
    (x : M'.val.obj U) :
    ((((SheafOfModules.homObjMap (J := J) (R := R) f g).val.app U z).app
      (op (Over.mk (𝟙 U.unop)))).hom x) =
      g.val.app U ((z.app (op (Over.mk (𝟙 U.unop)))).hom (f.val.app U x))
```

```lean
private theorem homValue_map (R : Sheaf J CommRingCat.{max u v r})
    {P P' Q Q' : CochainComplex (Modules.{u, v, r} J R) ℤ}
    (f : P' ⟶ P) (g : Q ⟶ Q') (n p q : ℤ) (hpq : p + n = q)
    (U : Cᵒᵖ) (z : ((homComplex (J := J) (R := R) P Q).X n).val.obj U)
    (x : (P'.X p).val.obj U) :
    homValue.{u, v, r} J R P' Q' n p q hpq U
        ((((Functor.uncurry.obj
          (homComplexFunctor.{u, v, max u v r, max u v r} (J := J) (R := R))).map
            (X := (op P, Q)) (Y := (op P', Q')) (f.op, g)).f n).val.app U z) x =
      (g.f q).val.app U
        (homValue.{u, v, r} J R P Q n p q hpq U z ((f.f p).val.app U x))
```

```lean
private def ScalarEvaluation {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings (J := J) φ M)
    [E.Additive] (P Q : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (V : CochainComplex (Modules.{u, v, r} J S) ℤ)
    (τ : (E.mapHomologicalComplex (.up ℤ)).obj Q ⟶ V)
    (α : (E.mapHomologicalComplex (.up ℤ)).obj
        (homComplex (J := J) (R := R) P Q) ⟶
      homComplex (J := J) (R := S) ((E.mapHomologicalComplex (.up ℤ)).obj P) V) : Prop
```

```lean
private theorem scalar_map_naturality {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings (J := J) φ M)
    (hmap : ∀ {M N : Modules.{u, v, r} J R} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom (J := J) φ M f ≫ eqToHom (h N).symm)
    [E.Additive] {P P' Q Q' : CochainComplex (Modules.{u, v, r} J R) ℤ}
    {V V' : CochainComplex (Modules.{u, v, r} J S) ℤ}
    (f : P' ⟶ P) (g : Q ⟶ Q') (k : V ⟶ V')
    (τ : (E.mapHomologicalComplex (.up ℤ)).obj Q ⟶ V)
    (τ' : (E.mapHomologicalComplex (.up ℤ)).obj Q' ⟶ V')
    (hsq : (E.mapHomologicalComplex (.up ℤ)).map g ≫ τ' = τ ≫ k)
    (α : (E.mapHomologicalComplex (.up ℤ)).obj
        (homComplex (J := J) (R := R) P Q) ⟶
      homComplex (J := J) (R := S) ((E.mapHomologicalComplex (.up ℤ)).obj P) V)
    (α' : (E.mapHomologicalComplex (.up ℤ)).obj
        (homComplex (J := J) (R := R) P' Q') ⟶
      homComplex (J := J) (R := S) ((E.mapHomologicalComplex (.up ℤ)).obj P') V')
    (hn : ScalarEvaluation.{u, v, r} J φ E h P Q V τ α)
    (hn' : ScalarEvaluation.{u, v, r} J φ E h P' Q' V' τ' α') :
    (E.mapHomologicalComplex (.up ℤ)).map
        ((Functor.uncurry.obj
          (homComplexFunctor.{u, v, max u v r, max u v r} (J := J) (R := R))).map
            (X := (op P, Q)) (Y := (op P', Q')) (f.op, g)) ≫ α' =
      α ≫ (Functor.uncurry.obj
        (homComplexFunctor.{u, v, max u v r, max u v r} (J := J) (R := S))).map
          (X := (op ((E.mapHomologicalComplex (.up ℤ)).obj P), V))
          (Y := (op ((E.mapHomologicalComplex (.up ℤ)).obj P'), V'))
          (((E.mapHomologicalComplex (.up ℤ)).map f).op, k)
```

```lean
private theorem extensionGenerator_restrict_all {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings φ M)
    (M : Modules.{u, v, r} J R) {U V : Cᵒᵖ} (i : U ⟶ V)
    (s : S.obj.obj U) (x : M.val.obj U) :
    (E.obj M).val.map i (extensionGenerator.{u, v, r} J φ E h M U s x) =
      extensionGenerator.{u, v, r} J φ E h M V (S.obj.map i s) (M.val.map i x)
```

```lean
private noncomputable def extensionHomRaw {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings φ M)
    (M N : Modules.{u, v, r} J R) (U : Cᵒᵖ)
    (f : (SheafOfModules.homObj (R := R) M N).val.obj U) :
    (PresheafOfModules.restrictOver S.obj U.unop).obj
        (SheafOfModules.changeOfRingsPresheaf.{v, u, max u v r} (J := J) φ M) ⟶
      (PresheafOfModules.restrictOver S.obj U.unop).obj (E.obj N).val where
  app W
```

```lean
private theorem extensionPresheafUnit_locallyInjective
    {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings φ M)
    (M : Modules.{u, v, r} J R) :
    Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map
      (extensionPresheafUnit.{u, v, r} J φ E h M))
```

```lean
private noncomputable def extensionHomSection {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings φ M)
    (M N : Modules.{u, v, r} J R) (U : Cᵒᵖ)
    (f : (SheafOfModules.homObj (R := R) M N).val.obj U) :
    (SheafOfModules.homObj (R := S) (E.obj M) (E.obj N)).val.obj U
```

```lean
private theorem extensionHomSection_apply {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings φ M)
    (M N : Modules.{u, v, r} J R) (U : Cᵒᵖ)
    (f : (SheafOfModules.homObj (R := R) M N).val.obj U)
    (W : (Over U.unop)ᵒᵖ) (s : S.obj.obj (op W.unop.left))
    (x : M.val.obj (op W.unop.left)) :
    (extensionHomSection.{u, v, r} J φ E h M N U f).app W
        (extensionGenerator.{u, v, r} J φ E h M (op W.unop.left) s x) =
      extensionGenerator.{u, v, r} J φ E h N (op W.unop.left) s (f.app W x)
```

```lean
private theorem extensionGenerator_add {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings φ M)
    (M : Modules.{u, v, r} J R) (U : Cᵒᵖ) (s : S.obj.obj U) (x y : M.val.obj U) :
    extensionGenerator.{u, v, r} J φ E h M U s (x + y) =
      extensionGenerator.{u, v, r} J φ E h M U s x +
        extensionGenerator.{u, v, r} J φ E h M U s y
```

```lean
private theorem extensionGenerator_scalar {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings φ M)
    (M : Modules.{u, v, r} J R) (U : Cᵒᵖ) (a : R.obj.obj U) (x : M.val.obj U) :
    extensionGenerator.{u, v, r} J φ E h M U 1 (a • x) =
      (φ.hom.app U a) • extensionGenerator.{u, v, r} J φ E h M U 1 x
```

```lean
private noncomputable def extensionHomBase {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings φ M)
    (M N : Modules.{u, v, r} J R) :
    SheafOfModules.homObj (R := R) M N ⟶
      (SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).map φ)).obj
          (SheafOfModules.homObj (R := S) (E.obj M) (E.obj N)) where
  val
```

```lean
private theorem scalar_degree_exists {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings φ M)
    [E.Additive]
    (a : E ⊣ SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).map φ))
    (ha : ∀ (M : Modules.{u, v, r} J R) (U : Cᵒᵖ) (x : M.val.obj U),
      (a.unit.app M).val.app U x = extensionGenerator.{u, v, r} J φ E h M U 1 x)
    (P Q : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (V : CochainComplex (Modules.{u, v, r} J S) ℤ)
    (τ : (E.mapHomologicalComplex (.up ℤ)).obj Q ⟶ V) (n : ℤ) :
    ∃ t : E.obj ((homComplex (R := R) P Q).X n) ⟶
        (homComplex (R := S) ((E.mapHomologicalComplex (.up ℤ)).obj P) V).X n,
      ∀ (p q : ℤ) (hpq : p + n = q) (U : Cᵒᵖ)
        (z : ((homComplex (R := R) P Q).X n).val.obj U) (x : (P.X p).val.obj U),
        homValue.{u, v, r} J S ((E.mapHomologicalComplex (.up ℤ)).obj P) V n p q hpq U
            (t.val.app U (extensionGenerator.{u, v, r} J φ E h _ U 1 z))
            (extensionGenerator.{u, v, r} J φ E h (P.X p) U 1 x) =
          (τ.f q).val.app U (extensionGenerator.{u, v, r} J φ E h (Q.X q) U 1
            (homValue.{u, v, r} J R P Q n p q hpq U z x))
```

```lean
private theorem map_units {A B F : Type*} [AddCommGroup A] [AddCommGroup B]
    [FunLike F A B] [AddMonoidHomClass F A B] (f : F) (e : ℤˣ) (x : A) :
    f (e • x) = e • f x
```

```lean
private theorem hom_section_sub_units (R : Sheaf J CommRingCat.{max u v r})
    (A B D : Modules.{u, v, r} J R)
    (f g : D ⟶ SheafOfModules.homObj (R := R) A B)
    (e : ℤˣ) (U : Cᵒᵖ) (s : D.val.obj U) (x : A.val.obj U) :
    ((((f - e • g).val.app U).hom s).app (op (Over.mk (𝟙 U.unop)))).hom x =
      (((f.val.app U).hom s).app (op (Over.mk (𝟙 U.unop)))).hom x -
        e • (((g.val.app U).hom s).app (op (Over.mk (𝟙 U.unop)))).hom x
```

```lean
private theorem homValue_d (R : Sheaf J CommRingCat.{max u v r})
    (P Q : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (n m p q q' p' : ℤ) (hnm : n + 1 = m) (hpq : p + m = q)
    (hq' : p + n = q') (hp' : p' + n = q) (U : Cᵒᵖ)
    (z : ((homComplex (R := R) P Q).X n).val.obj U) (x : (P.X p).val.obj U) :
    homValue.{u, v, r} J R P Q m p q hpq U
        (((homComplex (R := R) P Q).d n m).val.app U z) x =
      (Q.d q' q).val.app U (homValue.{u, v, r} J R P Q n p q' hq' U z x) -
        n.negOnePow • homValue.{u, v, r} J R P Q n p' q hp' U z
          ((P.d p p').val.app U x)
```

```lean
private theorem scalar_evaluation_exists {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings φ M)
    (hmap : ∀ {M N : Modules.{u, v, r} J R} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (h N).symm)
    [E.Additive] (P Q : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (V : CochainComplex (Modules.{u, v, r} J S) ℤ)
    (τ : (E.mapHomologicalComplex (.up ℤ)).obj Q ⟶ V) :
    ∃ α : (E.mapHomologicalComplex (.up ℤ)).obj (homComplex (R := R) P Q) ⟶
        homComplex (R := S) ((E.mapHomologicalComplex (.up ℤ)).obj P) V,
      ScalarEvaluation.{u, v, r} J φ E h P Q V τ α
```

```lean
private theorem homValue_smul (R : Sheaf J CommRingCat.{max u v r})
    (P Q : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (n p q : ℤ) (hpq : p + n = q) (U : Cᵒᵖ) (s t : R.obj.obj U)
    (f : ((homComplex (R := R) P Q).X n).val.obj U) (x : (P.X p).val.obj U) :
    homValue.{u, v, r} J R P Q n p q hpq U (s • f) (t • x) =
      (s * t) • homValue.{u, v, r} J R P Q n p q hpq U f x
```

```lean
private theorem scalarNormalized_evaluation {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings (J := J) φ M)
    [E.Additive] (P L : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (α : (E.mapHomologicalComplex (.up ℤ)).obj ((homFixed.{u, v, r} J R P).obj L) ⟶
      (homFixed.{u, v, r} J S ((E.mapHomologicalComplex (.up ℤ)).obj P)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj
          ((coefficientHomResolution.{r, u, v} J R).obj L)))
    (hn : ScalarNormalized.{u, v, r} J φ E h P L α) :
    ScalarEvaluation.{u, v, r} J φ E h P ((coefficientHomResolution.{r, u, v} J R).obj L)
      ((coefficientHomResolution.{r, u, v} J S).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj
          ((coefficientHomResolution.{r, u, v} J R).obj L)))
      ((resolutionUnit.{u, v, r} J S).app
        ((E.mapHomologicalComplex (.up ℤ)).obj
          ((coefficientHomResolution.{r, u, v} J R).obj L))) α
```

## New

The corresponding proof imports expose compiled private helper APIs within this file:

```lean
import all Sheaf.Paper.DerivedInternalHomFilteredColimitData
import all Sheaf.Paper.InternalHomFiniteFreeStage
import all Sheaf.Paper.InternalHomFilteredContinuity
```

The public import of DerivedInternalHomFilteredColimitData stays verbatim. Added
proof imports are StrictScalarHomChain, RightDerivedFunctor.Comp,
QuasiIsoHomComplexMapOfUniverses and TensorColimitsIndependentCoefficients.
The retained comparison existence/uniqueness and naturality theorems now use the
existing normalized scalar-chain declarations. The new private normalization bridge,
scalar-extension object/map equalities, and tensorTermwiseIso are completely proved.
There are no new public signatures. Public definitions including scalarComparison
and derivedComparison retain their exact bodies.

Local commands added for proof elaboration include:

```lean
section FilteredAssembly
attribute [local irreducible] comparison roofDenominator tensor homFixed
end FilteredAssembly
```

The actual theorem lies inside that local section. RestrictionProof also installs
local tensor instances and marks the monoidal/sheafification constructions,
singleTensorIso, tensorGenerator, tensor, comparison and scalarComparison locally
irreducible. ScalarExtensionBridge contains the proved transport equalities. QuasiIsoProof also
marks comparison, scalarComparison and roofDenominator locally irreducible so that
quasi-isomorphism rewrites use their naturality API without expanding their constructions.
These section-local settings end before the remaining public declarations and add
no exported attribute or instance.

## Users

Read-only tools/downstream.py finds two direct importers and 769 transitive
importers. With --uses scalarComparison_existsUnique scalarComparison_naturality
scalarComparison_quasiIso derivedInternalHom_filteredColimit_comparison, the only
Lean declaration-name hits are in the item itself; the direct Qlbar consumer's
restriction/filtered-comparison mention is in its natural-language proof plan.
All public declarations and imports are preserved, so the same unchanged interface
serves every transitive importer. Removed helpers are private and have no external
consumer. No other module is adapted or delivered.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DerivedInternalHomFilteredColimit | X6 | Two holes closed; private implementation pruned; all public statements and definitions preserved. |
| Sheaf.Paper.QlbarInternalHomCoefficientComparison | No adaptation; holder irrelevant to this proof-only change | Direct public importer; unchanged statements and definitions, so no edit needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | No adaptation; holder irrelevant to this proof-only change | Direct private importer; unchanged statements and definitions, so no edit needed. |

## Status

landed 20261021T225234-L-3804168 2026-10-21 (merge of deliver/X6/Sheaf.Paper.DerivedInternalHomFilteredColimit)
