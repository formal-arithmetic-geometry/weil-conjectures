# AlgebraicGeometry.singleComplexOpenComparison_union_ses_compatibility

## Reason

The old universal statement is false: it permits arbitrary a and m. Take identity scheme maps over Spec(Z), zero K and K′, U=V=top, and let a be constantly the identity of Q(A) for a nonzero degree-zero module complex A. Take both rows to be the split row A → A⊕A → A, with the natural six localized isomorphisms, and take m=0. The first equation then asserts 0=id on Q(A). Short exactness of the rows supplies no equation relating m to a. The corrected statement is the cylinder step of the source argument; the geometric compatible-chain-model step is stated separately and the parent conclusion is unchanged.

## Old

```lean
theorem singleComplexOpenComparison_union_ses_compatibility
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [IsAffine S] [IsAffine S']
    [QuasiCompact f] [QuasiSeparated f]
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K)
    (K' : schemeDerivedCategory X') (hK' : schemeDerivedQCohProperty X' K')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens)
    (hUqc : IsCompact (U : Set X)) (hVqc : IsCompact (V : Set X))
    (hUVqc : IsCompact ((U ⊓ V : X.Opens) : Set X)) 
    (a : X.Opens → Arrow (schemeDerivedCategory S'))
    (P P' : ShortComplex (CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ))
    (m : P ⟶ P')
    (e₁ : DerivedCategory.Q.obj P.X₁ ≅ (a (U ⊔ V)).left)
    (e₂ : DerivedCategory.Q.obj P.X₂ ≅ (a U).left ⊞ (a V).left)
    (e₃ : DerivedCategory.Q.obj P.X₃ ≅ (a (U ⊓ V)).left)
    (e₁' : DerivedCategory.Q.obj P'.X₁ ≅ (a (U ⊔ V)).right)
    (e₂' : DerivedCategory.Q.obj P'.X₂ ≅ (a U).right ⊞ (a V).right)
    (e₃' : DerivedCategory.Q.obj P'.X₃ ≅ (a (U ⊓ V)).right)
    (hP : P.ShortExact) (hP' : P'.ShortExact) :
    DerivedCategory.Q.map m.τ₁ ≫ e₁'.hom = e₁.hom ≫ (a (U ⊔ V)).hom ∧
    DerivedCategory.Q.map m.τ₂ ≫ e₂'.hom =
      e₂.hom ≫ biprod.map (a U).hom (a V).hom ∧
    DerivedCategory.Q.map m.τ₃ ≫ e₃'.hom = e₃.hom ≫ (a (U ⊓ V)).hom
```

## New

```lean
theorem singleComplexOpenComparison_union_ses_compatibility
    {C : Type u} [Category C] [Abelian C] [HasDerivedCategory.{w} C]
    (A B A' B' : CochainComplex C ℤ)
    (t : A ⟶ B) (t' : A' ⟶ B') (α : A ⟶ A') (β : B ⟶ B')
    (hc : t ≫ β = α ≫ t')
    {L₁ L₂ L₃ R₁ R₂ R₃ : DerivedCategory C}
    (b₁ : L₁ ⟶ R₁) (b₂ : L₂ ⟶ R₂) (b₃ : L₃ ⟶ R₃)
    (e₁ : DerivedCategory.Q.obj A ≅ L₁)
    (e₂ : DerivedCategory.Q.obj B ≅ L₂)
    (e₃ : DerivedCategory.Q.obj (mappingCone t) ≅ L₃)
    (e₁' : DerivedCategory.Q.obj A' ≅ R₁)
    (e₂' : DerivedCategory.Q.obj B' ≅ R₂)
    (e₃' : DerivedCategory.Q.obj (mappingCone t') ≅ R₃)
    (hα : DerivedCategory.Q.map α ≫ e₁'.hom = e₁.hom ≫ b₁)
    (hβ : DerivedCategory.Q.map β ≫ e₂'.hom = e₂.hom ≫ b₂)
    (hγ : DerivedCategory.Q.map (mappingCone.map t t' α β hc) ≫ e₃'.hom =
      e₃.hom ≫ b₃) :
    ∃ (P P' : ShortComplex (CochainComplex C ℤ)) (m : P ⟶ P')
      (d₁ : DerivedCategory.Q.obj P.X₁ ≅ L₁)
      (d₂ : DerivedCategory.Q.obj P.X₂ ≅ L₂)
      (d₃ : DerivedCategory.Q.obj P.X₃ ≅ L₃)
      (d₁' : DerivedCategory.Q.obj P'.X₁ ≅ R₁)
      (d₂' : DerivedCategory.Q.obj P'.X₂ ≅ R₂)
      (d₃' : DerivedCategory.Q.obj P'.X₃ ≅ R₃),
      P.ShortExact ∧ P'.ShortExact ∧
      DerivedCategory.Q.map m.τ₁ ≫ d₁'.hom = d₁.hom ≫ b₁ ∧
      DerivedCategory.Q.map m.τ₂ ≫ d₂'.hom = d₂.hom ≫ b₂ ∧
      DerivedCategory.Q.map m.τ₃ ≫ d₃'.hom = d₃.hom ≫ b₃
```

## Users

`tools/downstream.py --uses` finds one external declaration user and one direct importer. The 1,434 transitive importers retain exactly the original parent interface; no definition or target is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SingleComplexOpenUnionSESCompatibility | J2 (dispatcher item; local claim snapshot C1) | Corrected false statement and proved its source cylinder construction. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenUnionSESPresentation | unclaimed | Its old application is ill-typed against the corrected dependency. Preserve its entire signature and visibility; replace only the proof and the object-only proof import. |

The adapted parent obtains compatible chain models and invokes the proved cylinder step. No other module directly imports the item, and no other source mentions the declaration. The parent node proof follows the new route; its statement is unchanged. The unit record has no realized node steps; the same relative Mayer–Vietoris source-open induction route is kept.

## Status

landed 20261014T063818-L-2814065 2026-10-14 (merge of deliver/J2/Sheaf.AlgebraicGeometry.SingleComplexOpenUnionSESCompatibility)
