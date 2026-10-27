# SheafOfModules.coefficientHomComplex_comparison

## Reason

The existing comparison proof constructs an isomorphism by the product universal
property and proves its projection equation, then discards that equation.
The coefficient-Hom unit needs that normalization. Retain the equation in this
private proof interface and reuse it in the unit module. Both affected modules
were unclaimed except for the assigned unit module, held by E6.

The product specification is represented by named structure fields, as recorded
in `E6-product-hom-complex-data.md`. The comparison now uses the named Hom
bifunctor and its component API instead of a large local functor definition.
Its product argument is expressed over abstract categories before specializing
to sheaves. This repairs the repeated unfolding identified by the compiler;
no proof is moved into a new module and no new proof obligation is introduced.

The concrete sheaf declarations locally prefer `hasSheafCompose_of_preservesLimitsOfSize` over the multicospan instance. Both prove exactly `HasSheafCompose`; this changes the proof found by instance search and preserves the underlying ring sheaf.

## Old

The ambient parameters are the small site, the two ring sheaves, and `φ : R ⟶ B`.

```lean
private theorem coefficientHomComplex_comparison
    (H : (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))ᵒᵖ ×
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
    (i : H ⋙ restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) ≅
      (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).op.prod
        (𝟭 _) ⋙ Functor.uncurry.obj (homFunctor.{u, u, u, u} R))
    (G : (CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) ℤ)ᵒᵖ ⥤
      CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ ⥤
      CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) ℤ)
    (hG : ProductHomComplexSpecification (Functor.curry.obj H) G) :
    Nonempty (Functor.uncurry.obj G ⋙
      (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
        ).mapHomologicalComplex (.up ℤ) ≅
      ((restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
        ).mapHomologicalComplex (.up ℤ)).op.prod (𝟭 _) ⋙
        Functor.uncurry.obj (homComplexFunctor (R := R)))
```

## New

The private helper also abstracts the proof of
`J.HasSheafCompose (forget₂ CommRingCat RingCat)`. This is a proposition; its
canonical specialization has the same module categories and restriction functor.

```lean
theorem coefficientHomComplex_comparison
    (H : (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))ᵒᵖ ×
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
    (i : H ⋙ restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) ≅
      (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).op.prod
        (𝟭 _) ⋙ Functor.uncurry.obj (homFunctor.{u, u, u, u} R))
    (G : (CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) ℤ)ᵒᵖ ⥤
      CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ ⥤
      CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) ℤ)
    (dG : ProductHomComplexData (Functor.curry.obj H) G) :
    ∃ e : Functor.uncurry.obj G ⋙
      (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
        ).mapHomologicalComplex (.up ℤ) ≅
      ((restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
        ).mapHomologicalComplex (.up ℤ)).op.prod (𝟭 _) ⋙
        Functor.uncurry.obj (homComplexFunctor (R := R)),
      ∀ (L : CochainComplex (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) ℤ)
        (M : CochainComplex (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
        (n p q : ℤ) (h : p + n = q),
        (e.hom.app (op L, M)).f n ≫
          complexHomProjection (((restrictScalars.{u}
            ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
              ).mapHomologicalComplex (.up ℤ)).obj L) M n p q h =
          (restrictScalars.{u}
            ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).map
              (dG.π L M n p q h) ≫
            coefficientHomObjComparisonHom φ H i (op (L.X p), M.X q)
```

The public `complexHomProjection` is the actual `homComplexπ`, with its source
written using the named complex bifunctor and its target the native `homObj`. The proved
`complexHomProjection_eq` is reflexivity. Its limit, differential and induced-map
API lemmas express the existing projection laws with those same named types.
It is irreducible after these proofs to prevent repeated expansion of the
concrete sheaf-module structure during specialization.

The public `coefficientHomObjComparisonHom` is exactly `i.hom.app X`,
with its codomain written as the native `homObj`. Thus the projection equation
composes maps with matching named endpoints, avoiding repeated conversion
through the underived bifunctor object. It constructs no new mathematical data.

The normalized comparison helper is now a public proved API and takes the
product data explicitly. The public proof
unpacks its existing `Nonempty` specification once and passes that data to
the helper. The resulting isomorphism gives the old private conclusion by
forgetting its projection equation; no chosen projection family is recomputed.
The public `exists_restrictedCoefficientHomComplexFunctor` has exactly its former
statement and obtains an isomorphism of the same specified functors from the stronger private helper.
All old public imports and visibility are retained. All proofs are complete.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RestrictedCoefficientHomComplex | unclaimed | Its public existence theorem forgets the retained projection equation. Its signature and mathematical meaning are unchanged. |
| Sheaf.Paper.CoefficientHomUnit | E6 | An ordinary proof import reuses the normalized comparison to construct the unit and prove its evaluation identity. The assigned statement is unchanged. |

The original helper was private and used only by the public theorem in its own
module. There are no other direct users of its signature. No adopted source
module is changed and no target statement is weakened.

## Status

landed 20261026T111828-L-1744881 2026-10-26 (merge of deliver/E6/Sheaf.Paper.CoefficientHomUnit)

The public `complexHomProjection_map_left` specializes the existing typed
induced-map formula to the identity in the second variable, then uses
`comparisonHomMap` to express the resulting coefficient map by `homObjMap`.
It is fully proved and changes no existing declaration signature. Its only
consumer is the assigned coefficient-Hom unit proof.

The seven documented APIs are public: `coefficientHomObjComparisonHom`,
`comparisonHomMap`, `complexHomProjection`, `complexHomProjection_eq`,
`complexHomProjection_map_left`, `coefficientHomComplex_comparison` and
`extendProductFromSeparateAdditivity`. Their consumers use an ordinary import.
The actual projection definition requires a public import of the source
`HomComplexComponents` module; its existing public declarations are unchanged.
