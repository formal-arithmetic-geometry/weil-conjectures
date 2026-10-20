# AlgebraicGeometry.Etale.ordinaryGlobalKunnethMap

## Reason

Separate the four existing generic absolute-map definitions from their finite-level theorem.
This lets a general canonical-map comparison import the definitions without importing the
finite-level theorem that will use it. Names, binders and construction data are preserved.
The item publicly imports the new definition module, so existing importers retain the API.

The finite-level proof uses a scoped preference for `CommRing.toRing`. The quotient has both a
direct Ring instance and the Ring underlying its CommRing; these are definitionally equal, but
comparing their induced sheaf/derived monoidal structures exhausted the single-file compile
limit. The preference is local to the theorem's section, but it precedes the statement of
`isIso_ordinaryGlobalKunnethMap_finiteCoefficientRing`, so it also governs how that statement
elaborates: the source text is unchanged, while every `Ring (Padic.coefficientExtensionRing l E n)`
in the elaborated type is now `CommRing.toRing Ideal.Quotient.commRing` (before: a mixture with
`Ideal.Quotient.instRingQuotient` in `ModuleCat`). The two types are definitionally equal (no
hypothesis added, no conclusion weakened), but the conversion is not cheap: applying the theorem
in a file that elaborates the same text with the default instances fails with a kernel
deterministic timeout (reviewer check, more than 560 s). A consumer must state the theorem
under the same `attribute [local instance 2000] CommRing.toRing`, or work with the generic
`[CommRing Λ]` form. No Lean module uses the theorem at present. No source-library module is
modified.

## Old

The definitions were in `Sheaf.AlgebraicGeometry.OrdinaryKunnethFiniteRing`:

```lean
noncomputable def derivedConstantPullbackIso {X Z : Scheme.{u}} (p : Z ⟶ X) :
    (constantSheaf Z.smallEtaleTopology A).leftDerivedFunctor ≅
      (constantSheaf X.smallEtaleTopology A).leftDerivedFunctor ⋙
        L((p)^*[A]) :=
  (Functor.leftDerivedFunctorNatIso (constantSheaf Z.smallEtaleTopology A)
    (Scheme.upperStarConstantSheafIso A p).symm) ≪≫
      Functor.leftDerivedFunctorCompIso (constantSheaf X.smallEtaleTopology A) (upperStar A p)

/-- Pull the global-sections counit back to `Z`, identifying the pulled-back constant
complex with the constant complex on `Z` by `derivedConstantPullbackIso`.
Source: blueprint order 1740, terminal-topos specialization
(blueprint: lem-pur-ordinary-kunneth-finite-ring). -/
noncomputable def ordinaryKunnethPulledCounit {X Z : Scheme.{u}} (p : Z ⟶ X)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (constantSheaf Z.smallEtaleTopology A).leftDerivedFunctor.obj
      ((rightDerivedGlobalSections A X).obj K) ⟶
        (L((p)^*[A])).obj K :=
  (derivedConstantPullbackIso A p).hom.app _ ≫
    (L((p)^*[A])).map
      ((derivedConstantGlobalSectionsAdjunction A X).counit.app K)

/-- The tensor-of-counits adjunct construction, with its categories left abstract.
Source: blueprint order 1740, the displayed adjunct formula
(blueprint: lem-pur-ordinary-kunneth-finite-ring). This helper keeps the same tensor structures as
explicit parameters when specializing to the terminal geometric morphism. -/
noncomputable def ordinaryKunnethTensorMate
    {C : Type uC} [Category.{vC} C] {B : Type uB} [Category.{vB} B]
    (T : C ⥤ C ⥤ C) (T' : B ⥤ B ⥤ B)
    (F : C ⥤ B) (G : B ⥤ C) (adj : F ⊣ G)
    (δ : (Functor.postcompose₂.obj F).obj T ⟶
      (((Functor.whiskeringLeft₂ B).obj F).obj F).obj T')
    {P Q : C} {V W : B} (a : F.obj P ⟶ V) (b : F.obj Q ⟶ W) :
    (T.obj P).obj Q ⟶ G.obj ((T'.obj V).obj W) :=
  adj.homEquiv _ _ ((δ.app P).app Q ≫ (T'.map a).app _ ≫ (T'.obj _).map b)

/-- The absolute exterior-product arrow in the derived category of modules, adjoint to
the derived constant-sheaf tensor comparison followed by the tensor of the two
pulled-back global-sections counits. Its target is the derived sections of the ordinary
uncompleted derived external tensor product.
Source: blueprint order 1740 and Stacks Tag 0F1E (blueprint: lem-pur-ordinary-kunneth-finite-ring).
This is the terminal-topos form of the upstream `kunnethMap`, using the constant-complex
versus sections adjunction. No equivalence for the etale point is chosen. -/
noncomputable def ordinaryGlobalKunnethMap {X Y Z : Scheme.{u}}
    (p : Z ⟶ X) (q : Z ⟶ Y)
    [(constantSheaf Z.smallEtaleTopology A).Monoidal]
    [(constantSheaf Z.smallEtaleTopology A).PreservesFlat]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (rightDerivedGlobalSections A X).obj K ⊗
        (rightDerivedGlobalSections A Y).obj M ⟶
      (rightDerivedGlobalSections A Z).obj
        (((curriedTensor (DerivedCategory (Sheaf Z.smallEtaleTopology A))).obj
          ((L((p)^*[A])).obj K)).obj
            ((L((q)^*[A])).obj M)) :=
  ordinaryKunnethTensorMate (curriedTensor (DerivedCategory A))
    (curriedTensor (DerivedCategory (Sheaf Z.smallEtaleTopology A)))
    (constantSheaf Z.smallEtaleTopology A).leftDerivedFunctor
    (rightDerivedGlobalSections A Z) (derivedConstantGlobalSectionsAdjunction A Z)
    (constantSheaf Z.smallEtaleTopology A).leftDerivedTensorComparison
    (ordinaryKunnethPulledCounit A p K) (ordinaryKunnethPulledCounit A q M)


```

## New

The same definitions are in `Sheaf.AlgebraicGeometry.OrdinaryKunnethMap`, publicly imported by the
item.

```lean
noncomputable def derivedConstantPullbackIso {X Z : Scheme.{u}} (p : Z ⟶ X) :
    (constantSheaf Z.smallEtaleTopology A).leftDerivedFunctor ≅
      (constantSheaf X.smallEtaleTopology A).leftDerivedFunctor ⋙
        L((p)^*[A]) :=
  (Functor.leftDerivedFunctorNatIso (constantSheaf Z.smallEtaleTopology A)
    (Scheme.upperStarConstantSheafIso A p).symm) ≪≫
      Functor.leftDerivedFunctorCompIso (constantSheaf X.smallEtaleTopology A) (upperStar A p)

/-- Pull the global-sections counit back to `Z`, identifying the pulled-back constant
complex with the constant complex on `Z` by `derivedConstantPullbackIso`.
Source: blueprint order 1740, terminal-topos specialization
(blueprint: def-pur-ordinary-kunneth-absolute-map). -/
noncomputable def ordinaryKunnethPulledCounit {X Z : Scheme.{u}} (p : Z ⟶ X)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (constantSheaf Z.smallEtaleTopology A).leftDerivedFunctor.obj
      ((rightDerivedGlobalSections A X).obj K) ⟶
        (L((p)^*[A])).obj K :=
  (derivedConstantPullbackIso A p).hom.app _ ≫
    (L((p)^*[A])).map
      ((derivedConstantGlobalSectionsAdjunction A X).counit.app K)

/-- The tensor-of-counits adjunct construction, with its categories left abstract.
Source: blueprint order 1740, the displayed adjunct formula
(blueprint: def-pur-ordinary-kunneth-absolute-map). This helper keeps the same tensor structures as
explicit parameters when specializing to the terminal geometric morphism. -/
noncomputable def ordinaryKunnethTensorMate
    {C : Type uC} [Category.{vC} C] {B : Type uB} [Category.{vB} B]
    (T : C ⥤ C ⥤ C) (T' : B ⥤ B ⥤ B)
    (F : C ⥤ B) (G : B ⥤ C) (adj : F ⊣ G)
    (δ : (Functor.postcompose₂.obj F).obj T ⟶
      (((Functor.whiskeringLeft₂ B).obj F).obj F).obj T')
    {P Q : C} {V W : B} (a : F.obj P ⟶ V) (b : F.obj Q ⟶ W) :
    (T.obj P).obj Q ⟶ G.obj ((T'.obj V).obj W) :=
  adj.homEquiv _ _ ((δ.app P).app Q ≫ (T'.map a).app _ ≫ (T'.obj _).map b)

/-- The absolute exterior-product arrow in the derived category of modules, adjoint to
the derived constant-sheaf tensor comparison followed by the tensor of the two
pulled-back global-sections counits. Its target is the derived sections of the ordinary
uncompleted derived external tensor product.
Source: blueprint order 1740 and Stacks Tag 0F1E (blueprint: def-pur-ordinary-kunneth-absolute-map).
This is the terminal-topos form of the upstream `kunnethMap`, using the constant-complex
versus sections adjunction. No equivalence for the etale point is chosen. -/
noncomputable def ordinaryGlobalKunnethMap {X Y Z : Scheme.{u}}
    (p : Z ⟶ X) (q : Z ⟶ Y)
    [(constantSheaf Z.smallEtaleTopology A).Monoidal]
    [(constantSheaf Z.smallEtaleTopology A).PreservesFlat]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (rightDerivedGlobalSections A X).obj K ⊗
        (rightDerivedGlobalSections A Y).obj M ⟶
      (rightDerivedGlobalSections A Z).obj
        (((curriedTensor (DerivedCategory (Sheaf Z.smallEtaleTopology A))).obj
          ((L((p)^*[A])).obj K)).obj
            ((L((q)^*[A])).obj M)) :=
  ordinaryKunnethTensorMate (curriedTensor (DerivedCategory A))
    (curriedTensor (DerivedCategory (Sheaf Z.smallEtaleTopology A)))
    (constantSheaf Z.smallEtaleTopology A).leftDerivedFunctor
    (rightDerivedGlobalSections A Z) (derivedConstantGlobalSectionsAdjunction A Z)
    (constantSheaf Z.smallEtaleTopology A).leftDerivedTensorComparison
    (ordinaryKunnethPulledCounit A p K) (ordinaryKunnethPulledCounit A q M)


```

New support definitions `ordinaryKunnethSectionsIso` and
`ordinaryRelativeGlobalKunnethMap` give explicit conjugate/adjunction transport, with no chosen
existence witnesses. They belong to the separate comparison node, not to a redefinition of the
absolute arrow. Its equality theorem is the remaining categorical comparison obligation.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OrdinaryKunnethFiniteRing | G7 | Publicly reexports the four unchanged definitions and proves its original theorem from the relative finite-ring theorem and the comparison. |
| Sheaf.Paper.ExternalRHomConePairing | J7 | Uses derivedConstantPullbackIso; the name, signature and body are unchanged, and the public import still exports it. No adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | Uses ordinaryGlobalKunnethMap in compactProductMapCore; its name, signature, construction data and public re-export are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.SupportedProductLocalization | unclaimed | Indirect consumer of the item; its interface remains the same. No adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryKunnethMap | G7, new | Owns the moved definitions, with their exact original construction data. |
| Sheaf.AlgebraicGeometry.AbsoluteKunnethComparison | G7, new | Uses the definition module and provides canonical relative transport and its equality obligation. |

`tools/downstream.py --uses` was run again for all four moved names. The item,
ExternalRHomConePairing and CompactProductArrows mention them. The supported-product module
is also listed because it
imports the item. No consumer statement becomes weaker, stronger or different. Targets that
transitively use the map keep the same construction; the independent reader should verify
this preservation when reviewing the move and instance normalization.

Verification: all four definition bodies match their original source verbatim. The unchanged
SupportedProductLocalization and CompactProductArrows consumers compiled against the new
re-export (the latter in 14.2 seconds). ExternalRHomConePairing
timed out against both the changed item and the untouched original item, so no forced change to
J7's module is justified. An auxiliary formal equality test under all original imports also
exceeded the file limit; no successful formal equality test is claimed.

## Status

landed 20261020T221202-L-4154765 2026-10-20 (merge of deliver/G7/Sheaf.AlgebraicGeometry.OrdinaryKunnethFiniteRing)
