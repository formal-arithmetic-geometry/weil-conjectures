# internalScalarHom and ScalarTransport

## Reason

Delivery path: `coord/changes/T7-internal-section-scalar-hom-folding.md`.
If an independent reader needs to override this record with `--apply-fixes`, the
required fix-directory filename is `T7-internal-section-scalar-hom-folding.change.md`.
The delivered basename without `.change` is not a supported override alias.

The compiler repeatedly expands native derived closed structures when checking scalar
naturality and the two large transport fields. Add a generic parametrized-adjunction construction for the same evaluation transpose
and name the tensor and Hom predicates. Disable unused automatic size/injectivity generation for this record.
No hypotheses, section maps, normalization equations or conclusions change.

## Old

```lean
def internalScalarHom (K L : DerivedCategory.{u + 1} (Internal.{u} Λ X)) :
    (CondensedRing.internalScalarExtension.{u} a X).obj
      (((CondensedRing.derivedHom.{u} Λ X).obj (op K)).obj L) ⟶
    ((CondensedRing.derivedHom.{u} Γ X).obj
      (op ((CondensedRing.internalScalarExtension.{u} a X).obj K))).obj
        ((CondensedRing.internalScalarExtension.{u} a X).obj L) :=
  (CondensedRing.derivedTensorHomAdjunction.{u} Γ
    ((CondensedRing.internalScalarExtension.{u} a X).obj K)).homEquiv _ _
    (((CondensedRing.internalScalarTensorIso.{u} a X).inv.app K).app
        (((CondensedRing.derivedHom.{u} Λ X).obj (op K)).obj L) ≫
      (CondensedRing.internalScalarExtension.{u} a X).map
        ((CondensedRing.derivedTensorHomAdjunction.{u} Λ K).counit.app L))

```

The `tensor` and `hom` fields contained the full forall equations now named
`ScalarTransportTensor` and `ScalarTransportHom`, verbatim below.

## New

```lean
def scalarHomMate
    {C : Type a₀} [Category.{b₀} C] {D : Type a₁} [Category.{b₁} D]
    (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C)
    (S : D ⥤ D ⥤ D) (J : Dᵒᵖ ⥤ D ⥤ D)
    (adj : T ⊣₂ H) (adj' : S ⊣₂ J) (F : C ⥤ D)
    (μ : (Functor.postcompose₂.obj F).obj T ≅
      (((Functor.whiskeringLeft₂ _).obj F).obj F).obj S) (K L : C) :
    F.obj ((H.obj (op K)).obj L) ⟶ (J.obj (op (F.obj K))).obj (F.obj L) :=
  adj'.homEquiv ((μ.inv.app K).app ((H.obj (op K)).obj L) ≫
    F.map ((adj.adj K).counit.app L))


-- `internalScalarHom` keeps its original body verbatim (reviewer FIX, see below).

/-- The scalar tensor square as a named predicate, to keep transport data compact.
Source: Stacks 07A4 (blueprint: def-sfb-internal-section-scalar-hom-transport-data). -/
def ScalarTransportTensor
    (extension : CondensedRing.internalScalarExtension.{u} a X ⋙ forward.{u} Γ X ≅
      forward.{u} Λ X ⋙ (M.scalar (sectionCoefficientMap.{u} a)).derived) : Prop :=
  ∀ K L : DerivedCategory.{u + 1} (Internal.{u} Λ X),
    (forward.{u} Γ X).map (((CondensedRing.internalScalarTensorIso.{u} a X).hom.app K).app L) ≫
        PΓ.tensor.iso.hom.app
          ((CondensedRing.internalScalarExtension.{u} a X).obj K,
            (CondensedRing.internalScalarExtension.{u} a X).obj L) ≫
        (M.closed (ring.{u} Γ X)).tensor.map
          (X := ((forward.{u} Γ X).obj ((CondensedRing.internalScalarExtension.{u} a X).obj K),
            (forward.{u} Γ X).obj ((CondensedRing.internalScalarExtension.{u} a X).obj L)))
          (Y := ((M.scalar (sectionCoefficientMap.{u} a)).derived.obj
              ((forward.{u} Λ X).obj K),
            (M.scalar (sectionCoefficientMap.{u} a)).derived.obj
              ((forward.{u} Λ X).obj L)))
          (extension.hom.app K, extension.hom.app L) =
      extension.hom.app (((CondensedRing.derivedTensor.{u} Λ X).obj K).obj L) ≫
        (M.scalar (sectionCoefficientMap.{u} a)).derived.map (PΛ.tensor.iso.hom.app (K, L)) ≫
        (μ (sectionCoefficientMap.{u} a)).iso.hom.app
          ((forward.{u} Λ X).obj K, (forward.{u} Λ X).obj L)

/-- The scalar Hom square as a named predicate, retaining its actual evaluation map.
Source: Stacks 08J9 (blueprint: def-sfb-internal-section-scalar-hom-transport-data). -/
def ScalarTransportHom
    (extension : CondensedRing.internalScalarExtension.{u} a X ⋙ forward.{u} Γ X ≅
      forward.{u} Λ X ⋙ (M.scalar (sectionCoefficientMap.{u} a)).derived) : Prop :=
  ∀ K L : DerivedCategory.{u + 1} (Internal.{u} Λ X),
    (forward.{u} Γ X).map (internalScalarHom.{u} a K L) ≫
        PΓ.homIso.hom.app (op ((CondensedRing.internalScalarExtension.{u} a X).obj K),
          (CondensedRing.internalScalarExtension.{u} a X).obj L) ≫
        (ModuleObjectRingedComparison.hom.{u} Γ X).map
          (X := (op ((forward.{u} Γ X).obj
              ((CondensedRing.internalScalarExtension.{u} a X).obj K)),
            (forward.{u} Γ X).obj ((CondensedRing.internalScalarExtension.{u} a X).obj L)))
          (Y := (op ((M.scalar (sectionCoefficientMap.{u} a)).derived.obj
              ((forward.{u} Λ X).obj K)),
            (M.scalar (sectionCoefficientMap.{u} a)).derived.obj
              ((forward.{u} Λ X).obj L)))
          ((extension.inv.app K).op, extension.hom.app L) =
      extension.hom.app (((CondensedRing.derivedHom.{u} Λ X).obj (op K)).obj L) ≫
        (M.scalar (sectionCoefficientMap.{u} a)).derived.map (PΛ.homIso.hom.app (op K, L)) ≫
        coefficientBaseChangeHom (M.closed (ring.{u} Λ X)) (M.closed (ring.{u} Γ X))
          (M.scalar (sectionCoefficientMap.{u} a)).derived (μ (sectionCoefficientMap.{u} a)).iso
          ((forward.{u} Λ X).obj K) ((forward.{u} Λ X).obj L)

/-- The canonical scalar identifications, pinned by the unchanged section maps,
the localized restriction comparison and the normalized scalar Hom transposes.
Source: Stacks 03EK, 07A4, 07A6, 08J9
(blueprint: def-sfb-internal-section-scalar-hom-transport-data). -/
structure ScalarTransport where
  /-- Ordinary restriction fixes underlying sections. -/
  restriction : Mod.comap (coefficientMap.{u} a X) ⋙ (equivalence.{u} Λ X).functor ≅
    (equivalence.{u} Γ X).functor ⋙
      SheafOfModules.scalarRestriction.{u + 1, u, u + 1} (sectionCoefficientMap.{u} a)
  /-- No change of section maps is allowed. -/
  sections : ∀ (N : Internal.{u} Γ X) (U : X.ProEtᵒᵖ) (x : N.X.obj.obj U),
    (restriction.hom.app N).val.app U x = x
  /-- The actual localized restriction square. -/
  derivedRestriction : (Mod.comap (coefficientMap.{u} a X)).mapDerivedCategory ⋙ forward.{u} Λ X ≅
    forward.{u} Γ X ⋙
      SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
        (sectionCoefficientMap.{u} a)
  /-- Restriction is derived from the section identity just specified. -/
  restrictionNormalization : derivedRestriction =
    (Functor.mapDerivedCategoryCompIso (Mod.comap (coefficientMap.{u} a X))
      (equivalence.{u} Λ X).functor).symm ≪≫
      Functor.mapDerivedCategoryNatIso restriction ≪≫
      Functor.mapDerivedCategoryCompIso (equivalence.{u} Γ X).functor
        (SheafOfModules.scalarRestriction.{u + 1, u, u + 1} (sectionCoefficientMap.{u} a))
  /-- The scalar-extension comparison. -/
  extension : CondensedRing.internalScalarExtension.{u} a X ⋙ forward.{u} Γ X ≅
    forward.{u} Λ X ⋙ (M.scalar (sectionCoefficientMap.{u} a)).derived
  /-- Compatibility with actual normalized adjunction transposes fixes extension. -/
  adjunction : ∀ (K : DerivedCategory.{u + 1} (Internal.{u} Λ X))
    (N : DerivedCategory.{u + 1} (Internal.{u} Γ X))
    (f : (CondensedRing.internalScalarExtension.{u} a X).obj K ⟶ N),
    (forward.{u} Λ X).map
        ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap.{u} a X)).homEquiv K N f)
        ≫ derivedRestriction.hom.app N =
      (M.scalar (sectionCoefficientMap.{u} a)).adjunction.homEquiv _ _
        (extension.inv.app K ≫ (forward.{u} Γ X).map f)
  /-- The normalized scalar tensor maps agree. -/
  tensor : ScalarTransportTensor.{u} (a := a) (X := X) (M := M)
    (μ := μ) (PΛ := PΛ) (PΓ := PΓ) extension
  /-- Equality of the actual evaluation-transpose scalar Hom maps. -/
  hom : ScalarTransportHom.{u} (a := a) (X := X) (M := M)
    (μ := μ) (PΛ := PΛ) (PΓ := PΓ) extension

```

`internalScalarHom` keeps its original body (reviewer FIX, 2026-10-26; re-applied on re-delivery e52c4c18): the delivered
rewrite through `scalarHomMate`/`derivedTensorHomAdjunction₂` broke
`Sheaf.Paper.QlbarInternalHomCoefficientComparison` (U4), whose
`evaluationComparison_naturality` identifies its verbatim copy of the old body with
`internalScalarHom` by `change` while `derivedTensorHomAdjunction` is locally irreducible.
`scalarHomMate` is a new generic helper; the unary `derivedTensorHomAdjunction` is
definitionally the `.adj K` component of `derivedTensorHomAdjunction₂`, so
`internalScalarHom a K L` is definitionally `scalarHomMate … K L`, which the item uses
for naturality.
The two predicate bodies are precisely the previous field types.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.InternalSectionScalarHomTransportData | unclaimed | Definition refactor; no holes. |
| Sheaf.Paper.InternalSectionHomContinuityComparison | T7 | Naturality applies the generic scalar-mate lemma. All theorem signatures retained. |
| Sheaf.Paper.QlbarInternalHomCoefficientComparison | U4 | Uses `internalScalarHom` (naturality by `change`); unchanged, compiles because the body is unchanged. |

`tools/downstream.py` lists only the assigned item downstream. Searches for
`internalScalarHom` also find `Sheaf.Paper.QlbarInternalHomCoefficientComparison`.
The definitions occur under the project targets; their unchanged interpretation
is submitted for independent definition review.

## Status

landed 20261025T203246-L-2797225 2026-10-25 (merge of deliver/T7/Sheaf.Paper.InternalSectionHomContinuityComparison)
