# WeilConjectures.sfIdentityComposition

## Reason

The original theorem needs two independent left-adjoint normalization lemmas, while its
right-mate calculation is formal. Move the unchanged identity-point definitions to a shared
module so those lemmas can state their conclusions without importing the theorem they prove.
This is a dependency separation for proof decomposition, not a compile-time split. No object
is chosen from an unproved existence theorem and no existing mathematical interface changes.
The main module publicly reexports the data module. The data module imports SixFunctorDatum,
which is what the unchanged declarations need. The three former public proof-planning imports
are removed; no current Lean module imports the item.

## Old

The following declarations were defined in `Sheaf.Paper.IdentificationCoefficientTransport`:

```lean
def sfPointIdentityCompactification (D : FiniteFieldDatum.{u}) :
    Compactification (𝟙 (Spec.{u} (.of D.k))) :=
  Compactification.ofIsProper (𝟙 (Spec.{u} (.of D.k)))

def sfSupportEquality {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) {X Y : SixFunctorSpace D}
    (f g : X ⟶ Y) (h : f = g) (c : Compactification f.hom.left) :
    S.support g (h ▸ c) ≅ S.support f c := by
  subst g
  exact Iso.refl _

def sfIdentityComposition {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (X : SixFunctorSpace D)
    (c : Compactification (sixFunctorStructure X).hom.left) :
    S.support (sixFunctorStructure X) c ⋙
      S.support (𝟙 (sixFunctorPoint D)) (sfPointIdentityCompactification D) ≅
        S.support (sixFunctorStructure X) c :=
  (S.composition (sixFunctorStructure X) (𝟙 (sixFunctorPoint D)) c
    (sfPointIdentityCompactification D)
    ((Category.comp_id (sixFunctorStructure X)).symm ▸ c)).symm ≪≫
      sfSupportEquality S (sixFunctorStructure X)
        (sixFunctorStructure X ≫ 𝟙 (sixFunctorPoint D))
        (Category.comp_id (sixFunctorStructure X)).symm c

def sfIdentityNormalizedCounit {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (L : B (sixFunctorPoint D))
    (v : S.support (𝟙 (sixFunctorPoint D)) (sfPointIdentityCompactification D) ≅ 𝟭 _) :=
  v.inv.app ((S.exceptional (𝟙 (sixFunctorPoint D))
    (sfPointIdentityCompactification D)).obj L) ≫
      (S.exceptionalAdjunction (𝟙 (sixFunctorPoint D))
        (sfPointIdentityCompactification D)).counit.app L

def sfIdentityTransportMate {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (X : SixFunctorSpace D)
    (c : Compactification (sixFunctorStructure X).hom.left) :=
  conjugateIsoEquiv
    ((S.exceptionalAdjunction (sixFunctorStructure X) c).comp
      (S.exceptionalAdjunction (𝟙 (sixFunctorPoint D))
        (sfPointIdentityCompactification D)))
    (S.exceptionalAdjunction (sixFunctorStructure X) c)
    (sfIdentityComposition S X c).symm

structure SfIdentityStageLaws {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (P : ∀ X, B X → Prop)
    (L : B (sixFunctorPoint D))
    (v : S.support (𝟙 (sixFunctorPoint D))
      (sfPointIdentityCompactification D) ≅ 𝟭 _) : Prop where
  composition_identity : ∀ (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (c : Compactification (sixFunctorStructure X).hom.left)
    (K : B X), P X K →
    (sfIdentityComposition S X c).hom.app K =
      v.hom.app ((S.support (sixFunctorStructure X) c).obj K)
  normalized_counit_iso : IsIso (sfIdentityNormalizedCounit S L v)
  mate_iso : ∀ (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left),
    IsIso ((sfIdentityTransportMate S X c).hom.app L)
  mate_is_normalized_counit : ∀ (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (c : Compactification (sixFunctorStructure X).hom.left),
    (sfIdentityTransportMate S X c).hom.app L =
      (S.exceptional (sixFunctorStructure X) c).map (sfIdentityNormalizedCounit S L v)
  counit_equation : ∀ (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left),
    (S.support (sixFunctorStructure X) c).map
        ((sfIdentityTransportMate S X c).hom.app L) ≫
      (S.exceptionalAdjunction (sixFunctorStructure X) c).counit.app L =
    (S.exceptionalAdjunction (sixFunctorStructure X) c).counit.app
        ((S.exceptional (𝟙 (sixFunctorPoint D)) (sfPointIdentityCompactification D)).obj L) ≫
      sfIdentityNormalizedCounit S L v

def SfIdentityChange {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {B₁ : SixFunctorSpace D → Type v₁} [∀ X, Category.{w₁} (B₁ X)]
    {S : SixFunctorPushStage D B} {S₁ : SixFunctorPushStage D B₁}
    {F : ∀ X, B X ⥤ B₁ X} (Q : SixFunctorCoefficientComparison S S₁ F)
    (v : S.support (𝟙 (sixFunctorPoint D)) (sfPointIdentityCompactification D) ≅ 𝟭 _)
    (v₁ : S₁.support (𝟙 (sixFunctorPoint D)) (sfPointIdentityCompactification D) ≅ 𝟭 _) :
    Prop :=
  ∀ K : B (sixFunctorPoint D),
    (Q.supportAdjunction (𝟙 (sixFunctorPoint D))
        (sfPointIdentityCompactification D)).left.hom.app K ≫
      v₁.hom.app ((F (sixFunctorPoint D)).obj K) =
    (F (sixFunctorPoint D)).map (v.hom.app K)

def sfFiniteIdentityComparison
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorFiniteOperations D C E n hn) :
    (@SixFunctorPushStage.support.{u, u+2, u+2} D
      (sixFunctorFiniteCategory D C E n hn)
      (fun X ↦ inferInstanceAs (Category.{u+2} (sixFunctorFiniteCategory D C E n hn X)))
      S.finite) (𝟙 (sixFunctorPoint D)) (sfPointIdentityCompactification D) ≅
        Functor.id.{u+2, u+2} (sixFunctorFiniteCategory D C E n hn (sixFunctorPoint D)) :=
  ((intrinsicFiniteTorsionConstructible C.l E n hn
      (Spec (.of D.k))).fullyFaithfulι.{u+2, u+2}.whiskeringRight _).preimageIso
    (Functor.isoWhiskerRight
        (@SixFunctorPushStage.properIdentity.{u, u+2, u+2} D
          (sixFunctorFiniteCategory D C E n hn)
          (fun X ↦ inferInstanceAs (Category.{u+2} (sixFunctorFiniteCategory D C E n hn X)))
          S.finite _ _ (𝟙 (sixFunctorPoint D)) inferInstance)
        (intrinsicFiniteTorsionConstructible C.l E n hn (Spec (.of D.k))).ι ≪≫
      S.finiteDirectImage (𝟙 (sixFunctorPoint D)) ≪≫
      Functor.isoWhiskerLeft _
        (@sixFunctorDirectIdentity (Padic.coefficientExtensionRing C.l E n) _
          (Padic.finite_coefficientExtensionRing C.l E n hn) (Spec (.of D.k))) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)
```

## New

All declarations quoted above, with identical signatures, visibility and bodies, are defined
in `Sheaf.Paper.IdentityCoefficientTransportData` and publicly reexported by the original
module. Thus the quoted Lean declarations are also the verbatim new version. The new data
module additionally defines the following predicate to state only the left-adjoint part:

```lean
def SfIdentityCompositionLaw {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B)
    (v : S.support (𝟙 (sixFunctorPoint D))
      (sfPointIdentityCompactification D) ≅ 𝟭 _) : Prop :=
  ∀ (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left) (K : B X),
    (sfIdentityComposition S X c).hom.app K =
      v.hom.app ((S.support (sixFunctorStructure X) c).obj K)
```

`identificationCoefficientTransport` keeps its signature verbatim. It imports the two new
normalization statements privately and proves the right-mate and counit clauses by an
explicit adjunction calculation. The new normalization statements introduce proof holes,
not data holes, and retain the canonical finite comparisons and every coefficient square.

## Users

`tools/downstream.py Sheaf.Paper.IdentificationCoefficientTransport --direct --uses
sfIdentityComposition SfIdentityStageLaws identificationCoefficientTransport` found zero
direct Lean importers. The DAG parents remain unchanged: the existing module reexports
all definitions, and the original theorem has the same statement. No target signature or
existing definition body changes, so no target-statement review is reopened.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IdentificationCoefficientTransport | A7 | Same public declarations by reexport; theorem proved from normalization and formal adjunction laws. |
| Sheaf.Paper.IdentityCoefficientTransportData | new, A7 | Unchanged data declarations plus the explicit composition-law predicate. |
| Sheaf.Paper.FiniteIdentityCompositionNormalization | new, A7 | Finite left-adjoint normalization step only. |
| Sheaf.Paper.HigherIdentityCompositionNormalization | new, A7 | Completed and scalar left-adjoint normalization and the required coefficient squares. |

## Status

landed 20261025T201329-L-2429489 2026-10-25 (merge of deliver/A7/Sheaf.Paper.IdentificationCoefficientTransport)
