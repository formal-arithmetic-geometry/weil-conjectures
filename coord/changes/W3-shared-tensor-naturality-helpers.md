# SheafOfModules tensor naturality helpers

## Reason

The landing of returned head `7406ac83ac` was refused because
`SliceTensorNatural` proved four generic helper statements already proved
privately in `OpenRestrictionTensorNatural`. Make the existing helpers public in
place and import them, rather than maintaining duplicate proofs. The latter
module is unclaimed (no claim file at the repair's start). All four proof bodies
are unchanged. This visibility extension changes no mathematical statement,
definition, target type, existing public name or existing public visibility.

## Old

In `lean/Sheaf/Algebra/Homology/OpenRestrictionTensorNatural.lean`:

```lean
private theorem compose_four_squares {D : Type*} [Category* D]
    {A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ B₃ B₄ : D}
    (a₀ : A₀ ⟶ A₁) (a₁ : A₁ ⟶ A₂) (a₂ : A₂ ⟶ A₃) (a₃ : A₃ ⟶ A₄)
    (b₀ : B₀ ⟶ B₁) (b₁ : B₁ ⟶ B₂) (b₂ : B₂ ⟶ B₃) (b₃ : B₃ ⟶ B₄)
    (f₀ : A₀ ⟶ B₀) (f₁ : A₁ ⟶ B₁) (f₂ : A₂ ⟶ B₂)
    (f₃ : A₃ ⟶ B₃) (f₄ : A₄ ⟶ B₄)
    (h₀ : f₀ ≫ b₀ = a₀ ≫ f₁) (h₁ : f₁ ≫ b₁ = a₁ ≫ f₂)
    (h₂ : f₂ ≫ b₂ = a₂ ≫ f₃) (h₃ : f₃ ≫ b₃ = a₃ ≫ f₄) :
    f₀ ≫ (b₀ ≫ b₁ ≫ b₂ ≫ b₃) = (a₀ ≫ a₁ ≫ a₂ ≫ a₃) ≫ f₄

private theorem inverse_square {D : Type*} [Category* D]
    {A B A' B' : D} (e : A ≅ B) (e' : A' ≅ B') (f : A ⟶ A') (g : B ⟶ B')
    (h : f ≫ e'.hom = e.hom ≫ g) : g ≫ e'.inv = e.inv ≫ f

private theorem tensorObjIsoSheafification_natural
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    {M M' N N' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)}
    (f : M ⟶ M') (g : N ⟶ N') :
    letI := monoidalCategory R
    (f ⊗ₘ g) ≫ (tensorObjIsoSheafification (R := R) M' N').hom =
      (tensorObjIsoSheafification (R := R) M N).hom ≫
        (PresheafOfModules.sheafification.{u}
          (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).map
            (f.val ⊗ₘ g.val)

private theorem tensor_square {D : Type*} [Category* D] [MonoidalCategory D]
    {M N M' N' P Q P' Q' : D} (f : M ⟶ M') (g : N ⟶ N')
    (f' : P ⟶ P') (g' : Q ⟶ Q')
    (a : M ≅ P) (b : N ≅ Q) (a' : M' ≅ P') (b' : N' ≅ Q')
    (ha : f ≫ a'.hom = a.hom ≫ f') (hb : g ≫ b'.hom = b.hom ≫ g') :
    (f ⊗ₘ g) ≫ (a' ⊗ᵢ b').hom = (a ⊗ᵢ b).hom ≫ (f' ⊗ₘ g')
```

## New

In the same module:

```lean
theorem compose_four_squares {D : Type*} [Category* D]
    {A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ B₃ B₄ : D}
    (a₀ : A₀ ⟶ A₁) (a₁ : A₁ ⟶ A₂) (a₂ : A₂ ⟶ A₃) (a₃ : A₃ ⟶ A₄)
    (b₀ : B₀ ⟶ B₁) (b₁ : B₁ ⟶ B₂) (b₂ : B₂ ⟶ B₃) (b₃ : B₃ ⟶ B₄)
    (f₀ : A₀ ⟶ B₀) (f₁ : A₁ ⟶ B₁) (f₂ : A₂ ⟶ B₂)
    (f₃ : A₃ ⟶ B₃) (f₄ : A₄ ⟶ B₄)
    (h₀ : f₀ ≫ b₀ = a₀ ≫ f₁) (h₁ : f₁ ≫ b₁ = a₁ ≫ f₂)
    (h₂ : f₂ ≫ b₂ = a₂ ≫ f₃) (h₃ : f₃ ≫ b₃ = a₃ ≫ f₄) :
    f₀ ≫ (b₀ ≫ b₁ ≫ b₂ ≫ b₃) = (a₀ ≫ a₁ ≫ a₂ ≫ a₃) ≫ f₄

theorem inverse_square {D : Type*} [Category* D]
    {A B A' B' : D} (e : A ≅ B) (e' : A' ≅ B') (f : A ⟶ A') (g : B ⟶ B')
    (h : f ≫ e'.hom = e.hom ≫ g) : g ≫ e'.inv = e.inv ≫ f

theorem tensorObjIsoSheafification_natural
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    {M M' N N' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)}
    (f : M ⟶ M') (g : N ⟶ N') :
    letI := monoidalCategory R
    (f ⊗ₘ g) ≫ (tensorObjIsoSheafification (R := R) M' N').hom =
      (tensorObjIsoSheafification (R := R) M N).hom ≫
        (PresheafOfModules.sheafification.{u}
          (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).map
            (f.val ⊗ₘ g.val)

theorem tensor_square {D : Type*} [Category* D] [MonoidalCategory D]
    {M N M' N' P Q P' Q' : D} (f : M ⟶ M') (g : N ⟶ N')
    (f' : P ⟶ P') (g' : Q ⟶ Q')
    (a : M ≅ P) (b : N ≅ Q) (a' : M' ≅ P') (b' : N' ≅ Q')
    (ha : f ≫ a'.hom = a.hom ≫ f') (hb : g ≫ b'.hom = b.hom ≫ g') :
    (f ⊗ₘ g) ≫ (a' ⊗ᵢ b').hom = (a ⊗ᵢ b).hom ≫ (f' ⊗ₘ g')
```

`SliceTensorNatural` removes its four duplicate declarations and adds only:

```lean
import Sheaf.Algebra.Homology.OpenRestrictionTensorNatural
```

It removes its now-unneeded direct proof import of
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`.
No other proof or signature in the original helper module changes.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.OpenRestrictionTensorNatural --uses
compose_four_squares inverse_square tensorObjIsoSheafification_natural tensor_square`
reports 1248 transitive downstream modules. The helpers were private, so none
could use these declarations. Textual uses occur only in the original module
and, for `inverse_square`, one unrelated private lemma in
`ContinuousIntegralExchangeTargetAdjunct`. Direct importers and all name-use
hits are recorded below. No existing consumer requires adaptation; the public
existential tensor-comparison theorem and its proof are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.OpenRestrictionTensorNatural | unclaimed | Existing four generic helpers become public in place; no proof body changes. |
| Sheaf.Algebra.Homology.SliceTensorNatural | W3, new in this delivery | Removes duplicates and imports the existing public helpers for proofs. |
| Sheaf.Algebra.Homology.OpenRestrictionKFlat | unclaimed | Direct importer; existing public interface unchanged, no edit. |
| Sheaf.Algebra.Homology.OpenRestrictionTensorHomology | unclaimed | Direct importer; existing public interface unchanged, no edit. |
| Sheaf.AlgebraicGeometry.OpenScalarRestrictionStalkCriterion | unclaimed | Direct importer; existing public interface unchanged, no edit. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | Its private root-level inverse_square has different binders and namespace; no edit. |

No forced adaptation is made in any held module. No new DAG node or hole is
introduced by this repair. The slice-tensor node records use of the existing
open-localized tensor node for these generic naturality helpers.

## Status

landed 20261018T101338-L-3972963 2026-10-18 (merge of deliver/W3/Sheaf.Paper.RingedLocalizationRHomCalculus)
