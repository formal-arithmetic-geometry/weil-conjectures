# Retire the duplicate open restriction tensor comparison

## Reason

`coord/retire-items.tsv` assigns retirement of
`Sheaf.Algebra.Homology.OpenRestrictionTensorNatural` in favor of
`WeilConjectures.Algebra.Homology.OpenRestrictionTensorNatural`. Both contain the
same fully proved main theorem, with byte-identical signatures. The only public
API difference is that the Sheaf module exposes four generic naturality helpers
which are private upstream. Their sole remaining external user is
`Sheaf.Algebra.Homology.SliceTensorNatural`. Relocate those existing proved
public helpers to that consumer, preserving their names, statements and bodies.
No source-library file is edited, and no upstream declaration is removed.

## Old

In `lean/Sheaf/Algebra/Homology/OpenRestrictionTensorNatural.lean`, the public
main theorem was:

```lean
theorem exists_open_localized_tensor_natural
    {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (U : TopologicalSpace.Opens X) :
    let A := (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R
    let V := overFunctor.{u} A U
    letI := monoidalCategory R
    letI : MonoidalCategory (SheafOfModules.{u} (A.over U)) :=
      monoidalCategory (R.over U)
    ∃ e : ∀ (M N : SheafOfModules.{u} A), V.obj (M ⊗ N) ≅ V.obj M ⊗ V.obj N,
      ∀ (M M' N N' : SheafOfModules.{u} A) (f : M ⟶ M') (g : N ⟶ N'),
        V.map (f ⊗ₘ g) ≫ (e M' N').hom = (e M N).hom ≫ (V.map f ⊗ₘ V.map g)
```

The following four public helper signatures also lived there:

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
    letI

theorem tensor_square {D : Type*} [Category* D] [MonoidalCategory D]
    {M N M' N' P Q P' Q' : D} (f : M ⟶ M') (g : N ⟶ N')
    (f' : P ⟶ P') (g' : Q ⟶ Q')
    (a : M ≅ P) (b : N ≅ Q) (a' : M' ≅ P') (b' : N' ≅ Q')
    (ha : f ≫ a'.hom = a.hom ≫ f') (hb : g ≫ b'.hom = b.hom ≫ g') :
    (f ⊗ₘ g) ≫ (a' ⊗ᵢ b').hom = (a ⊗ᵢ b).hom ≫ (f' ⊗ₘ g')
```

The two remaining direct consumers each used:

```lean
import Sheaf.Algebra.Homology.OpenRestrictionTensorNatural
```

## New

Withdraw the duplicate module with `deleted.txt`. The unchanged main theorem
is supplied by the existing upstream module, whose source and proof are left
verbatim. The DAG attachment now points to that upstream theorem.
`OpenRestrictionKFlat` replaces only its private proof import:

```lean
import WeilConjectures.Algebra.Homology.OpenRestrictionTensorNatural
```

The four public helper signatures displayed above, with their existing proof
bodies, move verbatim to `lean/Sheaf/Algebra/Homology/SliceTensorNatural.lean`.
That file replaces the retired module's proof import by:

```lean
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
```

This supplies the two tensor-whiskering identities used to prove
`tensorObjIsoSheafification_natural`. The slice node no longer cites the
open-localized tensor comparison just to get these helpers. No new mathematical
statement or definition is introduced. Targets and all their definitions keep
the same meaning. No new node is needed for this relocation of existing helpers.

## Users

The read-only `tools/downstream.py` check reports the following 18 transitive
users. A source search finds just the first two direct importers, and finds all
four helper uses only in SliceTensorNatural. OpenRestrictionTensorHomology and
OpenScalarRestrictionStalkCriterion, listed in the retirement inventory, have
already been retired by other deliveries and are not edited here.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.OpenRestrictionKFlat | unclaimed | Replace the proof import by the upstream twin. The used theorem has a byte-identical signature. |
| Sheaf.Algebra.Homology.SliceTensorNatural | unclaimed | Move the four existing public helpers here verbatim; replace the old proof import by MonoidalClosed. All five pre-existing public declarations stay identical. |
| Sheaf.AlgebraicGeometry.OpenKFlatTensorHomologyComparison | unclaimed | Transitive consumer; no declaration, proof, or import edit required. |
| Sheaf.AlgebraicGeometry.StrictPerfectTensorRelativeTorBound | unclaimed | Transitive consumer; no declaration, proof, or import edit required. |
| Sheaf.CategoryTheory.RingedAugmentedCechRestriction | unclaimed | Transitive consumer; no declaration, proof, or import edit required. |
| Sheaf.CategoryTheory.RingedCechCompletionUnitIdempotence | M9 | Transitive consumer; no declaration, proof, or import edit required. |
| Sheaf.Paper.FiniteCoefficientTensorCtf | unclaimed | Transitive consumer; no declaration, proof, or import edit required. |
| Sheaf.Paper.FinitePerfectQuotientModels | W6 | Transitive consumer; no declaration, proof, or import edit required. |
| Sheaf.Paper.FiniteTensorConstructibleCohomology | unclaimed | Transitive consumer; no declaration, proof, or import edit required. |
| Sheaf.Paper.LocallyConstantTensor | unclaimed | Transitive consumer; no declaration, proof, or import edit required. |
| Sheaf.Paper.NilpotentReductionLissity | unclaimed | Transitive consumer; no declaration, proof, or import edit required. |
| Sheaf.Paper.NilpotentReductionStep | unclaimed | Transitive consumer; no declaration, proof, or import edit required. |
| Sheaf.Paper.NormalizedTowerCommonLisseStrata | unclaimed | Transitive consumer; no declaration, proof, or import edit required. |
| Sheaf.Paper.ProEtaleRestrictedTensorFiniteLocalConstancy | unclaimed | Transitive consumer; no declaration, proof, or import edit required. |
| Sheaf.Paper.RingedLocalizationRHomCalculus | unclaimed | Transitive consumer; no declaration, proof, or import edit required. |
| Sheaf.Paper.RingedModelCurryingCoherence | unclaimed | Transitive consumer; no declaration, proof, or import edit required. |
| Sheaf.Paper.RingedModelRestriction | unclaimed | Transitive consumer; no declaration, proof, or import edit required. |
| Sheaf.Paper.SiteTensorLocalModelComparison | unclaimed | Transitive consumer; no declaration, proof, or import edit required. |

## Status

landed 20261020T144247-L-2259345 2026-10-20 (merge of deliver/F4/Sheaf.Algebra.Homology.OpenRestrictionTensorNatural)
