# AlgebraicGeometry.ProEtale.VaryingRing.moduleAlpha_vertical and moduleAlpha_horizontal

## Reason

The two completed proofs use private categorical transport helpers with independent
object and morphism universes. Local variables and local irreducibility attributes
keep their comparison equations from unfolding large derived-category definitions.
The static command scan requests this record for these local proof commands.
All existing theorem signatures, definitions, public imports, and global attributes
remain identical. No target statement or definition in a target statement changes.

## Old

The original module had no `OrdinaryPastingProofs`, `OrdinaryVerticalTransport`, or
`OrdinaryHorizontalTransport` sections and no corresponding private helper variables.
The two original declarations were exactly:

```lean
theorem moduleAlpha_vertical {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (i : C ⟶ D) (j : E ⟶ F)
    (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (N : Modules R φ E) :
    (moduleGComp R φ p₁ p₂).hom.app ((extension R φ j).obj N) ≫
        (pull R φ p₁).map ((moduleAlpha R φ i r₂ p₂ j h₂).app N) ≫
        (moduleAlpha R φ k r₁ p₁ i h₁).app ((pull R φ r₂).obj N) =
      (moduleAlpha R φ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app N ≫
        (extension R φ k).map ((moduleGComp R φ r₁ r₂).hom.app N) := by
  sorry

theorem moduleAlpha_horizontal {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C) (p : B₀ ⟶ D) (q : E ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
    (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (N : Modules R φ C) :
    (pull R φ q).map ((moduleJComp R φ i j).hom.app N) ≫
        (moduleAlpha R φ (k ≫ l) r q (i ≫ j) h).app N =
      (moduleAlpha R φ l p q j h₂).app ((extension R φ i).obj N) ≫
        (extension R φ l).map ((moduleAlpha R φ k r p i h₁).app N) ≫
        (moduleJComp R φ k l).hom.app ((pull R φ r).obj N) := by
  sorry
```

## New

The same signatures now have complete proofs from ordinaryClopenEvaluation, the
strict-tower pasting laws, finite categorical transport, and componentwise
faithfulness. The added outer local commands are exactly:

```lean
section OrdinaryPastingProofs
attribute [local irreducible] ordinaryRealization ordinaryPullComparison ordinaryOpenComparison
  Functor.leftAdjoint
  StrictTower.G StrictTower.J
  StrictTower.alpha StrictTower.gComp StrictTower.jComp
```

The two nested sections bind category and functor variables only for their private
transport lemmas. Every such section ends before the existing public declarations
outside OrdinaryPastingProofs. The attributes are local. The proof-only import of
Sheaf.AlgebraicGeometry.VaryingRingOrdinaryClopenEvaluation supplies the new comparison
API and its one named single-square hole, recorded by
lem-sp-varying-ring-ordinary-clopen-evaluation. That new module also contains a
proved actual realization construction and ordinary pullback-compositor normalization.
No existing data definition is repaired or replaced.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting | C8 | Uses the local proof commands and private helpers; public signatures unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingOrdinaryClopenEvaluation | C8, new | Provides the separately recorded comparison API; no existing consumer to adapt. |

The added helpers are private and the attributes and variables are local, so no
external module can inherit these commands or mention the helper names. Existing
importers retain exactly the same statements and definitions. No downstream source
adaptation is required, and no module held by another group is edited.

## Status

landed 20261021T022432-L-2846658 2026-10-21 (merge of deliver/C8/Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting)
