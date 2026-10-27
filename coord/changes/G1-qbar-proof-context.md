# AlgebraicGeometry.Scheme.qbar_properBaseChange

## Reason

The proof uses generic private localization and stage-system lemmas, and scoped
elaboration settings for the existing concrete categorical definitions. This record
covers the added section commands and local reducibility controls. The final instance
attribute is restored before the section ends. No existing public signature, instance, public import, target, or mathematical
object changes. The two definition bodies are factored through generic constructions
with precisely their original formulas; they remain definitionally equal to the originals. The new public
normalization theorem has its own new module and DAG node.

## Old

The original theorem signature, verbatim:

```lean
theorem qbar_properBaseChange [IsProper f] :
    ∃ P : PbcQbarExchangePresentation l Ω sq,
      (∀ K : pbcQbarCategory l Ω X, IsIso ((P.exchange).app K)) ∧
      (∀ (M : Padic.FiniteCoefficientFields l Ω) (K : pbcStageCategory l Ω X M),
        IsIso ((P.Ex.τ M).app K)) ∧
      (∀ (K : pbcQbarCategory l Ω X) (M : Padic.FiniteCoefficientFields l Ω)
        (h : K.stage ≤ M),
        (P.exchange).app K = PbcQbarExchangePresentation.atStage l Ω sq P K M h) ∧
      (∀ (K L : pbcQbarCategory l Ω X) (h : K ≅ L),
        (P.Rf.base.functor ⋙ P.Lg.base.functor).map h.hom ≫ (P.exchange).app L =
          (P.exchange).app K ≫
            (P.Lg'.base.functor ⋙ P.Rf'.base.functor).map h.hom)
```

The proof was `by sorry`; there were no private proof helpers in this module.
The original definition bodies were:

```lean
def exchange : P.Rf.base.functor ⋙ P.Lg.base.functor ⟶
    P.Lg'.base.functor ⋙ P.Rf'.base.functor :=
  (StageSystem.Morphism.functorCompIso P.Rf.base P.Lg.base).inv ≫
    StageSystem.Morphism.descNatTrans P.Ex ≫
      (StageSystem.Morphism.functorCompIso P.Lg'.base P.Rf'.base).hom

def atStage (K : pbcQbarCategory l Ω X) (M : Padic.FiniteCoefficientFields l Ω)
    (h : K.stage ≤ M) :
    (P.Rf.base.functor ⋙ P.Lg.base.functor).obj K ⟶
      (P.Lg'.base.functor ⋙ P.Rf'.base.functor).obj K :=
  StageSystem.PairCategory.mkHom M h h
    (((P.Rf.base.comp P.Lg.base).β h).hom.app K.obj ≫
      (P.Ex.τ M).app ((pbcScalarSystem l Ω X dX.out iX.out).T h |>.obj K.obj) ≫
        ((P.Lg'.base.comp P.Rf'.base).β h).inv.app K.obj)
```

## New

The retained theorem signature, verbatim:

```lean
theorem qbar_properBaseChange [IsProper f] :
    ∃ P : PbcQbarExchangePresentation l Ω sq,
      (∀ K : pbcQbarCategory l Ω X, IsIso ((P.exchange).app K)) ∧
      (∀ (M : Padic.FiniteCoefficientFields l Ω) (K : pbcStageCategory l Ω X M),
        IsIso ((P.Ex.τ M).app K)) ∧
      (∀ (K : pbcQbarCategory l Ω X) (M : Padic.FiniteCoefficientFields l Ω)
        (h : K.stage ≤ M),
        (P.exchange).app K = PbcQbarExchangePresentation.atStage l Ω sq P K M h) ∧
      (∀ (K L : pbcQbarCategory l Ω X) (h : K ≅ L),
        (P.Rf.base.functor ⋙ P.Lg.base.functor).map h.hom ≫ (P.exchange).app L =
          (P.exchange).app K ≫
            (P.Lg'.base.functor ⋙ P.Rf'.base.functor).map h.hom)
```

All added private helpers are proved. Local irreducibility controls also keep the
canonical small coefficient field, uniformizer and adic datum from being expanded
during matching. The local priority for `DivisionSemiring.to_moduleIsTorsionFree`
uses the direct field proof instead of exploring flat-module instances repeatedly.
The annihilator proof unfolds the datum and uniformizer explicitly where needed.
Local priorities also choose the published canonical Abelian and derived-category
interfaces for pro-etale ring modules. The private proof section temporarily disables
`AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint`, then restores it. Local
irreducibility controls prevent proof search from expanding the actual completion,
scalar comparisons, and descended transformation constructions. Declaration-local
transparency settings control elaboration only. The existing `exchange` and `atStage` definitions retain their signatures. Their
bodies now call the following generic constructions, which have the same formulas.
This removes repeated concrete category-instance conversion during proof matching.
The item compiled cleanly in 33.7 seconds after this refactoring. Both packet modules
also compiled together; the sole unchanged downstream consumer compiled in 5.0 seconds
against the packet. No consumer adaptation is necessary.

```lean
def pbcExchangeOfStageSystems
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C D E B : I → Type*} [∀ i, Category (C i)] [∀ i, Category (D i)]
    [∀ i, Category (E i)] [∀ i, Category (B i)]
    {S : StageSystem C} {T : StageSystem D} {U : StageSystem E} {V : StageSystem B}
    (F : StageSystem.Morphism S T) (G : StageSystem.Morphism T V)
    (H : StageSystem.Morphism S U) (J : StageSystem.Morphism U V)
    (τ : StageSystem.Morphism.Hom (F.comp G) (H.comp J)) :
    F.functor ⋙ G.functor ⟶ H.functor ⋙ J.functor :=
  (StageSystem.Morphism.functorCompIso F G).inv ≫
    StageSystem.Morphism.descNatTrans τ ≫
    (StageSystem.Morphism.functorCompIso H J).hom

def pbcExchangeAtStage
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C D E B : I → Type*} [∀ i, Category (C i)] [∀ i, Category (D i)]
    [∀ i, Category (E i)] [∀ i, Category (B i)]
    {S : StageSystem C} {T : StageSystem D} {U : StageSystem E} {V : StageSystem B}
    (F : StageSystem.Morphism S T) (G : StageSystem.Morphism T V)
    (H : StageSystem.Morphism S U) (J : StageSystem.Morphism U V)
    (τ : StageSystem.Morphism.Hom (F.comp G) (H.comp J))
    (K : S.PairCategory) (M : I) (h : K.stage ≤ M) :
    (F.functor ⋙ G.functor).obj K ⟶ (H.functor ⋙ J.functor).obj K :=
  StageSystem.PairCategory.mkHom M h h
    (((F.comp G).β h).hom.app K.obj ≫ (τ.τ M).app ((S.T h).obj K.obj) ≫
      ((H.comp J).β h).inv.app K.obj)

def exchange : P.Rf.base.functor ⋙ P.Lg.base.functor ⟶
    P.Lg'.base.functor ⋙ P.Rf'.base.functor :=
  pbcExchangeOfStageSystems P.Rf.base P.Lg.base P.Lg'.base P.Rf'.base P.Ex

def atStage (K : pbcQbarCategory l Ω X) (M : Padic.FiniteCoefficientFields l Ω)
    (h : K.stage ≤ M) :
    (P.Rf.base.functor ⋙ P.Lg.base.functor).obj K ⟶
      (P.Lg'.base.functor ⋙ P.Rf'.base.functor).obj K :=
  pbcExchangeAtStage P.Rf.base P.Lg.base P.Lg'.base P.Rf'.base P.Ex K M h
```

## Users

`tools/downstream.py Sheaf.Paper.QbarProperBaseChange --uses qbar_properBaseChange
PbcQbarExchangePresentation` reports one downstream module. Its source was read in
full; its two presentation references use the identical public interface. No consumer
adaptation is required. Claim holders are the current read-only coordination snapshot.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.QbarProperBaseChange | G1 | Generic construction factoring, private helpers and completed theorem proof. |
| Sheaf.Paper.GeometricFiberQbar | unclaimed | Definitionally identical objects and unchanged signatures; no adaptation. |

## Status

landed 20261024T014827-L-2277720 2026-10-24 (merge of deliver/G1/Sheaf.Paper.QbarProperBaseChange)
