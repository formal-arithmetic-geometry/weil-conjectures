# WeilConjectures.PurityFiniteSetting ordinary external-product data

## Reason

The three strictly smaller transpose/comparison statements need the existing data while the
item theorem imports those statements. Extract the data into a public prerequisite to avoid
an import cycle. All existing data bodies and signatures are preserved; the item reexports
the new prerequisite, so its former public declarations remain available to every importer.
The two new explicit evaluation composites contain no proof holes or chosen witnesses.

## Old

The following declarations lived in Sheaf.SmoothPurity.OrdinaryTripleProductTranspose:

```lean
/-- Abbreviation for the ordinary constant-coefficient category, with the standard size lift.
Source: def-pur-conventions (blueprint: lem-pur-ordinary-triple-product-transpose). -/
abbrev ordinaryCategory (X : Scheme.{u}) :=
  DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))

/-- The existing K-flat pullback, without restricting its unbounded domain.
Source: def-weil-pbc-proetale-operations
(blueprint: lem-pur-ordinary-triple-product-transpose). -/
abbrev ordinaryPull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor

/-- The existing K-injective direct image on the ordinary unbounded category.
Source: def-weil-pbc-proetale-operations
(blueprint: lem-pur-ordinary-triple-product-transpose). -/
abbrev ordinaryPush {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (lowerStar (ModuleCat.{u + 1} P.Coefficient) f).rightDerivedFunctor

/-- The existing derived adjunction, with its specified unit and counit.
Source: def-weil-pbc-proetale-operations
(blueprint: lem-pur-ordinary-triple-product-transpose). -/
abbrev ordinaryAdj {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) f

/-- The specified pullback-tensor comparison, evaluated at two objects.
Source: Stacks 07A4 (blueprint: lem-pur-ordinary-triple-product-transpose). -/
abbrev ordinaryTensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K L : P.ordinaryCategory Y) :
    (P.ordinaryPull f).obj (K ⊗ L) ≅
      (P.ordinaryPull f).obj K ⊗ (P.ordinaryPull f).obj L :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  letI : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) f K L

/-- The specified pullback composition comparison.
Source: Stacks 07A4 (blueprint: lem-pur-ordinary-triple-product-transpose). -/
abbrev ordinaryPullComposition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f g

/-- Transport the existing direct image along equality of scheme maps.
Source: canonical composition identifications in the blueprint's coherence proof
(blueprint: lem-pur-ordinary-triple-product-transpose). -/
def ordinaryPushCongr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    P.ordinaryPush f ≅ P.ordinaryPush g :=
  h ▸ Iso.refl _

/-- The external product on a specified fibre-product cone.
Source: def-pc-fibre-product and the node's boxtimes formula
(blueprint: lem-pur-ordinary-triple-product-transpose). -/
abbrev ordinaryExternal {W X Y : Scheme.{u}} (r : W ⟶ X) (t : W ⟶ Y)
    (K : P.ordinaryCategory X) (L : P.ordinaryCategory Y) :=
  (P.ordinaryPull r).obj K ⊗ (P.ordinaryPull t).obj L

/-- The actual ordinary product: two signed swaps, projection, exchange tensored with
identity, projection again, then the inverse specified direct-image compositor.
Its codomain uses w = t followed by v, the common structure map of the square.
Source: def-exchange-projection and the node's displayed Omega formula
(blueprint: lem-pur-ordinary-triple-product-transpose). -/
abbrev ordinaryProduct {W X Y B : Scheme.{u}} {r : W ⟶ X} {t : W ⟶ Y}
    {f : X ⟶ B} {g : Y ⟶ B} (sq : IsPullback r t f g)
    (K : P.ordinaryCategory X) (L : P.ordinaryCategory Y) :
    (P.ordinaryPush f).obj K ⊗ (P.ordinaryPush g).obj L ⟶
      (P.ordinaryPush (t ≫ g)).obj (P.ordinaryExternal r t K L) :=
  finiteProductOrdinary P.Coefficient f g sq K L

/-- Chosen double products and one common triple product, with its four cartesian cones.
The last two equations say that both cones have the same second and third projections;
the first projection is literally a followed by p1. These are precisely the canonical
identifications of the two parenthesized products, not extra geometric hypotheses.
Source: def-pc-fibre-product; blueprint coherence proof, associativity clause
(blueprint: lem-pur-ordinary-triple-product-transpose). -/
structure OrdinaryTripleProductDiagram {X₁ X₂ X₃ B : Scheme.{u}}
    (f₁ : X₁ ⟶ B) (f₂ : X₂ ⟶ B) (f₃ : X₃ ⟶ B) where
  X₁₂ : Scheme.{u}
  X₂₃ : Scheme.{u}
  T : Scheme.{u}
  p₁ : X₁₂ ⟶ X₁
  p₂ : X₁₂ ⟶ X₂
  q₂ : X₂₃ ⟶ X₂
  q₃ : X₂₃ ⟶ X₃
  a : T ⟶ X₁₂
  b : T ⟶ X₂₃
  c : T ⟶ X₃
  square₁₂ : IsPullback p₁ p₂ f₁ f₂
  square₂₃ : IsPullback q₂ q₃ f₂ f₃
  squareL : IsPullback a c (p₂ ≫ f₂) f₃
  squareR : IsPullback (a ≫ p₁) b f₁ (q₂ ≫ f₂)
  second : b ≫ q₂ = a ≫ p₂
  third : b ≫ q₃ = c

variable {X₁ X₂ X₃ B : Scheme.{u}} {f₁ : X₁ ⟶ B} {f₂ : X₂ ⟶ B} {f₃ : X₃ ⟶ B}
    (d : OrdinaryTripleProductDiagram f₁ f₂ f₃)
    (K : P.ordinaryCategory X₁) (L : P.ordinaryCategory X₂) (M : P.ordinaryCategory X₃)

/-- The common, left-associated triple external tensor, with its ordered projections.
Source: the node's common codomain (blueprint: lem-pur-ordinary-triple-product-transpose). -/
abbrev ordinaryTripleObject :=
  ((P.ordinaryPull (d.a ≫ d.p₁)).obj K ⊗ (P.ordinaryPull (d.a ≫ d.p₂)).obj L) ⊗
    (P.ordinaryPull d.c).obj M

/-- Canonical identification of the left iterated external tensor with the common tensor.
Source: Stacks 07A4, pullback and tensor composition
(blueprint: lem-pur-ordinary-triple-product-transpose). -/
def ordinaryTripleLeftIdentification :
    P.ordinaryExternal d.a d.c (P.ordinaryExternal d.p₁ d.p₂ K L) M ≅
      P.ordinaryTripleObject d K L M :=
  tensorIso
    (P.ordinaryTensorComparison d.a _ _ ≪≫ tensorIso
      ((P.ordinaryPullComposition d.a d.p₁).symm.app K)
      ((P.ordinaryPullComposition d.a d.p₂).symm.app L)) (Iso.refl _)

/-- Canonical identification of the right iterated external tensor with the common tensor.
It retains the tensor associator and the equations identifying all three projections.
Source: Stacks 07A4; fibre-product associativity
(blueprint: lem-pur-ordinary-triple-product-transpose). -/
def ordinaryTripleRightIdentification :
    P.ordinaryExternal (d.a ≫ d.p₁) d.b K (P.ordinaryExternal d.q₂ d.q₃ L M) ≅
      P.ordinaryTripleObject d K L M :=
  tensorIso (Iso.refl _)
    (P.ordinaryTensorComparison d.b _ _ ≪≫ tensorIso
      (((P.ordinaryPullComposition d.b d.q₂).symm ≪≫
        leftDerivedUpperStarCongr (ModuleCat.{u + 1} P.Coefficient) d.second).app L)
      (((P.ordinaryPullComposition d.b d.q₃).symm ≪≫
        leftDerivedUpperStarCongr (ModuleCat.{u + 1} P.Coefficient) d.third).app M)) ≪≫
    (α_ _ _ _).symm

/-- Theta_L, with the canonical target and direct-image identifications inserted.
Source: the node's first iterated Omega formula
(blueprint: lem-pur-ordinary-triple-product-transpose). -/
def ordinaryTripleLeft :
    ((P.ordinaryPush f₁).obj K ⊗ (P.ordinaryPush f₂).obj L) ⊗
        (P.ordinaryPush f₃).obj M ⟶
      (P.ordinaryPush (d.a ≫ (d.p₂ ≫ f₂))).obj (P.ordinaryTripleObject d K L M) :=
  (P.ordinaryProduct d.square₁₂ K L ⊗ₘ 𝟙 _) ≫
    P.ordinaryProduct d.squareL (P.ordinaryExternal d.p₁ d.p₂ K L) M ≫
    (P.ordinaryPush (d.c ≫ f₃)).map (P.ordinaryTripleLeftIdentification d K L M).hom ≫
    (P.ordinaryPushCongr d.squareL.w.symm).hom.app _

/-- Theta_R, with the source associator and the canonical common-target identifications.
Source: the node's second iterated Omega formula
(blueprint: lem-pur-ordinary-triple-product-transpose). -/
def ordinaryTripleRight :
    ((P.ordinaryPush f₁).obj K ⊗ (P.ordinaryPush f₂).obj L) ⊗
        (P.ordinaryPush f₃).obj M ⟶
      (P.ordinaryPush (d.a ≫ (d.p₂ ≫ f₂))).obj (P.ordinaryTripleObject d K L M) :=
  (α_ _ _ _).hom ≫
    (𝟙 _ ⊗ₘ (P.ordinaryProduct d.square₂₃ L M ≫
      (P.ordinaryPushCongr d.square₂₃.w.symm).hom.app _)) ≫
    P.ordinaryProduct d.squareR K (P.ordinaryExternal d.q₂ d.q₃ L M) ≫
    (P.ordinaryPush (d.b ≫ (d.q₂ ≫ f₂))).map
      (P.ordinaryTripleRightIdentification d K L M).hom ≫
    (P.ordinaryPushCongr (d.squareR.w.symm.trans
      ((Category.assoc d.a d.p₁ f₁).trans
        (congrArg (fun z ↦ d.a ≫ z) d.square₁₂.w)))).hom.app _

/-- Pullback along the common structure map, factored through a specified projection.
Only equality transport and the canonical pullback compositor enter this isomorphism.
Source: the node's specified rho comparison
(blueprint: lem-pur-ordinary-triple-product-transpose). -/
def ordinaryTripleFactor {T X : Scheme.{u}} (r : T ⟶ X) (f : X ⟶ B)
    (v : T ⟶ B) (h : v = r ≫ f) :
    P.ordinaryPull v ≅ P.ordinaryPull f ⋙ P.ordinaryPull r :=
  leftDerivedUpperStarCongr (ModuleCat.{u + 1} P.Coefficient) h ≪≫
    P.ordinaryPullComposition r f

/-- The specified triple transpose: split tensor, factor each pullback, then apply
exactly the three pulled-back adjunction counits, in order, without exchanging factors.
Source: the node's displayed three-counit arrow
(blueprint: lem-pur-ordinary-triple-product-transpose). -/
def ordinaryTripleCounit :
    (P.ordinaryPull (d.a ≫ (d.p₂ ≫ f₂))).obj
        (((P.ordinaryPush f₁).obj K ⊗ (P.ordinaryPush f₂).obj L) ⊗
          (P.ordinaryPush f₃).obj M) ⟶ P.ordinaryTripleObject d K L M :=
  let F₁ := (P.ordinaryPush f₁).obj K
  let F₂ := (P.ordinaryPush f₂).obj L
  let F₃ := (P.ordinaryPush f₃).obj M
  let v := d.a ≫ (d.p₂ ≫ f₂)
  let e₁ := (P.ordinaryTripleFactor (d.a ≫ d.p₁) f₁ v
    ((congrArg (fun z ↦ d.a ≫ z) d.square₁₂.w.symm).trans
      (Category.assoc d.a d.p₁ f₁).symm)).hom.app F₁
  let e₂ := (P.ordinaryTripleFactor (d.a ≫ d.p₂) f₂ v
    (Category.assoc d.a d.p₂ f₂).symm).hom.app F₂
  let e₃ := (P.ordinaryTripleFactor d.c f₃ v d.squareL.w).hom.app F₃
  (P.ordinaryTensorComparison v (F₁ ⊗ F₂) F₃).hom ≫
    ((P.ordinaryTensorComparison v F₁ F₂).hom ⊗ₘ 𝟙 _) ≫
    ((e₁ ⊗ₘ e₂) ⊗ₘ e₃) ≫
    (((P.ordinaryPull (d.a ≫ d.p₁)).map ((P.ordinaryAdj f₁).counit.app K) ⊗ₘ
      (P.ordinaryPull (d.a ≫ d.p₂)).map ((P.ordinaryAdj f₂).counit.app L)) ⊗ₘ
      (P.ordinaryPull d.c).map ((P.ordinaryAdj f₃).counit.app M))

```

## New

Those exact declarations now live in Sheaf.SmoothPurity.OrdinaryProductTransposeData,
publicly imported by the original module. Only their documentation node tags change to the
new definition node. The original theorem's signature is unchanged. Two new public
composites, ordinaryBinaryEvaluation and ordinaryTripleEvaluation, generalize the stated
counit composites to arbitrary input maps; both are irreducible to keep categorical rewriting from unfolding the full derived operations;
their bodies use only specified existing
pullback/tensor comparisons and functor maps. No definition chooses data from an unproved
existence statement.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.SmoothPurity.OrdinaryTripleProductTranspose | H3 | Publicly reexports its data and proves its unchanged theorem from smaller obligations. |
| Sheaf.SmoothPurity.OrdinaryProductTransposeData | new in H3 | Owns the unchanged concrete data and the two new explicit evaluation composites. |
| Sheaf.SmoothPurity.OrdinaryBinaryProductTranspose | new in H3 | Uses the data for the strictly binary transpose assertion. |
| Sheaf.SmoothPurity.OrdinaryTripleLeftComparison | new in H3 | Uses only the pullback/tensor part of the data. |
| Sheaf.SmoothPurity.OrdinaryTripleRightComparison | new in H3 | Uses only the pullback/tensor part of the data. |

The read-only downstream.py query found zero existing importers of the item module;
text search likewise found no external uses of its data declarations. The DAG parent
lem-pur-even-line-product-integration-symmetry still needs the item theorem; it is preserved.
No source-library file is changed, and no consumer requires a forced adaptation.

## Status

landed 20261025T211038-L-3767432 2026-10-25 (merge of deliver/H3/Sheaf.SmoothPurity.OrdinaryTripleProductTranspose)
