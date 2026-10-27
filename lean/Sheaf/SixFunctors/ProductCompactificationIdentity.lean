module

public import Sheaf.Paper.SixFunctorDatum
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.SixFunctorDualNotation
public import Sheaf.SixFunctors.OpenExternalTensorNormalization
import Sheaf.Paper.ExchangeFunctoriality
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.CompactificationCoherence
import Sheaf.Paper.CanonicalOriginCompactSupportComposition

/-! # Product compactification and the specified exchange/projection composite

Source: current blueprint, sec-six-functors/sk-thm-sf-kunneth-relative,
lem-sf-kunneth-coherence.proof.md, symmetry paragraph: reduction to proper maps
(blueprint: lem-sf-product-compactification-identity).

All arrows below are evaluated in the canonical fixed-scalar presentation of the
finite coefficient category. Origin witnesses only evaluate the supplied compositor
and compactification comparisons; no arrow or comparison is supplied as free data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization WeilConjectures
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.ProductCompactification

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The recorded projection map, with exact inverse-image coordinates at its target.
Source: def-exchange-projection, projection formula composite
(blueprint: lem-sf-product-compactification-identity). -/
def projection {V W : Scheme.{u}} {h : V ⟶ W} (c : Compactification h)
    (K : FiniteD A V) (N : FiniteD A W) :=
  ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app K).app N ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
      (FiniteOpenProduct.tensorMap A V (𝟙 K)
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) h).hom.app N))

/-- Psi is signed symmetry, the specified projection, and the image of signed symmetry.
Source: the displayed definition of Psi in the node's statement
(blueprint: lem-sf-product-compactification-identity). -/
def psi {V W : Scheme.{u}} {h : V ⟶ W} (c : Compactification h)
    (F : FiniteD A W) (L : FiniteD A V) :=
  FiniteOpenProduct.sigma A W F
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj L) ≫
    projection A c L F ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
      (FiniteOpenProduct.sigma A V L ((FiniteOpenProduct.pull A h).obj F))

/-- The specified compact-support exchange in exact inverse-image coordinates.
Source: def-exchange-projection, chosen-compactification exchange
(blueprint: lem-sf-product-compactification-identity). -/
def exchange {T X Y B : Scheme.{u}} {p : T ⟶ X} {q : T ⟶ Y}
    {f : X ⟶ B} {g : Y ⟶ B} (sq : IsPullback p q f g)
    (cf : Compactification f) (K : FiniteD A X) :=
  (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).inv.app
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj K) ≫
    (rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} A) sq cf).app K ≫
    (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) (cf.ofIsPullback sq)).map
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p).hom.app K)

/-- Lambda before applying alpha: the actual exchange/projection chain, not its inverse.
Source: the displayed definition of lambda in the node's statement
(blueprint: lem-sf-product-compactification-identity). -/
def chain {T X Y B : Scheme.{u}} {p : T ⟶ X} {q : T ⟶ Y}
    {f : X ⟶ B} {g : Y ⟶ B} (sq : IsPullback p q f g)
    (cf : Compactification f) (cg : Compactification g)
    (K : FiniteD A X) (L : FiniteD A Y) :=
  psi A cg ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj K) L ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).map
      (FiniteOpenProduct.tensorMap A Y (exchange A sq cf K) (𝟙 L) ≫
        projection A (cf.ofIsPullback sq) ((FiniteOpenProduct.pull A p).obj K) L)

/-- Evaluate the supplied origin compositor at any chosen presentation of its input.
Source: thm-sf-comp-composition and the node's alpha_{g,q}
(blueprint: lem-sf-product-compactification-identity). -/
def compositor {T Y B : Scheme.{u}} {q : T ⟶ Y} {g : Y ⟶ B}
    [QuasiCompact q] [QuasiCompact g]
    (cq : Compactification q) (cg : Compactification g) (ct : Compactification (q ≫ g))
    (M : FiniteD A T)
    (O : _root_.DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (e : (coherenceBoundedSiteFunctor A T).obj O ≅ M) :=
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).map
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cq).map e.inv) ≫
    coherenceProEtaleCompositor A cq cg ct O ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) ct).map e.hom

/-- The specified lambda, with alpha last and D the tensor of the two projection pullbacks.
Source: the displayed lambda formula, read right to left
(blueprint: lem-sf-product-compactification-identity). -/
def lambda {T X Y B : Scheme.{u}} {p : T ⟶ X} {q : T ⟶ Y}
    {f : X ⟶ B} {g : Y ⟶ B} [QuasiCompact q] [QuasiCompact g]
    (sq : IsPullback p q f g) (cf : Compactification f) (cg : Compactification g)
    (ct : Compactification (q ≫ g)) (K : FiniteD A X) (L : FiniteD A Y)
    (O : _root_.DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (e : (coherenceBoundedSiteFunctor A T).obj O ≅
      FiniteOpenProduct.tensor A T
        ((FiniteOpenProduct.pull A p).obj K) ((FiniteOpenProduct.pull A q).obj L)) :=
  chain A sq cf cg K L ≫ compositor A (cf.ofIsPullback sq) cg ct _ O e

/-- The direct-image projection in the same exact inverse-image coordinates.
Source: proper specialization in the node and def-exchange-projection
(blueprint: lem-sf-product-compactification-identity). -/
def directProjection {V W : Scheme.{u}} (h : V ⟶ W)
    (K : FiniteD A V) (N : FiniteD A W) :=
  ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) h).app K).app N ≫
    (lowerStar (ModuleCat.{u + 1} A) h).rightDerivedFunctor.map
      (FiniteOpenProduct.tensorMap A V (𝟙 K)
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) h).hom.app N))

/-- The proper exchange/projection composite, including both signed symmetries and
proper direct-image composition. Source: lambda_{a,b} in the node's equation
(blueprint: lem-sf-product-compactification-identity). -/
def properLambda {T X Y B : Scheme.{u}} {p : T ⟶ X} {q : T ⟶ Y}
    {f : X ⟶ B} {g : Y ⟶ B} (sq : IsPullback p q f g)
    (K : FiniteD A X) (L : FiniteD A Y) :=
  FiniteOpenProduct.sigma A B
      ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj K)
      ((lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj L) ≫
    directProjection A g L
      ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj K) ≫
    (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.map
      (FiniteOpenProduct.sigma A Y L _ ≫
        FiniteOpenProduct.tensorMap A Y
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).inv.app _ ≫
            (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app K ≫
            (lowerStar (ModuleCat.{u + 1} A) q).rightDerivedFunctor.map
              ((leftDerivedUpperStarIsoMapDerivedCategory
                (ModuleCat.{u + 1} A) p).hom.app K)) (𝟙 L) ≫
        directProjection A q ((FiniteOpenProduct.pull A p).obj K) L) ≫
    (finiteDirectImageComposition A q g).inv.app
      (FiniteOpenProduct.tensor A T
        ((FiniteOpenProduct.pull A p).obj K) ((FiniteOpenProduct.pull A q).obj L))

/-- Canonical comparison between two candidates, evaluated on an origin presentation.
It is the proper-composition/proper-open refinement comparison by the recorded
compactification coherence theorem. Source: prop-compactification-coherence-detailed
(blueprint: lem-sf-product-compactification-identity). -/
def change {X B : Scheme.{u}} {f : X ⟶ B} [QuasiCompact f]
    (c c' : Compactification f) (M : FiniteD A X)
    (O : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (e : (coherenceBoundedSiteFunctor A X).obj O ≅ M) :=
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).mapIso e.symm ≪≫
    (coherenceBoundaryComponent A c O).symm ≪≫
    (coherenceBoundedSiteFunctor A B).mapIso ((coherenceEtaleChangeIso A c c').app O) ≪≫
    coherenceBoundaryComponent A c' O ≪≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c').mapIso e

/-- A chosen open/proper factorization as the existing compactification object.
Source: f=aj, g=bk in the node (blueprint: lem-sf-product-compactification-identity). -/
def factorCompactification {X Xb B : Scheme.{u}} (j : X ⟶ Xb) (a : Xb ⟶ B)
    [IsOpenImmersion j] [IsProper a] : Compactification (j ≫ a) where
  Z := Xb
  i := j
  g := a
  comm := rfl
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- The product compactification with its canonical product open and proper map.
Source: bar T, u and c in the node (blueprint: lem-sf-product-compactification-identity). -/
def productCompactification {X Y Xb Yb T Tb B : Scheme.{u}}
    {j : X ⟶ Xb} {k : Y ⟶ Yb} [IsOpenImmersion j] [IsOpenImmersion k]
    (a : Xb ⟶ B) (b : Yb ⟶ B) [IsProper a] [IsProper b]
    (d : OpenExternalTensor.Diagram j k T Tb) (sq : IsPullback d.pb d.qb a b) :
    Compactification (d.q ≫ k ≫ b) := by
  haveI : IsProper d.qb := MorphismProperty.of_isPullback (P := @IsProper) sq inferInstance
  exact {
    Z := Tb
    i := d.u
    g := d.qb ≫ b
    comm := by simp only [← Category.assoc, d.right]
    isProper := inferInstance
    isOpenImmersion := inferInstance }

/-- Quasi-compactness inherited from the finite-type structure maps over the field.
This only exposes the existing cancellation lemma for morphisms in SixFunctorSpace.
Source: the separated finite-type setting of the node
(blueprint: lem-sf-product-compactification-identity). -/
instance spaceQuasiCompact {D : FiniteFieldDatum.{u}} {X Y : SixFunctorSpace D}
    [IsSeparated Y.obj.hom] (f : X ⟶ Y) : QuasiCompact f.hom.left := by
  have : QuasiCompact (f.hom.left ≫ Y.obj.hom) := by
    rw [Over.w f.hom]
    exact X.property.2
  exact QuasiCompact.of_comp f.hom.left Y.obj.hom

/-- The full product identity and its refinement square in canonical fixed-scalar
coordinates. The universally quantified origin presentations only evaluate canonical
comparisons; they neither choose arbitrary maps nor restrict the finite-Tor inputs.
Source: all clauses of the node's statement
(blueprint: lem-sf-product-compactification-identity). -/
def Assertion
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (_S : SixFunctorDatum D C E n hn)
    {B X Y Xb Yb : SixFunctorSpace D}
    [IsSeparated B.obj.hom]
    (j : X ⟶ Xb) (k : Y ⟶ Yb)
    [IsOpenImmersion j.hom.left] [IsOpenImmersion k.hom.left]
    (a : Xb ⟶ B) (b : Yb ⟶ B) [IsProper a.hom.left] [IsProper b.hom.left]
    {T Tb : Scheme.{u}} (d : OpenExternalTensor.Diagram j.hom.left k.hom.left T Tb)
    (barSquare : IsPullback d.pb d.qb a.hom.left b.hom.left)
    (square : IsPullback d.p d.q (j.hom.left ≫ a.hom.left) (k.hom.left ≫ b.hom.left))
    (K : finiteTorConstructibleCategory C.l E n hn X.obj.left)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) : Prop :=
  letI : QuasiCompact (j.hom.left ≫ a.hom.left) := spaceQuasiCompact (j ≫ a)
  letI : QuasiCompact (k.hom.left ≫ b.hom.left) := spaceQuasiCompact (k ≫ b)
  letI : QuasiCompact d.q := MorphismProperty.of_isPullback (P := @QuasiCompact)
    square inferInstance
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let A₀ := ULift.{u + 1, u} (Padic.coefficientExtensionRing C.l E n)
  let K₀ := (sixFunctorFiniteRealization D C E n hn X).inverse.obj K.obj
  let L₀ := (sixFunctorFiniteRealization D C E n hn Y).inverse.obj L.obj
  let M := OpenExternalTensor.inside A₀ d K₀ L₀
  let cx := factorCompactification j.hom.left a.hom.left
  let cy := factorCompactification k.hom.left b.hom.left
  let ct := productCompactification a.hom.left b.hom.left d barSquare
  ∀ (OK : _root_.DerivedCategory.Plus
      (Sheaf X.obj.left.smallEtaleTopology (ModuleCat.{u + 1} A₀)))
    (OL : _root_.DerivedCategory.Plus
      (Sheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} A₀)))
    (OM : _root_.DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A₀)))
    (eK : (coherenceBoundedSiteFunctor A₀ X.obj.left).obj OK ≅ K₀)
    (eL : (coherenceBoundedSiteFunctor A₀ Y.obj.left).obj OL ≅ L₀)
    (eM : (coherenceBoundedSiteFunctor A₀ T).obj OM ≅ M),
    (lambda A₀ square cx cy ct K₀ L₀ OM eM =
      properLambda A₀ barSquare ((finiteShriek A₀ j.hom.left).obj K₀)
          ((finiteShriek A₀ k.hom.left).obj L₀) ≫
        (lowerStar (ModuleCat.{u + 1} A₀) (d.qb ≫ b.hom.left)).rightDerivedFunctor.map
          (OpenExternalTensor.comparison A₀ d K₀ L₀)) ∧
    (∀ (cx' : Compactification (j.hom.left ≫ a.hom.left))
      (cy' : Compactification (k.hom.left ≫ b.hom.left))
      (ct' : Compactification (d.q ≫ k.hom.left ≫ b.hom.left)),
      lambda A₀ square cx' cy' ct' K₀ L₀ OM eM =
        FiniteOpenProduct.tensorMap A₀ B.obj.left
          (change A₀ cx' cx K₀ OK eK).hom (change A₀ cy' cy L₀ OL eL).hom ≫
        lambda A₀ square cx cy ct K₀ L₀ OM eM ≫ (change A₀ ct ct' M OM eM).hom)

/-- Product compactification identity for the specified exchange/projection composite,
including compatibility with all compactification comparisons through common refinements.
Source: current blueprint, sec-six-functors/sk-thm-sf-kunneth-relative,
lem-sf-kunneth-coherence.proof.md, symmetry paragraph, reduction to proper maps
(blueprint: lem-sf-product-compactification-identity).

Proof: Step 1 applies lem-sf-kunneth-first-open-substitution to g=bk and the
intermediate product bar X times_B Y. The canonical origin witnesses exist by
lem-sf-proetale-constructible-origin, so thm-sf-comp-composition applies. It gives
lambda_{aj,bk}=S_b J_k S_s(e1) lambda_{a,bk}(J_j K,L).
Step 2 applies lem-sf-kunneth-second-open-substitution to M=J_j K. Its proper/open
square includes both signed symmetries and gives
lambda_{a,bk}=S_b S_Q(e2) lambda_{a,b}(J_j K,J_k L).
Step 3 substitutes this equation into Step 1. Naturality and associativity of
thm-sf-comp-composition identify the product-open tensor arrow with J_w(e1)e2.
The opposite-factorization clause of lem-sf-open-external-tensor-normalization
identifies it with the recorded comparison e_{j,k}. With bQ=c this is precisely
the first equality, using the supplied source and target compactification comparisons.
Step 4 applies the equality to each compactification in a refinement. Clause 4 of
fix-lem-exchanges intertwines exchange with refinement, and prop-sf-pf-coherence
intertwines projection. Tensor symmetry is natural and the associative compositors
of thm-sf-comp-composition are choice independent, giving the second displayed
square. Transitivity and independence of the common refinement in
prop-compactification-coherence-detailed extend it to every comparison in change.
No invertibility claim is substituted for equality of the specified arrows. -/
theorem product_compactification_identity
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorDatum D C E n hn)
    {B X Y Xb Yb : SixFunctorSpace D}
    [IsSeparated B.obj.hom] [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    [IsSeparated Xb.obj.hom] [IsSeparated Yb.obj.hom]
    (j : X ⟶ Xb) (k : Y ⟶ Yb)
    [IsOpenImmersion j.hom.left] [IsOpenImmersion k.hom.left]
    (a : Xb ⟶ B) (b : Yb ⟶ B) [IsProper a.hom.left] [IsProper b.hom.left]
    {T Tb : Scheme.{u}} (d : OpenExternalTensor.Diagram j.hom.left k.hom.left T Tb)
    (barSquare : IsPullback d.pb d.qb a.hom.left b.hom.left)
    (square : IsPullback d.p d.q (j.hom.left ≫ a.hom.left) (k.hom.left ≫ b.hom.left))
    (K : finiteTorConstructibleCategory C.l E n hn X.obj.left)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    Assertion S j k a b d barSquare square K L := by
  sorry

end AlgebraicGeometry.ProEtale.ProductCompactification
