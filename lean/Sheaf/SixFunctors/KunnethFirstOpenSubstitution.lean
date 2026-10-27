module

public import Sheaf.Paper.SixFunctorDatum
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.SixFunctorDualNotation
public import Sheaf.SixFunctors.OpenExternalTensorNormalization
public import Sheaf.SixFunctors.OpenTensorNormalization
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.ExchangeFunctoriality

/-! # First-open substitution for the specified relative product

Source: current blueprint, sec-six-functors/sk-thm-sf-kunneth-relative,
lem-sf-kunneth-coherence.proof.md, symmetry paragraph, reduction to proper morphisms
(blueprint: lem-sf-kunneth-first-open-substitution).

We expand the recorded canonical exchange/projection chain. The
lambda equation is expressed before its final common composition isomorphism:
its target is S_g R_s J_v D. Applying the canonical origin compositor identifies
this with S_{gq} D. Thus both equations retain the specified arrows, including the
signed symmetries, rather than merely asserting invertibility.
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

namespace AlgebraicGeometry.ProEtale.KunnethFirstOpen

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The specified proper direct-image exchange, in exact inverse-image coordinates.
Source: def-exchange-projection, direct-image mate formula, and proof step 2
(blueprint: lem-sf-kunneth-first-open-substitution). -/
def properExchange {U X Y B : Scheme.{u}} {r : U ⟶ X} {s : U ⟶ Y}
    {a : X ⟶ B} {g : Y ⟶ B} (sq : IsPullback r s a g) (M : FiniteD A X) :=
  (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).inv.app
      ((lowerStar (ModuleCat.{u + 1} A) a).rightDerivedFunctor.obj M) ≫
    (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app M ≫
    (lowerStar (ModuleCat.{u + 1} A) s).rightDerivedFunctor.map
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) r).hom.app M)

/-- The proper-first lambda before its final compositor, with g arbitrary.
This is Theta_g followed by S_g of exchange tensored with identity and PF_s.
Source: the displayed definition of lambda and proof steps 3 and 4
(blueprint: lem-sf-kunneth-first-open-substitution). -/
def properFirstChain {U X Y B : Scheme.{u}} {r : U ⟶ X} {s : U ⟶ Y}
    {a : X ⟶ B} {g : Y ⟶ B} (sq : IsPullback r s a g)
    (cg : Compactification g) (M : FiniteD A X) (L : FiniteD A Y) :=
  let Rg := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg
  let Ra := (lowerStar (ModuleCat.{u + 1} A) a).rightDerivedFunctor
  let Rs := (lowerStar (ModuleCat.{u + 1} A) s).rightDerivedFunctor
  let F := (FiniteOpenProduct.pull A r).obj M
  FiniteOpenProduct.sigma A B (Ra.obj M) (Rg.obj L) ≫
    ((projectionMapOfCompactification (ModuleCat.{u + 1} A) cg).app L).app (Ra.obj M) ≫
    Rg.map (FiniteOpenProduct.tensorMap A Y (𝟙 L)
      ((leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A) g).hom.app (Ra.obj M)) ≫
      FiniteOpenProduct.sigma A Y L ((FiniteOpenProduct.pull A g).obj (Ra.obj M)) ≫
      FiniteOpenProduct.tensorMap A Y (properExchange A sq M) (𝟙 L) ≫
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) s).app F).app L ≫
      Rs.map (FiniteOpenProduct.tensorMap A U (𝟙 F)
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) s).hom.app L)))

/-- The two substitution equations, using the canonical base-changed compactification.
Its compactifying scheme is U = bar X times_B Y, and its open is v = j times_B 1.
The local names only abbreviate actual constructions, never additional map data.
Source: both displayed equations and the definition of e1 in the node's statement
(blueprint: lem-sf-kunneth-first-open-substitution). -/
def Assertion
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (_S : SixFunctorDatum D C E n hn)
    {B X Xb Y : SixFunctorSpace D}
    (j : X ⟶ Xb) [IsOpenImmersion j.hom.left]
    (a : Xb ⟶ B) [IsProper a.hom.left] (g : Y ⟶ B)
    {T : Scheme.{u}} (p : T ⟶ X.obj.left) (q : T ⟶ Y.obj.left)
    (sq : IsPullback p q (j.hom.left ≫ a.hom.left) g.hom.left)
    (cg : Compactification g.hom.left)
    (K : finiteTorConstructibleCategory C.l E n hn X.obj.left)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) : Prop :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let A₀ := ULift.{u + 1, u} (Padic.coefficientExtensionRing C.l E n)
  let K₀ := (sixFunctorFiniteRealization D C E n hn X).inverse.obj K.obj
  let L₀ := (sixFunctorFiniteRealization D C E n hn Y).inverse.obj L.obj
  let cx : Compactification (j.hom.left ≫ a.hom.left) :=
    { Z := Xb.obj.left, i := j.hom.left, g := a.hom.left, comm := rfl,
      isProper := inferInstance, isOpenImmersion := inferInstance }
  let cq := cx.ofIsPullback sq
  let U := cq.Z
  let r : U ⟶ Xb.obj.left := pullback.fst a.hom.left g.hom.left
  let s : U ⟶ Y.obj.left := cq.g
  let v : T ⟶ U := cq.i
  let M := (FiniteOpenProduct.pull A₀ p).obj K₀
  let J := (finiteShriek A₀ j.hom.left).obj K₀
  let H := (FiniteOpenProduct.pull A₀ s).obj L₀
  let beta := (FiniteOpenProduct.beta A₀ p v j.hom.left r
    (cx.isPullback_i_ofIsPullback sq)).hom.app K₀
  let e₁ := FiniteOpenProduct.tensorMap A₀ U beta (𝟙 H) ≫
    FiniteOpenProduct.gamma A₀ v M H ≫
    (finiteShriek A₀ v).map
      (FiniteOpenProduct.tensorMap A₀ T (𝟙 M)
        ((FiniteOpenProduct.composeEq A₀ v s q cq.comm.symm).hom.app L₀))
  let Rf := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A₀) cx
  let Rq := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A₀) cq
  let Rg := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A₀) cg
  let ex :=
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A₀) g.hom.left).inv.app
        (Rf.obj K₀) ≫
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} A₀) sq cx).app K₀ ≫
      Rq.map ((leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A₀) p).hom.app K₀)
  (ex =
    properExchange A₀ (.of_hasPullback a.hom.left g.hom.left) J ≫
      (lowerStar (ModuleCat.{u + 1} A₀) s).rightDerivedFunctor.map beta) ∧
  (FiniteOpenProduct.sigma A₀ B.obj.left (Rf.obj K₀) (Rg.obj L₀) ≫
    ((projectionMapOfCompactification (ModuleCat.{u + 1} A₀) cg).app L₀).app (Rf.obj K₀) ≫
    Rg.map (FiniteOpenProduct.tensorMap A₀ Y.obj.left (𝟙 L₀)
      ((leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A₀) g.hom.left).hom.app (Rf.obj K₀)) ≫
      FiniteOpenProduct.sigma A₀ Y.obj.left L₀
        ((FiniteOpenProduct.pull A₀ g.hom.left).obj (Rf.obj K₀)) ≫
      FiniteOpenProduct.tensorMap A₀ Y.obj.left ex (𝟙 L₀) ≫
      ((projectionMapOfCompactification (ModuleCat.{u + 1} A₀) cq).app M).app L₀ ≫
      Rq.map (FiniteOpenProduct.tensorMap A₀ T (𝟙 M)
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A₀) q).hom.app L₀))) =
    properFirstChain A₀ (.of_hasPullback a.hom.left g.hom.left) cg J L₀ ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A₀) cg).map
        ((lowerStar (ModuleCat.{u + 1} A₀) s).rightDerivedFunctor.map e₁))

/-- First-open substitution for the specified exchange and relative product morphisms.
Source: current blueprint, sec-six-functors/sk-thm-sf-kunneth-relative,
lem-sf-kunneth-coherence.proof.md, symmetry paragraph, compactification reduction
(blueprint: lem-sf-kunneth-first-open-substitution).

Proof: Step 1 uses lem-sf-proetale-constructible-origin to place the finite-Tor
inputs in the etale-origin domain of thm-sf-comp-composition. Open base change
from lem-sf-open-tensor-normalization gives beta. Its composite with PF_v and
the pullback comparison for sv=q is exactly e1, by the identity-second-open
case of lem-sf-open-external-tensor-normalization.
Step 2 pastes the open and proper squares using clause 2 of fix-lem-exchanges.
For the compactification (j,id), def-exchange-projection reduces the proper
identity-square factor to the identity: both its unit and counit are the
identity and its pullback comparison is the canonical one. The remaining
exchange is beta by open-tensor normalization. Clause 4 of fix-lem-exchanges
identifies the compact-support comparisons. This gives the first equation.
Step 3 applies the (s,v) composition pentagon of prop-sf-pf-coherence and its
naturality square for beta. Substituting the first equation combines the two
maps inside S_s into e1, and gives PF_q(Ex_{aj,g} tensor 1) equal to
alpha_{s,v} S_s(e1) PF_s(Ex_{a,g} tensor 1).
Step 4 applies S_g and prepends Theta_g. Projection and signed-symmetry
naturality identify the source through alpha_{a,j}. Associativity of
thm-sf-comp-composition moves alpha_{s,v} through alpha_{g,q}; naturality
moves S_g S_s(e1) through alpha_{g,s}. Removing this common final isomorphism
leaves exactly the second equation here. No extra factor swap occurs, so
both Koszul signs are those of Theta_g. -/
theorem first_open_substitution
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorDatum D C E n hn)
    {B X Xb Y : SixFunctorSpace D}
    [IsSeparated B.obj.hom] [IsSeparated X.obj.hom]
    [IsSeparated Xb.obj.hom] [IsSeparated Y.obj.hom]
    (j : X ⟶ Xb) [IsOpenImmersion j.hom.left]
    (a : Xb ⟶ B) [IsProper a.hom.left]
    (g : Y ⟶ B) [IsSeparated g.hom.left]
    [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    {T : Scheme.{u}} (p : T ⟶ X.obj.left) (q : T ⟶ Y.obj.left)
    (sq : IsPullback p q (j.hom.left ≫ a.hom.left) g.hom.left)
    (cg : Compactification g.hom.left)
    (K : finiteTorConstructibleCategory C.l E n hn X.obj.left)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    Assertion S j a g p q sq cg K L := by
  sorry

end AlgebraicGeometry.ProEtale.KunnethFirstOpen
