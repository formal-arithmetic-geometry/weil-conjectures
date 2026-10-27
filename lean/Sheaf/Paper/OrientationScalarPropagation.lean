module

public import Sheaf.Paper.FiniteFieldFiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.SecSmoothPurity.FiniteGeneralRing
public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.SmoothPurityMap
public import Sheaf.Paper.CompositionComparisons
public import Sheaf.SecSmoothPurity.ReductionExceptional
public import Sheaf.Paper.FiniteSmoothCoefficientArrows
public import Sheaf.Paper.SmoothPurityCompositionFactors
import Sheaf.CategoryTheory.SmoothPurityCompositeTensorTranspose
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
import Sheaf.SecSmoothPurity.ReductionCompatibilities

/-! # Scalar transport of the composite unit orientation

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/sk-prop-sp-composition-factors.proof.md, (1) and final paragraph
(blueprint: lem-sp-orientation-scalar-propagation).

The first equation is in the ordinary pro-etale category. The unit equations use
its canonical ordinary-etale coordinates, mapped by the comparison inverse image.
The compositor, tensor mate and ordered Tate splitting are the existing specified
arrows; no composition-equality theorem from their owning module is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale
namespace SpOrientationScalarPropagation
open Etale.FiniteSmoothPurity SpCompositionFactors

/-- The iterated purity arrow, first Hf(gamma_g), then gamma_f at Gg(K).
Source: composition-factors, final paragraph
(blueprint: lem-sp-orientation-scalar-propagation). -/
def iterated (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g]
    (Lf : Etale.DerivedCategoryModule A X) (Lg : Etale.DerivedCategoryModule A Y)
    (af : Etale.dualizingComplex (ModuleCat.{u + 1} A) f ≅ Lf)
    (ag : Etale.dualizingComplex (ModuleCat.{u + 1} A) g ≅ Lg)
    (K : proCategory A Z) :
    (proSource A f Lf).obj ((proSource A g Lg).obj K) ⟶
      (exceptional A f).obj ((exceptional A g).obj K) :=
  (proSource A f Lf).map (proGamma A g Lg ag K) ≫
    proGamma A f Lf af ((exceptional A g).obj K)

/-- Exactly c(1) a_h = rho (f*a_g tensor a_f), with the canonical ordered source
splitting and the actual counit-normalized compositor. The equality is mapped into
D(X_proet,A); no inverse of rho is chosen or assumed.
Source: composition-factors, (1)
(blueprint: lem-sp-orientation-scalar-propagation). -/
def UnitEquation (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact (f ≫ g)]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hY : IsUnit (N : Γ(Y, ⊤))) (d e : ℕ)
    (af : Etale.dualizingComplex (ModuleCat.{u + 1} A) f ≅ line A N hA X d)
    (ag : Etale.dualizingComplex (ModuleCat.{u + 1} A) g ≅ line A N hA Y e)
    (ah : Etale.dualizingComplex (ModuleCat.{u + 1} A) (f ≫ g) ≅
      line A N hA X (d + e)) : Prop :=
  (comparison A X).map (ah.inv ≫ (finiteCompositor A f g).hom.app (𝟙_ _)) =
    (comparison A X).map
      ((finiteLineSplit A f N hN hA hY e d).hom ≫
        ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).map
          ((Etale.ordinaryFinitePullback A f).map ag.inv)).app _ ≫
        ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj _).map af.inv ≫
        finiteRho A f g)

/-- Scalar pasting of iterated purity, and propagation of the unit orientation identity,
for every unital map of finite ell-primary rings, without flatness or finite projective
 dimension of the new ring over the old one.
Source: composition-factors, (1) and final paragraph
(blueprint: lem-sp-orientation-scalar-propagation).

Proof:
1. lem-sp-composite-projection-coefficients puts omega_g and Gg(K) in the allowed
constructible finite-Tor domain. Its unital associative projections and the normalized
compositor satisfy lem-sp-composite-tensor-transpose. Thus t is natural and unital,
and gamma at the unit is the inverse orientation. det-sp-scalar-extension-functor
preserves the permitted inputs without a flatness assumption.
2. The source comparisons lambda are scalar/pullback balancing, tensor comparison,
and the generator-normalized Tate comparison. Their composite commutes with the
ordered shifted-Tate splitting: on K-flat representatives both routes send
((x tensor y) tensor z) tensor b to x tensor y tensor zb. Apply
lem-sfb-ringed-derived-monoidal-comparisons and
lem-pur-cochain-pullback-tensor-coherence. All Tate shifts are even, so the sign is +1.
3. det-sp-reduction-compatibilities(3), at each of f,g,h, identifies the direct
DNC/diagonal purity squares with these counit-transpose exceptional comparisons.
4. Paste the f square at Gg(K), naturality of gamma_f at r_g(K), naturality of
lambda_f at gamma_g(K), and the g square. This gives precisely the first equation,
with the two explicit source lambda factors on its right.
5. At the unit, functoriality of tensor gives Q_i(1)u_i = rho_i(f*a_g tensor a_f).
Apply scalar extension to the assumed unit equation and postcompose by the composite
exceptional comparison. det-sp-composition-comparisons(2) identifies its direct side
with c_1 r_h S(a_h); Step 3 identifies this with c_1 a_h lambda_h. Steps 2 and 4
identify the other side with Q_1(1)u_1 lambda_h. Cancel the source isomorphism.
Expand the tensor word to obtain UnitEquation at the new ring. This uses neither
faithfulness nor flatness of scalar extension. The canonical map Z/ell^r to any
finite ring killed by ell^r is a particular unital map covered by the assertion.
-/
theorem orientationScalarPropagation
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hne : ell ≠ D.p)
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))] [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
    [IsSeparated f] [IsSeparated g]
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (phi : A →+* B) (n : ℕ) (hn : 1 ≤ n)
    (hA : ((ell ^ n : ℕ) : A) = 0) (hB : ((ell ^ n : ℕ) : B) = 0)
    (geometryf : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (geometryg : Etale.FiniteRingSectionDeformation.Geometry e
      (pullback.fst g g) (pullback.diagonal g))
    (geometryh : Etale.FiniteRingSectionDeformation.Geometry (d + e)
      (pullback.fst (f ≫ g) (f ≫ g)) (pullback.diagonal (f ≫ g)))
    (afA : Etale.dualizingComplex (ModuleCat.{u + 1} A) f ≅
      line A (ell ^ n) hA X d)
    (_hfA : OrientationNormalized A (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hA f d geometryf
      ((finiteGeneralRingPrimeSetting D ell hne n hn).diagonalExponent_isUnit
        (X ↘ Spec (.of D.k))) afA)
    (agA : Etale.dualizingComplex (ModuleCat.{u + 1} A) g ≅
      line A (ell ^ n) hA Y e)
    (_hgA : OrientationNormalized A (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hA g e geometryg
      ((finiteGeneralRingPrimeSetting D ell hne n hn).diagonalExponent_isUnit
        (Y ↘ Spec (.of D.k))) agA)
    (ahA : Etale.dualizingComplex (ModuleCat.{u + 1} A) (f ≫ g) ≅
      line A (ell ^ n) hA X (d + e))
    (_hhA : OrientationNormalized A (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hA (f ≫ g) (d + e) geometryh
      ((finiteGeneralRingPrimeSetting D ell hne n hn).diagonalExponent_isUnit
        (X ↘ Spec (.of D.k))) ahA)
    (afB : Etale.dualizingComplex (ModuleCat.{u + 1} B) f ≅
      line B (ell ^ n) hB X d)
    (_hfB : OrientationNormalized B (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hB f d geometryf
      ((finiteGeneralRingPrimeSetting D ell hne n hn).diagonalExponent_isUnit
        (X ↘ Spec (.of D.k))) afB)
    (agB : Etale.dualizingComplex (ModuleCat.{u + 1} B) g ≅
      line B (ell ^ n) hB Y e)
    (_hgB : OrientationNormalized B (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hB g e geometryg
      ((finiteGeneralRingPrimeSetting D ell hne n hn).diagonalExponent_isUnit
        (Y ↘ Spec (.of D.k))) agB)
    (ahB : Etale.dualizingComplex (ModuleCat.{u + 1} B) (f ≫ g) ≅
      line B (ell ^ n) hB X (d + e))
    (_hhB : OrientationNormalized B (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hB (f ≫ g) (d + e) geometryh
      ((finiteGeneralRingPrimeSetting D ell hne n hn).diagonalExponent_isUnit
        (X ↘ Spec (.of D.k))) ahB)
    (eX : CoefficientLineComparison phi (ell ^ n) (ell ^ n) hA hB X)
    (eY : CoefficientLineComparison phi (ell ^ n) (ell ^ n) hA hB Y) :
    (∀ (K : proCategory A Z), IsCtf A Z K →
      (proScalar phi X).map
          (iterated A f g (line A (ell ^ n) hA X d) (line A (ell ^ n) hA Y e)
            afA agA K) ≫
          proCoefficientMap phi f ((exceptional A g).obj K) ≫
          (exceptional B f).map (proCoefficientMap phi g K) =
        proLambda f d eX ((proSource A g (line A (ell ^ n) hA Y e)).obj K) ≫
          (proSource B f (line B (ell ^ n) hB X d)).map (proLambda g e eY K) ≫
          iterated B f g (line B (ell ^ n) hB X d) (line B (ell ^ n) hB Y e)
            afB agB ((proScalar phi Z).obj K)) ∧
      (UnitEquation A f g (ell ^ n) (pow_pos (Fact.out : ell.Prime).pos n) hA
          ((finiteGeneralRingPrimeSetting D ell hne n hn).diagonalExponent_isUnit
            (Y ↘ Spec (.of D.k))) d e afA agA ahA →
        UnitEquation B f g (ell ^ n) (pow_pos (Fact.out : ell.Prime).pos n) hB
          ((finiteGeneralRingPrimeSetting D ell hne n hn).diagonalExponent_isUnit
            (Y ↘ Spec (.of D.k))) d e afB agB ahB) := by
  sorry

end SpOrientationScalarPropagation
end AlgebraicGeometry.ProEtale
