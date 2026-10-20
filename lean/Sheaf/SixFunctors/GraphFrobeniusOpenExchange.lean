/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.SixFunctors.SchemeFrobenius
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.SixFunctors.SelectedSchemeGaloisComparison
public import Sheaf.AlgebraicGeometry.FrobeniusFactorization
public import Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite
public import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
public import Sheaf.AlgebraicGeometry.FrobeniusOpenSquare
public import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback
import Sheaf.AlgebraicGeometry.ProEtaleTensorCompositionUnit
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.SixFunctors.OpenTensorNormalization

/-!
# Open extension commutes with the canonical scheme/Galois comparison

Source: main-20261015, `sec-trace-formula/sk-d-weil/`
`prop-trf-graph-frobenius-operator.proof.md`, Step 2
(blueprint: lem-trf-graph-frobenius-open-exchange).

The equation is stated in the functor category after restriction to D^b_ctf(X,A).
Thus it includes naturality in M. Scheme and Galois maps are morphisms of schemes;
no linearity over k is imposed on the Galois maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.TraceFormulaCoefficientConventions

/-- The open immersion obtained by geometric base change of the given model open.
Source: blueprint graph-Frobenius-operator proof, Step 2
(blueprint: lem-trf-graph-frobenius-open-exchange). -/
abbrev graphFrobeniusBaseChangedOpen (T : TraceFormulaCoefficientConventions.{u})
    (Y₀ : Over (Spec (CommRingCat.of T.datum.k₀))) (j₀ : T.X₀ ⟶ Y₀) :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap T.datum.k₀ T.datum.k)))).map j₀).left

/-- The base-changed map is open by the existing base-change theorem for morphism
properties, applied to the given open immersion. This registers the constructed map,
without imposing a new hypothesis.
Source: blueprint graph-Frobenius-operator proof, Step 2; Mathlib overPullbackMap
(blueprint: lem-trf-graph-frobenius-open-exchange). -/
noncomputable instance graphFrobeniusBaseChangedOpen_isOpenImmersion
    (T : TraceFormulaCoefficientConventions.{u})
    (Y₀ : Over (Spec (CommRingCat.of T.datum.k₀)))
    (j₀ : T.X₀ ⟶ Y₀) [IsOpenImmersion j₀.left] :
    IsOpenImmersion (T.graphFrobeniusBaseChangedOpen Y₀ j₀) :=
  MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
    (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) j₀ inferInstance

/-- The canonical exchange for the m-fold scheme-Frobenius open square.
Source: blueprint graph-Frobenius-operator proof, Step 2;
`lem-trf-frobenius-open-square` and `lem-trf-open-square-exchange`
(blueprint: lem-trf-graph-frobenius-open-exchange). -/
def graphFrobeniusSchemeExchange (T : TraceFormulaCoefficientConventions.{u})
    (Y₀ : Over (Spec (CommRingCat.of T.datum.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (j₀ : T.X₀ ⟶ Y₀) [IsOpenImmersion j₀.left] (m : ℕ) :
    sfIntrinsicDerivedOpen T.coefficientRing (T.graphFrobeniusBaseChangedOpen Y₀ j₀) ⋙
        proEtaleConstantRingDerivedPullback T.coefficientRing
          (T.datum.schemeFrobeniusIterate Y₀ m) ≅
      proEtaleConstantRingDerivedPullback T.coefficientRing
          (T.datum.schemeFrobeniusIterate T.X₀ m) ⋙
        sfIntrinsicDerivedOpen T.coefficientRing (T.graphFrobeniusBaseChangedOpen Y₀ j₀) :=
  constantOpenSquareExchange T.coefficients.l T.coefficientField T.level T.level_pos
    (T.datum.schemeFrobeniusIterate T.X₀ m) _ _
    (T.datum.schemeFrobeniusIterate Y₀ m)
    (T.datum.frobenius_open_square T.X₀ Y₀ j₀ m).1

/-- The canonical exchange for the m-fold geometric-Galois-Frobenius open square.
Source: blueprint graph-Frobenius-operator proof, Step 2;
`lem-trf-frobenius-open-square` and `lem-trf-open-square-exchange`
(blueprint: lem-trf-graph-frobenius-open-exchange). -/
def graphFrobeniusGaloisExchange (T : TraceFormulaCoefficientConventions.{u})
    (Y₀ : Over (Spec (CommRingCat.of T.datum.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (j₀ : T.X₀ ⟶ Y₀) [IsOpenImmersion j₀.left] (m : ℕ) :
    sfIntrinsicDerivedOpen T.coefficientRing (T.graphFrobeniusBaseChangedOpen Y₀ j₀) ⋙
        proEtaleConstantRingDerivedPullback T.coefficientRing
          (HPow.hPow (α := End (T.datum.geometricFiber Y₀).left)
            (T.datum.geometricGaloisFrobenius Y₀) m) ≅
      proEtaleConstantRingDerivedPullback T.coefficientRing
          (HPow.hPow (α := End (T.datum.geometricFiber T.X₀).left)
            (T.datum.geometricGaloisFrobenius T.X₀) m) ⋙
        sfIntrinsicDerivedOpen T.coefficientRing (T.graphFrobeniusBaseChangedOpen Y₀ j₀) :=
  constantOpenSquareExchange T.coefficients.l T.coefficientField T.level T.level_pos
    (HPow.hPow (α := End (T.datum.geometricFiber T.X₀).left)
      (T.datum.geometricGaloisFrobenius T.X₀) m) _ _
    (HPow.hPow (α := End (T.datum.geometricFiber Y₀).left)
      (T.datum.geometricGaloisFrobenius Y₀) m)
    (T.datum.frobenius_open_square T.X₀ Y₀ j₀ m).2.1

/-- Open extension commutes with the specified scheme/Galois comparison, naturally on
D^b_ctf(X,A), for every positive iterate m. The functor-category equality evaluates at M
as kappa_Y(j_!M) followed by b_g equals b_Phi followed by j_!(kappa_X(M)).
Source: main-20261015, graph-Frobenius-operator proof, Step 2
(blueprint: lem-trf-graph-frobenius-open-exchange).

Proof, following the seven steps of the node:
1. For Z = X,Y put H_Z = F_Z^(a*m), P_Z = L(Phi_Z^m)^*, G_Z = L(g_Z^m)^*.
   The recorded factorization and inverse arithmetic/geometric Galois maps give
   Phi_Z^m = H_Z followed by g_Z^m. The comparison is c_Z followed by tau_Z at G_Z.
2. Fix canonical constant-section coefficient maps. On pure tensors the ordinary
   composition sends (v tensor a) tensor b to v tensor c_h(a)b. Both reassociations
   of three pullbacks give v tensor c_h(c_k(a))c_h(b)d. Fibre-product reassociation
   has the same projections. These formulas survive restriction to the open and exact
   termwise descent by the localization universal property, and coincide with the
   canonical K-flat comparison of the recorded pullback-composition theorem.
3. Write r = Lj^*. The Cartesian squares give alpha_P and alpha_G. Pullback naturality
   of the absolute-Frobenius trivialization, with exponent a*m, gives
   tau_X at rN composed after alpha_T = r(tau_Y at N). Composition coherence gives
   c_X at rN after alpha_P = T_X(alpha_G) after alpha_T at G_Y N after r(c_Y).
4. Substitute kappa = tau after c and use naturality of tau_X to obtain
   kappa_X at rN after alpha_P = alpha_G after r(kappa_Y at N).
5. Use the canonical open unit and its inverse nu. Identity normalization of the
   canonical exchanges gives nu after r(b_P) = P_X(nu) after alpha_P, and the same
   formula with G. The coordinate transport preserves precisely these units.
6. Put L = b_G after kappa_Y and R = j_!(kappa_X) after b_P. Apply Step 4 at j_!M,
   naturality of kappa_X for nu_M, and Step 5. Both nu after r(L) and nu after r(R)
   equal kappa_X after P_X(nu_M) after alpha_P. Cancel the invertible nu to get r(L)=r(R).
7. Precompose L and R by b_P inverse. They are maps between two objects in the image
   of j_!. Derived full faithfulness of open extension, via the open unit, detects
   their equality after r. Cancel b_P inverse to obtain L=R. All comparisons and
   exchanges are natural transformations, and restriction to D^b_ctf gives the displayed
   equality in its functor category. The argument applies to arbitrary m ≥ 1.
The not-yet-stated proof dependency lem-sf-open-tensor-normalization supplies the derived
open-unit isomorphism and full faithfulness in Steps 5 and 7; its import is deferred. -/
theorem graphFrobenius_open_exchange (T : TraceFormulaCoefficientConventions.{u})
    (Y₀ : Over (Spec (CommRingCat.of T.datum.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (j₀ : T.X₀ ⟶ Y₀) [IsOpenImmersion j₀.left] (m : ℕ) (hm : 1 ≤ m) :
    Functor.whiskerLeft T.boundedConstructibleFiniteTor.ι
        (Functor.whiskerLeft
            (sfIntrinsicDerivedOpen T.coefficientRing (T.graphFrobeniusBaseChangedOpen Y₀ j₀))
            (T.selectedSchemeGaloisComparison Y₀ m hm).hom ≫
          (T.graphFrobeniusGaloisExchange Y₀ j₀ m).hom) =
      Functor.whiskerLeft T.boundedConstructibleFiniteTor.ι
        ((T.graphFrobeniusSchemeExchange Y₀ j₀ m).hom ≫
          Functor.whiskerRight (T.selectedSchemeGaloisComparison T.X₀ m hm).hom
            (sfIntrinsicDerivedOpen T.coefficientRing
              (T.graphFrobeniusBaseChangedOpen Y₀ j₀))) := by
  sorry

end WeilConjectures.TraceFormulaCoefficientConventions
