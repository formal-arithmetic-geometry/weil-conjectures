module

public import Sheaf.AlgebraicGeometry.GroupScheme.RationalCompositionSeries
public import Sheaf.AlgebraicGeometry.GroupScheme.AffineWeightOrderAction
import Sheaf.AlgebraicGeometry.GroupScheme.AffineReflectionDominantDescent
public import Sheaf.AlgebraicGeometry.RhoSectionModules
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
import Sheaf.AlgebraicGeometry.GroupScheme.RhoRegularWeylOrbit
import Sheaf.AlgebraicGeometry.GroupScheme.SimpleModuleDualHighestWeight
import Sheaf.AlgebraicGeometry.GroupScheme.SimplyConnectedCharacterLattice

/-! # Composition factors and affine linkage of dominant induced modules

Source: Jantzen, Representations of Algebraic Groups (2003), II.2 and II.6;
Andersen, The strong linkage principle (1980), pp.54--58; Milne, Algebraic Groups
(2017), Definition 22.21 and Propositions 22.22 and 22.27.
(blueprint: lem-sfb-induced-composition-linkage)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct MonObj

namespace AlgebraicGeometry

/-- The actual induced subspace I(eta), with the positive-Borel convention:
f(gb) = (w0 eta)(p(b)) inverse times f(g). The inverse character and exponent one
reuse the recorded right-semi-invariant regular-function submodule.
Source: Milne, Definition 22.21 and Proposition 22.27; Jantzen, II.2
(blueprint: lem-sfb-induced-composition-linkage). -/
abbrev dominantInducedModule {F : Type u} [Field F]
    (S T B : Grp (Over (Spec (.of F)))) (iB : B ⟶ S) (pB : B ⟶ T)
    [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    (e : T ≅ T) (lam : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) :=
  RhoSection.sectionModule S B iB ((pB ≫ e.inv ≫ lam)⁻¹) 1

/-- A coaction on the actual regular-function subspace is left translation.
For every tensor presentation of c(f), evaluation on its two factors at g and s
is f(s inverse g), after every commutative F-algebra extension. Thus the coaction
is specified, rather than an unrelated rational representation on the same space.
Source: Milne, Definition 22.21, and the coaction dictionary of Section 4a
(blueprint: lem-sfb-induced-composition-linkage). -/
def IsRegularLeftTranslation {F : Type u} [Field F]
    (S : Grp (Over (Spec (.of F)))) [IsAffine S.X.left]
    (W : Submodule F (RhoSection.Coordinate S.X))
    (c : W →ₗ[F] W ⊗[F] RationalHighestWeight.coordinateAlgebra S) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra F A]
    (s g : StandardGroupSchemes.affine F A ⟶ S.X) (f : W)
    (n : ℕ) (fi : Fin n → W) (hi : Fin n → RationalHighestWeight.coordinateAlgebra S),
    c f = ∑ i, fi i ⊗ₜ[F] hi i →
      RhoSection.evaluate (s⁻¹ * g) f.val =
        ∑ i, RhoSection.evaluate g (fi i).val * RhoSection.evaluate s (hi i)

/-- A dominant induced module is nonzero and finite-dimensional. Every rational
composition series has exactly one factor of highest weight eta; all other factors
have strictly lower dominant highest weights in the rho-shifted affine Weyl orbit.

Source: Jantzen, II.2 and II.6; Andersen (1980), pp.54--58;
Milne, Definition 22.21 and Propositions 22.22 and 22.27.
(blueprint: lem-sfb-induced-composition-linkage)

Proof plan (the node's thirteen steps):
1. Put lambda=-w0 eta, dominant since -w0 permutes simple roots and coroots
   (lem-sfb-rho-regular-weyl-orbit and lem-sfb-reductive-borel-pair-structure).
   Apply lem-sfb-induced-weyl-dimension-formula for finiteness. The matrix coefficient
   ell(gv) from lem-sfb-dominant-character-highest-line has value one at the identity,
   proving nonvanishing. The actual subspace is E_B(-lambda).
2. Induct on dimension, choosing a submodule of least positive dimension, for a
   composition series. Split-torus coactions decompose vectors into character
   components; extracting components from lifts proves exactness on weight spaces.
3. The evaluation functional e(f)=f(1) on the dual has B-weight lambda. Its rational
   span has zero annihilator: f(g)=(g e)(f), and the universal point detects f=0.
   Hence e generates the dual, without a density or reciprocity theorem.
4. Apply lem-sfb-primitive-cyclic-weight-bound to this cyclic dual. Normalizer
   representatives permute weights and dualization negates them. Apply -w0 to get
   all weights of I(eta) at most eta, and its eta weight space has dimension one.
5. By lem-sfb-simple-module-dual-highest-weight every simple factor has a highest
   line. The cyclic weight bound and lem-sfb-weyl-reflection-realization imply its
   highest weight mu is dominant, using independence of simple roots from
   lem-sfb-simply-connected-character-lattice. Exact weight spaces give mu<=eta.
6. Add dimensions of eta weight spaces along the arbitrary series. Only factors
   with highest weight eta contribute, each contributes one, and the total is one.
   Thus exactly one does; the remaining highest weights are strictly smaller.
7. By lem-sfb-induced-module-primitive-line the U-invariants of I(eta) form its eta
   line. Two nonzero summands would each contain a simple submodule and therefore
   give two invariant lines, contradicting that dimension. Thus I(eta) is indecomposable.
8. Right translation by a representative n of w0 identifies H^0(eta) for the opposite
   Borel with I(eta), by f(g) mapping to f(gn); its inverse is right translation by
   n inverse. This uses lem-sfb-flag-cohomology-finite-exact and preserves the S-action.
9. Prove simultaneously that every constituent of H^i(w dot x) has highest weight
   nu strongly linked below x. Induct in the well-founded order on x+rho dominant
   (lem-sfb-affine-reflection-dominant-descent), then on Weyl length. The wall case
   is covered by lem-sfb-minimal-parabolic-line-cohomology and
   lem-sfb-demazure-reflection-sequences; pairing -1 gives zero fibre cohomology.
10. Error modules have weights z=s_alpha dot y+kp alpha, with 0<kp<r. Their
    cohomological constituents occur in H^j(z), by lem-sfb-flag-cohomology-finite-exact.
    Dominant descent gives d(z)<x and d(z) linked below x; the outer induction gives
    linkage of all error constituents. The reflection exact sequences give the same
    for the extension term E. Empty error ranges give zero modules.
11. For the inner base follow a reduced word from 1 to w0. Reflection sequences
    give a composite H^(i+N)(w0 dot x) to H^i(x) with cokernel consisting of error
    constituents. For i>0 its source vanishes by dimension. For i=0 use
    lem-sfb-top-bottom-cohomology-simple-image: H^0(x)=0 if x is not dominant;
    otherwise the image is zero or L(x). This proves the base without circularity.
12. For positive length use a left descent v=s_alpha w. The exact segment from
    H^(i-1)(E) to H^i(w dot x) to H^(i-1)(v dot x) combines outer-error and
    inner-induction bounds. Negative cohomology is zero. Apply the result at eta,
    w=1 and i=0, and the explicit identification of step 8.
13. Each affine lowering step is z mapping to w(z+rho)-rho+p gamma with gamma
    in the integral root span. Composition preserves this form because W preserves
    the root lattice. A finite chain gives the displayed linkage equation. No prime
    or irreducibility restriction was used. Rank zero has no lower factor.
-/
theorem induced_composition_linkage
    {F : Type u} [Field F] [IsAlgClosed F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (S T B : Grp (Over (Spec (.of F))))
    (hS : IsSemisimpleGroupScheme S.X)
    (hsc : ∀ (S' : Over (Spec (.of F))) [GrpObj S'],
      IsSemisimpleGroupScheme S' → ∀ (f : S' ⟶ S.X) [IsMonHom f],
      Surjective f.left → IsFinite (GrpObj.ker f).hom →
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker f)
        (s : StandardGroupSchemes.affine F A ⟶ S'),
        (x ≫ GrpObj.kerι f) * s = s * (x ≫ GrpObj.kerι f)) → IsIso f)
    (iT : T ⟶ S) (iB : B ⟶ S) (j : T ⟶ B)
    (hTB : IsRhoBorelPair iT iB j)
    [IsCommMonObj T.X] [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    (aS : ModObj T.X S.X) (aB : ModObj T.X B.X)
    (Φ : Finset (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
    (P : RootDatum Φ
      (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)))
    (b : P.Base) [P.IsReduced]
    (hconjS : aS.smul = (iT.hom.hom ⊗ₘ 𝟙 S.X) ≫ GrpObj.conj S.X)
    (hconjB : aB.smul = (j.hom.hom ⊗ₘ 𝟙 B.X) ≫ GrpObj.conj B.X)
    (hroot : ∀ α : Φ, P.root α = α.val)
    (hpair : ∀ (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)),
      ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (P.toLinearMap χ ν))
    (hweights : ∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
      χ ∈ Φ ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ T S aS χ.toMul ≠ ⊥)
    (hpos : ∀ α : Φ, b.IsPos α ↔
      @TorusCharacterTangent.weightSpace F _ T B aB α.val.toMul ≠ ⊥)
    (ρ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
    (hρ : (2 : ℤ) • ρ =
      ∑ β ∈ (@Finset.filter Φ b.IsPos (Classical.decPred _) Finset.univ), P.root β)
    [IsAffine S.X.left] [IsAffine T.X.left]
    (U : Grp (Over (Spec (.of F)))) [IsAffine U.X.left]
    (iU : U ⟶ B)
    (hUclosed : IsClosedSubgroupScheme iU.hom.hom)
    (hUnormal : IsNormalSubgroupScheme iU.hom.hom)
    (hUsmooth : Smooth U.X.hom) (hUconnected : ConnectedSpace U.X.left)
    (hUunipotent : SolvableGroupStructure.IsUnipotent U)
    (hUmax : ∀ (N : Grp (Over (Spec (.of F)))) (iN : N ⟶ B),
      IsClosedSubgroupScheme iN.hom.hom → IsNormalSubgroupScheme iN.hom.hom →
      Smooth N.X.hom → ConnectedSpace N.X.left →
      SolvableGroupStructure.IsUnipotent N → ∃ f : N ⟶ U, f ≫ iU = iN)
    (pB : B ⟶ T) (hpB : j ≫ pB = 𝟙 T)
    (hker : IsPullback iU.hom.hom (toUnit U.X) pB.hom.hom η[T.X])
    (act : RankOneRoots.Weyl iT →* Aut T)
    (hact : ∀ (n : RankOneRoots.normalizer iT) (A : CommAlgCat.{u} F)
      (t : StandardGroupSchemes.affine F A ⟶ T.X),
      t ≫ (act (QuotientGroup.mk n)).hom.hom.hom ≫ iT.hom.hom =
        (toUnit (StandardGroupSchemes.affine F A) ≫ n.val) * (t ≫ iT.hom.hom) *
          (toUnit (StandardGroupSchemes.affine F A) ≫ n.val)⁻¹)
    (w₀ : RankOneRoots.Weyl iT)
    (hlongest : Set.image (fun β : Φ ↦ AffineWeight.characterAction iT act w₀ β.val)
      {β : Φ | b.IsPos β} = Set.image (fun β : Φ ↦ -β.val) {β : Φ | b.IsPos β})
    (lam : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
    (hlam : ∀ α ∈ b.support, 0 ≤ P.toLinearMap lam (P.coroot α)) :
    Nontrivial (dominantInducedModule S T B iB pB (act w₀) lam.toMul) ∧
    Module.Finite F (dominantInducedModule S T B iB pB (act w₀) lam.toMul) ∧
    ∃ c : dominantInducedModule S T B iB pB (act w₀) lam.toMul →ₗ[F]
        dominantInducedModule S T B iB pB (act w₀) lam.toMul ⊗[F]
          RationalHighestWeight.coordinateAlgebra S,
      HopfAction.Coassociative F (RationalHighestWeight.coordinateAlgebra S) _ c ∧
      HopfAction.Counital F (RationalHighestWeight.coordinateAlgebra S) _ c ∧
      IsRegularLeftTranslation S _ c ∧
      Nonempty (RationalHighestWeight.RationalCompositionSeries c) ∧
      ∀ q : RationalHighestWeight.RationalCompositionSeries c,
        (∃! k : Fin q.length,
          RationalHighestWeight.HasHighestWeight (q.factorCoaction k) iT (iU ≫ iB) lam.toMul) ∧
        ∀ k : Fin q.length,
          ¬ RationalHighestWeight.HasHighestWeight (q.factorCoaction k) iT (iU ≫ iB) lam.toMul →
          ∃ mu : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
            RationalHighestWeight.HasHighestWeight (q.factorCoaction k) iT (iU ≫ iB) mu.toMul ∧
            (∀ α ∈ b.support, 0 ≤ P.toLinearMap mu (P.coroot α)) ∧
            AffineWeight.LT P b mu lam ∧
            ∃ (w : RankOneRoots.Weyl iT) (gamma : P.rootSpan ℤ),
              mu + ρ = AffineWeight.characterAction iT act w (lam + ρ) + (p : ℤ) • gamma.val := by
  sorry

end AlgebraicGeometry
