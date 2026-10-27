/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q134
-/
module

public import Sheaf.AlgebraicGeometry.RhoSectionModules
public import Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
import Sheaf.AlgebraicGeometry.GroupScheme.RhoRegularWeylOrbit
import Sheaf.AlgebraicGeometry.GroupScheme.SimpleModuleDualHighestWeight

/-! # Simplicity of the Steinberg induced module

Source: Jantzen, Representations of Algebraic Groups (2003), II.3.18--3.19;
Alexandre, Positivity, plethysm and hyperbolicity of Siegel varieties in positive
characteristic, Definitions 2.4 and 2.8, Proposition 2.9, pp.263--264.
(blueprint: lem-sfb-steinberg-induced-module-irreducible)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj TensorProduct

namespace AlgebraicGeometry

/-- The actual right-semi-invariant regular-function space at a Steinberg weight
is simple for its rational left-translation coaction.

Source: Jantzen, II.3.18--3.19; Alexandre, Definitions 2.4 and 2.8, Proposition 2.9,
pp.263--264 (blueprint: lem-sfb-steinberg-induced-module-irreducible).

The character identity rho squared = product of positive roots expresses the
integral half sum, including in characteristic two. The extension is trivial on
all smooth connected normal unipotent subgroups, equivalently on the radical.
The coaction is pinned by evaluating every finite tensor presentation at every
pair of algebra-valued points: the value is f(s inverse g). This determines c
uniquely, since the affine coordinate tensor product represents the product
scheme and tensoring the inclusion of the actual section subspace is injective.
Thus the existential does not choose an unrelated rational action.

Proof plan:
1. By lem-sfb-reductive-borel-pair-structure and lem-sfb-rho-regular-weyl-orbit,
   the simple-coroot pairings of rho are one. Thus m rho is dominant for m >= 0,
   and (p-1)rho is p-restricted. These are integer identities, with no division in F.
2. Put E_k = W_(p^k-1). The lem-sfb-rho-section-modules theorem gives a nonzero
   finite-dimensional rational left-translation module. By
   lem-sfb-induced-module-primitive-line its U-invariants form the line of weight
   w0(-(p^k-1)rho) = (p^k-1)rho, using w0 rho = -rho from step 1.
3. The lem-sfb-induced-weyl-dimension-formula theorem gives dim E_k = p^(k N),
   where N is the number of positive roots: each rational Weyl factor is p^k.
4. Choose a rational submodule L_k of least positive dimension in E_k. It is
   simple. By lem-sfb-simple-module-dual-highest-weight it has a highest line,
   which injects into E_k's highest line, so its highest weight is (p^k-1)rho.
   Inclusions preserve restricted fixed vectors since tensoring over F is exact.
5. By lem-sfb-restricted-rho-simple-dimension, dim L_1 = p^N. Apply
   lem-sfb-restricted-highest-weight-dimension-product to L_1, L_k and L_(k+1),
   whose weights satisfy eta_(k+1) = eta_1 + p eta_k. Induction gives
   dim L_k = p^(k N).
6. Equal finite dimensions in L_r <= E_r give equality, hence simplicity.
   The coaction is the restriction of regular left translation as in step 2.
   When the root system is empty, both dimension products equal one.
-/
theorem steinberg_induced_module_irreducible
    {F : Type u} [Field F] [IsAlgClosed F]
    (p : ℕ) [CharP F p] (hp : 0 < p)
    (S T B : Grp (Over (Spec (.of F)))) [IsAffine S.X.left]
    (hS : IsSemisimpleGroupScheme S.X)
    (hsc : ∀ (S' : Over (Spec (.of F))) [GrpObj S'],
      IsSemisimpleGroupScheme S' → ∀ (f : S' ⟶ S.X) [IsMonHom f],
      Surjective f.left → IsFinite (GrpObj.ker f).hom →
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker f)
        (s : StandardGroupSchemes.affine F A ⟶ S'),
        (x ≫ GrpObj.kerι f) * s = s * (x ≫ GrpObj.kerι f)) → IsIso f)
    (i : T ⟶ S) (j : B ⟶ S) (k : T ⟶ B) (hpair : IsRhoBorelPair i j k)
    (a : ModObj T.X B.X)
    (hconj : ∀ (Z : Over (Spec (.of F))) (t : Z ⟶ T.X) (b : Z ⟶ B.X),
      lift t b ≫ a.smul = (t ≫ k.hom.hom) * b * (t ≫ k.hom.hom)⁻¹)
    (Φ : List (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
    (hΦ : Φ.Nodup)
    (hroots : ∀ α, α ∈ Φ ↔ α.hom.hom ≠ 1 ∧
      @TorusCharacterTangent.weightSpace F _ T B a α ≠ ⊥)
    (ρ : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))
    (hρ : ρ.hom.hom ^ 2 = (Φ.map (fun α ↦ α.hom.hom)).prod)
    (ρB : B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))
    (hρB : k ≫ ρB = ρ)
    (htrivial : ∀ (U : Grp (Over (Spec (.of F)))) (l : U ⟶ B),
      IsClosedSubgroupScheme l.hom.hom → IsNormalSubgroupScheme l.hom.hom →
      Smooth U.X.hom → ConnectedSpace U.X.left → SolvableGroupStructure.IsUnipotent U →
      l.hom.hom ≫ ρB.hom.hom = 1)
    (r : ℕ) (hr : 0 < r) :
    ∃ c : RhoSection.sectionModule S B j ρB (p ^ r - 1) →ₗ[F]
        RhoSection.sectionModule S B j ρB (p ^ r - 1) ⊗[F]
          RationalHighestWeight.coordinateAlgebra S,
      HopfAction.Coassociative F (RationalHighestWeight.coordinateAlgebra S)
        (RhoSection.sectionModule S B j ρB (p ^ r - 1)) c ∧
      HopfAction.Counital F (RationalHighestWeight.coordinateAlgebra S)
        (RhoSection.sectionModule S B j ρB (p ^ r - 1)) c ∧
      (∀ (f : RhoSection.sectionModule S B j ρB (p ^ r - 1)) (n : ℕ)
        (v : Fin n → RhoSection.sectionModule S B j ρB (p ^ r - 1))
        (z : Fin n → RationalHighestWeight.coordinateAlgebra S),
        c f = ∑ q, v q ⊗ₜ[F] z q →
        ∀ (A : Type u) [CommRing A] [Algebra F A]
          (s g : StandardGroupSchemes.affine F A ⟶ S.X),
          ∑ q, RhoSection.evaluate g (v q).val * RhoSection.evaluate s (z q) =
            RhoSection.evaluate (s⁻¹ * g) f.val) ∧
      RationalHighestWeight.IsSimple c := by
  sorry

end AlgebraicGeometry
