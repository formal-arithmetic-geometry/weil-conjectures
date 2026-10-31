/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.Algebra.Category.Grp.Ulift
import WeilConjectures.AlgebraicGeometry.FiniteLocalAbelianForget
import WeilConjectures.Mathlib.RingTheory.Extension.Presentation.Submersive
import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale
import WeilConjectures.AlgebraicGeometry.Sites.InverseImageRepresentable
import WeilConjectures.AlgebraicGeometry.FiniteOperationLocalConstancy
import WeilConjectures.LinearAlgebra.SemilinearFrobenius
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleUnderlyingSets
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleQcqsAffineLocal
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlyingSupplement
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.PointedEtaleStalk

/-!
# Frobenius-linear kernels on finite locally free sheaves

Source: Stacks Project, `more-etale.tex`, Tag 0GKU, lines 4213--4270
(blueprint: lem-fd-frobenius-linear-vector-bundle-constructible).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

namespace Scheme

open Modules

/-- A Frobenius-linear endomorphism of a finite locally free vector bundle has zero
cokernel and constructible fixed-point sheaf.

Source: Stacks Project, `more-etale.tex`, Tag 0GKU, lemma-frobenius-linear-on-vb
(blueprint: lem-fd-frobenius-linear-vector-bundle-constructible).

The open `U` ranges over the quasi-compact and quasi-separated open subschemes of `S`
(`CompactSpace U.toScheme`, `QuasiSeparatedSpace U.toScheme`): every affine open, and
`U = ⊤` exactly when `S` is quasi-compact and quasi-separated.  No such hypothesis is put
on `S` or on the inclusion morphism `U.ι`.

Proof:
1. Cover `S` by affine opens `V = Spec A` on which `E` is free of rank `n`
   (def-sc-finite-locally-free-sheaf).  The étale sheaf has sections `Γ(T, u^*E)`
   (def-sc-etale-qcoherent-module); on `V` they are `n`-tuples of functions, and restriction
   to an étale open is inverse image (lem-weil-pbc-etale-inverse-image-restriction).  Writing
   `F(e_j) = ∑_i a_{ij} e_i`, additivity and the scalar law give
   `(F - 1)(x)_i = ∑_j a_{ij} x_j^p - x_i`.  The kernel `K` is an `𝔽_p`-module sheaf.
2. For `b ∈ A^n` put `B_b = A[x_1, …, x_n]/(b_i + x_i - ∑_j a_{ij} x_j^p)` and
   `Z_b = Spec B_b`; `A`-algebra maps `B_b → C` are the solutions of `(F - 1)(x) = b` in `C^n`
   (def-weil-affine-spectrum), and both sides are étale sheaves
   (lem-weil-pbc-small-etale-representable-presheaf-sheaf), so `K|_V = h_{Z_0}`.
3. In characteristic `p` the Jacobian matrix of the relations is the identity, with
   determinant `1` also for `n = 0` (def-exc-jacobian-presentation); by
   lem-exc-etale-jacobian-presentation, `B_b` is étale over `A`, so `Z_b → V` is étale
   (def-weil-etale-morphism).
4. At every point of `V`, Lang--Steinberg over an algebraic closure `Ω` of the residue field
   (lem-sc-lang-steinberg) solves `T(x) - x = b̄` for `T(x)_i = ∑_j ā_{ij} x_j^p`, so
   `Z_b → V` is surjective; no invertibility of `(a_{ij})` is used.
5. For a section `b` over an étale `T → S`, the covers `Z_b` over affine pieces of `T` solve
   `(F - 1)(x) = b` locally (def-weil-pbc-etale-site), so `F - 1` is an epimorphism
   (lem-weil-pbc-abelian-sheaf-epi-locally-surjective) and its cokernel is zero.
6. The étale stratification lemma (lem-weil-pbc-etale-stratified-finite) applied to
   `Z_0 → V` gives a finite constructible locally closed partition `(V_r)` with
   `Z_0 ×_V V_r → V_r` finite étale; the inverse image of `h_{Z_0}` on `V_r` is represented
   (lem-galois-inverse-image-representable) and finite locally constant
   (lem-galois-flc-representable); the abelian/set comparison
   (lem-weil-pbc-site-pullback-abelian-underlying, lem-weil-pbc-sets-etale-inverse-image-exact)
   transfers this to the underlying sets of the abelian inverse image of `K`.
7. As an `𝔽_p`-module sheaf (prop-weil-pbc-inverse-image-modules-exact (2),
   lem-pod-module-local-constancy-of-finite-underlying-operation-compatible-cover,
   lem-weil-pbc-finite-locally-constant-module-values (2)⇒(1)), `K|_V` is constructible in the
   module sense of def-weil-pbc-etale-constructible-sheaf on every trivializing affine `V`.
8. For a quasi-compact quasi-separated open `W ⊆ S`, cover `W` by such affines `V`;
   lem-weil-pbc-constructible-qcqs-affine-local, (3)⇒(1) on each `V` and (2)⇒(3) on `W`,
   gives a finite constructible stratification of `W` witnessing module constructibility of
   `K|_W`; forgetting the module structure (lem-weil-pbc-constructible-module-underlying-sets)
   and lem-weil-pbc-finite-local-abelian-forget give the stated finite locally constant
   underlying sets on each stratum.
-/
theorem frobenius_linear_vector_bundle_constructible
    (p : ℕ) [Fact p.Prime]
    (S : Scheme.{u}) [S.Over (Spec (.of (ULift.{u} (ZMod p))))]
    (E : S.Modules) [E.IsQuasicoherent] [E.IsFiniteLocallyFree]
    (F : (Modules.etaleTensorSectionsSheaf E) ⟶ Modules.etaleTensorSectionsSheaf E)
    (hF : ∀ (U : S.Etale) (a : Γ(U.left, ⊤))
      (e : Γ((Modules.tensorPullback U.hom).obj E, ⊤)),
      F.hom.app (op U)
          ((((Modules.tensorPullback U.hom).obj E).smul a).hom e) =
        (((Modules.tensorPullback U.hom).obj E).smul (a ^ p)).hom
          (F.hom.app (op U) e)) :
    IsZero (cokernel (F - 𝟙 _)) ∧
      ∀ (U : S.Opens), CompactSpace U.toScheme → QuasiSeparatedSpace U.toScheme →
        ∃ T : FiniteLocallyClosedStratification U.toScheme,
          (∀ k : Fin T.n, Topology.IsConstructible (T.stratum k)) ∧
          (∀ k : Fin T.n,
            IsFiniteLocallyConstantSheafOfTypes
              ((sheafCompose (T.domain k).smallEtaleTopology
                (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
                ((Etale.upperStar (AddCommGrpCat.{u + 1})
                  (T.immersion k ≫ U.ι)).obj
                  ((sheafCompose S.smallEtaleTopology
                    AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
                    (kernel (F - 𝟙 _)))))) := by
  sorry

end Scheme

end AlgebraicGeometry
