/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.Algebra.Category.Grp.Ulift

/-!
# Kernel transport to an open étale chart

Source: Stacks Project, Tags 03DR, 03DT and 0GKU.
(blueprint: lem-fd-frobenius-linear-kernel-etale-pullback).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Restriction to an open étale chart transports F, its scalar law, and its kernel.

Source: Stacks Project, Tags 03DR (35.8.0.1), 03DT, and 0GKU, the passage to a
trivializing open in the proof of lemma-frobenius-linear-on-vb.
(blueprint: lem-fd-frobenius-linear-kernel-etale-pullback).

Proof: use etaleTensorSectionsSheaf_openIdentification to identify restriction of
the given sheaf with the tensor-section sheaf of the ordinary module restriction.
The unit-normalized tensor/abstract pullback comparison identifies this restriction
with E_V; compose it with the supplied isomorphism to G and apply the tensor-section
functor. These natural comparisons are linear over each test object's section ring,
as their prescribed components are evaluations of module isomorphisms. Conjugate the
restricted endomorphism by their composite to define F_V. Linearity of the comparison
and its inverse transports the scalar-power law. Étale inverse image is site
restriction, hence preserves kernels; universe lifting of abelian sheaves also
preserves the sectionwise kernel universal property. Combine these comparisons with
the kernel isomorphism induced by conjugating F-1. Identity and empty open immersions
use the same comparisons; no characteristic, finite-rank, or affineness is required.
-/
theorem frobenius_linear_kernel_etale_pullback
    (p : ℕ) (S : Scheme.{u}) (E : S.Modules) [E.IsQuasicoherent]
    (F : (Modules.etaleTensorSectionsSheaf E) ⟶ Modules.etaleTensorSectionsSheaf E)
    (hF : ∀ (U : S.Etale) (a : Γ(U.left, ⊤))
      (e : Γ((Modules.tensorPullback U.hom).obj E, ⊤)),
      F.hom.app (op U)
          ((((Modules.tensorPullback U.hom).obj E).smul a).hom e) =
        (((Modules.tensorPullback U.hom).obj E).smul (a ^ p)).hom
          (F.hom.app (op U) e))
    (V : S.Etale) [IsOpenImmersion V.hom] (G : V.left.Modules) [G.IsQuasicoherent]
    (α : (Modules.tensorPullback V.hom).obj E ≅ G) :
    ∃ F' : Modules.etaleTensorSectionsSheaf G ⟶ Modules.etaleTensorSectionsSheaf G,
      (∀ (W : V.left.Etale) (a : Γ(W.left, ⊤))
        (m : Γ((Modules.tensorPullback W.hom).obj G, ⊤)),
        F'.hom.app (op W) ((((Modules.tensorPullback W.hom).obj G).smul a).hom m) =
          (((Modules.tensorPullback W.hom).obj G).smul (a ^ p)).hom
            (F'.hom.app (op W) m)) ∧
      Nonempty
        (((Etale.upperStar AddCommGrpCat.{u + 1} V.hom).obj
          ((sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
            (kernel (F - 𝟙 _)))) ≅
          ((sheafCompose V.left.smallEtaleTopology
            AddCommGrpCat.uliftFunctor.{u + 1, u}).obj (kernel (F' - 𝟙 _)))) := by
  sorry

end AlgebraicGeometry.Scheme
