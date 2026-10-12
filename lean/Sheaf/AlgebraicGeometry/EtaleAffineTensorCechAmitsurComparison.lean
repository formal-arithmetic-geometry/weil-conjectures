/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleFiniteAffineCechBasis
public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.RingTheory.FaithfullyFlat.Amitsur

import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.Paper.EtaleStandardCoverCech
import Sheaf.AlgebraicGeometry.EtaleSiteCechComplexComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.EtaleQuasiCoherentDescent
import Sheaf.AlgebraicGeometry.TensorPullback

/-! # Affine tensor-section Čech complexes as Amitsur complexes
Source: Stacks Project, Tags 03OZ and 03P2, affine-case proof.
(blueprint: new-etale-affine-tensor-cech-amitsur-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

/-- The finite affine tensor-section Čech complex is a lifted Amitsur complex.
Source: Stacks Project, Tag 03OZ and Tag 03P2, proof in the affine case.
(blueprint: new-etale-affine-tensor-cech-amitsur-comparison)

Proof: pull F back to U, retaining quasi-coherence, and identify its tensor sections
with the restriction from X using pullback composition. Reindex I by Fin n. Apply
Tag 03OZ to replace the finite affine cover by its affine disjoint union W → U.
Take A = Γ(U, O_U), B = Γ(W, O_W), a the restriction homomorphism, and
M = Γ(U, U.hom* F). The map W → U is flat and surjective, so a is faithfully flat.
Affine fibre products identify the rings of the iterated products of W over U
with tensor powers of B over A. The affine pullback-section formula identifies
sections of the pulled back module with M tensor those rings. Its pure-tensor
formula and pullback composition identify each restriction with the corresponding
Amitsur coface, so the degreewise isomorphisms commute with the differentials.
The equivalence between U's étale site and the over category over U preserves
products. Use nonempty_etale_siteCech_complex_iso for the chosen product cones;
Tag 03OZ supplies the comparison with the original family. Lift the group maps
and use the finite-product isomorphism for ULift to obtain the displayed complex
isomorphism. For an empty covering, U and W are empty, A and B are zero rings,
and M is zero; both complexes are zero. No exactness or cohomology vanishing is
used in this comparison. -/
theorem exists_etaleTensorSectionsSheaf_ulift_cech_amitsur_iso
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Etale) (I : Type (u + 1)) (V : I → X.Etale) (f : ∀ i : I, V i ⟶ U)
    (hf : finiteAffineEtaleCechCover X U I V f) :
    ∃ (B : CommRingCat.{u}) (a : Γ(U.left, ⊤) →+* B),
      letI : Algebra Γ(U.left, ⊤) B := a.toAlgebra
      Module.FaithfullyFlat Γ(U.left, ⊤) B ∧
        Nonempty (((cechComplexFunctor fun i : I ↦ Over.mk (f i)).obj
          ((Over.forget U).op ⋙
            ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
              (Modules.etaleTensorSectionsSheaf F)).obj)) ≅
          (((forget₂ (ModuleCat.{u} Γ(U.left, ⊤)) AddCommGrpCat.{u}) ⋙
            AddCommGrpCat.uliftFunctor.{u + 1, u}).mapHomologicalComplex (.up ℕ)).obj
              (Algebra.TensorProduct.amitsurComplex Γ(U.left, ⊤) B
                Γ((Modules.tensorPullback U.hom).obj F, ⊤))) := by sorry

end AlgebraicGeometry.Scheme
