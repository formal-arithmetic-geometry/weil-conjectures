/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.Paper.DerivedLocalIsomorphismSourceEvaluation
import Sheaf.Paper.NormalizedDerivedIsomorphismTransport
import Sheaf.Paper.ConstantDerivedNormalizationUniversal

/-! # Reduction and evaluation of normalized derived Isom-sheaf sections

Source: Stacks Project, Tags 06YY, 09BV and 0F63; step 6 of the compatible
finite derived trivializations proof.
(blueprint: lem-weil-pbc-normalized-derived-isomorphism-section-reduction).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Universal normalization arrows induce reduction on the actual local Isom sheaves,
and canonical source-site evaluation respects its normalization square.
The evaluation map is constructed separately, without an additional hole.
This assertion constructs no covering and assumes no local existence of isomorphisms.

Source: Stacks Project, Tags 06YY, 09BV and 0F63; step 6 of the compatible
finite derived trivializations proof.
(blueprint: lem-weil-pbc-normalized-derived-isomorphism-section-reduction).

Proof: On each localized etale site, scalar extension carries an isomorphism to an
isomorphism. Conjugate it by the normalization isomorphisms adjunct to dE and dK.
Exact restriction to a site object commutes with coefficient restriction; its mate
identifies scalar extension with restriction of scalar extension. Thus the specified
universal normalization arrows give these same conjugations on every slice. Their
naturality under restriction makes this a map of the local Isom presheaves and hence
of their sheafifications. The separately constructed sourceDerivedIsoEvaluation identifies
the slice and source Isom presheaves using localization equivalences, pulls back their
sheafifications, and applies the unique inverse of the pro-etale sheafification unit
on a weakly contractible affine (0F63). Naturality, composition and scalar-extension
compatibility of this evaluation identify
reduction with the normalized scalar extension. Adjunction takes this equation to the
displayed square involving exactly the canonical localProEtaleNormalization maps.
No boundedness, finite Tor dimension or nonempty-stalk assumption is needed for this
map construction; bijectivity of the comparison evaluation is not asserted. -/
theorem normalized_derived_isomorphism_section_reduction
    (X : Scheme.{u}) (B : ℕ → Type (u + 1)) [∀ n : ℕ, CommRing (B n)]
    [∀ n : ℕ, Finite (B n)] (q : ∀ n : ℕ, B (n + 1) →+* B n)
    (E : ∀ n : ℕ, DerivedCategory (ModuleCat.{u + 1} (B n)))
    (K : ∀ n : ℕ, DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (B n))))
    (dE : ∀ n : ℕ, E (n + 1) ⟶ (normalizationModuleRestrict (q n)).obj (E n))
    (dK : ∀ n : ℕ, K (n + 1) ⟶
      (normalizationRestrict X.smallEtaleTopology (q n)).obj (K n))
    (hη : ∀ n : ℕ, Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk (dE n))))
    (hρ : ∀ n : ℕ, Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk (dK n)))) :
    ∃ r : ∀ n : ℕ,
      derivedLocalIsomorphismSheaf ((normalizationConstant X.smallEtaleTopology).obj
        (E (n + 1))) (K (n + 1)) ⟶
      derivedLocalIsomorphismSheaf ((normalizationConstant X.smallEtaleTopology).obj
        (E n)) (K n),
      ∀ (n : ℕ) (U : X.ProEt) (ha : IsAffine U.left)
        (hw : (ProEt.topology X).IsWeaklyContractible.{u + 1} U)
        (s : ((Functor.sheafPullbackConstruction.sheafPullback (toProEt X)
          (Type (u + 1)) X.smallEtaleTopology (ProEt.topology X)).obj
          (derivedLocalIsomorphismSheaf ((normalizationConstant X.smallEtaleTopology).obj
            (E (n + 1))) (K (n + 1)))).obj.obj (op U)),
        (sourceDerivedIsoEvaluation X (B (n + 1))
          ((normalizationConstant X.smallEtaleTopology).obj (E (n + 1)))
          (K (n + 1)) U ha hw s).hom ≫ localProEtaleNormalization U.hom (q n) (dK n) =
          localProEtaleNormalization U.hom (q n)
              (normalizationConstantArrow X.smallEtaleTopology (q n) (dE n)) ≫
            (normalizationRestrict (ProEt.topology U.left) (q n)).map
              (sourceDerivedIsoEvaluation X (B n)
                ((normalizationConstant X.smallEtaleTopology).obj (E n)) (K n) U ha hw
                (((Functor.sheafPullbackConstruction.sheafPullback (toProEt X)
                  (Type (u + 1)) X.smallEtaleTopology (ProEt.topology X)).map
                    (r n)).hom.app (op U) s)).hom := by
  classical
  have h (n : ℕ) := source_normalized_iso_reduction X (B (n + 1)) (B n) (q n)
    ((normalizationConstant X.smallEtaleTopology).obj (E (n + 1))) (K (n + 1))
    ((normalizationConstant X.smallEtaleTopology).obj (E n)) (K n)
    (normalizationConstantArrow X.smallEtaleTopology (q n) (dE n)) (dK n)
    (normalizationConstantArrow_isUniversal X.smallEtaleTopology (q n) (dE n) (hη n)).some
    (hρ n).some
  choose r hr using h
  exact ⟨r, hr⟩

end AlgebraicGeometry.Scheme
