/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-! # The symmetric algebra of a quasi-coherent module

Source: Stacks Project, Modules, Section 01CF and Lemmas 01CG, 01CL; Schemes,
Section 01LA (9) (blueprint: lem-weil-pbc-quasi-coherent-symmetric-algebra).

The algebra is a commutative ring sheaf under the structure sheaf. The affine comparison
is a ring equivalence commuting with the structure homomorphism and the degree-one map;
this is precisely the canonical algebra isomorphism, without choosing algebra instances.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- The symmetric algebra of a quasi-coherent module is a quasi-coherent algebra sheaf,
with its universal degree-one map and the canonical affine-section algebra isomorphisms.
Source: Stacks Project, Modules, Section 01CF, Lemmas 01CG, 01CL; Schemes, Section 01LA (9)
(blueprint: lem-weil-pbc-quasi-coherent-symmetric-algebra).

Proof: (1) Form the presheaf of sectionwise symmetric algebras. Its restrictions are the
unique algebra maps extending module restriction, by
lem-weil-pbc-symmetric-algebra-universal-property; uniqueness gives the presheaf identities.
(2) Sheafify its commutative rings using lem-weil-pbc-ring-sheafification-space-underlying-
abelian. Compose the sheafification unit with the degree-one maps to obtain `j`.
(3) Extend a module map sectionwise by the symmetric algebra universal property; uniqueness
makes the extensions natural. The sheafification universal property gives exactly one
algebra-sheaf morphism. Uniqueness also gives functoriality in the input module.
(4) On an affine open `U`, compare the tilde of Sym(F(U)) with the restriction of the
algebra sheaf, using lem-weil-pbc-affine-tilde-gamma-adjunction and
lem-weil-pbc-spec-module-tilde-sections. The comparison extends the sheafification unit.
(5) On nested affine opens, lem-weil-pbc-quasi-coherent-affine-section-base-change and
lem-weil-pbc-symmetric-algebra-base-change identify both presheaf sections with the same
base change; the comparisons respect restrictions.
(6) The unit is bijective on stalks by lem-weil-pbc-stalk-sheafification-space and the
underlying-abelian sheafification comparison. Represent germs on affine neighbourhoods:
Step (5) gives surjectivity, and injectivity follows by restricting a zero germ further.
Then lem-weil-pbc-module-iso-on-stalks makes the tilde comparison an isomorphism.
(7) These local tilde descriptions give quasi-coherence. Taking sections on `U` in the
comparison and the tilde global-section isomorphism gives the canonical algebra
isomorphism. Its compatibility with degree one identifies it with the algebra lift. -/
theorem exists_quasiCoherentSymmetricAlgebra
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent] :
    ∃ (S : X.CommAlgebraSheaf) (j : F ⟶ S.toModule),
      S.toModule.IsQuasicoherent ∧
      (∀ (B : X.CommAlgebraSheaf) (f : F ⟶ B.toModule),
        ∃! t : S ⟶ B, ∀ (U : X.Opens) (x : F.val.obj (op U)),
          (t.right.hom.app (op U)) (j.val.app (op U) x) = f.val.app (op U) x) ∧
      (∀ (U : X.affineOpens),
        ∃ e : SymmetricAlgebra (X.presheaf.obj (op U.1)) (F.val.obj (op U.1)) ≃+*
            S.right.obj.obj (op U.1),
          (∀ r : X.presheaf.obj (op U.1),
            e (algebraMap (X.presheaf.obj (op U.1))
              (SymmetricAlgebra (X.presheaf.obj (op U.1)) (F.val.obj (op U.1))) r) =
              S.hom.hom.app (op U.1) r) ∧
          (∀ x : F.val.obj (op U.1),
            e (SymmetricAlgebra.ι (X.presheaf.obj (op U.1)) (F.val.obj (op U.1)) x) =
              j.val.app (op U.1) x)) := by
  sorry

end AlgebraicGeometry
