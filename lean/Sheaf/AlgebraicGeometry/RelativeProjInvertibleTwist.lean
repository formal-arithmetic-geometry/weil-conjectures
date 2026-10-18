/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q137
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
import Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Projective bundles are invariant under invertible twists

Source: Stacks Project, Constructions, Tag 02NC, lemma-twisting-and-proj, specialized
to the symmetric algebra (blueprint: lem-trf-relative-proj-invertible-twist).
The affine frame formula specifies the canonical isomorphism: its inverse is Proj of
the symmetric-algebra map sending v to v tensor s for any local frame s of L tensor-power n.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry

/-- The canonical S-isomorphism P(E) ≅ P(E tensor L tensor-power n).
Source: Stacks Project, Constructions, Tag 02NC (lemma-twisting-and-proj)
(blueprint: lem-trf-relative-proj-invertible-twist).

Proof: (1) Trivialize L on an affine open cover using def-sc-invertible-module and
lem-weil-pbc-affine-opens-basis. Tensoring with the nth power of each frame identifies E
with its twist (def-pur-sheaf-tensor-product), so the twist is quasi-coherent and finite type
(pqf-def-coherent). The zeroth power is the structure sheaf.
(2) Extend these module isomorphisms by the universal property of the symmetric algebra
(lem-weil-pbc-quasi-coherent-symmetric-algebra). Both composites fix its generators, hence
are identities. Their monomial description makes the maps graded and fixes degree zero
(lem-weil-pbc-symmetric-algebra-graded).
(3) Apply lem-nagata-affine-proj-scalar-extension with the identity base map: on each standard
chart the map is a/f^m ↦ beta(a)/beta(f)^m in the degree-zero homogeneous localization
(def-nagata-homogeneous-localization-degree-zero).
(4) Apply the same construction to the inverse algebra map. The fraction formulas compose
to the identity, so gluing uniqueness gives inverse scheme maps (def-weil-affine-spectrum,
lem-weil-pbc-scheme-morphism-gluing). The affine identifications of def-nagata-relative-proj
regard these as maps of the relative projective bundles over each affine base.
(5) Replacing a frame of L by u times that frame scales degree k by u^(n*k). In a/f^m,
a has degree m*d and f degree d, so the unit factors cancel. This uses no cancellation of f.
Equivalently, any frame of L tensor-power n gives the same Proj map, since its change of
frame scales degree k by the kth power of a unit.
(6) The generator formulas and fraction maps commute with restriction of the affine base;
this is the compatibility in def-nagata-relative-proj, also for the inverse maps.
(7) Refine overlaps by affine opens, compare on the standard chart cover
(prop-nagata-proj-standard-open), and glue the local maps and inverses. Their structure-map
equalities glue as well. The same comparison on common refinements proves independence of
all frames and covers, and uniqueness with the displayed affine formula. The resulting
inverse gives the requested isomorphism in the projective-bundle convention of
def-trf-projective-bundle-morphism. -/
theorem exists_unique_relativeProj_invertible_twist
    (S : Scheme.{u}) (E L : S.Modules) [E.IsQuasicoherent] [E.IsFiniteType]
    [L.IsInvertible] (n : ℕ) :
    ∃! e : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj ≅
        (@SymmetricAlgebraSheaf.gradedAlgebraData S (E ⊗ L.tensorPow n)
          (Scheme.Modules.isQuasicoherent_tensorObj E (L.tensorPow n))).relProj,
      e.hom ≫ (@SymmetricAlgebraSheaf.gradedAlgebraData S (E ⊗ L.tensorPow n)
          (Scheme.Modules.isQuasicoherent_tensorObj E (L.tensorPow n))).relProjHom =
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ∧
      ∀ (U : S.affineOpens) (s : Γ(L.tensorPow n, U.1)),
        Scheme.Modules.IsFreeGenerator s →
        ∃ (β : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U →+*ᵍ
              (@SymmetricAlgebraSheaf.gradedAlgebraData S (E ⊗ L.tensorPow n)
                (Scheme.Modules.isQuasicoherent_tensorObj E (L.tensorPow n))).grading U)
          (hβ : HomogeneousIdeal.irrelevant
              ((@SymmetricAlgebraSheaf.gradedAlgebraData S (E ⊗ L.tensorPow n)
                (Scheme.Modules.isQuasicoherent_tensorObj E (L.tensorPow n))).grading U) ≤
            (HomogeneousIdeal.irrelevant
              ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)).map β),
          (∀ r : Γ(S, U.1),
            β (algebraMap Γ(S, U.1) (SymmetricAlgebraSheaf.sections E (op U.1)) r) =
              algebraMap Γ(S, U.1)
                (SymmetricAlgebraSheaf.sections (E ⊗ L.tensorPow n) (op U.1)) r) ∧
          (∀ v : Γ(E, U.1),
            β (SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1)) v) =
              SymmetricAlgebra.ι Γ(S, U.1) ((E ⊗ L.tensorPow n).val.obj (op U.1))
                (Scheme.Modules.tmulSection v s)) ∧
          (@SymmetricAlgebraSheaf.gradedAlgebraData S (E ⊗ L.tensorPow n)
              (Scheme.Modules.isQuasicoherent_tensorObj E (L.tensorPow n))).relProjι U ≫
            e.inv = Proj.map β hβ ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U := by
  sorry

end AlgebraicGeometry
