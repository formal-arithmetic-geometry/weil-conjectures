/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Sheaf.AlgebraicGeometry.ProjGradedModuleSheafExists
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules

import Sheaf.AlgebraicGeometry.ProjShiftedFreeTwist
import Sheaf.AlgebraicGeometry.ProjStandardOpenProperties
import Sheaf.Topology.SheafOfModulesFromBasis

/-!
# Associated sheaves of homogeneous bases on polynomial Proj

Source: Stacks Project, Constructions, Definitions 01M6, 01MN and Lemma 01M7.
(blueprint: lem-sc-p1-homogeneous-basis-proj-coproduct).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace LocalizedModule HomogeneousLocalization
open MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A homogeneous basis identifies its associated sheaf with the coproduct of Proj twists.
Source: Stacks Project, Constructions, Definitions 01M6, 01MN and Lemma 01M7;
blueprint lem-sc-p1-graded-resolution, shifted-free clause.
(blueprint: lem-sc-p1-homogeneous-basis-proj-coproduct).

Proof: The basis coordinate equivalence identifies M with the finite product of S.
Expand each coefficient into its homogeneous components. Multiplication of its degree-n
part by the basis vector b a places it in degree n-d a, by scalar compatibility.
Uniqueness of the internal decomposition implies that the degree-j elements correspond
exactly to tuples with a-coordinate homogeneous of degree d a+j, and zero if this integer
is negative. Thus the coordinate equivalence and its inverse preserve the grading.
The finite coproduct of Proj twists has precisely the associated-sheaf charts of this
shifted coordinate module, by proj_shifted_free_is_twist. On each positive homogeneous
standard open, localize the coordinate equivalence and restrict to degree-zero fractions.
Compose with the supplied injective chart maps and the inverse of the canonical chart
maps to obtain mutually inverse linear section maps. These commute with restrictions:
both send y/f^m to its coordinate tuple divided by f^m, and restricting to D(g), where
g^e=a*f, multiplies the numerator by a^m and changes the denominator to g^(e*m).
The positive homogeneous standard opens form a basis. Glue these compatible maps and
their inverses; equality on this basis proves their composites are identities.
This construction requires only the given charts, not additional stalk identifications.
For r=0 the basis identifies M with zero and the sheaf with the empty coproduct. -/
theorem homogeneous_basis_proj_coproduct (k : Type u) [Field k]
    (M : ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (𝓜 : ℤ → AddSubgroup M) (h𝓜 : DirectSum.IsInternal 𝓜)
    (hsmul : ∀ (n : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : M),
      a ∈ homogeneousSubmodule (Fin 2) k n → y ∈ 𝓜 z → a • y ∈ 𝓜 (n + z))
    (F : (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    (alpha : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ),
      0 < d → f ∈ homogeneousSubmodule (Fin 2) k d →
      F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
        LocalizedModule.Away f M)
    (halpha : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d),
        Function.Injective (alpha f d hd hf) ∧
        Set.range (alpha f d hd hf) = degreeZeroFractions
          (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
          (fun n : ℕ ↦ (𝓜 n : Set M)) (Submonoid.powers f))
    (hscalar : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
        (r : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
        (s : F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
        alpha f d hd hf (awayToSection (homogeneousSubmodule (Fin 2) k) f r • s) =
          algebraMap (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
            (Localization.Away f) r • alpha f d hd hf s)
    (hres : ∀ (f g : MvPolynomial (Fin 2) k) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
        (hg : g ∈ homogeneousSubmodule (Fin 2) k b)
        (inc : basicOpen (homogeneousSubmodule (Fin 2) k) g ≤
          basicOpen (homogeneousSubmodule (Fin 2) k) f)
        (e c : ℕ) (a : MvPolynomial (Fin 2) k),
        0 < e → a ∈ homogeneousSubmodule (Fin 2) k c → g ^ e = a * f →
        ∀ (m : ℕ) (y : M)
          (s : F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
          alpha f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
          alpha g b hb hg (F.val.map (homOfLE inc).op s) =
            mk (a ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g))
    (r : ℕ) (d : Fin r → ℤ)
    (b : Module.Basis (Fin r) (MvPolynomial (Fin 2) k) M)
    (hb : ∀ a : Fin r, b a ∈ 𝓜 (-(d a))) :
    Nonempty (F ≅ ∐ (fun a ↦ twist (homogeneousSubmodule (Fin 2) k) (d a))) := by
  sorry

end AlgebraicGeometry.Proj
