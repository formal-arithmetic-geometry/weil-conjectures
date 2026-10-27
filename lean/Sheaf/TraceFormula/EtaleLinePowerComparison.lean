/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65, SHEAF group W4
-/
module

public import Sheaf.TraceFormula.EtalePowerProductNormalization

/-!
# Restriction comparison for canonical étale tensor-power products

Source: Stacks Project, sites-modules.tex, Tag 03EL, iterated with the tensor unit;
spaces-descent.tex, Tag 0D3C
(blueprint: lem-trf-etale-line-power-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Restriction of a canonically normalized power algebra is identified with the
actual powers of the restricted module. Only a single étale map is involved; no
direct image, cartesian square, coproduct, or evaluation is needed here.
Source: Stacks Project, sites-modules.tex, Tag 03EL, and spaces-descent.tex, Tag 0D3C
(blueprint: lem-trf-etale-line-power-comparison).

Proof: on scheme charts localization leaves regular functions unchanged. The
localized sheaf-tensor comparison keeps both factors of every pure tensor and
commutes with the sheafification unit. The tensor universal property makes the
comparisons agree on overlaps, so they descend through the small-site restriction
equivalences. In degree zero use the identity on regular functions. In degree one
use the canonical unitors and the equivalence unit, so that the first-power square
in the conclusion commutes. Iterating the tensor comparison gives theta in every
degree, with inverse obtained by the inverse tensor comparisons. Define the target
products and unit by transporting D along these isomorphisms; the algebra laws
follow from those of D. These are genuine constructions from the isomorphisms,
not arbitrary witnesses selected from a mere existence statement.
To check their canonical normalization, concatenate local tensors. Both paths
retain the same ordered factors and multiply the same scalar coefficients. When
one degree is zero this is multiplication by a regular function. The sheaf tensor
universal property and uniqueness of sheafification extension give the equality
on all sections. The assumptions identifying D with restriction of A therefore
identify the transported products with the prescribed canonical products. Theta
is an algebra homomorphism by its transport construction. -/
theorem etale_line_power_comparison {X X' : AlgebraicSpace S}
    (h : X' ⟶ X) (hh : IsEtale h.hom.hom) (L : X.Modules)
    (A : EtaleGradedModuleAlgebra (evaluationLinePower X L))
    (hA : HasCanonicalEtalePowerProducts X L A)
    (D : EtaleGradedModuleAlgebra
      (fun d ↦ (pullback h hh).obj (evaluationLinePower X L d)))
    (hmul : ∀ (m n : ℕ) (V : X'.EtaleSite)
      (s : ((pullback h hh).obj (evaluationLinePower X L m)).val.obj (op V))
      (t : ((pullback h hh).obj (evaluationLinePower X L n)).val.obj (op V)),
      D.mul m n V s t = A.mul m n ((etaleMap h hh).obj V) s t)
    (hunit : ∀ (V : X'.EtaleSite) (a : X'.structureSheaf.obj.obj (op V)),
      D.unit.val.app (op V) a = A.unit.val.app (op ((etaleMap h hh).obj V)) a) :
    ∃ (A' : EtaleGradedModuleAlgebra (evaluationLinePower X' ((pullback h hh).obj L)))
      (theta : ∀ d : ℕ, (pullback h hh).obj (evaluationLinePower X L d) ≅
        evaluationLinePower X' ((pullback h hh).obj L) d)
      (thetaHom : D.Hom A'),
      HasCanonicalEtalePowerProducts X' ((pullback h hh).obj L) A' ∧
      (∀ d, thetaHom.degree d = (theta d).hom) ∧
      ((theta 1).hom ≫ (gradedPowerOneIso X' ((pullback h hh).obj L)).hom =
        (pullback h hh).map (gradedPowerOneIso X L).hom) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
