/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionMap
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators

/-! # Compatibility of Veronese numerators with tensor-power transitions

Source: Stacks Project, Properties, equation module-invert-s (Tag 0B5L),
Lemma 01PW(2), and the Veronese localization in the proof of Lemma 01Q1.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory DirectSum

namespace AlgebraicGeometry.Scheme.Modules

/-- Transporting a tensor-power transition to the section ring multiplies the numerator
by the corresponding power of the homogeneous section.
Source: Stacks Project, Properties, equation module-invert-s (Tag 0B5L),
Lemma 01PW(2), and the Veronese localization in the proof of Lemma 01Q1.
(blueprint: lem-sc-section-ring-veronese-numerator-transition)

Proof: cover X by opens on which L has a free generator e. Its tensor powers have generators
obtained by repeatedly tensoring e, with the zeroth generator the unit section. Induction on
the exponent in tensorPowAddIso and tensorPowMulIso shows that these isomorphisms send the
respective tensor products of these generators to the generator of the total tensor exponent;
the left unitor deletes the unit generator. Thus the inverse numerator isomorphism sends a
numerator with coefficient f to the same coefficient f in degree n*d. Write s locally as
c times the degree-d generator. The morphism homOfGlobalSection sends 1 to this section;
its b-th tensor power sends 1 to c^b times the degree-b*d generator. The definition of
mulTensorPowSection therefore sends the numerator with coefficient f to the numerator with
coefficient f*c^b. By the definition of graded multiplication, multiplying its ring numerator
by s^b has that same coefficient in degree (n+b)*d. Naturality of all the isomorphisms and
of tensor sections identifies these calculations with restrictions of the two global ring
numerators. The sheaf separatedness axiom glues their equality. The calculation includes
n=0, b=0, d=0, and zero coefficients, without dividing by c or assuming s nonzero.
-/
theorem sectionRingVeroneseNumerator_transition
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) (n b : ℕ)
    (t : Γ((𝟙_ X.Modules) ⊗ (L.tensorPow d).tensorPow n, ⊤)) :
    (sectionRingVeroneseNumerator X L d (n + b)
      ((mulTensorPowSection (homOfGlobalSection (L.tensorPow d) (s.val d))
        (𝟙_ X.Modules) n b).app ⊤ t)).val =
      (sectionRingVeroneseNumerator X L d n t).val * s.val ^ b := by sorry

end AlgebraicGeometry.Scheme.Modules
