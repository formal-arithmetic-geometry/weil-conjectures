/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import Sheaf.AlgebraicGeometry.ProEtaleStalkConservative
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationExact
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Detection of vanishing on affine weakly contractible pro-etale objects

Source: Stacks Project, Tags 0990, 0946 and 0947
(blueprint: lem-sf-proetale-vanishing-detection).

The two equivalences give zero and acyclicity detection on the whole pro-etale topos.
The final theorem states the resulting joint conservativity. This does not assert
conservativity of geometric stalks: the warning in clause (4) of
`lem-cbc-proetale-stalk-conservative` is supplied by the imported
`Scheme.proEtaleFunctionsQuotient_counterexample`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (T : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
  [TopologicalSpace Λ] [DiscreteTopology Λ]

/-- A finite-coefficient module sheaf is zero exactly when all of its sections on affine
weakly contractible pro-etale objects are zero.
Source: Stacks Project, Tag 0990 and the sheaf equalizer axiom, clause (i)
(blueprint: lem-sf-proetale-vanishing-detection).

Proof: zero module sheaves have zero sections. Conversely, for each site object V,
use lem-weil-pbc-proetale-affine-wcontractible-covering-family to cover V by affine
weakly contractible objects. The set-sheaf local-surjectivity definition used here
is equivalent to its epimorphism formulation in that covering lemma. The equalizer
axiom of def-weil-pbc-sites-and-cohomology embeds F(V) into the product of its
sections on the covering objects. If these sections vanish, F(V) vanishes. Since V
was arbitrary, the underlying abelian sheaf and hence the module sheaf are zero.
The empty cover gives the same argument over the empty scheme. -/
theorem finiteCoefficient_isZero_iff_forall_affine_weaklyContractible
    (F : FiniteCoefficientModules T Λ) :
    IsZero F ↔
      ∀ (W : T.ProEt), IsAffine W.left →
        (Scheme.ProEt.topology T).IsWeaklyContractible.{u + 1} W →
          Subsingleton
            ((SheafOfModules.evaluation (finiteCoefficientRingSheaf T Λ) (op W)).obj F):= by
  sorry

/-- A complex of finite-coefficient module sheaves is acyclic exactly when every evaluation
on an affine weakly contractible pro-etale object is acyclic.
Source: Stacks Project, Tags 0990, 0946 (1), 0947 (1), 03CY and 03DA, clause (ii)
(blueprint: lem-sf-proetale-vanishing-detection).

Proof:
1. Forget the possibly noncommutative coefficient action. By the kernel and
   sheafified-cokernel descriptions of def-weil-sheaf-of-modules-category, the
   forgetful functor to abelian sheaves preserves homology and detects zero.
2. Give an abelian sheaf its sectionwise integer action. Apply
   lem-pc-sites-module-sheafification-interface to the constant integer ring
   presheaf and this module presheaf. Its ring sheafification is the integer
   coefficient sheaf from def-weil-pbc-proetale-site. Since the abelian presheaf
   already is a sheaf, its sheafification is canonically itself. This equips it
   functorially with that ring-sheaf action without changing sections or homology.
3. At each weakly contractible W, apply
   lem-weil-pbc-proetale-weakly-contractible-evaluation-exact to that commutative
   integer ring sheaf. It identifies the underlying groups of H^n(K(W)) and
   (H^n(K))(W), for every n. Thus K acyclic implies every K(W) acyclic.
4. Conversely, if all K(W) are acyclic, all sections (H^n(K))(W) vanish. Clause
   (i) makes each homology sheaf zero, so K is acyclic. Work degree by degree;
   no boundedness assumption or commutativity of the original ring is used. -/
theorem finiteCoefficient_acyclic_iff_forall_affine_weaklyContractible
    (K : CochainComplex (FiniteCoefficientModules T Λ) ℤ) :
    K.Acyclic ↔
      ∀ (W : T.ProEt), IsAffine W.left →
        (Scheme.ProEt.topology T).IsWeaklyContractible.{u + 1} W →
          HomologicalComplex.Acyclic
            (((SheafOfModules.evaluation
              (finiteCoefficientRingSheaf T Λ) (op W)).mapHomologicalComplex _).obj K):= by
  sorry

/-- The affine weakly contractible evaluation functors are jointly conservative on
finite-coefficient module sheaves on the entire small pro-etale site.
Source: Stacks Project, Tags 0946 and 0947; the blueprint's concluding detection sentence
(blueprint: lem-sf-proetale-vanishing-detection).

Proof: an isomorphism stays an isomorphism under every evaluation functor.
Conversely, use the homology-preserving evaluation argument from clause (ii)
(first forget coefficients and give abelian sheaves the integer-sheaf action).
If all evaluations of f are isomorphisms, its kernel and cokernel have zero
sections on all affine weakly contractible objects. Clause (i) makes them zero.
In the abelian module-sheaf category, a morphism with zero kernel and cokernel
is an isomorphism. The stalk warning is precisely clause (4) of the imported
lem-cbc-proetale-stalk-conservative and makes no universal claim for every scheme. -/
theorem finiteCoefficient_isIso_iff_forall_affine_weaklyContractible
    (F G : FiniteCoefficientModules T Λ) (f : F ⟶ G) :
    IsIso f ↔
      ∀ (W : T.ProEt), IsAffine W.left →
        (Scheme.ProEt.topology T).IsWeaklyContractible.{u + 1} W →
          IsIso ((SheafOfModules.evaluation (finiteCoefficientRingSheaf T Λ) (op W)).map f):= by
  sorry

end AlgebraicGeometry.ProEtale
