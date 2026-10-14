/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.Paper.CechComplexAugmentations

/-! # Resolution columns of the Cech map induced by lambda

Source: Stacks Project, Tags 01FD and 01EX; Derived Categories, Tag 015E.
(blueprint: lem-sc-cech-pushforward-lambda-columns)
-/

@[expose] public section

universe v
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules

/-- Cech of a quasi-isomorphism from pushed-forward injectives to injectives is
columnwise a quasi-isomorphism in the resolution direction.
Source: Stacks 01FD, the arrow B-double-prime to B-prime; 01EX and Derived Categories 015E.
(blueprint: lem-sc-cech-pushforward-lambda-columns)

Proof: For each source tuple intersection V, pushforwards of injectives are acyclic
for sections on V by 01EX. The target injectives are section-acyclic as well. Apply
Leray acyclicity 015E to the given bounded-below quasi-isomorphism, restricted to V.
It follows that evaluation of lambda on V is a quasi-isomorphism. In each fixed
Cech degree q the resolution column is the product over all (q+1)-tuples of those
section complexes. Products of module groups are exact, so their homology is the
product of the homology groups. Thus the product map is a quasi-isomorphism. The
finite-product open chosen by the Cech functor is canonically the intersection V,
so its scalar restriction does not change this conclusion. Empty tuple sets give
zero complexes, and empty intersections and zero terms cause no exception. No
covering, quasi-coherence, or invertibility of an alpha map is used.
-/
theorem cech_pushforward_lambda_columns {X X' : Scheme.{v}} (f : X' ⟶ X)
    {ι : Type v} (U : ι → X.Opens) (A : CochainComplex X'.Modules ℕ)
    (K : CochainComplex X.Modules ℕ)
    (hA : ∀ n : ℕ, Injective (A.X n)) (hK : ∀ n : ℕ, Injective (K.X n))
    (l : ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj A ⟶ K)
    (hl : QuasiIso l) (q : ℕ) :
    QuasiIso (((HomologicalComplex₂.flipFunctor (ModuleCat.{v} Γ(X, ⊤))
      (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map
        ((moduleCechDoubleFunctor U).map l)).f q) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
