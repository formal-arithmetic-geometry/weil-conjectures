/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V5
-/
module

public import Sheaf.Paper.ExternalRHomConePairing
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel
import Sheaf.SixFunctors.ResolvingDerivedAdjunction
import Sheaf.Algebra.Homology.OneKFlatChainTranspose

/-! # Evaluation-normalized representatives of global derived Hom -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Etale.ExternalRHom
variable (A : Type (u + 1)) [CommRing A]

/-- Global cochains compute global derived Hom, with the canonical evaluation.
Source: Stacks Project, Cohomology on Sites, Tags 0A8X, 0A96, 08J9 and 08JA
(blueprint: lem-pur-global-hom-evaluation-model).

Proof: the upper degree bound and flat terms make E K-flat. Realize ordinary
module sheaves as modules over the constant ring sheaf. The internal Hom from E
into I is K-injective: tensoring an acyclic complex with E is acyclic, and the
chain tensor-Hom adjunction sends maps to I to null homotopic maps. Thus both
internal derived Hom and its right-derived sections are computed on this Hom
complex. Product projections and the constant/sections adjunction identify its
sections A-linearly with the displayed global cochains; the projections send the
Hom differential to d_I f - (-1)^n f d_E. With the native product-total
internal Hom convention this identification multiplies the (p,n) component by
(-1)^(p*n); its internal differential has the extra (-1)^p. The sign identities
p*(n+1)=p*n+p and (p+1)*n=p*n+n verify compatibility. This yields the
comparison isomorphism.
For an arbitrary alpha and chain map satisfying the stated evaluation equation,
the projections show that its ordinary transpose is alpha. The resolving derived
adjunction identity for constants and sections, followed by the one-sided K-flat
tensor-Hom identity, identifies its localized transpose with Q(alpha) followed
by this isomorphism. These equations are exactly the defining property of HomModel.
Products allow unbounded I and arbitrary coefficient complexes. Zero complexes,
negative degrees, and the zero coefficient ring obey the same formulas. -/
theorem globalHom_evaluation_model {X : Scheme.{u}} (E I : Complexes A X)
    [I.IsKInjective] (hE : IsBoundedFlat A E) : Nonempty (HomModel A E I) := by
  sorry

end AlgebraicGeometry.Etale.ExternalRHom
