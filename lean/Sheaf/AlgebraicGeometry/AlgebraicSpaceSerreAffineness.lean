/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceCommAlgebraSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme

import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteAffineSubatlas
import WeilConjectures.AlgebraicGeometry.QuasiCompactH1Zero
import WeilConjectures.AlgebraicGeometry.EtaleZariskiQcohComparison
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import Mathlib.AlgebraicGeometry.Limits

/-! # Serre affineness for algebraic spaces

Source: Stacks Project, Spaces Cohomology, Proposition 07V6 and Situation 07UY
(blueprint: lem-sfb-space-serre-affineness).

Cohomology is Mathlib's cohomology of the underlying additive sheaf on the full small
etale site, with its standard Ext universe. No atlas, affine base, or separation of
X over the given base S is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A qcqs algebraic space with vanishing H1 for every quasi-coherent module is affine.
Source: Stacks Project, Spaces Cohomology, Tag 07V6, in Situation 07UY
(blueprint: lem-sfb-space-serre-affineness).

Proof:
1. Set A = Gamma(X,O_X). By lem-sfb-space-acyclic-affinization-geometry, the absolute
   canonical map p : X -> Spec A is separated and universally injective. Use
   lem-a1-space-affine-etale-cover, lem-a1-space-finite-affine-subatlas and
   lem-weil-pbc-finite-affine-coproduct-spectrum to obtain a surjective etale chart
   phi : U = Spec B -> X with U affine.
2. By lem-sfb-space-affine-etale-polynomial-generators there is a surjection
   O_X[z_1,...,z_m] -> phi_*O_U with quasi-coherent kernel K. The hypothesis kills
   H1(X,K). The long exact sequence lem-weil-pbc-derived-functor-long-exact on
   underlying additive sheaves makes the induced map of global sections onto B
   surjective, using def-weil-pbc-sites-and-cohomology.
3. By lem-sfb-space-cohomology-filtered-colimit in degree zero, sections of the
   polynomial algebra are A[z_1,...,z_m]: use the finite sums of monomial summands
   O_X as its filtered system. Finite sums are finite products, preserved by sections.
   Multiplication agrees on monomials, so this is a ring identification. Hence B is
   a finite type A-algebra.
4. Regard X as a space over Spec Z by def-trf-algebraic-space and Stacks 04SG:
   on T its absolute sheaf is the disjoint union of X(T -> S) over all T -> S.
   This preserves charts, fibre products, points and the small etale ringed site.
   Apply lem-sfb-space-local-properties-chart-test over Spec Z to U -> X -> Spec A.
   By def-weil-finite-type-morphism, U -> Spec A is locally of finite type, so p is.
   Universal injectivity makes each field fibre have at most one point and hence
   discrete. Then lem-sfb-space-discrete-fibres-locally-quasifinite makes p locally
   quasi-finite.
5. Apply lem-a1-separated-locally-qf-space-representable to p, obtaining a scheme Z
   representing the absolute space X. Its point space is quasi-compact. For each
   quasi-coherent Zariski ideal I, lem-trf-scheme-zariski-etale-quasi-coherent-equivalence
   gives a quasi-coherent etale module. Transport the hypothesis to Z and apply
   lem-sc-etale-zariski-qcoh-comparison in degree one. Thus H1(Z,I) vanishes, and
   lem-pqf-quasicompact-h1-zero makes Z affine. Evaluate h_Z -> X -> h_S on id_Z
   to recover the scheme map Z -> S. Naturality and the 04SG equivalence identify
   its relative Yoneda presheaf with the original X, giving the stated conclusion. -/
theorem exists_affine_scheme_of_qcqs_h1_zero {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hqc : CompactSpace (Point X.obj.obj)) (hqs : IsAbsolutelyQuasiSeparated X)
    (hH : ∀ (F : X.Modules) (_ : F.IsQuasicoherent),
      Subsingleton (@Sheaf.H _ _ X.etaleTopology
        ((SheafOfModules.toSheaf X.structureSheaf).obj F) inferInstance
        (HasExt.standard (Sheaf X.etaleTopology AddCommGrpCat.{u})) 1)) :
    ∃ Z : Over S, IsAffine Z.left ∧ Nonempty (yoneda.obj Z ≅ X.obj.obj) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
