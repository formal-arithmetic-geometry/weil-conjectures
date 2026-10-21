/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.AlgebraicGeometry.CondensedScalarRealization
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.Topology.Irreducible

import Sheaf.AlgebraicGeometry.ProEtale.WeaklyContractibleBasis
import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.RingTheory.ProEtale.ClosedLiftMap
import WeilConjectures.RingTheory.ProEtale.ClosedLift
import Sheaf.RingTheory.IndEtaleUniverseTransport
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity
import Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality
import Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation
import Sheaf.AlgebraicGeometry.GenericFiberComponentsSection
import Sheaf.RingTheory.ProEtale.HenselianClosedLift

/-! # Dualizable condensed complexes and local perfect scalar models

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Definition 3.3(1),
the following stability observation, Definition 3.5 and Theorem 4.13
(blueprint: lem-zl-condensed-dualizable-local-perfect-models).
All categories are ordinary unbounded derived categories of the published internal module
sheaves. Scalar realization uses the constant-section coefficient map, with derived extension.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})

/-- Dualizable objects contain zero and are closed under isomorphisms, all integer shifts
and distinguished cones, with no condition on the components of X.
`HasRightDual` is the existing exact pairing with both evaluation/coevaluation identities.
Source: HRS, observation after Definition 3.3
(blueprint: lem-zl-condensed-dualizable-local-perfect-models).

Proof (DAG step 1): choose a w-contractible affine pro-etale basis
(sk-thm-pe-weakly-contractible-basis). By lem-zl-condensed-lisse-proetale-locality,
dualizability can be checked there. The equivalence of
lem-zl-condensed-wcontractible-lisse-evaluation identifies dualizable terms and their map
with perfect complexes over the section ring. Choose bounded finite-projective
representatives (def-pc-perfect-ring-complex). By lem-pc-ring-derived-map-representative
the map has a chain representative. Its cone has terms Q^n plus P^(n+1), hence is again
bounded finite projective. The evaluation functor is exact, so this gives the third
term of the distinguished triangle. The zero and shifted complexes are likewise bounded
finite projective, and isomorphisms preserve the pairing. Descend by locality. -/
theorem condensed_dualizable_stable :
    Nonempty (HasRightDual (0 : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))) ∧
    (∀ K L : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      Nonempty (K ≅ L) → Nonempty (HasRightDual K) → Nonempty (HasRightDual L)) ∧
    (∀ (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
        (n : ℤ), Nonempty (HasRightDual K) → Nonempty (HasRightDual (K⟦n⟧))) ∧
    (∀ T : Triangle (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      T ∈ distTriang _ → Nonempty (HasRightDual T.obj₁) →
        Nonempty (HasRightDual T.obj₂) → Nonempty (HasRightDual T.obj₃)) := by
  sorry

/-- On schemes with Zariski locally finitely many irreducible components, dualizability
is equivalent to pro-etale local realization of perfect complexes over Γ(*,Λ).
The cover members have independent scalar complexes. No coefficient flatness or
regularity is assumed.
Source: HRS, Definition 3.5 and Theorem 4.13
(blueprint: lem-zl-condensed-dualizable-local-perfect-models).

Proof, following DAG steps 2--7:
2. A perfect scalar complex remains perfect after any base change: a finite projective
summand of R^n becomes the corresponding summand of A^n, without flatness of A/R.
On a w-contractible affine the evaluation equivalence makes its realization dualizable.
Use lem-zl-condensed-lisse-proetale-locality twice to descend from that basis to each
cover member and then to X. This direction holds for every scheme.
3. For nonempty irreducible affine X choose a geometric generic point η. Pullback
preserves dualizability. Evaluation at η gives a perfect R-complex P. Choose an affine
faithfully flat ind-etale w-contractible cover U by
lem-weil-pbc-source-wcontractible-extension; evaluation writes K|U as π_U^*M.
4. lem-zl-generic-fiber-components-section gives a section of π₀(U_η) → π₀(U).
The component-square equivalence identifies the restriction of M with the scalar model
of P. Pull back along the section, then apply π_U^* and its scalar compatibility.
Thus K|U has that same scalar model P.
5. On affine X with finitely many irreducible components, give each component its
reduced closed structure (lem-weil-pbc-reduced-induced-closed-subscheme). They cover X
(lem-sc-irreducible-components-cover). Cover each by a w-contractible ind-etale affine
W_a and apply steps 3--4 there, obtaining possibly different P_a.
6. Lift W_a via def-exc-ind-etale-closed-lift. Its indexing category is filtered
(lem-exc-closed-lift-filtered), its closed fiber is W_a (lem-exc-closed-lift-reduction),
and its pair is henselian (lem-zl-henselian-indetale-closed-lift). By
lem-zl-condensed-henselian-lisse-rigidity the lift V_a is w-contractible and restriction
on dualizable complexes is fully faithful. Both the restricted K and its scalar model
are dualizable, so lift the isomorphism and its inverse; faithfulness proves they invert.
7. The finite family V_a → X is weakly etale (lem-weil-pbc-ind-etale-stability), and its
images cover the components. Its finite affine disjoint union is fpqc, hence a pro-etale
cover. For general X, take affine open neighborhoods inside the finite-component open
neighborhoods and compose their covers. Intersecting finitely many irreducible closed
sets with an open gives finitely many possible components. The empty scheme uses the
empty cover. No uniform rank or amplitude is imposed on the scalar models. -/
theorem condensed_dualizable_iff_local_perfect
    (_hcomponents : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ (irreducibleComponents U).Finite)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    Nonempty (HasRightDual K) ↔
      ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
        ∃ P : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ)),
          DerivedCategory.IsPerfectRingComplex P ∧
          Nonempty (((CondensedRing.upperStar Λ (𝒰.f i)).mapDerivedCategory).obj K ≅
            (condensedScalarRealization Λ (𝒰.X i)).obj P) := by
  sorry

end AlgebraicGeometry.ProEtale
