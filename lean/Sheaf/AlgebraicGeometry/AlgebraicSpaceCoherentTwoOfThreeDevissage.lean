/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedIdealFiltration
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.Topology.Irreducible

import Sheaf.AlgebraicGeometry.AlgebraicSpaceCoherentAbelian
import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedCoherentModules
import Sheaf.AlgebraicGeometry.AlgebraicSpaceCoherentSupportIdealPower
import Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport
import Sheaf.AlgebraicGeometry.AlgebraicSpacePowerIdealKills
import Sheaf.AlgebraicGeometry.AlgebraicSpaceCoherentIdealFiltration

/-! # Two-out-of-three coherent devissage on a Noetherian algebraic space

Source: Stacks Project, Spaces Cohomology, Tag 08AN,
lemma-property-higher-rank-cohomological-variant
(blueprint: lem-sfb-space-coherent-two-of-three-devissage).

Coherence is site quasi-coherence together with coherence on every scheme chart.
Annihilator equality is expanded using all local restrictions, and the defining ideal
is the existing kernel computed by the canonical direct-image chart projections.
Finite sums are specified by bilimit bicones in the ambient module-sheaf category.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A property satisfying zero, two-out-of-three, positive finite-sum reflection and
one witness with prescribed annihilator on each reduced irreducible closed subspace
holds for every coherent module.
Source: Stacks Project, Spaces Cohomology, Tag 08AN,
lemma-property-higher-rank-cohomological-variant, with the zero hypothesis explicit
(blueprint: lem-sfb-space-coherent-two-of-three-devissage).

Proof:
1. The coherent-abelian, Noetherian-coherent-support, closed-coherent-modules and
   closed-immersion-quasi-coherent-modules lemmas ensure that kernels, cokernels,
   finite sums, extensions, ideals and their closed pushforwards used below are
   coherent; closed pushforward is exact on quasi-coherent modules.
2. For a witness M on i : Z → X, write J for the defining ideal. Since Ann(M) = J,
   JM = 0, so coherent-support-ideal-power gives Supp(M) ⊆ |Z|. Conversely give the
   closed support of M its reduced structure W, using reduced-closed-support. A
   power of its defining ideal L kills M, hence L^n ⊆ J. On affine charts this gives
   V(J) ⊆ V(L^n) = V(L), and therefore Supp(M) = |Z|.
3. On a nonempty reduced Noetherian Z, a nonzero quasi-coherent ideal A has proper
   zero locus: otherwise power-ideal-kills applied to O_Z makes A nilpotent, contrary
   to reducedness (exponent zero would force the nonempty structure sheaf to vanish).
   A module killed by A consequently has proper support.
4. If an ideal pushforward fails P, noetherian-space-topology supplies a minimal bad
   nonempty irreducible closed support T. Reduced-closed-support makes its reduced
   structure unique. The zero ideal cannot be bad by P(0) and isomorphism invariance.
5. The support-controlled coherent-ideal-filtration lemma and minimality give P for
   every coherent module supported strictly inside T, by successive short exact
   sequences starting at zero. Empty support gives a length-zero filtration.
6. Choose the witness M for T. The reduced-support-generic-ideal-inclusion lemma
   gives r ≥ 1, a nonzero coherent ideal K on Z, and an injection i_*(K^r) → M with
   coherent cokernel supported strictly inside T. Closed-coherent-modules makes i_*K
   coherent. The direct-image universal property identifies i_*(K^r) with (i_*K)^r:
   finite module sums are products, which commute with the defining section limits.
7. Step 5 gives P for this cokernel. Two-out-of-three and P(M) give P(i_*(K^r));
   finite-sum reflection and isomorphism invariance give P(i_*K).
8. For another nonzero ideal A on Z, put C = K ∩ A. Coherent-abelian and the coherent
   submodule lemma make C and both quotients coherent. Since A(K/C) = K(A/C) = 0,
   step 3 and the closed-pushforward support formula give both quotient pushforwards
   proper support inside T, hence P by step 5. The zero ideal is handled by P(0).
9. Exact closed pushforward of 0 → C → K → K/C → 0 first gives P(i_*C), and of
   0 → C → A → A/C → 0 then gives P(i_*A). This contradicts minimal badness.
10. Thus all ideal-pushforward factors have P. The coherent-ideal-filtration lemma
    and induction using two-out-of-three, starting at P(0), give P for every coherent
    F. Length zero includes F = 0 and the empty space. -/
theorem coherent_two_of_three_devissage
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    (hqc : CompactSpace (Point X.obj.obj))
    (hqs : ∀ (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj)
      (b : yoneda.obj V ⟶ X.obj.obj), IsAffine U.left → IsAffine V.left →
        CompactSpace (Point (Limits.pullback a b)))
    (P : X.Modules → Prop)
    (hP_iso : ∀ (F G : X.Modules) (_e : F ≅ G),
      F.IsQuasicoherent →
      (∀ T : X.EtaleSite, RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
        ((X.schemeRestriction T).obj F)) →
      G.IsQuasicoherent →
      (∀ T : X.EtaleSite, RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
        ((X.schemeRestriction T).obj G)) → P F → P G)
    (hP_zero : P (⊤_ X.Modules))
    (hP_seq : ∀ c : ShortComplex X.Modules, c.ShortExact →
      c.X₁.IsQuasicoherent →
      (∀ T : X.EtaleSite, RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
        ((X.schemeRestriction T).obj c.X₁)) →
      c.X₂.IsQuasicoherent →
      (∀ T : X.EtaleSite, RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
        ((X.schemeRestriction T).obj c.X₂)) →
      c.X₃.IsQuasicoherent →
      (∀ T : X.EtaleSite, RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
        ((X.schemeRestriction T).obj c.X₃)) →
      ((P c.X₁ ∧ P c.X₂) ∨ (P c.X₁ ∧ P c.X₃) ∨ (P c.X₂ ∧ P c.X₃)) →
        P c.X₁ ∧ P c.X₂ ∧ P c.X₃)
    (hP_sum : ∀ F : X.Modules, F.IsQuasicoherent →
      (∀ T : X.EtaleSite, RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
        ((X.schemeRestriction T).obj F)) →
      ∀ r : ℕ, 1 ≤ r → ∀ b : Bicone (fun _ : Fin r ↦ F),
        b.IsBilimit → P b.pt → P F)
    (hP_witness : ∀ (Z : AlgebraicSpace S) (i : Z ⟶ X),
      IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom →
      (∀ T : Z.EtaleSite, IsReduced (Z.etaleForget.obj T)) →
      IrreducibleSpace (Point Z.obj.obj) →
      ∃ M : X.Modules, M.IsQuasicoherent ∧
        (∀ T : X.EtaleSite, RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
          ((X.schemeRestriction T).obj M)) ∧ P M ∧
        ∀ (T : X.EtaleSite) (a : X.structureSheaf.obj.obj (op T)),
          (∀ (V : X.EtaleSite) (f : V ⟶ T) (m : M.val.obj (op V)),
            X.structureSheaf.obj.map f.op a • m = 0) ↔ a ∈ closedIdealSections i T) :
    ∀ F : X.Modules, F.IsQuasicoherent →
      (∀ T : X.EtaleSite, RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
        ((X.schemeRestriction T).obj F)) → P F := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
