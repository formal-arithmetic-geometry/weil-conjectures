/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceArtinRees
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

import Sheaf.AlgebraicGeometry.AlgebraicSpaceCoherentAbelian
import Sheaf.AlgebraicGeometry.AlgebraicSpaceCoherentIdealFiltration
import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedCoherentModules
import Sheaf.AlgebraicGeometry.SpaceGenericMultipleEmbedding

/-! # Higher-rank coherent devissage on algebraic spaces

Source: Stacks Project, Spaces Cohomology, Tag 07UT,
lemma-property-higher-rank-cohomological (blueprint: lem-sfb-space-coherent-devissage).

On locally Noetherian spaces, coherence is finite presentation on the small etale site
(Tag 07UB), as in the coherent ideal filtration. Finite products are finite direct sums
in the additive module category. Quotients are specified by their cokernel universal
property; the containment in IG uses the existing locally generated ideal-product sections.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- An isomorphism-invariant property containing zero, closed under coherent extensions
and descending from positive finite sums, holds for all coherent modules if each reduced
irreducible closed subspace admits the full-support module and ideal-submodule witnesses
below. The zero condition includes the empty space.

Source: Stacks Project, Spaces Cohomology, Tag 07UT,
lemma-property-higher-rank-cohomological (blueprint: lem-sfb-space-coherent-devissage).

Proof:
1. By lem-sfb-space-coherent-abelian, finite sums are coherent. The zero and extension
   hypotheses and isomorphism invariance pass P along finite coherent filtrations and
   give closure under positive finite sums, by the split short exact sequences.
2. Induct on closed subsets T of |X| using lem-sfb-noetherian-space-topology. Apply
   lem-sfb-space-coherent-ideal-filtration to F supported in T. Empty support gives zero.
   Factors supported properly inside T satisfy P by induction. It remains to treat a
   full-support factor i_*H on a reduced irreducible closed subspace Z with image T.
3. By lem-sfb-space-closed-coherent-modules, Z is Noetherian. Choose G from the closed
   subspace hypothesis. By lem-sfb-space-generic-multiple-embedding there are positive
   a,b, a nonzero quasi-coherent ideal J and a monomorphism (JG)^a -> H^b, an isomorphism
   on a nonempty open V.
4. The hypothesis for J gives G' inside JG, with P(i_*G') and proper closed support B
   of G/G'. By lem-sfb-space-noetherian-coherent-support, G' is coherent. By
   lem-sfb-space-coherent-abelian the cokernel C of (G')^a -> H^b is coherent. On V minus
   B this map is an isomorphism; irreducibility makes that open nonempty. The support
   lemma therefore makes Supp(C) proper closed in |Z|.
5. By lem-sfb-space-closed-immersion-quasi-coherent-modules, closed direct image is exact.
   By lem-sfb-space-closed-coherent-modules it preserves coherence and transports support.
   Push forward the short exact sequence. Induction gives P(i_*C); finite sums give
   P((i_*G')^a). Extension closure gives P((i_*H)^b), and positive-sum descent gives
   P(i_*H). Assemble the filtration by step 1 and take T = |X|. -/
theorem coherent_property_higher_rank_devissage
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    (hqc : CompactSpace (Point X.obj.obj))
    (hqs : ∀ (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj)
      (b : yoneda.obj V ⟶ X.obj.obj), IsAffine U.left → IsAffine V.left →
        CompactSpace (Point (Limits.pullback a b)))
    (P : X.Modules → Prop)
    (hP_iso : ∀ (F H : X.Modules), (F ≅ H) → P F → P H)
    (hP_zero : ∀ F : X.Modules, IsZero F → P F)
    (hP_extension : ∀ c : ShortComplex X.Modules, c.ShortExact →
      c.X₁.IsFinitePresentation → c.X₂.IsFinitePresentation → c.X₃.IsFinitePresentation →
      P c.X₁ → P c.X₃ → P c.X₂)
    (hP_sum : ∀ (F : X.Modules) (r : ℕ), F.IsFinitePresentation → 1 ≤ r →
      P (∏ᶜ fun _ : Fin r ↦ F) → P F)
    (hP_closed : ∀ (Z : AlgebraicSpace S) (i : Z ⟶ X),
      IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom →
      (∀ T : Z.EtaleSite, IsReduced (Z.etaleForget.obj T)) →
      IrreducibleSpace (Point Z.obj.obj) →
      ∃ G : Z.Modules, G.IsFinitePresentation ∧ moduleSupport G = Set.univ ∧
        ∀ I : QuasiCoherentIdeal Z, ¬ IsZero (I.val : Z.Modules) →
          ∃ (G' : Z.Modules) (g : G' ⟶ G), Mono g ∧ G'.IsQuasicoherent ∧
            (∀ (T : Z.EtaleSite) (s : G'.val.obj (op T)),
              g.val.app (op T) s ∈ idealPowerSubsheafSections I.val.arrow G
                (fun _ ↦ Set.univ) 1 T) ∧
            (∃ (Q : Z.Modules) (q : G ⟶ Q) (w : g ≫ q = 0),
              Nonempty (IsColimit (CokernelCofork.ofπ q w)) ∧
              IsClosed (moduleSupport Q) ∧ moduleSupport Q ≠ Set.univ) ∧
            P ((moduleDirectImage i).obj G')) :
    ∀ F : X.Modules, F.IsFinitePresentation → P F := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
