/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LineSubbundleProjectiveDivisorData
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.LineSubbundleProjectiveDivisorCore
import WeilConjectures.AlgebraicGeometry.LineSubbundleProjectiveDivisorFiniteType

/-! # The projective quotient by a line subbundle

Source: Stacks Project, Tag 0FI5, `proposition-chern-class`, the line-subbundle paragraph;
Tags 01OB and 01X0 for the quotient convention and the divisor line.
(blueprint: lem-pur-line-subbundle-projective-divisor).

Projective bundles and their twists are the normalized symmetric-algebra realizations already
used by `ProjectiveBundleTautologicalGeometry`. The section has the literal target
`O(1) ⊗ p*(Lᵛ)`, using the inverse of the canonical
transpose-of-evaluation dual comparison. The divisor-line isomorphism is normalized by its
canonical section.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- The quotient projective bundle is the regular zero divisor of the tautological
line-subbundle section. The equation on the tautological quotient specifies the morphism
induced by `F → G`; the equation on the divisor section specifies the canonical divisor-line
identification, not just an isomorphism class. The finite-type conclusion is conditional on
the base structure morphism, so the main assertion holds over every scheme.

Source: Stacks Project, Tag 0FI5, `proposition-chern-class`, line-subbundle paragraph;
Tag 01OB (quotient projective bundles), Tag 01X0 (`lemma-characterize-OD`).
(blueprint: lem-pur-line-subbundle-projective-divisor).

Proof:
1. By def-amb-finite-locally-free-module, trivialize L and G near each base point. Lift the
   finitely many basis sections of G after shrinking. Exactness gives an adapted frame of F,
   with L its first coordinate.
2. In this frame Sym(F) → Sym(G) is A[X_0,...,X_(r-1)] → A[X_1,...,X_(r-1)], X_0 ↦ 0.
   prop-nagata-relative-proj-functoriality gives the closed immersion over S. Its tautological
   quotient identifies i*O_P(1) with O_Q(1), using
   lem-trf-projective-bundle-quotient-geometry and the normalized charts of
   lem-pur-projective-bundle-tautological-geometry.
3. The composite p*L → O_P(1) has coefficient X_0/X_j on D_+(X_j), j>0, and coefficient
   1 on D_+(X_0). The adjoint section has the same coefficients and the same zero ideal.
   def-pc-zero-scheme and lem-pc-zero-scheme-divisor-iso identify these local ideals; hence
   the zero ideal equals the kernel ideal of the closed immersion scheme-theoretically.
4. def-nagata-relative-projective-space and lem-weil-pbc-dehomogenization-polynomial-ring
   make X_0/X_j a polynomial variable over A, hence a nonzerodivisor even
   if A has nilpotents. On D_+(X_0) use the nonzerodivisor 1. This proves invertibility of
   the zero ideal by def-nagata-effective-cartier-ideal, making i an effective Cartier centre.
5. As in lem-pc-zero-scheme-divisor-iso, the dual of the section maps its inverse line
   isomorphically onto the kernel ideal; def-pc-divisor-line-bundle identifies its dual.
   Dualizing gives O_P(Q) ≅ O_P(1) ⊗ p*(Lᵛ). This isomorphism sends the dual of the ideal
   inclusion, the canonical divisor section, to the original section, as recorded below.
6. Both projective-bundle projections are proper, since r and r-1 are positive. Composing
   them with any separated finite-type structure map S → Spec(k) gives separated
   finite-type structure maps for P and Q, by lem-weil-pbc-proper-fp-permanence and
   lem-sfb-finite-type-composition-base-change. No regularity or reducedness of S is used.

In Lean, steps 1-5 are `lineSubbundle_projective_divisor_core`
(blueprint: lem-pur-line-subbundle-projective-divisor-core) and step 6 is
`lineSubbundle_projective_divisor_finite_type`
(blueprint: lem-pur-line-subbundle-projective-divisor-finite-type); the proof below
combines their conjunctions. -/
theorem lineSubbundle_projective_divisor
    (S : Scheme.{u}) (r : ℕ) (hr : 2 ≤ r)
    (L F G : S.Modules) [L.IsInvertible]
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank (r - 1)]
    (ι : L ⟶ F) (π : F ⟶ G) (w : ι ≫ π = 0)
    (hexact : (ShortComplex.mk ι π w).ShortExact)
    (P : ProjectiveBundleRealization S F) (Q : ProjectiveBundleRealization S G) :
    P.L.IsInvertible ∧ Q.L.IsInvertible ∧
    ∃ (i : Q.A.data.relProj ⟶ P.A.data.relProj)
      (hi : i ≫ P.A.data.relProjHom = Q.A.data.relProjHom)
      (θ : (Scheme.Modules.tensorPullback i).obj P.L ≅ Q.L),
      IsClosedImmersion i ∧
      (Scheme.Modules.tensorPullback i).map P.quotient ≫ θ.hom =
        ((projectiveBundlePullbackComp i P.A.data.relProjHom).app F).hom ≫
          (projectiveBundlePullbackCongr hi).hom.app F ≫
          (Scheme.Modules.tensorPullback Q.A.data.relProjHom).map π ≫ Q.quotient ∧
      i.ker = (lineSubbundleProjectiveSection P ι).zeroLocus ∧
      (lineSubbundleProjectiveSection P ι).zeroLocus.IsInvertible ∧
      IsEffectiveCartierCenter i ∧
      (∃ δ : i.ker.toModulesᵛ ≅
          P.L ⊗ (Scheme.Modules.tensorPullback P.A.data.relProjHom).obj Lᵛ,
        Scheme.Modules.dualUnitIso.inv ≫ Scheme.Modules.dualMap i.ker.toModulesι ≫ δ.hom =
          lineSubbundleProjectiveSection P ι) ∧
      ∀ (k : Type u) [Field k] (a : S ⟶ Spec (.of k)),
        IsSeparated a → LocallyOfFiniteType a → QuasiCompact a →
        IsSeparated (P.A.data.relProjHom ≫ a) ∧
          LocallyOfFiniteType (P.A.data.relProjHom ≫ a) ∧
          QuasiCompact (P.A.data.relProjHom ≫ a) ∧
          IsSeparated (Q.A.data.relProjHom ≫ a) ∧
          LocallyOfFiniteType (Q.A.data.relProjHom ≫ a) ∧
          QuasiCompact (Q.A.data.relProjHom ≫ a) := by
  obtain ⟨hP, hQ, i, hi, θ, hclosed, hquot, hker, hreg, heff, hδ⟩ :=
    lineSubbundle_projective_divisor_core S r hr L F G ι π w hexact P Q
  have hfin := lineSubbundle_projective_divisor_finite_type S r hr L F G P Q
  exact ⟨hP, hQ, i, hi, θ, hclosed, hquot, hker, hreg, heff, hδ, hfin⟩

end AlgebraicGeometry
