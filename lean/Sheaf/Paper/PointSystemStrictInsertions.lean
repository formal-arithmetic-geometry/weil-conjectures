/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.Paper.PointSystemInsertionData

/-! # Strict point insertions before localization

Source: Stacks Tags 03CB, 0H7J and 0941; the indicated steps of the parent proof.
(blueprint: lem-trf-point-system-strict-insertions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [local irreducible] HasDerivedCategory.standard
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PointSystemInsertion
variable (k : Type t) [Field k] (h : Aut (Spec (.of k)))
  (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
attribute [local irreducible] G sections

/-- Point restriction gives a natural insertion of entire strict systems, with the
specified restriction formula and tower composition identity.
Source: Stacks 03CB, 03CW, 03EK, 0941 and 015F; steps 5 and 6 of
`lem-trf-point-system-insertion-composition`.
(blueprint: lem-trf-point-system-strict-insertions).

Proof: at each level take restriction in the original abelian sheaf along the
arrow from the final object reindexed by h^(r+1) to the final object. At completed
scalars the coefficient map and restriction agree on constant scalars: project
to each finite coefficient ring, use normalization of the constant sheaf map,
and use joint monicity of the limit projections. The restriction is consequently
linear over the common integral scalar ring. Equivalently, restrict scalars on
the completed-module restriction map and use b to identify its target with
sections of G. The section identity for b gives exactly the stated formula.
Naturality of presheaf restriction with respect to a morphism of the original
sequence module proves compatibility with all transitions and naturality in M;
there is no need to regard a semilinear transition as linear over one finite ring.
For composition, the two restriction arrows followed by the reindexing compositor
have the same underlying scheme arrow as the direct restriction: this is the
power identity h^(m+1) times h = h^(m+2). The section identity for t identifies its
underlying action with that compositor. Presheaf functoriality therefore gives
the equality at every coefficient level. Extensionality for tower maps proves
the equality of natural insertions. Their termwise construction and chain identity
are proved separately in the parent by degreewise extensionality. The zero module,
zero transitions and unbounded complexes are included;
no normalization or boundedness property is used. -/
theorem pointSystemStrictInsertions [IsAlgClosed k] (P : Maps k h l E)
    (_hP : SectionLaws k h l E P) :
    ∃ u : ∀ r : ℕ, sections k l E ⟶ G k h l E r ⋙ sections k l E,
      (∀ (r : ℕ) (M : coefficientSequenceModules l E (Spec (.of k))) (n : ℕ),
        HEq (fun x : ((sections k l E).obj M).obj (op n) ↦
            (((u r).app M).app (op n)) x)
          (fun x : M.val.obj (op (n, ProEt.mk (𝟙 (Spec (.of k))))) ↦
            M.val.presheaf.map
              (Prod.mkHom (𝟙 n) (pointRestrictionArrow (h ^ (r + 1)).hom)).op x)) ∧
      (∀ (m : ℕ) (M : coefficientSequenceModules l E (Spec (.of k))),
        (u (m + 1)).app M = (u m).app M ≫ (u 0).app ((G k h l E m).obj M) ≫
          (sections k l E).map ((P.t m).hom.app M)) := by sorry

end WeilConjectures.PointSystemInsertion
