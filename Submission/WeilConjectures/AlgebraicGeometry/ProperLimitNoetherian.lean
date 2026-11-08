/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Submission.WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
import Submission.WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Submission.WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Submission.WeilConjectures.CategoryTheory.CommAlgebraSheafModule
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Submission.WeilConjectures.AlgebraicGeometry.AffineAlgebraLocalMaps
import Submission.WeilConjectures.AlgebraicGeometry.EventuallyProper
import Submission.WeilConjectures.AlgebraicGeometry.ProperFinitePresentationClosedLimit
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Submission.WeilConjectures.AlgebraicGeometry.ProperLimitNoetherianCore

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Proper morphisms as limits of proper finite-type models

Source: Stacks limits.tex, Tag 0A0P (proper-limit-of-proper-finite-presentation-noetherian)
(blueprint: lem-weil-pbc-proper-limit-noetherian).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A proper morphism over a quasi-compact and quasi-separated scheme is a limit of
proper morphisms over schemes of finite type over `ℤ`, with affine transitions.
Source: Stacks limits.tex, Tag 0A0P (proper-limit-of-proper-finite-presentation-noetherian)
(blueprint: lem-weil-pbc-proper-limit-noetherian).
Proof:
1. Use lem-weil-pbc-proper-closed-in-proper-fp (09ZR) to choose a closed immersion
   X → Y over S with Y → S proper and finitely presented.
2. Apply prop-nagata-noetherian-inverse-system (01ZA) and
   lem-weil-pbc-cofiltered-limit-directed-reindex to approximate S by finite-type
   schemes Sⱼ over ℤ with affine transitions. If S is affine, use the finitely generated
   subrings from lemma-nagata-noetherian-inverse-system-affine instead.
3. Descend Y to a finitely presented Yⱼ₀ → Sⱼ₀ by thm-pd-spreading-out (01ZM).
   Its base changes Yⱼ have affine transition maps and limit Y.
4. Enlarge j₀ using lem-weil-pbc-eventually-proper (081F). All Yⱼ → Sⱼ are now proper
   by lem-weil-pbc-proper-base-change.
5. For j ≥ j₀, take the scheme-theoretic image Zⱼ of X → Yⱼ, using
   lem-weil-pbc-scheme-image-qc-kernel. The closed immersion Zⱼ → Yⱼ makes Zⱼ → Sⱼ
   proper by lem-weil-pbc-closed-immersion-proper.
6. The image ideals are the kernels on affine opens, so transitions Yⱼ' → Yⱼ induce
   unique compatible Zⱼ' → Zⱼ. These are affine: their factorization through
   Zⱼ ×_{Sⱼ} Sⱼ' is a closed immersion by lem-weil-pbc-closed-immersion-from-composite,
   followed by an affine projection. The image factorizations give cones from X and S.
7. On affine opens of Yⱼ₀, write the coordinate ring of X as (B ⊗ R)/𝔞. The rings of
   Zⱼ are (B ⊗ Rⱼ)/ker(B ⊗ Rⱼ → (B ⊗ R)/𝔞). Their filtered colimit is (B ⊗ R)/𝔞:
   injectivity follows from the kernel definition and surjectivity from R = colim Rⱼ.
   By lem-weil-pbc-limit-affine-transition and lem-weil-pbc-spec-colimit-limit these
   local computations identify X with lim Zⱼ, and the local isomorphisms glue.
8. Restricting to j ≥ j₀ preserves the base limit by
   lem-weil-pbc-colimit-initial-full-subcategory. The commuting cone equations identify
   f with the limiting morphism, and all the required properties hold.
9. For affine S = Spec A, the chosen base stages are spectra of finitely generated
   subrings. Their directed union is A; restricting to the cofinal tail preserves this
   colimit (def-weil-pbc-category-colimit). The global-section maps induced by the
   base cone form the colimit cocone, whose vertex is Γ(S) ≅ A. -/
theorem exists_proper_limit_noetherian
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
      (Xs Ss : Λᵒᵖ ⥤ Scheme.{u}) (fs : Xs ⟶ Ss)
      (πX : (Functor.const Λᵒᵖ).obj X ⟶ Xs) (πS : (Functor.const Λᵒᵖ).obj S ⟶ Ss),
      Nonempty (IsLimit (Cone.mk X πX)) ∧ Nonempty (IsLimit (Cone.mk S πS)) ∧
      (∀ (i j : Λᵒᵖ) (a : i ⟶ j), IsAffineHom (Xs.map a) ∧ IsAffineHom (Ss.map a)) ∧
      (∀ i : Λᵒᵖ, IsProper (fs.app i)) ∧
      (∀ i : Λᵒᵖ, LocallyOfFiniteType (specULiftZIsTerminal.from (Ss.obj i)) ∧
        QuasiCompact (specULiftZIsTerminal.from (Ss.obj i))) ∧
      (∀ i : Λᵒᵖ, πX.app i ≫ fs.app i = f ≫ πS.app i) ∧
      (IsAffine S →
        (∀ i : Λᵒᵖ, IsAffine (Ss.obj i) ∧
          RingHom.FiniteType (algebraMap ℤ (Scheme.Γ.obj (Opposite.op (Ss.obj i))))) ∧
        Nonempty (IsColimit (Scheme.Γ.mapCocone (Cone.mk S πS).op))) := by
  by_cases hS : IsAffine S
  · obtain ⟨Λ, hpre, hne, hdir, Xs, Ss, fs, πX, πS, hlimX, hlimS,
      htrans, hproper, hfinite, hcomm, haff, hcol⟩ :=
      proper_limit_noetherian_affine_clause f hS
    exact ⟨Λ, hpre, hne, hdir, Xs, Ss, fs, πX, πS, hlimX, hlimS,
      htrans, hproper, hfinite, hcomm, fun _ => ⟨haff, hcol⟩⟩
  · obtain ⟨Λ, hpre, hne, hdir, Xs, Ss, fs, πX, πS, hlimX, hlimS,
      htrans, hproper, hfinite, hcomm⟩ := exists_proper_limit_noetherian_core f
    exact ⟨Λ, hpre, hne, hdir, Xs, Ss, fs, πX, πS, hlimX, hlimS,
      htrans, hproper, hfinite, hcomm, fun h => (hS h).elim⟩

end AlgebraicGeometry
