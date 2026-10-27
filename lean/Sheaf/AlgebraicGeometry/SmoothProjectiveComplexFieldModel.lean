module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Ring.ULift
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.DescendSmoothQcqs
import WeilConjectures.AlgebraicGeometry.DescendClosedImmersion
import Sheaf.FieldTheory.CountableSimpleExtensionEmbedding
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Cardinality
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange

/-! # Smooth projective models over fields embeddable in the complex numbers

Source: Stacks Project, Limits, Tags 01ZM, 01ZP and 0C0C; Fields, Tags 09FZ and 09G1
(blueprint: lem-sfb-smooth-projective-complex-field-model).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A smooth projective scheme over a characteristic-zero field descends to a smooth
projective scheme over a finitely generated rational subfield with a complex embedding.
The isomorphism is over the given field. The complex base change uses the actual embedding
`σ`; `ULift` only places the complex numbers in the same universe as the schemes.

Source: Stacks Project, Limits, Tags 01ZM, 01ZP and 0C0C; Fields, Tags 09FZ and 09G1;
Morphisms, Tags 01VB and 01WF
(blueprint: lem-sfb-smooth-projective-complex-field-model).

Proof plan:
1. Index the subfields Q(A) by finite subsets A of F. The empty subset gives an index,
   unions give upper bounds, and every x lies in Q({x}). Compatible ring maps glue on
   elements using common upper bounds, so F is their ring colimit. Use
   lem-weil-pbc-limit-affine-transition to identify Spec F with their inverse limit.
   Stages are qcqs by lem-weil-pbc-affine-scheme-qcqs; transition morphisms are affine
   (pqf-def-affine-morphism), since field spectra have just one point.
2. Choose X embedded into finite projective space using def-pc-projective-morphism.
   Projectivity implies properness (lem-pc-projective-proper), hence quasi-compactness
   and separatedness (def-weil-proper-morphism). Smoothness gives local finite
   presentation (def-sbc-smooth-morphisms, def-sbc-locally-finite-presentation), so X
   is finitely presented. Projective spaces over the stages are proper by
   lemma-nagata-projective-space-base-change-proper. Fields are Noetherian since
   each ideal is zero or the unit ideal (def-weil-pbc-noetherian-ring); their spectra
   are locally Noetherian (pqf-def-locnoeth), so pqf-lem-lft-fp-locnoeth makes these
   projective spaces finitely presented as well.
3. Descend X and its chosen projective embedding by clauses (1) and (2) of
   thm-pd-spreading-out. Identify projective-space base changes by
   lemma-nagata-projective-space-base-change-pullback. The descended morphism is
   over the stage field. The source and target remain finitely presented and qcqs
   by lem-weil-pbc-qcqs-morphism-permanence and lem-weil-pbc-affine-scheme-qcqs.
4. The descended map to projective space is locally of finite type: choose affine
   target and source neighbourhoods, shrinking the source to a principal open in
   the inverse image. Its finite list of field-algebra generators also generates
   over the target coordinate ring, since the map respects the field structures
   (def-weil-finite-type-morphism).
5. Apply lem-weil-pbc-descend-smooth-qcqs to the structural map and then
   lem-weil-pbc-descend-closed-immersion to the descended projective embedding.
   Increase the stage as needed. Smoothness persists; the closed immersion and
   quasi-compactness give projectivity (def-pc-projective-morphism). The original
   base-change isomorphism is retained over F.
6. Write k = Q(b_1,...,b_r). Starting with the countable rationals and their usual
   complex embedding, apply lem-sfb-countable-simple-extension-embedding to each
   simple extension. The target is algebraically closed by
   lem-weil-complex-algebraically-closed and uncountable by
   lem-weil-complex-cardinality and Cantor's diagonal argument. This yields the
   embedding σ, including the case r = 0.
7. Form the pullback along Spec σ. Smoothness and projectivity follow from
   lem-pc-proper-base-change (smoothness clause) and lem-pc-projective-base-change.
   None of these steps needs nonemptiness, connectedness or geometric integrality.
-/
theorem exists_smooth_projective_complex_field_model
    (F : Type u) [Field F] [CharZero F] (X : Scheme.{u})
    (f : X ⟶ Spec (.of F)) [Smooth f] [IsProjective f] :
    ∃ k : IntermediateField ℚ F, k.FG ∧
      ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (.of k)),
        Smooth f₀ ∧ IsProjective f₀ ∧
        ∃ e : pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap k F))) ≅ X,
          e.hom ≫ f = pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap k F))) ∧
          ∃ σ : k →+* ℂ,
            Smooth (pullback.snd f₀ (Spec.map (CommRingCat.ofHom
              ((ULift.ringEquiv.symm : ℂ ≃+* ULift.{u} ℂ).toRingHom.comp σ)))) ∧
            IsProjective (pullback.snd f₀ (Spec.map (CommRingCat.ofHom
              ((ULift.ringEquiv.symm : ℂ ≃+* ULift.{u} ℂ).toRingHom.comp σ)))) := by
  sorry

end AlgebraicGeometry
