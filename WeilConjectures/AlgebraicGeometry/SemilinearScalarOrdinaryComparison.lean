/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearScalarOrdinaryInterface
import WeilConjectures.AlgebraicGeometry.SemilinearScalarProperOpen
import Mathlib.CategoryTheory.Functor.OfSequence

/-! # Section-normalized ordinary scalar restriction

Source: Stacks Project, Tags 03CY, 03D7, 03D8, 03DA, 03DI, 03DJ and 0F7B;
blueprint fix-prop-coherence, coefficient comparisons of adjunction units and counits
(blueprint: lem-sf-semilinear-scalar-ordinary-comparison).

The existence theorem below supplies one simultaneous package on the actual ordinary
semilinear-system and strict-tower categories. Every comparison has a section or
adjunction normalization. The constant-tower beta, projector and alpha in the package
are fixed by the same intrinsic ordinary words as their varying-ring counterparts.
No choice of a package is made into a definition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.VaryingRing

variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
  (B : Type (u + 1)) [CommRing B] (ψ : ∀ n : ℕ, CommRingCat.of B ⟶ R n)

/-- Ordinary scalar restriction and all its section-normalized comparisons exist.
Source: Stacks 03CY, 03D7, 03D8, 03DA, 03DI, 03DJ and 0F7B;
blueprint fix-prop-coherence
(blueprint: lem-sf-semilinear-scalar-ordinary-comparison).
Proof: restrict each level along psi and retain the section maps. Compatibility with
phi makes all transitions B-linear. These prescriptions define rho on objects and
morphisms. Restriction commutes with module sheafification: both actions uniquely extend
the same presheaf action on the same abelian sheafification. Hence kernels and cokernels
are unchanged, and componentwise exactness gives exactness on systems. Pushforward has
the same fibre-product sections, giving the identity comparison d. On inverse images
the transported B actions coincide by functoriality of inverse image and its finite-product
comparison; this gives b. The comparisons retain the underlying abelian unit and counit.
The mate formula, counit equation, naturality and the triangle identity give d = mate(b^-1).
The section formulas preserve direct-image composition; taking normalized adjoints
preserves inverse-image composition and identities. For opens, use the localized direct
sum extension presheaf: identity on each summand respects restricted scalars, the open
unit, the counit and the composite-open maps. Pass through sheafification to obtain a.
The transported cartesian beta has the same open-unit transpose and hence equals beta.
The open-to-direct comparison is the mate of the inverse open unit, so its clopen inverse
and the intrinsic projector are preserved. Substituting these equalities in the beta,
projector and compositor word proves preservation of alpha, even when the square is not
cartesian. No step uses coefficient flatness. -/
theorem ordinaryScalarComparison (hψ : ∀ n : ℕ, ψ (n + 1) ≫ φ n = ψ n) :
    Nonempty (OrdinaryScalarComparison R φ B ψ) := by
  obtain ⟨C⟩ := ordinaryScalarRestriction R φ B ψ hψ
  obtain ⟨G⟩ := ordinaryScalarAdjunctions R φ B ψ hψ C
  obtain ⟨P⟩ := ordinaryScalarProperOpen R φ B ψ hψ C G
  exact ⟨{
    rho := C.rho
    additive := C.additive
    limits := C.limits
    colimits := C.colimits
    level := C.level
    level_sections := C.level_sections
    transitions := C.transitions
    b := G.b
    d := G.d
    d_sections := G.d_sections
    unit := OrdinaryScalarAdjunctions.unit R φ B ψ C G
    counit := OrdinaryScalarAdjunctions.counit R φ B ψ C G
    mate := G.mate
    a := G.a
    open_unit := G.open_unit
    beta := P.beta
    beta_unit := P.beta_unit
    beta_comparison := P.beta_comparison
    clopen := P.clopen
    clopen_unit := P.clopen_unit
    pi := scalarOrdinaryPi B P.clopen
    pi_eq := by intros; rfl
    pi_comparison := P.pi_comparison
    alpha := P.alpha
    alpha_eq := P.alpha_eq
    alpha_comparison := P.alpha_comparison }⟩

private def scalarComparisonHom (D E : OrdinaryScalarComparison R φ B ψ)
    (X : Scheme.{u}) (M : Modules R φ X) : (D.rho X).obj M ⟶ (E.rho X).obj M := by
  refine NatTrans.ofOpSequence
    (fun n ↦ (D.level X n).hom.app M ≫ (E.level X n).inv.app M) ?_
  intro n
  apply (cancel_mono ((E.level X n).hom.app M)).1
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  ext H x
  change ((D.level X n).hom.app M).val.app H
      ((((D.rho X).obj M).map (homOfLE (Nat.le_succ n)).op).val.app H x) = _
  rw [D.transitions]
  have he := E.transitions X M n H
    (((E.level X (n + 1)).inv.app M).val.app H
      (((D.level X (n + 1)).hom.app M).val.app H x))
  have hi := congrArg (fun f ↦ f.val.app H
    (((D.level X (n + 1)).hom.app M).val.app H x))
    ((E.level X (n + 1)).inv_hom_id_app M)
  change ((E.level X (n + 1)).hom.app M).val.app H
    (((E.level X (n + 1)).inv.app M).val.app H
      (((D.level X (n + 1)).hom.app M).val.app H x)) = _ at hi
  rw [hi] at he
  exact he.symm

/-- The section prescriptions determine restriction uniquely up to the unique
section-normalized natural isomorphism, the usual uniqueness for constructed functors.
Source: Stacks 03CT and 03D6 (blueprint: lem-sf-semilinear-scalar-ordinary-comparison).
Proof: at each level compose the first level identification with the inverse second
identification. The transition equations make these into tower morphisms; naturality of
level identifications gives naturality in systems. Inverse composites give the inverse.
The level equations determine every component, so sectionwise extensionality gives uniqueness. -/
theorem ordinaryScalarComparison_unique
    (D E : OrdinaryScalarComparison R φ B ψ) (X : Scheme.{u}) :
    ∃! e : D.rho X ≅ E.rho X, ∀ (M : Modules R φ X) (n : ℕ),
      (e.hom.app M).app (op n) ≫ (E.level X n).hom.app M = (D.level X n).hom.app M := by
  let t : D.rho X ⟶ E.rho X :=
    { app := scalarComparisonHom R φ B ψ D E X
      naturality := by
        intro M N f
        apply NatTrans.ext
        funext n
        change ((D.rho X).map f).app n ≫
            ((D.level X n.unop).hom.app N ≫ (E.level X n.unop).inv.app N) =
          ((D.level X n.unop).hom.app M ≫ (E.level X n.unop).inv.app M) ≫
            ((E.rho X).map f).app n
        have hd := (D.level X n.unop).hom.naturality f
        have he := (E.level X n.unop).inv.naturality f
        change ((D.rho X).map f).app n ≫ (D.level X n.unop).hom.app N =
          (D.level X n.unop).hom.app M ≫
            (eval R φ X n.unop ⋙ res (ordinaryScalarMap R B ψ X n.unop)).map f at hd
        change (eval R φ X n.unop ⋙ res (ordinaryScalarMap R B ψ X n.unop)).map f ≫
            (E.level X n.unop).inv.app N =
          (E.level X n.unop).inv.app M ≫ ((E.rho X).map f).app n at he
        rw [← Category.assoc, hd, Category.assoc, he, ← Category.assoc] }
  have hi (M : Modules R φ X) (n : ℕᵒᵖ) : IsIso ((t.app M).app n) := by
    change IsIso ((D.level X n.unop).hom.app M ≫ (E.level X n.unop).inv.app M)
    infer_instance
  have ht (M : Modules R φ X) : IsIso (t.app M) :=
    NatIso.isIso_of_isIso_app _
  have : IsIso t := NatIso.isIso_of_isIso_app _
  refine ⟨asIso t, ?_, ?_⟩
  · intro M n
    change ((D.level X n).hom.app M ≫ (E.level X n).inv.app M) ≫
      (E.level X n).hom.app M = (D.level X n).hom.app M
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  · intro e he
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext n
    apply (cancel_mono ((E.level X n.unop).hom.app M)).1
    change (e.hom.app M).app n ≫ (E.level X n.unop).hom.app M =
      ((D.level X n.unop).hom.app M ≫ (E.level X n.unop).inv.app M) ≫
        (E.level X n.unop).hom.app M
    rw [he M n.unop]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

end AlgebraicGeometry.ProEtale.VaryingRing
