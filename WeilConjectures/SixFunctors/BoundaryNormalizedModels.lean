/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.BoundaryDualityInput
public import WeilConjectures.AlgebraicGeometry.BoundaryBidualTranspose
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleIhom
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleDevissageSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleBound
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-! # Normalized geometric models before the boundary transpose argument

Source: boundary-duality discharge, finite-Tor domains and evaluation comparisons
(blueprint: lem-weil-boundary-normalized-models).

These data contain no assertion about invertibility of boundary exchange and no
boundary double-dual compatibility equation. Those follow by the formal transpose
argument in BoundaryDualityDischarge.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe i b c e v w u
open CategoryTheory CategoryTheory.MonoidalCategory MonoidalClosed Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.BoundaryDualityInput

section Formal
variable {I : Type i} {B : I → I → Type b}
  {P : I → Type c} [∀ T, Category.{v} (P T)] [∀ T, MonoidalCategory (P T)]
  [∀ T, SymmetricCategory (P T)] [∀ T, MonoidalClosed (P T)]
  {E : I → Type e} [∀ T, Category.{w} (E T)] [∀ T, MonoidalCategory (E T)]

/-- Geometric preservation and normalized comparison maps, before proving either
assertion about the boundary transpose.
Source: discharge proof, finite-Tor domains and comparison of evaluations
(blueprint: def-weil-boundary-normalized-model). -/
structure NormalizedModel (o : Operations B P E) (ctf : ∀ T, P T → Prop) where
  preserves : ∀ T K, ctf T K → ctf T ((o.dual T).obj (op K))
  symmetry : ∀ T K L, o.symmetry T K L = β_ K L
  evaluation : ∀ T K,
    o.evaluation T K = (β_ ((o.dual T).obj (op K)) K).hom ≫
      (ihom.ev K).app (o.omega T)
  theta : ∀ {Z T} (f : B Z T), (o.exceptional f).obj (o.omega T) ≅ o.omega Z
  theta_normalization : ∀ {Z T} (f : B Z T),
    (o.nu Z).map ((o.eexc f).map ((o.adj T).unit.app (o.eOmega T))) ≫
      (theta f).hom = (o.nu Z).map (o.ecomp f).hom
  tau : ∀ {Z T} (f : B Z T) (M N : P T), ctf T M →
    ((o.star f).obj M ⊗ (o.exceptional f).obj N ⟶ (o.exceptional f).obj (M ⊗ N))
  tau_normalization : ∀ {Z T} (f : B Z T) M N hM,
    ((o.star f).map ((o.adj T).counit.app M) ⊗ₘ 𝟙 ((o.exceptional f).obj N)) ≫
      tau f M N hM = o.tensorModel f M N
  star_preserves : ∀ {Z T} (f : B Z T) K, ctf T K → ctf Z ((o.star f).obj K)
  delta_iso : ∀ T K, ctf T K → IsIso (toIhomIhom (o.omega T) K)
  tau_natural : ∀ {Z T} (f : B Z T) M M' N N' (hM : ctf T M)
    (hM' : ctf T M') (_hN : ctf T N) (_hN' : ctf T N') (a : M ⟶ M') (b : N ⟶ N'),
    ((o.star f).map a ⊗ₘ (o.exceptional f).map b) ≫ tau f M' N' hM' =
      tau f M N hM ≫ (o.exceptional f).map (a ⊗ₘ b)
  alpha_iso : ∀ {Z T} (f : B Z T) K (hK : ctf T K),
    IsIso (BoundaryBidualTranspose.alpha (o.omega T) (o.omega Z)
      (o.star f) (o.exceptional f) (theta f) (ctf T) (preserves T)
      (fun M N hM _ ↦ tau f M N hM) K hK)

end Formal

attribute [local instance] DerivedCategory.symmetricCategory

/-- The specified site operations admit the geometric normalized model on every piece.
This assertion stops before the formal bidual transpose: it neither assumes boundary
exchange is invertible nor assumes its double-dual compatibility.

Source: current blueprint, cor-weil-boundary-duality-discharge.proof.md, first paragraph
and the evaluation-transposition sentences of the second paragraph
(blueprint: lem-weil-boundary-normalized-models).

Proof: Apply boundary_finite_tor_domains to every immersion into Y, at level n+1.
Use its separated finite-type conclusions for each piece and closed pair. Set nu,
nuR, star, estar, eexc, eOmega, square, etau and ecomp equal to the corresponding
recorded operations in CanonicalOperations; use the pairing witnesses of
ambient_duality_pairing for symmetry and evaluation. Their normalization gives the
native braiding and evaluation formulas displayed here. Finite-stage biduality gives
preservation and delta_iso.
For theta apply the comparison of the etale dualizing-composition mate, retaining
its pasted-counit normalization. Define tau by cancelling the comparison counit in
tensorModel on the finite-Tor first input. Etale origin, comparison full faithfulness
on bounded-below objects and the projection formula give this cancellation and its
naturality. Apply boundaryAlphaNormalization on the etale sites using the preserved
finite-Tor domains; it gives invertibility of the evaluation-normalized alpha. Finally use
boundary_finite_site_realization to identify the comparison q, dualizing objects,
evaluation and biduality on every etale-origin input. Its evaluation squares carry
the alpha isomorphism to the specified pro-etale operations. Every finite-Tor
pro-etale object has an etale representative. These
constructions work also for the empty piece, and require no ambient pro-etale adjoint.
-/
theorem boundary_normalized_models
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (CommRingCat.of D.k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
    letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
    letI : IsNoetherian Y := ⟨⟩
    ∃ o : Operations Boundary
        (fun T : Piece Y ↦ FixedCategory (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) T.scheme)
        (fun T : Piece Y ↦ FixedEtaleCategory (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) T.scheme),
      CanonicalOperations
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) Y aY
        (finiteComposition (Padic.coefficientExtensionRing l E (n + 1)) Y aY) o ∧
      Nonempty (NormalizedModel o (fun T ↦ ctf l E n T.scheme)) := by sorry

end AlgebraicGeometry.ProEtale.BoundaryDualityInput
