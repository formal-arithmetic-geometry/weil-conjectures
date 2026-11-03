/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CoefFiniteHom

/-! # Finite coefficient tensor and internal-Hom site coherence

Source: latest blueprint, `thm-coef-finite-hom.proof.md`, final paragraph
(blueprint: lem-coef-finite-hom-site-tensor-coherence).
All categories are ordinary derived categories of constant-ring module sheaves.
The scalar, tensor, evaluation-transpose and scalar/site maps are constructions in
`CoefFiniteHom`; none is supplied as a field. The equations below express monoidality,
the site square, and its pasting for a genuine chain A → B → C.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
namespace WeilConjectures

/-- The original small pro-etale site has the ordinary coefficient universe size.
Source: finite coefficient size convention in thm-coef-finite-hom, statement
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
local instance siteComparisonProEtSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1, u, u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- The unit component of the canonical derived comparison inverse image.
Source: thm-coef-finite-hom proof, final paragraph; Stacks 03EL, 08J7
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
def finiteHomSiteUnit
    (R : Type (u + 1)) [CommRing R] [Finite R] (X : Scheme.{u}) :
    (comparisonNu (R := R) X).obj (𝟙_ (EtaleDerived R X)) ⟶
      𝟙_ (ProEtaleDerived R X) := by
  letI : (comparisonNu (R := R) X).Monoidal :=
    AlgebraicGeometry.ProEtale.siteComparisonDerivedMonoidal (ModuleCat R) X
  exact (Functor.Monoidal.εIso (comparisonNu (R := R) X)).inv

/-- The specified beta/rho/v site square, including the contravariant rho inverse.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
def finiteHomSiteSquare
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (X : Scheme.{u}) (φ : A →+* B) (K M : EtaleDerived A X) : Prop :=
  (comparisonNu X).map (etaleHom X φ K M) ≫
      comparisonBeta X ((etaleScalar X φ).obj K) ((etaleScalar X φ).obj M) ≫
      (MonoidalClosed.pre (canonicalRho X φ K)).app
        ((comparisonNu X).obj ((etaleScalar X φ).obj M)) ≫
      (ihom ((proEtaleScalar X φ).obj ((comparisonNu X).obj K))).map
        (canonicalRhoInv X φ M) =
    canonicalRhoInv X φ ((ihom K).obj M) ≫
      (proEtaleScalar X φ).map (comparisonBeta X K M) ≫
      proHom X φ ((comparisonNu X).obj K) ((comparisonNu X).obj M)

/-- The inverse of the successive scalar/site comparison, before scalar reassociation.
Source: thm-coef-finite-hom proof, final paragraph, successive coefficient change
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
def finiteHomRhoChain
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (X : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C) (K : EtaleDerived A X) :=
  (proEtaleScalar X ψ).map (canonicalRho X φ K) ≫
    canonicalRho X ψ ((etaleScalar X φ).obj K)

/-- The successive scalar/site comparison, before scalar reassociation.
Source: thm-coef-finite-hom proof, final paragraph, successive coefficient change
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
def finiteHomRhoChainInv
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (X : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C) (K : EtaleDerived A X) :=
  canonicalRhoInv X ψ ((etaleScalar X φ).obj K) ≫
    (proEtaleScalar X ψ).map (canonicalRhoInv X φ K)

/-- Pasting of the two coefficient-change squares, before reassociation. The
`rho_successive` and the tensor/Hom compositor equations identify this equation
with the direct A → C square.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
def finiteHomSuccessiveSiteSquare
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (X : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C) (K M : EtaleDerived A X) : Prop :=
  (comparisonNu X).map
      ((etaleScalar X ψ).map (etaleHom X φ K M) ≫
        etaleHom X ψ ((etaleScalar X φ).obj K) ((etaleScalar X φ).obj M)) ≫
      comparisonBeta X ((etaleScalar X ψ).obj ((etaleScalar X φ).obj K))
        ((etaleScalar X ψ).obj ((etaleScalar X φ).obj M)) ≫
      (MonoidalClosed.pre (finiteHomRhoChain X φ ψ K)).app
        ((comparisonNu X).obj ((etaleScalar X ψ).obj ((etaleScalar X φ).obj M))) ≫
      (ihom ((proEtaleScalar X ψ).obj
        ((proEtaleScalar X φ).obj ((comparisonNu X).obj K)))).map
        (finiteHomRhoChainInv X φ ψ M) =
    finiteHomRhoChainInv X φ ψ ((ihom K).obj M) ≫
      (proEtaleScalar X ψ).map ((proEtaleScalar X φ).map (comparisonBeta X K M)) ≫
      (proEtaleScalar X ψ).map
        (proHom X φ ((comparisonNu X).obj K) ((comparisonNu X).obj M)) ≫
      proHom X ψ ((proEtaleScalar X φ).obj ((comparisonNu X).obj K))
        ((proEtaleScalar X φ).obj ((comparisonNu X).obj M))

section SiteLawPredicates

variable {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
  [Finite A] [Finite B] [Finite C]
  (X : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C)

/-- The `rho_tensor` equation for the canonical scalar/site comparisons.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
@[irreducible]
def finiteHomSiteLaw_rho_tensor : Prop :=
  ∀ (K M : EtaleDerived A X),
    (comparisonNu X).map (etaleTensor X φ K M) ≫
        (AlgebraicGeometry.ProEtale.siteComparisonTensorIso (ModuleCat B) X
          ((etaleScalar X φ).obj K)).hom.app ((etaleScalar X φ).obj M) ≫
        (canonicalRhoInv X φ K ⊗ₘ canonicalRhoInv X φ M) =
      canonicalRhoInv X φ (K ⊗ M) ≫
        (proEtaleScalar X φ).map
          ((AlgebraicGeometry.ProEtale.siteComparisonTensorIso (ModuleCat A) X K).hom.app M) ≫
        proTensor X φ ((comparisonNu X).obj K) ((comparisonNu X).obj M)

/-- The `rho_unit` equation for the canonical scalar/site comparisons.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
@[irreducible]
def finiteHomSiteLaw_rho_unit : Prop :=
  (comparisonNu X).map (etaleCore X φ).εIso.inv ≫ finiteHomSiteUnit B X =
      canonicalRhoInv X φ (𝟙_ (EtaleDerived A X)) ≫
        (proEtaleScalar X φ).map (finiteHomSiteUnit A X) ≫ (proCore X φ).εIso.inv

/-- The `rho_successive` equation for the canonical scalar/site comparisons.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
@[irreducible]
def finiteHomSiteLaw_rho_successive : Prop :=
  ∀ (K : EtaleDerived A X),
    (finiteHomScalarComp (ProEt.topology X) φ ψ).hom.app ((comparisonNu X).obj K) ≫
        canonicalRho X (ψ.comp φ) K =
      finiteHomRhoChain X φ ψ K ≫
        (comparisonNu X).map ((finiteHomScalarComp X.smallEtaleTopology φ ψ).hom.app K)

/-- The `rho_identity` equation for the canonical scalar/site comparisons.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
@[irreducible]
def finiteHomSiteLaw_rho_identity : Prop :=
  ∀ (K : EtaleDerived A X),
    canonicalRho X (RingHom.id A) K ≫
        (comparisonNu X).map ((finiteHomScalarId X.smallEtaleTopology A).hom.app K) =
      (finiteHomScalarId (ProEt.topology X) A).hom.app ((comparisonNu X).obj K)

/-- The `site_square` equation for the canonical scalar/site comparisons.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
@[irreducible]
def finiteHomSiteLaw_site_square : Prop :=
  ∀ (K M : EtaleDerived A X), finiteHomSiteSquare X φ K M

/-- The `site_square_next` equation for the canonical scalar/site comparisons.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
@[irreducible]
def finiteHomSiteLaw_site_square_next : Prop :=
  ∀ (K M : EtaleDerived B X), finiteHomSiteSquare X ψ K M

/-- The `site_square_composite` equation for the canonical scalar/site comparisons.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
@[irreducible]
def finiteHomSiteLaw_site_square_composite : Prop :=
  ∀ (K M : EtaleDerived A X), finiteHomSiteSquare X (ψ.comp φ) K M

/-- The `site_square_identity` equation for the canonical scalar/site comparisons.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
@[irreducible]
def finiteHomSiteLaw_site_square_identity : Prop :=
  ∀ (K M : EtaleDerived A X), finiteHomSiteSquare X (RingHom.id A) K M

/-- The `site_square_successive` equation for the canonical scalar/site comparisons.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: lem-coef-finite-hom-site-tensor-coherence). -/
@[irreducible]
def finiteHomSiteLaw_site_square_successive : Prop :=
  ∀ (K M : EtaleDerived A X), finiteHomSuccessiveSiteSquare X φ ψ K M

end SiteLawPredicates

/-- Equations for the canonical tensor, Hom and scalar/site comparisons.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: lem-coef-finite-hom-site-tensor-coherence).
The `laws` field includes the actual A → C tensor/Hom equations on both sites,
with the canonical compositor and identity isomorphisms. The rho tensor and unit
fields assert monoidality; the direct and pasted square fields assert its site
compatibility. No invertibility of beta is asserted. -/
structure FiniteHomSiteTensorCoherence
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (X : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C) where
  laws : FiniteCoefficientHomLaws X φ ψ
  rho_tensor : finiteHomSiteLaw_rho_tensor X φ
  rho_unit : finiteHomSiteLaw_rho_unit X φ
  rho_successive : finiteHomSiteLaw_rho_successive X φ ψ
  rho_identity : finiteHomSiteLaw_rho_identity (A := A) X
  site_square : finiteHomSiteLaw_site_square X φ
  site_square_next : finiteHomSiteLaw_site_square_next X ψ
  site_square_composite : finiteHomSiteLaw_site_square_composite X φ ψ
  site_square_identity : finiteHomSiteLaw_site_square_identity (A := A) X
  site_square_successive : finiteHomSiteLaw_site_square_successive X φ ψ

/-- Finite coefficient tensor and internal-Hom coherence on both ordinary sites.
Source: latest blueprint thm-coef-finite-hom.proof.md, final paragraph
(blueprint: lem-coef-finite-hom-site-tensor-coherence).
Proof: use the canonical K-flat scalar pullback tensor comparison, including its
symmetric monoidal, composition and identity normalizations. Apply thm-coef-finite-hom
for invertibility of v on bounded constructible finite-Tor objects. Its evaluation
transpose gives the displayed normalization. The derived mate of the ordinary
upper-star/scalar square is monoidal and has the stated composition and identity
comparisons. Uncurry the two sides of the beta/rho square: monoidality of rho and
naturality of evaluation make the resulting evaluations equal, so uniqueness of
transpose gives the square. Paste twice for A → B → C; the scalar compositor's
monoidality and the successive-v equation identify the pasted and direct squares.
The same argument with the scalar unit isomorphism gives the identity case. -/
theorem coefFiniteHomSiteTensorCoherence
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    (ell : ℕ) [Fact ell.Prime] (hell : (ell : k) ≠ 0)
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (φ : A →+* B) (ψ : B →+* C)
    (hA : ∃ n : ℕ, (ell ^ n : A) = 0)
    (hB : ∃ n : ℕ, (ell ^ n : B) = 0)
    (hC : ∃ n : ℕ, (ell ^ n : C) = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    Nonempty (FiniteHomSiteTensorCoherence X φ ψ) := by
  sorry

end WeilConjectures
