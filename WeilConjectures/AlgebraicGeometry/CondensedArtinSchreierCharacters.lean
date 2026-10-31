/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTraceComparison
public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.CategoryTheory.RingObjects.GlobalSections
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransportSupplement
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import WeilConjectures.AlgebraicGeometry.FrobeniusFixedSections
import WeilConjectures.DeligneLaumon.FiniteEtaleCondensedBaseChange
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.LocalProperties
import WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import WeilConjectures.CategoryTheory.SheafificationTensorLocalIso
import Mathlib.CategoryTheory.Sites.Sheafification

/-! # Character decomposition with condensed Artin–Schreier coefficients

Source: latest blueprint, sec-fourier-transform/sk-lem-as-properties,
lem-fd-as-characters and its proof, Steps 1–5 (blueprint: lem-fd-as-characters).

The coefficient ring is the recorded pulled-back condensed ring, not a discrete
constant ring. The projectors, pullbacks and degree-q sheaves are specializations
of the constructions in ArtinSchreierTraceComparison. The coproduct comparison is
specified by its actual image inclusions, which fixes the canonical decomposition.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ArtinSchreierTrace

/-- Regard a Qbar-valued character as a character into the global sections of the
condensed coefficient ring, using its canonical constant-section ring homomorphism.
Source: blueprint lem-fd-as-characters, coefficient convention in proof Step 1
(blueprint: lem-fd-as-characters). -/
abbrev qlbarCharacter (ℓ : ℕ) [Fact ℓ.Prime] {G : Type v} [AddMonoid G]
    (χ : AddChar G (PadicAlgCl ℓ)) :
    AddChar G (MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ)) :=
  (Profinite.PadicAlgCl.constRingHom ℓ).toMonoidHom.compAddChar χ

/-- The prime-cover projector, with exactly the translations from lem-fd-as-cover.
This only specializes the existing condensed projector to Qbar coefficients.
Source: blueprint lem-fd-as-characters, proof Step 3
(blueprint: lem-fd-as-characters). -/
abbrev qlbarPrimeProjector (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime]
    (X : Scheme.{u}) (f : Γ(X, ⊤))
    (σ : Multiplicative (ZMod p) →* Aut (artinSchreierCover p X f))
    (χ : AddChar (ZMod p) (PadicAlgCl ℓ)) :=
  condensedProjector (Profinite.padicAlgClRingObj ℓ) (ZMod p)
    (artinSchreierCover p X f) (fun a ↦ (σ (Multiplicative.ofAdd a)).hom)
    (qlbarCharacter ℓ χ)

/-- The recorded degree-q sheaf of def-fd-artin-schreier-sheaf,
`ProEtale.condensedArtinSchreierSheafOf`, with its actual condensed Qbar coefficients
and the character Psi composed with the field trace. This is an abbreviation, not a
second Artin–Schreier construction.
Source: blueprint lem-fd-as-characters, the clause beginning "In particular"
(blueprint: lem-fd-as-characters). -/
abbrev qlbarTraceSheafOf (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fintype k] [Algebra (ZMod p) k]
    (Ψ : AddChar (ZMod p) (PadicAlgCl ℓ))
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (f : Γ(X, ⊤)) :=
  ProEtale.condensedArtinSchreierSheafOf (Profinite.padicAlgClRingObj ℓ) k X
    ((qlbarCharacter ℓ Ψ).compTrace k) f

/-- The canonical direct-sum decomposition, its rank-one local models, the trivial
summand, and the split case f=0, for the specified prime-degree cover.
Source: blueprint lem-fd-as-characters, first paragraph and proof Steps 1–4
(blueprint: lem-fd-as-characters).

Proof: split the finite etale torsor on etale affine charts, using
lem-weil-pbc-finite-etale-etale-local-split. Differences of roots are locally constant
F_p-valued functions by lem-fd-frobenius-fixed-sections; refine their clopen fibres.
The charts then have components r+a with translation a -> a+b, including on a
disconnected base. Finite etale condensed base change
(lem-a1-finite-etale-condensed-base-change) and finite coproduct evaluation
(lem-weil-pbc-proetale-finite-coproduct-evaluation) identify the pushforward with
functions on F_p valued in the pulled-back coefficient ring. Internal module
operations are sectionwise by lem-sfb-internal-module-operations-transport.
The averaging projector has image precisely the chi-eigenfunctions, since
sigma_b e_chi = chi(b)e_chi and averaging fixes every eigenfunction.
Character orthogonality (lem-fd-character-orthogonality) gives orthogonal projectors.
The classification in lem-wft-as-comparison over F_p gives all characters and
sum_chi e_chi=1. Thus the sum of image inclusions is invertible, with inverse
whose components are the corestricted projectors. Evaluation at r identifies each
image with the regular coefficient module; its inverse sends lambda to
(a -> chi(a)lambda). For chi=1 these functions are constant and coefficient
pullback gives the global unit identification; detect the isomorphism by
lem-sfb-sheaf-cover-local-isomorphism. For f=0 choose the global root 0, so every
character has this global trivialization. The empty base requires no charts. -/
theorem qlbar_artinSchreier_isotypic_properties
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) (hchar : (p : Γ(X, ⊤)) = 0) (f : Γ(X, ⊤))
    (σ : Multiplicative (ZMod p) →* Aut (artinSchreierCover p X f))
    (hσ : ∀ a : ZMod p,
      (σ (Multiplicative.ofAdd a)).hom.left.appTop (artinSchreierCoverCoordinate p X f) =
        artinSchreierCoverCoordinate p X f +
          (a.val : Γ((artinSchreierCover p X f).left, ⊤))) :
    Nonempty (IsColimit (Cofan.mk
      ((ProEtale.CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ)
        (artinSchreierCover p X f).hom).obj
          (Mod.regular (ProEtale.padicAlgClRingObj (artinSchreierCover p X f).left ℓ)))
      (fun χ : AddChar (ZMod p) (PadicAlgCl ℓ) ↦
        image.ι (qlbarPrimeProjector p ℓ X f σ χ)))) ∧
    (∀ χ : AddChar (ZMod p) (PadicAlgCl ℓ),
      ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
        Nonempty ((ProEtale.CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
          (𝒰.f i)).obj (image (qlbarPrimeProjector p ℓ X f σ χ)) ≅
            Mod.regular (ProEtale.padicAlgClRingObj (𝒰.X i) ℓ))) ∧
    Nonempty (image (qlbarPrimeProjector p ℓ X f σ 1) ≅
      Mod.regular (ProEtale.padicAlgClRingObj X ℓ)) ∧
    (f = 0 → ∀ χ : AddChar (ZMod p) (PadicAlgCl ℓ),
      Nonempty (image (qlbarPrimeProjector p ℓ X f σ χ) ≅
        Mod.regular (ProEtale.padicAlgClRingObj X ℓ))) := by
  sorry

/-- For a=1 the trace comparison identifies the named degree-q sheaf with the
Psi-summand of the prime cover, using Psi itself rather than its trace character
restricted to F_p.
Source: blueprint lem-fd-as-characters, parenthetical comparison clause
(blueprint: lem-fd-as-characters).

Proof: apply lem-wft-as-comparison (2) with a=1 and the condensed Qbar coefficient
ring. The cover of af becomes the cover of f. Its specified pullback map on
projector images and the final degree-q identification give the displayed
isomorphism. The coordinate formula identifies its translations with sigma.
The degree-q sheaf of that comparison is f^* of the image of
q^{-1} sum psi(-c) sigma_c^* on (AS_q)_* Lambda; this is literally the recorded
def-fd-artin-schreier-sheaf construction: both translation maps are the pullback of
sections along the deck translation (the module map sending 1 to the coefficient
unit), and the scalars are the same q^{-1} psi(-c) transported from the point.
The comparison is valid on the empty scheme as well. -/
theorem qlbar_artinSchreier_trace_summand
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [Fintype k] [Algebra (ZMod p) k]
    (Ψ : AddChar (ZMod p) (PadicAlgCl ℓ)) (hΨ : Ψ ≠ 1)
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (f : Γ(X, ⊤))
    (σ : Multiplicative (ZMod p) →* Aut (artinSchreierCover p X f))
    (hσ : ∀ a : ZMod p,
      (σ (Multiplicative.ofAdd a)).hom.left.appTop (artinSchreierCoverCoordinate p X f) =
        artinSchreierCoverCoordinate p X f +
          (a.val : Γ((artinSchreierCover p X f).left, ⊤))) :
    Nonempty (image (qlbarPrimeProjector p ℓ X f σ Ψ) ≅ qlbarTraceSheafOf p ℓ k Ψ X f) := by
  sorry

/-- Tensor addition and the tensor inverse, with inverse-character identification,
for the trace character psi=Psi o Tr. Both tensor orders express the inverse object.
Source: blueprint lem-fd-as-characters, final sentence and proof Step 5
(blueprint: lem-fd-as-characters).

Proof: lem-wft-as-comparison with a=1 identifies the degree-q sheaves for f, g,
f+g and -f with the Psi-images for the prime covers. On common splitting charts
for these three covers choose roots r,s,t. Their difference r+s-t is locally
F_p-valued by lem-fd-frobenius-fixed-sections; refine so r+s is a component label.
The eigenfunction v_{f,r}(r+a)=Psi(a) freely generates its image. Send
(lambda v_{f,r}) tensor (mu v_{g,s}) to lambda mu v_{f+g,r+s}; the balanced-map
universal property of def-sfb-modobj-relative-tensor constructs this module map
and its inverse. Changing roots to r+c,s+d multiplies the generators by
Psi(-c),Psi(-d), and Psi(-c-d), respectively, so maps and inverses agree on overlaps.
The sheaf equalizer condition (def-weil-pbc-sites-and-cohomology) glues them.
With g=-f the zero-function trivialization gives both inverse pairings.
Finally root negation sends an inverse-character function w(r+b)=Psi(-b)lambda
to w(r-a)=Psi(a)lambda on the cover of -f. The overlap factors agree, so these
maps glue too. This includes p=2, and never uses psi restricted to F_p, which
can be trivial when p divides [k:F_p]. Transport by the comparison gives all
displayed formulas in the recorded degree-q model. -/
theorem qlbar_artinSchreier_trace_tensor_properties
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [Fintype k] [Algebra (ZMod p) k]
    (Ψ : AddChar (ZMod p) (PadicAlgCl ℓ)) (hΨ : Ψ ≠ 1)
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (f g : Γ(X, ⊤)) :
    Nonempty (qlbarTraceSheafOf p ℓ k Ψ X f ⊗ qlbarTraceSheafOf p ℓ k Ψ X g ≅
      qlbarTraceSheafOf p ℓ k Ψ X (f + g)) ∧
    Nonempty (qlbarTraceSheafOf p ℓ k Ψ X f ⊗ qlbarTraceSheafOf p ℓ k Ψ X (-f) ≅
      Mod.regular (ProEtale.padicAlgClRingObj X ℓ)) ∧
    Nonempty (qlbarTraceSheafOf p ℓ k Ψ X (-f) ⊗ qlbarTraceSheafOf p ℓ k Ψ X f ≅
      Mod.regular (ProEtale.padicAlgClRingObj X ℓ)) ∧
    Nonempty (qlbarTraceSheafOf p ℓ k Ψ⁻¹ X f ≅ qlbarTraceSheafOf p ℓ k Ψ X (-f)) := by
  -- The circular lisse shortcut was removed; construct these maps on root charts.
  sorry

end AlgebraicGeometry.ArtinSchreierTrace
