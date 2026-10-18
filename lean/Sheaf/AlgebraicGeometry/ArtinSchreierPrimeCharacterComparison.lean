/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.AlgebraicGeometry.ArtinSchreierTraceCoverMap
public import WeilConjectures.FourierTransform.ArtinSchreier
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.SixFunctors.Finite.BaseChange
import WeilConjectures.SixFunctors.Finite.Stalk
import Mathlib.FieldTheory.Finite.Trace
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit

/-!
# Comparison with the prime-field Artin–Schreier character sheaf

Source: Laumon, Transformation de Fourier (1987), (0.2), (1.1.3), (1.1.3.6),
pp. 135 and 139–140; the explicit trace-polynomial comparison in the DAG proof
(blueprint: lem-a1-artin-schreier-prime-character-comparison).

The auxiliary definitions specialize the existing character projectors and function sheaf
with the canonical invertibility instance in characteristic zero. The base-change arrow is
pullback of sections, expressed as an arrow into a direct image. This adjoint formulation
records the naturality square without choosing identifications of images under pullback.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

noncomputable section

variable {L : Type (u + 1)} [Field L] [CharZero L]

/-- The degree-q character projector on the explicit cover, using the upstream projector.
Source: Laumon (1.1.3), pp. 139–140
(blueprint: lem-a1-artin-schreier-prime-character-comparison). -/
def artinSchreierComparisonQIdempotent {k : Type u} [Field k] [Fintype k]
    {p r : ℕ} [Algebra (ZMod p) k] {b : k} {X : Scheme.{u}}
    [X.Over (Spec (.of k))] {f : Γ(X, ⊤)}
    (M : ArtinSchreierTraceMaps k p r b X f) (ψ : AddChar k L) :=
  letI : Invertible (Fintype.card k : L) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  isotypicIdempotent (artinSchreierFunctionProjection X (p ^ r) f)
    (fun c ↦ (M.σ c).hom) M.σ_over ψ

/-- The prime-degree projector for the function bf and the character of the prime field.
Source: Laumon (1.1.3), pp. 139–140
(blueprint: lem-a1-artin-schreier-prime-character-comparison). -/
def artinSchreierComparisonPIdempotent {k : Type u} [Field k]
    {p r : ℕ} [Fact p.Prime] [Algebra (ZMod p) k] {b : k} {X : Scheme.{u}}
    [X.Over (Spec (.of k))] {f : Γ(X, ⊤)}
    (M : ArtinSchreierTraceMaps k p r b X f) (Ψ : AddChar (ZMod p) L) :=
  letI : Invertible (Fintype.card (ZMod p) : L) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  isotypicIdempotent
    (artinSchreierFunctionProjection X p (artinSchreierBaseConstants k X b * f))
    (fun d ↦ (M.τ d).hom) M.τ_over Ψ

/-- The existing function Artin–Schreier sheaf with characteristic-zero invertibility.
Source: Laumon (1.1.3.6), p. 140; def-fd-artin-schreier-sheaf
(blueprint: lem-a1-artin-schreier-prime-character-comparison). -/
def artinSchreierComparisonSheafOf {k : Type u} [Field k] [Fintype k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (ψ : AddChar k L) (f : Γ(X, ⊤)) :=
  letI : Invertible (Fintype.card k : L) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  artinSchreierSheafOf X ψ f

/-- The canonical arrow on pushed-forward constant sheaves associated to a map of covers
above h. Its adjoint is finite base change followed by the constant-sheaf unit isomorphism.
Source: finite exchange in the DAG proof of Laumon (1.1.3.6), p. 140
(blueprint: lem-a1-artin-schreier-prime-character-comparison). -/
def artinSchreierComparisonBaseMap {X X' Y Y' : Scheme.{u}}
    (π : Y ⟶ X) (π' : Y' ⟶ X') (h : X' ⟶ X) (a : Y' ⟶ Y)
    (ha : a ≫ π = π' ≫ h) :
    (π)_*[ModuleCat L].obj (𝟙_ _) ⟶ (h)_*[ModuleCat L].obj
      ((π')_*[ModuleCat L].obj (𝟙_ _)) :=
  lowerStarConstantSheafMapOfOver π (π' ≫ h) a ha ≫
    (lowerStarComp (ModuleCat L) π' h (π' ≫ h) rfl).inv.app (𝟙_ _)

/-- Finite-field characters have a unique nonzero trace parameter, and the character
summands of the degree-q and degree-p covers are naturally isomorphic lisse sheaves.
The isomorphism is oriented from the prime summand to the q summand so that its composite
with the image inclusion is exactly pullback of sections along the trace-polynomial map.
The last equation is its naturality square in adjoint form; the projector on the new prime
cover supplies the canonical retraction onto its image.

Source: Laumon (0.2), (1.1.3), (1.1.3.6), pp. 135 and 139–140, and the explicit
trace-polynomial comparison in the DAG proof
(blueprint: lem-a1-artin-schreier-prime-character-comparison).

Proof:
1. All character values lie in the p-th roots of unity. The nontrivial prime-field
   character identifies its additive group with those roots. Hence psi factors uniquely
   through an F_p-linear functional. Nondegeneracy of the trace pairing
   (lem-a1-trace-pairing-nondegenerate) identifies it with c ↦ Tr(bc), uniquely.
   Nontriviality excludes b=0. This is Laumon (0.2).
2. The trace-cover map (lem-a1-artin-schreier-trace-cover-map) supplies the covers,
   translations, and theta with theta sigma_c = tau_Tr(bc) theta. Both covers are finite
   etale torsors (also lem-fd-as-cover), and theta is surjective on geometric fibres.
3. The finite stalk formula (lemma-weil-pbc-finite-stalk-formula) identifies pushed-forward
   constant sheaves with functions on the finite geometric fibres. Pullback along theta
   is precomposition, hence injective, and intertwines the two translation actions.
4. Reindexing the character sum identifies each projector image with its eigensheaf.
   The trace identity makes theta pullback carry the prime eigensheaf to the q eigensheaf.
   Each geometric stalk is one dimensional by the regular representation of the torsor.
   The resulting injective map of lines is invertible; geometric stalks detect isomorphisms.
5. Finite etale local splitting (lem-weil-pbc-finite-etale-etale-local-split) trivializes
   the pushed-forward constant sheaves. On connected local pieces the translations are
   fixed permutations, so each projector image is a constant line, hence lisse.
6. Finite exchange (lemma-weil-pbc-finite-exchange), equivariant for translations,
   identifies the pulled-back universal sheaf of def-fd-artin-schreier-sheaf with the
   q-projector image. Exact pullback preserves images. The coordinate-preserving cartesian
   squares supplied by the trace-cover lemma identify the two new covers and theta with
   their base changes. On stalks, all arrows are precomposition on the same fibres.
   Thus the comparison commutes with pullback. The final equation writes this square
   after adjunction to h_* and the image inclusions; the prime projector retraction acts
   identically on the transported prime eigensheaf.
-/
theorem artinSchreier_prime_character_comparison (k : Type u) [Field k] [Fintype k]
    (p r ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] [CharP k p] [Algebra (ZMod p) k]
    (hr : 1 ≤ r) (hcard : Fintype.card k = p ^ r) (hℓ : ℓ ≠ p)
    [Algebra (Padic ℓ) L] [IsAlgClosure (Padic ℓ) L]
    (Ψ : AddChar (ZMod p) L) (hΨ : Ψ ≠ 1) (ψ : AddChar k L) (hψ : ψ ≠ 1) :
    ∃ b : kˣ,
      (∀ c : k, ψ c = Ψ (Algebra.trace (ZMod p) k ((b : k) * c))) ∧
      (∀ b' : kˣ, (∀ c : k, ψ c = Ψ (Algebra.trace (ZMod p) k ((b' : k) * c))) →
        b' = b) ∧
      ∀ (X : Scheme.{u}) [X.Over (Spec (.of k))]
        [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
        [QuasiCompact (X ↘ Spec (.of k))] (f : Γ(X, ⊤)),
      ∃ (M : ArtinSchreierTraceMaps k p r (b : k) X f)
        (e : image (artinSchreierComparisonPIdempotent M Ψ) ≅
          image (artinSchreierComparisonQIdempotent M ψ)),
        e.hom ≫ image.ι (artinSchreierComparisonQIdempotent M ψ) =
          image.ι (artinSchreierComparisonPIdempotent M Ψ) ≫
            lowerStarConstantSheafMapOfOver
              (artinSchreierFunctionProjection X p (artinSchreierBaseConstants k X b * f))
              (artinSchreierFunctionProjection X (p ^ r) f) M.θ M.θ_over ∧
        Scheme.IsLocallyConstantSheaf (image (artinSchreierComparisonQIdempotent M ψ)) ∧
        Scheme.IsLocallyConstantSheaf (image (artinSchreierComparisonPIdempotent M Ψ)) ∧
        Nonempty (artinSchreierComparisonSheafOf X ψ f ≅
          image (artinSchreierComparisonQIdempotent M ψ)) ∧
        ∀ (X' : Scheme.{u}) [X'.Over (Spec (.of k))]
          [IsSeparated (X' ↘ Spec (.of k))] [LocallyOfFiniteType (X' ↘ Spec (.of k))]
          [QuasiCompact (X' ↘ Spec (.of k))] (h : X' ⟶ X) [h.IsOver (Spec (.of k))],
        ∃ (M' : ArtinSchreierTraceMaps k p r (b : k) X' (h.appTop f))
          (uq : artinSchreierFunctionCover X' (p ^ r) (h.appTop f) ⟶
            artinSchreierFunctionCover X (p ^ r) f)
          (up : artinSchreierFunctionCover X' p
              (artinSchreierBaseConstants k X' b * h.appTop f) ⟶
            artinSchreierFunctionCover X p (artinSchreierBaseConstants k X b * f))
          (hq : IsPullback uq (artinSchreierFunctionProjection X' (p ^ r) (h.appTop f))
            (artinSchreierFunctionProjection X (p ^ r) f) h)
          (hp : IsPullback up (artinSchreierFunctionProjection X' p
              (artinSchreierBaseConstants k X' b * h.appTop f))
            (artinSchreierFunctionProjection X p (artinSchreierBaseConstants k X b * f)) h)
          (e' : image (artinSchreierComparisonPIdempotent M' Ψ) ≅
            image (artinSchreierComparisonQIdempotent M' ψ)),
          uq.appTop (artinSchreierFunctionRoot X (p ^ r) f) =
            artinSchreierFunctionRoot X' (p ^ r) (h.appTop f) ∧
          up.appTop (artinSchreierFunctionRoot X p (artinSchreierBaseConstants k X b * f)) =
            artinSchreierFunctionRoot X' p
              (artinSchreierBaseConstants k X' b * h.appTop f) ∧
          e'.hom ≫ image.ι (artinSchreierComparisonQIdempotent M' ψ) =
            image.ι (artinSchreierComparisonPIdempotent M' Ψ) ≫
              lowerStarConstantSheafMapOfOver
                (artinSchreierFunctionProjection X' p
                  (artinSchreierBaseConstants k X' b * h.appTop f))
                (artinSchreierFunctionProjection X' (p ^ r) (h.appTop f)) M'.θ M'.θ_over ∧
          image.ι (artinSchreierComparisonPIdempotent M Ψ) ≫
              artinSchreierComparisonBaseMap
                (artinSchreierFunctionProjection X p (artinSchreierBaseConstants k X b * f))
                (artinSchreierFunctionProjection X' p
                  (artinSchreierBaseConstants k X' b * h.appTop f)) h up hp.w ≫
              (h)_*[ModuleCat L].map
                (factorThruImage (artinSchreierComparisonPIdempotent M' Ψ)) ≫
              (h)_*[ModuleCat L].map e'.hom ≫
              (h)_*[ModuleCat L].map (image.ι (artinSchreierComparisonQIdempotent M' ψ)) =
            e.hom ≫ image.ι (artinSchreierComparisonQIdempotent M ψ) ≫
              artinSchreierComparisonBaseMap
                (artinSchreierFunctionProjection X (p ^ r) f)
                (artinSchreierFunctionProjection X' (p ^ r) (h.appTop f)) h uq hq.w := by
  sorry

end

end AlgebraicGeometry.Etale
