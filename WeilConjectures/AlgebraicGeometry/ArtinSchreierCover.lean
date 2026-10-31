/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.Algebra.Field.ULift
import Mathlib.RingTheory.Etale.StandardEtale
import WeilConjectures.AlgebraicGeometry.ArtinSchreier
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.AlgebraicGeometry.ConstantSheafSectionsLocallyConstant
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Topology.LocallyConstant.Basic

/-! # Artin–Schreier covers of global functions

Source: blueprint, Fourier–Deligne transform, sk-lem-as-properties,
lem-fd-as-cover; Stacks Project, Tag 0A3J (blueprint: lem-fd-as-cover).

The cover is constructed by base change from the polynomial quotient over the global
functions. Its affine presentations identify it with the relative spectrum in the source.
The empty scheme is included: the characteristic hypothesis says only that `p * 1 = 0`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Polynomial

noncomputable section

namespace AlgebraicGeometry

/-- The equation defining the Artin–Schreier cover.
Source: blueprint, lem-fd-as-cover, first sentence (blueprint: lem-fd-as-cover). -/
def artinSchreierCoverPolynomial (p : ℕ) (X : Scheme.{u}) (f : Γ(X, ⊤)) :
    Polynomial Γ(X, ⊤) :=
  Polynomial.X ^ p - Polynomial.X - Polynomial.C f

/-- The Artin–Schreier cover of `f`, as a scheme over `X`. This is the base change along
`X.toSpecΓ` of the spectrum of the actual quotient ring `Γ(X)[T]/(T^p-T-f)`.
Source: blueprint, lem-fd-as-cover, first sentence (blueprint: lem-fd-as-cover). -/
def artinSchreierCover (p : ℕ) (X : Scheme.{u}) (f : Γ(X, ⊤)) : Over X :=
  Over.mk (pullback.fst X.toSpecΓ
    (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, ⊤) (AdjoinRoot (artinSchreierCoverPolynomial p X f))))))

/-- The class of `T` on the Artin–Schreier cover, pulled back from its quotient-ring model.
Source: blueprint, lem-fd-as-cover, the coordinate `T` (blueprint: lem-fd-as-cover). -/
def artinSchreierCoverCoordinate (p : ℕ) (X : Scheme.{u}) (f : Γ(X, ⊤)) :
    Γ((artinSchreierCover p X f).left, ⊤) :=
  (pullback.snd X.toSpecΓ
    (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, ⊤) (AdjoinRoot (artinSchreierCoverPolynomial p X f)))))).appTop
    ((Scheme.ΓSpecIso (.of (AdjoinRoot (artinSchreierCoverPolynomial p X f)))).inv
      (AdjoinRoot.root (artinSchreierCoverPolynomial p X f)))

/-- The affine charts of the cover are the polynomial quotients in the source, with the
specified coefficient homomorphism and coordinate. Thus the construction is the relative
spectrum of `𝒪_X[T]/(T^p-T-f)`.
Source: blueprint, lem-fd-as-cover, first sentence (blueprint: lem-fd-as-cover).

Proof: localization commutes with adjoining a root. Restrict the base-change construction
to an affine open, identify that open with the spectrum of its sections, and use the
quotient presentation after localization. This gives the displayed isomorphism, its
coefficient formula, and its formula on the class of `T`. The relative-spectrum affine
charts of lem-weil-pbc-affine-morphism-relative-spec then identify the constructions. -/
theorem artinSchreierCover_affinePresentation (p : ℕ) [Fact p.Prime]
    (X : Scheme.{u}) (hchar : (p : Γ(X, ⊤)) = 0) (f : Γ(X, ⊤))
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsAffineOpen ((artinSchreierCover p X f).hom ⁻¹ᵁ U) ∧
      ∃ e : AdjoinRoot (artinSchreierCoverPolynomial p U.toScheme (U.ι.appTop f)) ≃+*
        Γ(((artinSchreierCover p X f).hom ⁻¹ᵁ U).toScheme, ⊤),
        (∀ r : Γ(U.toScheme, ⊤), e (algebraMap _ _ r) =
          ((artinSchreierCover p X f).hom ∣_ U).appTop r) ∧
        e (AdjoinRoot.root
          (artinSchreierCoverPolynomial p U.toScheme (U.ι.appTop f))) =
          ((artinSchreierCover p X f).hom ⁻¹ᵁ U).ι.appTop
            (artinSchreierCoverCoordinate p X f) := by
  sorry

/-- All properties of the Artin–Schreier covering, including its translation action and
canonical equivariant automorphism group. The source of the centralizer is the group of
locally constant functions, canonically the global sections of the constant étale sheaf.
The normalization on every open where such a function is constant specifies the canonical
isomorphism, including on disconnected bases. The sheaf torsor is identified with the
represented presheaf, and the action of each constant section is identified with the
specified translation.
Source: blueprint, lem-fd-as-cover (blueprint: lem-fd-as-cover).

Proof: (1) The affine quotient has monic basis `1,T,...,T^(p-1)` by
lem-weil-pbc-monic-quotient-free. Its derivative is `-1`, so
lem-weil-pbc-standard-etale-monic-derivative gives étaleness and degree `p`.
(2) Maps into the cover are roots, by lem-weil-pbc-morphism-into-affine-scheme,
lem-asd-polynomial-quotient-hom-equivalence and lem-weil-pbc-scheme-morphism-gluing.
(3) Translation preserves the equation since `a^p=a`, by
lem-sc-field-artin-schreier-kernel; its inverse subtracts `a`.
(4) Over an algebraically closed field every root is uniquely `r+a`, by
lem-sc-artin-schreier-k. This proves simple transitivity and surjectivity.
(5) Representability is a sheaf by lem-weil-pbc-small-etale-representable-presheaf-sheaf.
Differences of roots are locally constant by lem-fd-frobenius-fixed-sections and
lem-weil-pbc-constant-sheaf-sections-locally-constant. The cover trivializes this sheaf;
lem-weil-pbc-etale-base-change-continuous supplies covers after pullback.
(6) For an automorphism `g`, the difference `g*T-T` is a Frobenius-fixed function on `Y`.
It commutes with all translations exactly when that function is invariant.
(7) Invariant functions descend uniquely to the base: geometric transitivity gives
constancy on fibres, and lem-weil-pbc-etale-morphism-open-map makes the descended function
locally constant. Conversely, glue translations on its clopen fibres. Addition corresponds
to composition. This gives the normalized centralizer isomorphism.
(8) A geometric fibre proves faithfulness when the base is nonempty. On connected `Y`
the difference function is constant, so all automorphisms are translations. Over an empty
base the cover is empty and its automorphism group has one element. -/
theorem artinSchreier_cover_properties (p : ℕ) [Fact p.Prime]
    (X : Scheme.{u}) (hchar : (p : Γ(X, ⊤)) = 0) (f : Γ(X, ⊤)) :
    IsFinite (artinSchreierCover p X f).hom ∧
    Etale (artinSchreierCover p X f).hom ∧
    (artinSchreierCover p X f).hom.IsFiniteLocallyFreeOfDegree p ∧
    ∃ σ : Multiplicative (ZMod p) →* Aut (artinSchreierCover p X f),
      (∀ a : ZMod p, (σ (Multiplicative.ofAdd a)).hom.left.appTop
          (artinSchreierCoverCoordinate p X f) =
        artinSchreierCoverCoordinate p X f + (a.val : Γ((artinSchreierCover p X f).left, ⊤))) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
        Nonempty {s : Spec (.of Ω) ⟶ (artinSchreierCover p X f).left //
          s ≫ (artinSchreierCover p X f).hom = x} ∧
        ∀ s t : {s : Spec (.of Ω) ⟶ (artinSchreierCover p X f).left //
          s ≫ (artinSchreierCover p X f).hom = x},
          ∃! a : ZMod p, t.val = s.val ≫ (σ (Multiplicative.ofAdd a)).hom.left) ∧
      (∃ (R : Sheaf.Torsor
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod p)))))
          (e : R.sheaf.obj ≅ (Scheme.Etale.forget X).op ⋙
            yoneda.obj (artinSchreierCover p X f) ⋙ uliftFunctor.{u + 1}),
        ∀ (U : X.Etale) (a : ZMod p) (s : R.sheaf.obj.obj (Opposite.op U)),
          (e.hom.app (Opposite.op U)
            (R.vadd (Opposite.op U)
              (((toSheafify X.smallEtaleTopology
                ((Functor.const X.Etaleᵒᵖ).obj
                  (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))).app
                    (Opposite.op U)) (ULift.up a)) s)).down =
            (e.hom.app (Opposite.op U) s).down ≫ (σ (Multiplicative.ofAdd a)).hom) ∧
      (Nonempty X → Function.Injective σ) ∧
      (∃ E : Multiplicative (LocallyConstant X (ZMod p)) ≃*
          Subgroup.centralizer (Set.range σ),
        ∀ (b : LocallyConstant X (ZMod p)) (a : ZMod p) (U : X.Opens),
          (∀ x : U, b x = a) →
          ((artinSchreierCover p X f).hom ⁻¹ᵁ U).ι ≫
              (E (Multiplicative.ofAdd b)).val.hom.left =
            ((artinSchreierCover p X f).hom ⁻¹ᵁ U).ι ≫
              (σ (Multiplicative.ofAdd a)).hom.left) ∧
      (ConnectedSpace (artinSchreierCover p X f).left → Function.Bijective σ) ∧
      (IsEmpty X → IsEmpty (artinSchreierCover p X f).left ∧
        Subsingleton (Aut (artinSchreierCover p X f))) := by
  sorry

/-- The cover of the zero function is the split cover, with its summands labelled by the
coordinate values in the prime field.
Source: blueprint, lem-fd-as-cover, split example (blueprint: lem-fd-as-cover).

Proof: the root correspondence and lem-fd-frobenius-fixed-sections identify roots with
locally constant prime-field functions. By lem-galois-coproduct-copies-morphisms-clopen
these are morphisms to the coproduct of copies of `X`. The maps with `T=a` on each summand
and the clopen decomposition specified by `T` are mutually inverse. -/
theorem artinSchreierCover_zero_split (p : ℕ) [Fact p.Prime]
    (X : Scheme.{u}) (hchar : (p : Γ(X, ⊤)) = 0) :
    ∃ e : Over.mk (Sigma.desc (fun _ : ZMod p ↦ 𝟙 X)) ≅ artinSchreierCover p X 0,
      ∀ a : ZMod p, (Sigma.ι (fun _ : ZMod p ↦ X) a ≫ e.hom.left).appTop
        (artinSchreierCoverCoordinate p X 0) = (a.val : Γ(X, ⊤)) := by
  sorry

/-- Over `Spec 𝔽₃` the split cover has full automorphism group `S₃`. Its translations form
only a proper subgroup, so the translation homomorphism is not generally an isomorphism.
Source: blueprint, lem-fd-as-cover, last example (blueprint: lem-fd-as-cover).

Proof: apply the zero-function splitting. A scheme automorphism over the one-point base
permutes the three summands, and its map on each summand is the identity over that base.
Every permutation gives an automorphism, and composition gives permutation composition.
The resulting group has six elements; the translation group has three elements, so no
homomorphism from the translation group to it can be surjective. -/
theorem artinSchreierCover_three_fullAut :
    Nonempty (Aut (artinSchreierCover 3 (Spec (.of (ZMod 3))) 0) ≃*
      Equiv.Perm (Fin 3)) ∧
    ∀ σ : Multiplicative (ZMod 3) →*
      Aut (artinSchreierCover 3 (Spec (.of (ZMod 3))) 0), ¬ Function.Surjective σ := by
  sorry

end AlgebraicGeometry
