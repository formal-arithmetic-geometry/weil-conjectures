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
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Conj
public import Mathlib.Data.Finite.Perm
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import WeilConjectures.RingTheory.AdjoinRootBaseChangePushout

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

private theorem coverHom_ext (p : ℕ) (X W : Scheme.{u}) (f : Γ(X, ⊤))
    (s t : W ⟶ (artinSchreierCover p X f).left)
    (hbase : s ≫ (artinSchreierCover p X f).hom =
      t ≫ (artinSchreierCover p X f).hom)
    (hcoord : s.appTop (artinSchreierCoverCoordinate p X f) =
      t.appTop (artinSchreierCoverCoordinate p X f)) : s = t := by
  let F := artinSchreierCoverPolynomial p X f
  let φ : Γ(X, ⊤) ⟶ CommRingCat.of (AdjoinRoot F) :=
    CommRingCat.ofHom (algebraMap _ _)
  let g := pullback.snd X.toSpecΓ (Spec.map φ)
  apply pullback.hom_ext hbase
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro r
    have hc : φ ≫ (Scheme.ΓSpecIso (.of (AdjoinRoot F))).inv ≫ g.appTop =
        (artinSchreierCover p X f).hom.appTop := by
      have h := congrArg Scheme.Hom.appTop
        (pullback.condition (f := X.toSpecΓ) (g := Spec.map φ))
      have h' := congrArg (fun k ↦ (Scheme.ΓSpecIso Γ(X, ⊤)).inv ≫ k) h.symm
      simpa [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
        ← Scheme.ΓSpecIso_inv_naturality_assoc, g, φ, F, artinSchreierCover] using h'
    change s.appTop (g.appTop ((Scheme.ΓSpecIso (.of (AdjoinRoot F))).inv
        (φ r))) = t.appTop (g.appTop ((Scheme.ΓSpecIso (.of (AdjoinRoot F))).inv
        (φ r)))
    have hcr := congrArg (fun k : Γ(X, ⊤) ⟶ Γ((artinSchreierCover p X f).left, ⊤)
      ↦ k r) hc
    change g.appTop ((Scheme.ΓSpecIso (.of (AdjoinRoot F))).inv (φ r)) =
      (artinSchreierCover p X f).hom.appTop r at hcr
    exact (congrArg s.appTop hcr).trans
      ((congrArg (fun k : W ⟶ X ↦ k.appTop r) hbase).trans
        (congrArg t.appTop hcr).symm)
  · change s.appTop (g.appTop ((Scheme.ΓSpecIso (.of (AdjoinRoot F))).inv
        (AdjoinRoot.root F))) =
      t.appTop (g.appTop ((Scheme.ΓSpecIso (.of (AdjoinRoot F))).inv
        (AdjoinRoot.root F)))
    exact hcoord

private theorem coverLift_exists (p : ℕ) (X W : Scheme.{u}) (f : Γ(X, ⊤))
    (v : W ⟶ X) (z : Γ(W, ⊤)) (hz : z ^ p - z = v.appTop f) :
    ∃ s : W ⟶ (artinSchreierCover p X f).left,
      s ≫ (artinSchreierCover p X f).hom = v ∧
      s.appTop (artinSchreierCoverCoordinate p X f) = z := by
  let F := artinSchreierCoverPolynomial p X f
  let φ : Γ(X, ⊤) ⟶ CommRingCat.of (AdjoinRoot F) :=
    CommRingCat.ofHom (algebraMap _ _)
  have hz' : F.eval₂ v.appTop.hom z = 0 := by
    simpa [F, artinSchreierCoverPolynomial, sub_eq_zero] using hz
  let ψ : CommRingCat.of (AdjoinRoot F) ⟶ Γ(W, ⊤) :=
    CommRingCat.ofHom (AdjoinRoot.lift v.appTop.hom z hz')
  have hψ : φ ≫ ψ = v.appTop := by
    apply CommRingCat.hom_ext
    exact AdjoinRoot.lift_comp_of hz'
  let w := W.toSpecΓ ≫ Spec.map ψ
  have hw : w ≫ Spec.map φ = v ≫ X.toSpecΓ := by
    rw [Scheme.toSpecΓ_naturality, ← hψ, Spec.map_comp]
    simp [w]
  refine ⟨pullback.lift v w hw.symm, pullback.lift_fst _ _ _, ?_⟩
  change (pullback.lift v w hw.symm).appTop
    ((pullback.snd X.toSpecΓ (Spec.map φ)).appTop
      ((Scheme.ΓSpecIso (.of (AdjoinRoot F))).inv (AdjoinRoot.root F))) = z
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, pullback.lift_snd]
  change ((Scheme.ΓSpecIso (.of (AdjoinRoot F))).inv ≫ w.appTop)
    (AdjoinRoot.root F) = z
  have he : (Scheme.ΓSpecIso (.of (AdjoinRoot F))).inv ≫ w.appTop = ψ := by
    simp [w]
  rw [he]
  exact AdjoinRoot.lift_root hz'

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
  classical
  let Y := (artinSchreierCover p X 0).left
  let π := (artinSchreierCover p X 0).hom
  let t := artinSchreierCoverCoordinate p X 0
  have hY : (p : Γ(Y, ⊤)) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg π.appTop hchar
  have ht : t ^ p = t := by
    let F := artinSchreierCoverPolynomial p X 0
    have hr : AdjoinRoot.root F ^ p - AdjoinRoot.root F = 0 := by
      simpa [F, artinSchreierCoverPolynomial] using AdjoinRoot.eval₂_root F
    let q := pullback.snd X.toSpecΓ (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, ⊤) (AdjoinRoot F))))
    dsimp only [t, artinSchreierCoverCoordinate]
    exact sub_eq_zero.mp (by
      simpa only [map_sub, map_pow, map_zero, F, q] using
        congrArg (fun z ↦ q.appTop ((Scheme.ΓSpecIso (.of (AdjoinRoot F))).inv z)) hr)
  obtain ⟨S, ι, hι⟩ := Scheme.exists_frobeniusFixedSections_ringEquiv p Fact.out
  let b := (ι Y hY).symm ⟨t, ((hι Y hY).1 t).mpr ht⟩
  have hb : ((ι Y hY b : S Y hY) : Γ(Y, ⊤)) = t := by
    exact congrArg Subtype.val ((ι Y hY).apply_symm_apply _)
  have roots (a : ZMod p) : (a.val : Γ(X, ⊤)) ^ p - a.val = (𝟙 X : X ⟶ X).appTop 0 := by
    rw [map_zero, sub_eq_zero]
    rcases subsingleton_or_nontrivial Γ(X, ⊤) with h | h
    · exact Subsingleton.elim _ _
    have : CharP Γ(X, ⊤) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hchar
    simpa only [map_pow, ZMod.castHom_apply, ZMod.cast_eq_val] using
      congrArg (fun z : ZMod p ↦ (ZMod.castHom (dvd_refl p) Γ(X, ⊤)) z)
        (ZMod.pow_card a)
  choose s hs hc using fun a ↦ coverLift_exists p X X 0 (𝟙 X) a.val (roots a)
  let G : ZMod p → Scheme.{u} := fun _ ↦ X
  let d : (∐ G) ⟶ Y := Sigma.desc s
  let P : ZMod p → Y.Opens := fun a ↦
    ⟨{y | b y = a}, b.isLocallyConstant.isOpen_fiber a⟩
  have hP : (⨆ a, P a) = ⊤ := by
    apply top_unique
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨b y, rfl⟩
  have hdisj (a a' : ZMod p) (h : a ≠ a') : Disjoint (P a) (P a') := by
    rw [disjoint_iff]
    apply le_bot_iff.mp
    intro y hy
    exact h (hy.1.symm.trans hy.2)
  let c : IsColimit (Cofan.mk Y (fun a ↦ (P a).ι)) :=
    Nonempty.some (nonempty_isColimit_cofanMk_of (fun a ↦ (P a).ι)
      (by simpa using hP) (by intro a a' h; simpa using hdisj a a' h))
  let v : Y ⟶ ∐ G := c.desc (Cofan.mk (∐ G)
    (fun a ↦ ((P a).ι ≫ π) ≫ Sigma.ι G a))
  have hv (a : ZMod p) : (P a).ι ≫ v = ((P a).ι ≫ π) ≫ Sigma.ι G a :=
    c.fac _ ⟨a⟩
  have hd : d ≫ π = Sigma.desc (fun _ : ZMod p ↦ 𝟙 X) := by
    apply Sigma.hom_ext
    intro a
    simpa [d, G, π, Category.assoc] using hs a
  have hrestrict (a : ZMod p) : (P a).ι.appTop t = (a.val : Γ((P a).toScheme, ⊤)) := by
    have hPchar : (p : Γ((P a).toScheme, ⊤)) = 0 := by
      simpa only [map_natCast, map_zero] using congrArg (P a).ι.appTop hY
    rw [← hb, (hι Y hY).2.2.2 _ hPchar (P a).ι b]
    have he : LocallyConstant.comap (P a).ι.base.hom b =
        LocallyConstant.const (P a).toScheme a := by
      apply LocallyConstant.ext
      intro y
      exact y.property
    rw [he, (hι (P a).toScheme hPchar).2.2.1 a]
  have hvo : v ≫ d = 𝟙 Y := by
    apply c.hom_ext
    intro j
    obtain ⟨a⟩ := j
    change (P a).ι ≫ (v ≫ d) = (P a).ι ≫ 𝟙 Y
    rw [← Category.assoc, hv]
    simp only [Category.assoc, d, G, Sigma.ι_desc, Category.comp_id]
    apply coverHom_ext p X (P a).toScheme 0
    · simp only [Category.assoc, hs, Category.comp_id]
      rfl
    · simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hc, map_natCast]
      exact (hrestrict a).symm
  have hconst (a : ZMod p) : LocallyConstant.comap (s a).base.hom b =
      LocallyConstant.const X a := by
    apply (ι X hchar).injective
    apply Subtype.ext
    rw [← (hι Y hY).2.2.2 X hchar (s a) b, hb, hc,
      (hι X hchar).2.2.1 a]
  have hdo : d ≫ v = 𝟙 (∐ G) := by
    apply Sigma.hom_ext
    intro a
    simp only [← Category.assoc, d, G, Sigma.ι_desc, Category.comp_id]
    have hrange : Set.range (s a) ⊆ Set.range (P a).ι := by
      rintro _ ⟨x, rfl⟩
      refine ⟨⟨s a x, ?_⟩, rfl⟩
      exact congrArg (fun l : LocallyConstant X (ZMod p) ↦ l x) (hconst a)
    let l := IsOpenImmersion.lift (P a).ι (s a) hrange
    have hl : l ≫ (P a).ι = s a := IsOpenImmersion.lift_fac _ _ _
    rw [← hl, Category.assoc, hv, ← Category.assoc, ← Category.assoc, hl, hs]
    rfl
  let e : Over.mk (Sigma.desc (fun _ : ZMod p ↦ 𝟙 X)) ≅ artinSchreierCover p X 0 :=
    Over.isoMk (⟨d, v, hdo, hvo⟩ : (∐ G) ≅ Y) hd
  refine ⟨e, ?_⟩
  intro a
  change (Sigma.ι G a ≫ d).appTop t = _
  simpa [d, G] using hc a

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
  classical
  let X := Spec (.of (ZMod 3))
  have : Subsingleton X := inferInstanceAs (Subsingleton (PrimeSpectrum (ZMod 3)))
  have : Nonempty X := inferInstanceAs (Nonempty (PrimeSpectrum (ZMod 3)))
  have hchar : (3 : Γ(X, ⊤)) = 0 := by
    apply (Scheme.ΓSpecIso (.of (ZMod 3))).commRingCatIsoToRingEquiv.injective
    change (Scheme.ΓSpecIso (.of (ZMod 3))).hom (3 : Γ(X, ⊤)) =
      (Scheme.ΓSpecIso (.of (ZMod 3))).hom (0 : Γ(X, ⊤))
    change (Scheme.ΓSpecIso (.of (ZMod 3))).hom.hom (3 : Γ(X, ⊤)) =
      (Scheme.ΓSpecIso (.of (ZMod 3))).hom.hom (0 : Γ(X, ⊤))
    rw [map_ofNat, map_zero]
    exact ZMod.natCast_self 3
  obtain ⟨e, _⟩ := artinSchreierCover_zero_split 3 X hchar
  obtain ⟨d⟩ := coproductCopies_onePoint_aut X (ZMod 3)
  let E : Aut (artinSchreierCover 3 X 0) ≃* Equiv.Perm (Fin 3) :=
    e.symm.conjAut.trans (d.trans ((ZMod.finEquiv 3).toEquiv.symm.permCongrHom))
  refine ⟨⟨E⟩, ?_⟩
  intro σ hσ
  have hcard := Nat.card_le_card_of_surjective (E ∘ σ) (E.surjective.comp hσ)
  have hperm : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm, Nat.card_fin]
    decide
  have hdom : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card]
    exact ZMod.card 3
  omega

end AlgebraicGeometry
