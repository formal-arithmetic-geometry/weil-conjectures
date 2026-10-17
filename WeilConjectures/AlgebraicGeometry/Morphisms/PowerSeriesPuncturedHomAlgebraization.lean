/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleAdicUniqueLift
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedCoverSections
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# Algebraization of compatible formal morphisms on a punctured power-series open

Source: Stacks Project, Tags 0EY9, 0EKP and 0EL8.
(blueprint: lem-sbc-power-series-punctured-formal-hom-algebraization)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- Compatible maps on all quotient-power thickenings of finite étale covers
algebraize on the power-series open.

Source: Stacks Project, Tag 0EY9, the comparison argument of Tag 0EKP and
algebra-map verification of Tag 0EL8.
(blueprint: lem-sbc-power-series-punctured-formal-hom-algebraization)

Proof: Write B = A[[x_1,...,x_d]] and I = ker(constantCoeff) = (x_1,...,x_d).
Put U = Spec(A) minus its closed point. Hartogs at depth two identifies
Gamma(U,O_U) with A. Since B/I^(n+1) is finite free over A on the monomials
of degree at most n, the limit of the sections on the infinitesimal
neighbourhoods of U in V is B. The comparison from Gamma(V,O_V) to this
limit is injective: Krull intersection detects zero germs along U, and
flat local depth shows that every associated prime of B is pB for an
associated prime p of A. Depth positive excludes the maximal ideal of A;
the prime pB specializes to pB+I, which belongs to U. Thus a section zero
formally is zero at every associated point of V, hence zero. The composite
B -> Gamma(V,O_V) -> B is the canonical isomorphism, so both maps are
isomorphisms. For any finite locally free E on the Noetherian quasi-affine
V, global generation of the dual gives a universally exact presentation
0 -> E -> O^r -> O^s: first embed E in O^r with locally free cokernel,
then embed that cokernel in O^s. Sections and inverse limits preserve the
kernel. The structure-sheaf comparison therefore gives the same comparison
for E and hence for internal Hom bundles, as in Tag 0EKP.
A compatible family g_n gives compatible maps between the finite locally
free direct-image algebras of Q and P. The Hom comparison lifts these to
a module map. Its multiplication and unit identities hold after completion;
faithfulness for the tensor square of the source algebra and for O_V gives
the identities before completion. Relative Spec turns the resulting algebra
map into g over V. Its pullback to every thickening is g_n by the construction.
No infinitesimal lifting or existence of a map on the reduced section is
used here: the entire compatible family is an input. Zero algebras, empty
covers, and variable ranks are included in the module comparison. -/
theorem finiteEtale_powerSeries_punctured_formal_hom_algebraization
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (d : ℕ) (hd : 0 < d)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : ∀ x : Spec (.of A),
      (Spec.map (CommRingCat.ofHom
        (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)))) x ∈ V ↔
        x ≠ IsLocalRing.closedPoint A)
    (P Q : V.toScheme.FiniteEtale)
    (g : ∀ n : ℕ, FiniteEtale.Adic.cover
      (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) V P n ⟶ Q.obj.left)
    (hover : ∀ n, g n ≫ Q.obj.hom = FiniteEtale.Adic.coverMap
      (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) V P n ≫ P.obj.hom)
    (hcompat : ∀ n, FiniteEtale.Adic.coverTransition
      (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) V P n ≫ g (n + 1) = g n) :
    ∃ φ : P.obj.left ⟶ Q.obj.left, φ ≫ Q.obj.hom = P.obj.hom ∧
      ∀ n, FiniteEtale.Adic.coverMap
        (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) V P n ≫ φ = g n := by
  classical
  let f := MvPowerSeries.constantCoeff (σ := Fin d) (R := A)
  let p (n : ℕ) := FiniteEtale.Adic.coverMap f V P n
  let t (n : ℕ) := FiniteEtale.Adic.coverTransition f V P n
  have hsections := finiteEtale_powerSeries_punctured_cover_sections_comparison
    A hdepth d hd V hV P
  have hinj (a b : Γ(P.obj.left, ⊤))
      (hab : ∀ n, (p n).appTop a = (p n).appTop b) : a = b := by
    have hc (n : ℕ) : (t n).appTop ((p (n + 1)).appTop a) = (p n).appTop a := by
      change ((p (n + 1)).appTop ≫ (t n).appTop) a = _
      rw [← Scheme.Hom.comp_appTop, FiniteEtale.Adic.coverTransition_coverMap]
    obtain ⟨c, hc', hu⟩ := hsections (fun n ↦ (p n).appTop a) hc
    exact (hu a (fun _ ↦ rfl)).trans (hu b (fun n ↦ (hab n).symm)).symm
  have hfamily (a : Γ(Q.obj.left, ⊤)) (n : ℕ) :
      (t n).appTop ((g (n + 1)).appTop a) = (g n).appTop a := by
    change ((g (n + 1)).appTop ≫ (t n).appTop) a = _
    rw [← Scheme.Hom.comp_appTop, hcompat]
  have hex (a : Γ(Q.obj.left, ⊤)) :
      ∃ b : Γ(P.obj.left, ⊤), ∀ n, (p n).appTop b = (g n).appTop a :=
    (hsections (fun n ↦ (g n).appTop a) (hfamily a)).exists
  choose b hb using hex
  let α : Γ(Q.obj.left, ⊤) →+* Γ(P.obj.left, ⊤) :=
    { toFun := b
      map_one' := by
        apply hinj
        intro n
        rw [hb, map_one, map_one]
      map_mul' := by
        intro a a'
        apply hinj
        intro n
        rw [hb, map_mul, map_mul, hb, hb]
      map_zero' := by
        apply hinj
        intro n
        rw [hb, map_zero, map_zero]
      map_add' := by
        intro a a'
        apply hinj
        intro n
        rw [hb, map_add, map_add, hb, hb] }
  let α' := CommRingCat.ofHom α
  have hα (n : ℕ) : α' ≫ (p n).appTop = (g n).appTop := by
    ext a
    exact hb a n
  have hbase : Q.obj.hom.appTop ≫ α' = P.obj.hom.appTop := by
    ext a
    apply hinj
    intro n
    change (Q.obj.hom.appTop ≫ α' ≫ (p n).appTop) a =
      (P.obj.hom.appTop ≫ (p n).appTop) a
    rw [hα, ← Scheme.Hom.comp_appTop, hover, Scheme.Hom.comp_appTop]
    rfl
  have : IsNoetherian (Spec (.of (MvPowerSeries (Fin d) A))) := inferInstance
  have : TopologicalSpace.NoetherianSpace (Spec (.of (MvPowerSeries (Fin d) A))) := inferInstance
  have : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : CompactSpace V.toScheme := TopologicalSpace.NoetherianSpace.compactSpace V.toScheme
  have : V.toScheme.IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion V.ι
  have : IsFinite Q.obj.hom := Q.property
  let q : Q.obj.left ⟶ V.toScheme := Q.obj.hom
  have : IsAffineHom q := inferInstanceAs (IsAffineHom Q.obj.hom)
  have : Q.obj.left.IsQuasiAffine := Scheme.IsQuasiAffine.of_isAffineHom q
  let square := isPullback_toSpecΓ_toSpecΓ q
  have hw : P.obj.hom ≫ V.toScheme.toSpecΓ =
      (P.obj.left.toSpecΓ ≫ Spec.map α') ≫ Spec.map Q.obj.hom.appTop := by
    rw [Category.assoc, ← Spec.map_comp, hbase]
    exact Scheme.toSpecΓ_naturality P.obj.hom
  let φ := square.lift P.obj.hom (P.obj.left.toSpecΓ ≫ Spec.map α') hw
  refine ⟨φ, square.lift_fst _ _ _, ?_⟩
  intro n
  apply (cancel_mono Q.obj.left.toSpecΓ).mp
  change p n ≫ (φ ≫ Q.obj.left.toSpecΓ) = g n ≫ Q.obj.left.toSpecΓ
  rw [show φ ≫ Q.obj.left.toSpecΓ = P.obj.left.toSpecΓ ≫ Spec.map α' from
    square.lift_snd _ _ _]
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc,
    ← Spec.map_comp, hα, ← Scheme.toSpecΓ_naturality]

end AlgebraicGeometry.Scheme
