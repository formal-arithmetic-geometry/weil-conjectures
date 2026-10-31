/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientGeometry
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyConstantLineTwist
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.ProjectiveBundlePicardClassification.ProjectiveBundleLocalNormalForm
import WeilConjectures.AlgebraicGeometry.ProjectiveBundlePicardClassification.ProjectiveBundleLocalTwistDescent
import WeilConjectures.AlgebraicGeometry.Locally.LocallyConstantLineTwistIdentities
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor

/-!
# Picard classification on projective bundles over arbitrary schemes

Source: EGA II, Remark 4.2.7, printed p.75; arbitrary-base extension by Stacks,
Tag 0B8W, with the field normalization of Tag 0BXJ
(blueprint: lem-sfb-projective-bundle-picard-classification).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProjectiveBundlePicardClassification

open Scheme.Modules ProjectiveBundleQuotientGeometry

/-- The decomposition with degree d and coefficient line N, using the concrete glued twist.
Source: EGA II, Remark 4.2.7; Stacks, Tag 0B8W
(blueprint: lem-sfb-projective-bundle-picard-classification). -/
def Decomposes {S P : Scheme.{u}} (p : P ⟶ S) (A : P.Modules)
    (hA : A.IsInvertible) (L : P.Modules) (d : LocallyConstant S ℤ)
    (N : S.Modules) : Prop :=
  N.IsInvertible ∧ Nonempty (L ≅
    locallyConstantLineTwist A hA (d.comap p.base.hom) ⊗ (tensorPullback p).obj N)

/-- The equivalent local formulation: a neighbourhood of each base point supports
an integer twist, with no coefficient line left after shrinking.
Source: EGA II, Remark 4.2.7; Stacks, Tags 0B8W and 0BXJ
(blueprint: lem-sfb-projective-bundle-picard-classification). -/
def IsLocallyTwist {S P : Scheme.{u}} (p : P ⟶ S) (A : P.Modules)
    (hA : A.IsInvertible) (L : P.Modules) : Prop :=
  ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ m : ℤ,
    Nonempty ((tensorPullback (p ⁻¹ᵁ U).ι).obj L ≅
      (tensorPullback (p ⁻¹ᵁ U).ι).obj (integerLinePower A hA m))

/-- All clauses of the classification, for a fixed projection and tautological line.
Base change is expressed on any pullback square, hence includes the canonical
projective bundle of the pulled-back E by quotient geometry.
Source: EGA II, Remarks 4.2.7 and 4.2.10; Stacks, Tags 0B8W and 0BXJ
(blueprint: lem-sfb-projective-bundle-picard-classification). -/
structure HasPicardClassification {S P : Scheme.{u}} (p : P ⟶ S)
    (A : P.Modules) (hA : A.IsInvertible) : Prop where
  /-- The glued twist has the specified restriction on each disjoint open stratum. -/
  twist_restrict (d : LocallyConstant S ℤ) (m : ℤ) :
    Nonempty ((tensorPullback (p ⁻¹ᵁ lineDegreeOpen d m).ι).obj
      (locallyConstantLineTwist A hA (d.comap p.base.hom)) ≅
      (tensorPullback (p ⁻¹ᵁ lineDegreeOpen d m).ι).obj (integerLinePower A hA m))
  /-- Existence and uniqueness of degree and of the coefficient's isomorphism class. -/
  classification (L : P.Modules) (hL : L.IsInvertible) :
    ∃ (d : LocallyConstant S ℤ) (N : S.Modules), Decomposes p A hA L d N ∧
      ∀ (d' : LocallyConstant S ℤ) (N' : S.Modules),
        Decomposes p A hA L d' N' → d' = d ∧ Nonempty (N' ≅ N)
  /-- The displayed local formulation is equivalent to existence of a decomposition. -/
  local_iff (L : P.Modules) (hL : L.IsInvertible) :
    IsLocallyTwist p A hA L ↔
      ∃ (d : LocallyConstant S ℤ) (N : S.Modules), Decomposes p A hA L d N
  /-- Every invertible module has the local twist form. -/
  locally_twist (L : P.Modules) (hL : L.IsInvertible) : IsLocallyTwist p A hA L
  /-- Tensor products add degrees and tensor the coefficient lines. -/
  tensor (L L' : P.Modules) (d d' : LocallyConstant S ℤ) (N N' : S.Modules) :
    Decomposes p A hA L d N → Decomposes p A hA L' d' N' →
      Decomposes p A hA (L ⊗ L') (d + d') (N ⊗ N')
  /-- Arbitrary base change pulls back the degree function and the coefficient line. -/
  base_change (T Q : Scheme.{u}) (h : T ⟶ S) (a : Q ⟶ P) (q : Q ⟶ T)
      (sq : IsPullback a q p h) (L : P.Modules) (d : LocallyConstant S ℤ)
      (N : S.Modules) :
    Decomposes p A hA L d N →
      ∃ hAQ : ((tensorPullback a).obj A).IsInvertible,
        Decomposes q ((tensorPullback a).obj A) hAQ ((tensorPullback a).obj L)
          (d.comap h.base.hom) ((tensorPullback h).obj N)
  /-- Over a field the coefficient line is trivial, leaving a unique integer twist. -/
  field (k : Type u) [Field k] (e : S ≅ Spec (CommRingCat.of k))
      (L : P.Modules) (hL : L.IsInvertible) :
    ∃! m : ℤ, Nonempty (L ≅ integerLinePower A hA m)

/-- The explicit tensor pullback preserves local triviality, by uniqueness of left
adjoints and the ordinary module pullback. Source: Stacks, Tag 0096
(blueprint: lem-sfb-projective-bundle-picard-classification). -/
private theorem invertible_tensorPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (hM : M.IsInvertible) : ((tensorPullback f).obj M).IsInvertible := by
  have : M.IsInvertible := hM
  let e := (tensorPullbackSectionAdjunction f).leftAdjointUniq
    (pullbackPushforwardAdjunction f)
  exact IsInvertible.of_iso (e.app M).symm

/-- Invertible modules on a projective bundle of constant rank at least two have the
unique degree/coefficient decomposition, its local form, tensor law and arbitrary
base-change compatibility. The existential quasi-coherence proof is a consequence
of finite local freeness, so it adds no hypothesis.

Source: EGA II, Remark 4.2.7, printed p.75; Stacks, Tags 0B8W, 0BXJ and 07VK
(blueprint: lem-sfb-projective-bundle-picard-classification).

Proof:
1. Over a field trivialize L on the polynomial affine charts using
lem-sfb-affine-space-invertible-trivial. Units on a double overlap are exactly
c times an integer power of the coordinate ratio, by polynomial and Laurent degrees.
2. For dimension one use lem-sfb-projective-line-invertible-classification. In higher
dimension the triple-overlap cocycle forces all exponents equal; rescale chart bases
to remove the scalar cocycle. The remaining transitions define O(m). Chart units
are constants, proving uniqueness and invariance under field extension.
3. Over a Noetherian affine base trivialize the fibre after twisting by -m. Properness,
flatness of polynomial charts, H^1(P^n,O)=0 and
lem-sfb-proper-flat-fibre-section-lifting lift its generator. Its generation locus
contains the fibre; properness lets us remove the closed image of its complement.
This gives the asserted local twist near the base point.
4. For an arbitrary base trivialize E on affine opens. Write each coordinate ring
as a limit of finite-type integer algebras. The projective-space models are qcqs
with affine transitions and have the required limit by lem-weil-pbc-limit-fibre-products.
Descend L by lem-trf-invertible-affine-limit-descent and pull back step 3.
5. Field uniqueness identifies the local exponents on overlaps, giving the locally
constant d. Glue its powers on the disjoint open strata; the direct-image product
used here has precisely those sections, including on the empty scheme.
6. The degree-zero projective-space cohomology calculation identifies O_S with
p_*O_P as sheaves of rings on every open, compatibly with restriction and base change.
7. The transition units of L tensor O(-d) therefore descend uniquely to units on
the base. Glue them to N using lem-weil-pbc-glue-sheaves-of-modules. The compatible
local maps glue to p^*N isomorphic to L tensor O(-d). Conversely trivialize N locally
and make d constant to recover the local formulation.
8. Restrict any decomposition to each residue-field fibre to recover d. To recover
N up to isomorphism, trivialize both candidate lines locally; an isomorphism of
their pullbacks is multiplication by a unit, which descends uniquely by step 6.
The descended local maps glue; no section of p is needed.
9. Multiplication of transitions gives the tensor law. Quotient geometry identifies
the base change with P(h^*E) and its tautological line, by representable uniqueness.
Pullback preserves tensor, duals and composition, so on each degree stratum it
pulls the decomposition back to (d composed with h,h^*N). Field coefficient lines
are trivial, yielding the final assertion. -/
theorem projective_bundle_picard_classification (S : Scheme.{u}) (E : S.Modules)
    (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (hr : 2 ≤ r) :
    ∃ hE : E.IsQuasicoherent,
      ∀ D : @TautologicalQuotient S E hE,
        HasPicardClassification
          (@SymmetricAlgebraSheaf.gradedAlgebraData S E hE).relProjHom D.line D.invertible := by
  have : E.IsLocallyFree := SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree E r
  let hE : E.IsQuasicoherent := inferInstance
  refine ⟨hE, ?_⟩
  intro D
  let p := (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom
  obtain ⟨hlocal, hfield⟩ := projective_bundle_local_normal_form S E r hr D
  have hclass (L : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.Modules)
      (hL : L.IsInvertible) :
      ∃ (d : LocallyConstant S ℤ) (N : S.Modules), Decomposes p D.line D.invertible L d N ∧
        ∀ (d' : LocallyConstant S ℤ) (N' : S.Modules),
          Decomposes p D.line D.invertible L d' N' → d' = d ∧ Nonempty (N' ≅ N) :=
    projective_bundle_local_twist_descent S E r hr D L hL (hlocal L hL)
  obtain ⟨hrestrict, hadd, hpull⟩ := locallyConstantLineTwist_identities D.line D.invertible
  refine
    { twist_restrict := ?_
      classification := hclass
      local_iff := ?_
      locally_twist := hlocal
      tensor := ?_
      base_change := ?_
      field := hfield }
  · intro d m
    exact hrestrict (d.comap p.base.hom) m (p ⁻¹ᵁ lineDegreeOpen d m) (fun _ hx ↦ hx)
  · intro L hL
    constructor
    · intro _
      obtain ⟨d, N, hN, _⟩ := hclass L hL
      exact ⟨d, N, hN⟩
    · intro _
      exact hlocal L hL
  · intro L L' d d' N N' h h'
    obtain ⟨hN, ⟨e⟩⟩ := h
    obtain ⟨hN', ⟨e'⟩⟩ := h'
    have : N.IsInvertible := hN
    have : N'.IsInvertible := hN'
    refine ⟨inferInstance, ?_⟩
    obtain ⟨et⟩ := hadd (d.comap p.base.hom) (d'.comap p.base.hom)
    have hd : d.comap p.base.hom + d'.comap p.base.hom = (d + d').comap p.base.hom := by
      ext x
      rfl
    obtain ⟨ep, _, _⟩ := module_pullback_tensor p
    let swap :
        (locallyConstantLineTwist D.line D.invertible (d.comap p.base.hom) ⊗
          (tensorPullback p).obj N) ⊗
        (locallyConstantLineTwist D.line D.invertible (d'.comap p.base.hom) ⊗
          (tensorPullback p).obj N') ≅
        (locallyConstantLineTwist D.line D.invertible (d.comap p.base.hom) ⊗
          locallyConstantLineTwist D.line D.invertible (d'.comap p.base.hom)) ⊗
        ((tensorPullback p).obj N ⊗ (tensorPullback p).obj N') :=
      { hom := tensorμ _ _ _ _, inv := tensorδ _ _ _ _ }
    exact ⟨(e ⊗ᵢ e') ≪≫ swap ≪≫
      ((et ≪≫ eqToIso (congrArg (locallyConstantLineTwist D.line D.invertible) hd)) ⊗ᵢ
        (ep N N').symm)⟩
  · intro T Q h a q sq L d N hdec
    obtain ⟨hN, ⟨e⟩⟩ := hdec
    have hAQ := invertible_tensorPullback a D.line D.invertible
    refine ⟨hAQ, invertible_tensorPullback h N hN, ?_⟩
    obtain ⟨et⟩ := hpull Q a hAQ (d.comap p.base.hom)
    have hd : (d.comap p.base.hom).comap a.base.hom =
        (d.comap h.base.hom).comap q.base.hom := by
      ext x
      exact congrArg d (congrArg (fun f ↦ f x) sq.w)
    obtain ⟨ep, _, _⟩ := module_pullback_tensor a
    obtain ⟨cp⟩ := nonempty_tensorPullbackComp a p
    obtain ⟨cq⟩ := nonempty_tensorPullbackComp q h
    let ec : (tensorPullback a).obj ((tensorPullback p).obj N) ≅
        (tensorPullback q).obj ((tensorPullback h).obj N) :=
      (cp.app N).symm ≪≫
        eqToIso (congrArg (fun f ↦ (tensorPullback f).obj N) sq.w) ≪≫ cq.app N
    exact ⟨(tensorPullback a).mapIso e ≪≫ ep _ _ ≪≫
      ((et ≪≫ eqToIso (congrArg
        (locallyConstantLineTwist ((tensorPullback a).obj D.line) hAQ) hd)) ⊗ᵢ ec)⟩

end AlgebraicGeometry.ProjectiveBundlePicardClassification
