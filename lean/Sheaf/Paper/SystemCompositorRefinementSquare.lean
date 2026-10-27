/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import Sheaf.Paper.SystemCompatibleCompositorNormalization
public import Sheaf.Paper.SystemCompactificationProjectionSubstitution
public import Sheaf.Paper.RefinementComparisonIsomorphism
public import WeilConjectures.Compactification.Triangle
import WeilConjectures.Compactification.OverRefinement

/-! # Refinement squares for the actual semilinear compact-support compositor

Source: Stacks Project, more-etale.tex, Tag 0F7J, lemma-shriek-composition,
independence-of-choices diagrams A--F and the final pasted rectangle
(blueprint: lem-pur-system-compositor-refinement-square).

The helpers spell the specified words in the same geometric system presentation as
compatibleCompositorWord. In particular no equality is detected by level evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
open CategoryTheory CategoryTheory.Limits WeilConjectures
namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen


variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)

/-- The supplied compactification word, in the compositor's system presentation.
Source: Stacks 0F7J (blueprint: lem-pur-system-compositor-refinement-square). -/
abbrev systemCompactificationImage {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) := J C τ c.i ⋙ R C τ c.g

/-- Quasi-compactness of the open follows from quasi-compactness of its proper composite.
Source: Stacks 0F7J (blueprint: lem-pur-system-compositor-refinement-square). -/
instance systemCompactificationOpenQC {X Y : Scheme.{u}} {f : X ⟶ Y}
    [QuasiCompact f] (c : Compactification f) : QuasiCompact c.i :=
  c.quasiCompact_openImmersion inferInstance

/-- The second open in a compatible triangle is a base change of its base open.
Source: Stacks 0F7J (blueprint: lem-pur-system-compositor-refinement-square). -/
instance systemTriangleOpenQC {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact g] (T : Compactification.Triangle f g) : QuasiCompact T.q :=
  MorphismProperty.of_isPullback T.isPullback inferInstance

/-- The intrinsic refinement mate, retaining the normalized identity direct-image edge.
No Cartesian condition is imposed on the refinement square.
Source: Stacks 0F7J, square A (blueprint: lem-pur-system-compositor-refinement-square). -/
def systemRefinementGamma {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂) (M : Derived C τ X) :
    (J C τ c₂.i).obj M ⟶ (R C τ r.hom).obj ((J C τ c₁.i).obj M) :=
  (J C τ c₂.i).map ((sId C τ X).inv.app M) ≫
    (gamma C τ c₁.i (𝟙 X) r.hom c₂.i
      (r.i_hom.trans (Category.id_comp _).symm)).app M

/-- The specified proper compositor, oriented from the finer compactification.
Source: Stacks 0F7J (blueprint: lem-pur-system-compositor-refinement-square). -/
def systemRefinementCompositor {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂) :
    R C τ c₁.g ≅ R C τ r.hom ⋙ R C τ c₂.g :=
  eqToIso (congrArg (R C τ) r.hom_g.symm) ≪≫ (sComp C τ r.hom c₂.g).symm

/-- The triangle's word beta, with its two factorization equality transports.
This is exactly compatibleCompositorWord, followed by j₁b=j_h and ps=r_h.
Source: Stacks 0F7J, squares B,C (blueprint: lem-pur-system-compositor-refinement-square). -/
def systemTriangleBeta {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g] (T : Compactification.Triangle f g) :
    systemCompactificationImage C τ T.cf ⋙ systemCompactificationImage C τ T.cg ⟶
      systemCompactificationImage C τ T.cfg :=
  compatibleCompositorWord C τ T.cf.i T.q T.cf.g T.p T.cg.i T.cg.g
      T.isPullback.w.symm ≫
    Functor.whiskerRight (jCongr C τ T.i_q).hom (R C τ (T.p ≫ T.cg.g)) ≫
    Functor.whiskerLeft (J C τ T.cfg.i) (eqToIso (congrArg (R C τ) T.p_g)).hom

/-- Exactly the three proper refinements and their two cross compatibilities.
Unlike Triangle.Hom this imposes no extra Cartesian refinement faces.
Source: Stacks 0F7J, diagrams A--F
(blueprint: lem-pur-system-compositor-refinement-square). -/
structure SystemTriangleRefinement {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T₁ T₂ : Compactification.Triangle f g) where
  rf : T₁.cf.Refinement T₂.cf
  rg : T₁.cg.Refinement T₂.cg
  rh : T₁.cfg.Refinement T₂.cfg
  b_comm : T₁.q ≫ rh.hom = rf.hom ≫ T₂.q
  p_comm : rh.hom ≫ T₂.p = T₁.p ≫ rg.hom

end AlgebraicGeometry.ProEtale.SemilinearProperOpen

namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen


variable (l : ℕ) [Fact l.Prime] (E₀ : Type u) [Field E₀]
  [Algebra (Padic l) E₀] [FiniteDimensional (Padic l) E₀]
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

section OneMap
variable {X Y : Scheme.{u}}
  [overX : X.Over (Spec (.of D.k))] [overY : Y.Over (Spec (.of D.k))]
  [ftX : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [qcX : QuasiCompact (X ↘ Spec (.of D.k))] [sepX : IsSeparated (X ↘ Spec (.of D.k))]
  [ftY : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [qcY : QuasiCompact (Y ↘ Spec (.of D.k))] [sepY : IsSeparated (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [overF : f.IsOver (Spec (.of D.k))]
  [sepF : IsSeparated f] [ftF : LocallyOfFiniteType f] [qcF : QuasiCompact f]

include D hl overX overY ftX qcX sepX ftY qcY sepY overF sepF ftF qcF

/-- The actual refinement mate is invertible on the full levelwise domain.
Source: Stacks 0F7J; proof Step 1
(blueprint: lem-pur-system-compositor-refinement-square).
Proof: choose a bounded constructible etale origin at each positive level by
lem-sf-proetale-constructible-origin. The finite proper/open mate is invertible.
The simultaneous-section evaluation and its specified identity normalization identify
these with evaluations of systemRefinementGamma. Joint conservativity proves its
invertibility, as in lem-pur-system-compactification-pf-substitution. No uniform bound,
normalization or finite Tor amplitude is required. -/
theorem systemRefinementGamma_isIso {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂)
    (M : Derived (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) X)
    (hM : compatibleCompositorDomain l E₀ X M) :
    IsIso (systemRefinementGamma (compactSupportSystemLevel l E₀)
      (compactSupportSystemQuotient l E₀) r M) := by
  sorry

/-- Theta is precisely the proper compositor followed by R of the inverse intrinsic mate.
Source: Stacks 0F7J; specified refinement comparison
(blueprint: lem-pur-system-compositor-refinement-square). -/
def systemRefinementTheta {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂)
    (M : Derived (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) X)
    (hM : compatibleCompositorDomain l E₀ X M) :
    (systemCompactificationImage (compactSupportSystemLevel l E₀)
      (compactSupportSystemQuotient l E₀) c₁).obj M ≅
    (systemCompactificationImage (compactSupportSystemLevel l E₀)
      (compactSupportSystemQuotient l E₀) c₂).obj M :=
  (systemRefinementCompositor (compactSupportSystemLevel l E₀)
      (compactSupportSystemQuotient l E₀) r).app
      ((J (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) c₁.i).obj M) ≪≫
    (R (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) c₂.g).mapIso
      (@asIso _ _ _ _ (systemRefinementGamma (compactSupportSystemLevel l E₀)
        (compactSupportSystemQuotient l E₀) r M)
        (systemRefinementGamma_isIso l E₀ D hl r M hM)).symm

/-- The input to the g-comparison again has bounded constructible levels.
Source: Stacks 0GL0 and 0F7J; proof Step 1
(blueprint: lem-pur-system-compositor-refinement-square).
Proof: evaluate the compactification word by simultaneous sections. At each level
lem-sf-proetale-constructible-origin and prop-finite-compact-support-constructibility
preserve bounded constructibility. Transport the cohomology predicates back through
the canonical encoding. Each level retains its own interval. -/
theorem systemCompactificationImage_domain (c : Compactification f)
    (M : Derived (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) X)
    (hM : compatibleCompositorDomain l E₀ X M) :
    compatibleCompositorDomain l E₀ Y
      ((systemCompactificationImage (compactSupportSystemLevel l E₀)
        (compactSupportSystemQuotient l E₀) c).obj M) := by
  sorry

/-- Comparison through the supplied common refinement, with the specified leg maps.
Source: Stacks 0F7J (blueprint: lem-pur-system-compositor-refinement-square). -/
def systemSpanComparison {c₁ c₂ c : Compactification f}
    (a : c.Refinement c₁) (b : c.Refinement c₂)
    (M : Derived (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) X)
    (hM : compatibleCompositorDomain l E₀ X M) :=
  (systemRefinementTheta l E₀ D hl a M hM).symm ≪≫
    systemRefinementTheta l E₀ D hl b M hM

/-- Common-refinement comparisons are independent of the object and both arrows.
Source: Stacks 0F7J and 0ATU; proof Step 6
(blueprint: lem-pur-system-compositor-refinement-square).
Proof: apply vertical mate pasting to obtain the composition law for theta and the
identity law from the normalized units. Equalize parallel refinement arrows by
prop-nagata-compactification-category, then cancel the invertible comparison.
Refine two spans to a common object and use this equalization on both endpoints.
This is the common-refinement clause of lem-pur-system-compactification-pf-substitution
in the geometric simultaneous-section presentation, before evaluation. -/
theorem systemSpanComparison_independent {c₁ c₂ c d : Compactification f}
    (a : c.Refinement c₁) (b : c.Refinement c₂)
    (a' : d.Refinement c₁) (b' : d.Refinement c₂)
    (M : Derived (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) X)
    (hM : compatibleCompositorDomain l E₀ X M) :
    systemSpanComparison l E₀ D hl a b M hM =
      systemSpanComparison l E₀ D hl a' b' M hM := by
  sorry

/-- Transitivity of the three common-refinement comparisons.
Source: Stacks 0F7J and 0ATU; proof Step 6
(blueprint: lem-pur-system-compositor-refinement-square).
Proof: take a common refinement of all three spans, use the preceding independence,
then cancel the inverse-forward middle theta. All maps are system maps. -/
theorem systemSpanComparison_trans {c₁ c₂ c₃ c₁₂ c₂₃ c₁₃ : Compactification f}
    (a₁₂ : c₁₂.Refinement c₁) (b₁₂ : c₁₂.Refinement c₂)
    (a₂₃ : c₂₃.Refinement c₂) (b₂₃ : c₂₃.Refinement c₃)
    (a₁₃ : c₁₃.Refinement c₁) (b₁₃ : c₁₃.Refinement c₃)
    (M : Derived (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) X)
    (hM : compatibleCompositorDomain l E₀ X M) :
    systemSpanComparison l E₀ D hl a₁₂ b₁₂ M hM ≪≫
        systemSpanComparison l E₀ D hl a₂₃ b₂₃ M hM =
      systemSpanComparison l E₀ D hl a₁₃ b₁₃ M hM := by
  let u := Compactification.infFst c₁₂ c₂₃
  let v := Compactification.infSnd c₁₂ c₂₃
  let a := u.comp a₁₂
  let b := u.comp b₁₂
  let c := v.comp b₂₃
  rw [systemSpanComparison_independent l E₀ D hl a₁₂ b₁₂ a b M hM,
    systemSpanComparison_independent l E₀ D hl a₂₃ b₂₃ b c M hM,
    systemSpanComparison_independent l E₀ D hl a₁₃ b₁₃ a c M hM]
  simp [systemSpanComparison, Iso.trans_assoc]

end OneMap
end AlgebraicGeometry.ProEtale.SemilinearProperOpen

namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen


variable (l : ℕ) [Fact l.Prime] (E₀ : Type u) [Field E₀]
  [Algebra (Padic l) E₀] [FiniteDimensional (Padic l) E₀]
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y Z : Scheme.{u}}
  [overX : X.Over (Spec (.of D.k))] [overY : Y.Over (Spec (.of D.k))]
  [overZ : Z.Over (Spec (.of D.k))]
  [ftX : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [qcX : QuasiCompact (X ↘ Spec (.of D.k))] [sepX : IsSeparated (X ↘ Spec (.of D.k))]
  [ftY : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [qcY : QuasiCompact (Y ↘ Spec (.of D.k))] [sepY : IsSeparated (Y ↘ Spec (.of D.k))]
  [ftZ : LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
  [qcZ : QuasiCompact (Z ↘ Spec (.of D.k))] [sepZ : IsSeparated (Z ↘ Spec (.of D.k))]
  {f : X ⟶ Y} {g : Y ⟶ Z}
  [overF : f.IsOver (Spec (.of D.k))] [overG : g.IsOver (Spec (.of D.k))]
  [sepF : IsSeparated f] [ftF : LocallyOfFiniteType f] [qcF : QuasiCompact f]
  [sepG : IsSeparated g] [ftG : LocallyOfFiniteType g] [qcG : QuasiCompact g]

include D hl overX overY overZ ftX qcX sepX ftY qcY sepY ftZ qcZ sepZ
  overF overG sepF ftF qcF sepG ftG qcG

/-- The refinement square for the specified proper/open compositor, before evaluation.
Source: Stacks 0F7J, independence-of-choices diagrams A--F
(blueprint: lem-pur-system-compositor-refinement-square).
Proof: Step 1 supplies the inverses on M and F₁M. Write a,d,e,z,t₁,t₂ for the
intrinsic mates of faces A,D,E,F,Q₁,Q₂. Horizontal mate pasting gives
 e = (z J_j₁)(J_b₂ a). Vertical pasting gives
 (R_u t₁)(d R_q₁) = (R_p₂ z)(t₂ R_w).
Insert canonical compositors, coherent by lem-sf-semilinear-compositor-coherence.
Expand beta and the inverse theta words. Naturality of t₂ at a interchanges the
A and Q₂ faces; the two pasting equations then give
 rho_h beta₂ = beta₁ rho_g G₂(rho_f).
Postcompose with theta_h and precompose with G₂(theta_f) theta_g; cancel the three
inverse pairs. This gives exactly the displayed equality. The F face need not be
Cartesian, and evaluation has not been used to prove equality. -/
theorem systemCompositorRefinementSquare
    {T₁ T₂ : Compactification.Triangle f g} (r : SystemTriangleRefinement T₁ T₂)
    (M : Derived (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) X)
    (hM : compatibleCompositorDomain l E₀ X M) :
    (systemTriangleBeta (compactSupportSystemLevel l E₀)
        (compactSupportSystemQuotient l E₀) T₁).app M ≫
        (systemRefinementTheta l E₀ D hl r.rh M hM).hom =
      (systemRefinementTheta l E₀ D hl r.rg
          ((systemCompactificationImage (compactSupportSystemLevel l E₀)
            (compactSupportSystemQuotient l E₀) T₁.cf).obj M)
          (systemCompactificationImage_domain l E₀ D hl T₁.cf M hM)).hom ≫
        (systemCompactificationImage (compactSupportSystemLevel l E₀)
          (compactSupportSystemQuotient l E₀) T₂.cg).map
          (systemRefinementTheta l E₀ D hl r.rf M hM).hom ≫
        (systemTriangleBeta (compactSupportSystemLevel l E₀)
          (compactSupportSystemQuotient l E₀) T₂).app M := by
  sorry

set_option linter.unusedSectionVars false in
/-- Every finite family, including the empty family, has a common compatible triangle.
Source: Stacks 0F7J and 0ATU; proof Step 5
(blueprint: lem-pur-system-compositor-refinement-square).
Proof: forget the two extra Cartesian faces of Triangle.Hom to obtain a
SystemTriangleRefinement, and compose these refinements componentwise. Induct on a
finite set of triangles using Triangle.inf and its two projections. Nagata supplies
Triangle.ofHasCompactification for the empty set. Apply this to the image of the
finite indexed family, which also handles repeated triangles. -/
theorem systemCompatibleTriangles_common (ι : Type v) [Finite ι]
    (T : ι → Compactification.Triangle f g) :
    ∃ S : Compactification.Triangle f g, ∀ a : ι, Nonempty (SystemTriangleRefinement S (T a)) := by
  classical
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian
    (Z ↘ Spec (.of D.k))
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace
    (Z ↘ Spec (.of D.k))
  have : QuasiSeparatedSpace Z := IsLocallyNoetherian.quasiSeparatedSpace
  have fromHom {S T : Compactification.Triangle f g} (r : S.Hom T) :
      SystemTriangleRefinement S T :=
    ⟨r.rf, r.rg, r.rfg, r.q_comm.symm, r.p_comm.symm⟩
  have comp {S T U : Compactification.Triangle f g}
      (r : SystemTriangleRefinement S T) (s : SystemTriangleRefinement T U) :
      SystemTriangleRefinement S U := by
    refine ⟨r.rf.comp s.rf, r.rg.comp s.rg, r.rh.comp s.rh, ?_, ?_⟩
    · change S.q ≫ r.rh.hom ≫ s.rh.hom = (r.rf.hom ≫ s.rf.hom) ≫ U.q
      rw [← Category.assoc, r.b_comm, Category.assoc, s.b_comm, Category.assoc]
    · change (r.rh.hom ≫ s.rh.hom) ≫ U.p = S.p ≫ r.rg.hom ≫ s.rg.hom
      rw [Category.assoc, s.p_comm, ← Category.assoc, r.p_comm, Category.assoc]
  have finiteCommon (s : Finset (Compactification.Triangle f g)) :
      ∃ S : Compactification.Triangle f g,
        ∀ T ∈ s, Nonempty (SystemTriangleRefinement S T) := by
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨Compactification.Triangle.ofHasCompactification f g, by simp⟩
    | @insert T s _ ih =>
      obtain ⟨S, hS⟩ := ih
      refine ⟨S.inf T, ?_⟩
      intro U hU
      rcases Finset.mem_insert.mp hU with hU | hU
      · subst U
        exact ⟨fromHom (S.infSnd T)⟩
      · obtain ⟨r⟩ := hS U hU
        exact ⟨comp (fromHom (S.infFst T)) r⟩
  let := Fintype.ofFinite ι
  obtain ⟨S, hS⟩ := finiteCommon (Finset.univ.image T)
  exact ⟨S, fun a ↦ hS (T a) (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)⟩

/-- The geometric composition word in any three specified compactification choices.
Each supplied leg is an actual proper refinement, and each inverse is the specified mate.
Source: Stacks 0F7J; proof Step 6
(blueprint: lem-pur-system-compositor-refinement-square). -/
def systemCompositorInChoices
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (T : Compactification.Triangle f g)
    (a : T.cf.Refinement c) (b : T.cg.Refinement d) (h : T.cfg.Refinement e)
    (M : Derived (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) X)
    (hM : compatibleCompositorDomain l E₀ X M) :
    (systemCompactificationImage (compactSupportSystemLevel l E₀)
        (compactSupportSystemQuotient l E₀) d).obj
        ((systemCompactificationImage (compactSupportSystemLevel l E₀)
          (compactSupportSystemQuotient l E₀) c).obj M) ⟶
      (systemCompactificationImage (compactSupportSystemLevel l E₀)
        (compactSupportSystemQuotient l E₀) e).obj M :=
  (systemCompactificationImage (compactSupportSystemLevel l E₀)
      (compactSupportSystemQuotient l E₀) d).map
      (systemRefinementTheta l E₀ D hl a M hM).inv ≫
    (systemRefinementTheta l E₀ D hl b
      ((systemCompactificationImage (compactSupportSystemLevel l E₀)
        (compactSupportSystemQuotient l E₀) T.cf).obj M)
      (systemCompactificationImage_domain l E₀ D hl T.cf M hM)).inv ≫
    (systemTriangleBeta (compactSupportSystemLevel l E₀)
      (compactSupportSystemQuotient l E₀) T).app M ≫
    (systemRefinementTheta l E₀ D hl h M hM).hom

set_option linter.unusedSectionVars false in
/-- A compatible common triangle exists also for arbitrary specified choices of f,g,gf.
Source: Stacks 0F7J; proof Steps 5--6
(blueprint: lem-pur-system-compositor-refinement-square).
Proof: densely compactify the proper factor of c followed by the open factor of d.
Properness makes its square with that open Cartesian, giving a triangle with first
two compactifications c and d. The source graph-image construction e.ofComp d
gives another triangle whose total compactification refines e. The binary common
triangle of these two has the required three refinement legs. -/
theorem systemCompositorInChoices_exists
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g)) :
    ∃ T : Compactification.Triangle f g,
      Nonempty (T.cf.Refinement c) ∧ Nonempty (T.cg.Refinement d) ∧
        Nonempty (T.cfg.Refinement e) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian
    (Z ↘ Spec (.of D.k))
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace
    (Z ↘ Spec (.of D.k))
  have : QuasiSeparatedSpace Z := IsLocallyNoetherian.quasiSeparatedSpace
  have : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  have : QuasiSeparatedSpace d.Z := quasiSeparatedSpace_of_quasiSeparated d.g
  obtain ⟨b, hb⟩ := exists_isDense_compactification (c.g ≫ d.i)
  have : IsSchemeTheoreticallyDominant b.i := hb
  have : QuasiCompact b.i := b.quasiCompact_openImmersion inferInstance
  let a : Compactification (f ≫ g) :=
    { Z := b.Z
      i := c.i ≫ b.i
      g := b.g ≫ d.g
      comm := by
        calc
          f ≫ g = (c.i ≫ c.g) ≫ (d.i ≫ d.g) := by rw [← c.comm, ← d.comm]
          _ = c.i ≫ (c.g ≫ d.i) ≫ d.g := by simp only [Category.assoc]
          _ = c.i ≫ (b.i ≫ b.g) ≫ d.g := by rw [← b.comm]
          _ = (c.i ≫ b.i) ≫ (b.g ≫ d.g) := by simp only [Category.assoc]
      isProper := inferInstance
      isOpenImmersion := inferInstance }
  let S : Compactification.Triangle f g :=
    { cf := c
      cg := d
      cfg := a
      q := b.i
      p := b.g
      i_q := rfl
      p_g := rfl
      isPullback := b.isPullback_of_isProper_of_isSchemeTheoreticallyDominant }
  let e' := e.ofComp d
  let T := Compactification.Triangle.ofRestrict d e'
  let k : T.cfg.Refinement e :=
    { hom := (e.ofCompLift d).imageι ≫ pullback.fst e.g d.g
      i_hom := by
        change (e.ofCompLift d).toImage ≫ _ = _
        rw [Scheme.Hom.toImage_imageι_assoc, Compactification.ofCompLift_fst]
      hom_g := by
        change ((e.ofCompLift d).imageι ≫ pullback.fst e.g d.g) ≫ e.g =
          ((e.ofCompLift d).imageι ≫ pullback.snd e.g d.g) ≫ d.g
        simp only [Category.assoc, pullback.condition] }
  exact ⟨S.inf T, ⟨(S.infFst T).rf⟩, ⟨(S.infFst T).rg⟩,
    ⟨(S.infSnd T).rfg.comp k⟩⟩

/-- Conjugating the proper/open word by the exact refinement maps is choice independent.
Source: Stacks 0F7J, final choice-independence argument; proof Step 6
(blueprint: lem-pur-system-compositor-refinement-square).
Proof: choose a common compatible triangle dominating S and T. Apply
systemCompositorRefinementSquare to both projections. The common-refinement
independence of theta identifies the three endpoint comparisons, and cancellation
identifies these conjugates. compatibleCompositorWord is the geometric composition
word by lem-pur-system-compatible-compositor-normalization. Thus this is its
expression in precisely c,d,e, with no unspecified comparison isomorphisms. -/
theorem systemCompositorInChoices_independent
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (S T : Compactification.Triangle f g)
    (a : S.cf.Refinement c) (b : S.cg.Refinement d) (h : S.cfg.Refinement e)
    (a' : T.cf.Refinement c) (b' : T.cg.Refinement d) (h' : T.cfg.Refinement e)
    (M : Derived (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) X)
    (hM : compatibleCompositorDomain l E₀ X M) :
    systemCompositorInChoices l E₀ D hl c d e S a b h M hM =
      systemCompositorInChoices l E₀ D hl c d e T a' b' h' M hM := by
  sorry

end AlgebraicGeometry.ProEtale.SemilinearProperOpen

namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen


variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)

/-- The canonical support evaluation at a retained finite etale-origin witness.
Source: Stacks 099R, 0F7J (blueprint: lem-pur-system-compositor-refinement-square). -/
def systemFiniteTransport {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (n : ℕ) (M : Derived C τ X)
    (w : StrictTower.ScalarEtaleOrigin (C n) X ((compositorLevel C τ X n).obj M)) :=
  compositorSupportTransport C τ c.i c.g n w.Λ w.φ w.origin.L M
    (StrictTower.originIso (C n) w)

/-- The iterated source evaluation, using the same retained origin for both factors.
Source: Stacks 099R, 0F7J (blueprint: lem-pur-system-compositor-refinement-square). -/
def systemFiniteSource {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (c : Compactification f) (d : Compactification g) (n : ℕ) (M : Derived C τ X)
    (w : StrictTower.ScalarEtaleOrigin (C n) X ((compositorLevel C τ X n).obj M)) :=
  compositorFiniteSource C τ c.i c.g d.i d.g n M w

end AlgebraicGeometry.ProEtale.SemilinearProperOpen

namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen


variable (l : ℕ) [Fact l.Prime] (E₀ : Type u) [Field E₀]
  [Algebra (Padic l) E₀] [FiniteDimensional (Padic l) E₀]
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y Z : Scheme.{u}}
  [overX : X.Over (Spec (.of D.k))] [overY : Y.Over (Spec (.of D.k))]
  [overZ : Z.Over (Spec (.of D.k))]
  [ftX : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [qcX : QuasiCompact (X ↘ Spec (.of D.k))] [sepX : IsSeparated (X ↘ Spec (.of D.k))]
  [ftY : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [qcY : QuasiCompact (Y ↘ Spec (.of D.k))] [sepY : IsSeparated (Y ↘ Spec (.of D.k))]
  [ftZ : LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
  [qcZ : QuasiCompact (Z ↘ Spec (.of D.k))] [sepZ : IsSeparated (Z ↘ Spec (.of D.k))]
  {f : X ⟶ Y} {g : Y ⟶ Z}
  [overF : f.IsOver (Spec (.of D.k))] [overG : g.IsOver (Spec (.of D.k))]
  [sepF : IsSeparated f] [ftF : LocallyOfFiniteType f] [qcF : QuasiCompact f]
  [sepG : IsSeparated g] [ftG : LocallyOfFiniteType g] [qcG : QuasiCompact g]

include D hl overX overY ftX qcX sepX ftY qcY sepY overF sepF ftF qcF

/-- Evaluation gives the specified finite refinement, including its actual proper/open word.
Source: Stacks 0F7I, 0F7J; proof Step 7
(blueprint: lem-pur-system-compositor-refinement-square).
Proof: evaluate systemRefinementCompositor and systemRefinementGamma by
lem-coef-semilinear-derived-sections and the finite-normalization clause of
lem-sf-semilinear-proper-open-mate-pasting. Evaluation preserves inverses. The
normalized finite proper/open refinement is precisely the inverse of the named
etale refinement isomorphism, transported by systemFiniteTransport; its site
comparison is def-sf-refinement-comparison-isomorphism. Constructible-origin supplies
the retained witness with the actual quotient ring and identity scalar map. -/
theorem systemRefinementTheta_evaluation {c₁ c₂ : Compactification f}
    (r : c₁.Refinement c₂)
    (M : Derived (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) X)
    (hM : compatibleCompositorDomain l E₀ X M) (n : ℕ) :
    ∃ w : StrictTower.ScalarEtaleOrigin (compactSupportSystemLevel l E₀ n) X
      ((compositorLevel (compactSupportSystemLevel l E₀)
        (compactSupportSystemQuotient l E₀) X n).obj M),
      w.Λ = (compactSupportSystemLevel l E₀ n : Type (u + 1)) ∧
      HEq w.φ (RingHom.id (compactSupportSystemLevel l E₀ n)) ∧
      (systemFiniteTransport (compactSupportSystemLevel l E₀)
          (compactSupportSystemQuotient l E₀) c₁ n M w).hom ≫
          (compositorLevel (compactSupportSystemLevel l E₀)
            (compactSupportSystemQuotient l E₀) Y n).map
            (systemRefinementTheta l E₀ D hl r M hM).hom =
        (StrictTower.HD (compactSupportSystemLevel l E₀ n) Y w.Λ w.φ).map
          ((Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso w.Λ r).inv.app
            w.origin.L) ≫
          (systemFiniteTransport (compactSupportSystemLevel l E₀)
            (compactSupportSystemQuotient l E₀) c₂ n M w).hom := by
  sorry

include overZ ftZ qcZ sepZ overG sepG ftG qcG

/-- In any specified choices, evaluation is the finite composition of thm-sf-comp-composition.
Together with systemRefinementTheta_evaluation this sends the refinement square to its
specified finite square. The equation in systems is established first.
Source: Stacks 0F7J; proof Steps 6--7
(blueprint: lem-pur-system-compositor-refinement-square).
Proof: choose the retained bounded constructible origin at each level. Evaluation
of the triangle word is the canonical finite compositor by
lem-pur-system-compatible-compositor-normalization. Apply
systemRefinementTheta_evaluation to each of the three conjugating legs. Naturality
of the two support transports cancels their inverse pairs. Finite refinement
coherence identifies the result with coherenceEtaleCompositor in exactly c,d,e,
which the canonical origin compositor of thm-sf-comp-composition realizes. Functors
preserve the already proved square, all inverse pairs, and the span cocycle.
Thus the finite equation uses precisely these finite maps, with no common bound
and without using evaluation to detect an equality of system morphisms. -/
theorem systemCompositorInChoices_evaluation
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (T : Compactification.Triangle f g)
    (a : T.cf.Refinement c) (b : T.cg.Refinement d) (h : T.cfg.Refinement e)
    (M : Derived (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) X)
    (hM : compatibleCompositorDomain l E₀ X M) (n : ℕ) :
    ∃ w : StrictTower.ScalarEtaleOrigin (compactSupportSystemLevel l E₀ n) X
      ((compositorLevel (compactSupportSystemLevel l E₀)
        (compactSupportSystemQuotient l E₀) X n).obj M),
      w.Λ = (compactSupportSystemLevel l E₀ n : Type (u + 1)) ∧
      HEq w.φ (RingHom.id (compactSupportSystemLevel l E₀ n)) ∧
      (systemFiniteSource (compactSupportSystemLevel l E₀)
          (compactSupportSystemQuotient l E₀) c d n M w).hom ≫
          (compositorLevel (compactSupportSystemLevel l E₀)
            (compactSupportSystemQuotient l E₀) Z n).map
            (systemCompositorInChoices l E₀ D hl c d e T a b h M hM) =
        (StrictTower.HD (compactSupportSystemLevel l E₀ n) Z w.Λ w.φ).map
          ((coherenceEtaleCompositor w.Λ c d e).hom.app w.origin.L) ≫
          (systemFiniteTransport (compactSupportSystemLevel l E₀)
            (compactSupportSystemQuotient l E₀) e n M w).hom := by
  sorry

end AlgebraicGeometry.ProEtale.SemilinearProperOpen
