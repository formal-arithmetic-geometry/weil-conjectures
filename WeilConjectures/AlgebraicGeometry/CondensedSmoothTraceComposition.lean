/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedSmoothTrace
public import WeilConjectures.SixFunctors.CondensedCompactSupportCompositionData
import WeilConjectures.AlgebraicGeometry.SmoothPurityComposition

/-! # Transitivity of the smooth trace

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-trace-composition/_section.md, displayed three-arrow composite
(blueprint: sk-prop-sp-trace-composition).

The source comparison is the recorded pullback/Tate/even-shift comparison. The support
comparison is the inverse of the normalized compact-support compositor. Equality is
written after the faithful full inclusion of Dctf into the native derived category.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

attribute [local irreducible] DerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

namespace AlgebraicGeometry.ProEtale.PurityTransport

variable (ell : ℕ) [Fact ell.Prime]
variable (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
variable (c : Coefficient ell) (s : SmoothDatum D)
variable (Z : Over (Spec (.of D.k)))
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
variable (g : s.Y.left ⟶ Z.left) [g.IsOver (Spec (.of D.k))]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
variable (e : ℕ) [SmoothOfRelativeDimension e g]
variable (cg : Compactification g) (ch : Compactification (s.map ≫ g))

/-- The second smooth map with its specified compactification, in the existing
geometric index type. Source: the composable pair in the trace-transitivity statement
(blueprint: sk-prop-sp-trace-composition). -/
def smoothTraceSuccessor : SmoothDatum D :=
  { X := s.Y, Y := Z, map := g, dim := e, compactification := cg }

/-- The composite smooth map has relative dimension d+e, with any specified
compactification. Source: the composite in the trace-transitivity statement
(blueprint: sk-prop-sp-trace-composition). -/
def smoothTraceComposite : SmoothDatum D :=
  { X := s.X, Y := Z, map := s.map ≫ g, dim := s.dim + e, compactification := ch }

/-- Specialize the recorded source comparison to the finite-field domain. Invertibility
of ell follows from the base-field unit; it is not an additional hypothesis.
The supplied Tate coordinates satisfy the existing root-projection normalization.
Source: the first isomorphism in the trace-transitivity statement
(blueprint: sk-prop-sp-trace-composition). -/
def smoothTraceSourceComp (p : LinePullCoordinates ell c s.map) (K : c.derived ell Z.left) :
    (c.smoothSource ell (s.map ≫ g) (s.dim + e)).obj K ≅
      (c.smoothSource ell s.map s.dim).obj ((c.smoothSource ell g e).obj K) :=
  letI : ∀ x : s.X.left, Invertible (ell : s.X.left.residueField x) :=
    fun x ↦ (by
      simpa using (primeUnit D ell hEll).map
        ((s.X.left ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
          IsUnit (ell : s.X.left.residueField x)).invertible
  sourceComp ell c s.map g s.dim e p K

/-- The inverse normalized compact-support compositor, evaluated on the smooth source.
It is the compositor of the recorded coherent system, including its proper/open and
refinement normalization laws. Source: the initial isomorphism, compact-support factor
(blueprint: sk-prop-sp-trace-composition). -/
def smoothTraceSupportComp
    (H : CondensedRing.CompactSupportComposition.CoherentData (c.obj.{u} ell) D.k)
    (K : c.ctf ell Z.left) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) ch).obj
        ((c.smoothSource ell (s.map ≫ g) (s.dim + e)).obj K.obj) ≅
      (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) cg).obj
        ((CondensedRing.rightDerivedLowerShriekOfCompactification
          (c.obj ell) s.compactification).obj
            ((c.smoothSource ell (s.map ≫ g) (s.dim + e)).obj K.obj)) :=
  ((H.comp
    (SepFinType.homMk (Over.homMk s.map (comp_over s.map (Spec (.of D.k)))))
    (SepFinType.homMk (Over.homMk g (comp_over g (Spec (.of D.k)))))
    s.compactification cg ch).app
      ((inclusion ell c s.X.left).obj
        ((source ell c (s.map ≫ g) (s.dim + e)
          (WeilConjectures.PurityWeil.Condensed.normalizedFamily ell D hEll c
            (smoothTraceComposite D s Z g e ch)).source_closed).obj K))).symm

set_option maxHeartbeats 6400000 in
-- Comparing the restricted functors with their ambient maps needs many definitional reductions.
/-- Transitivity of the specified smooth trace for every admissible coefficient and
finite-Tor constructible K. The equality is viewed in the ambient derived category
through the fully faithful inclusion, so it is exactly the equality in Dctf.
Source: latest blueprint sk-prop-sp-trace-composition/_section.md, full display
(blueprint: sk-prop-sp-trace-composition).

Proof plan, following the three DAG steps:
1. Write F_a=Ra_!, G_a=a^!, J_a=a^*(-)(m_a)[2m_a], h=gf, and L=J_g K.
Apply sk-prop-sp-composition to obtain its source comparison w and compositor v.
The uniqueness clause of integralComparison and the normalization fields of
def-pur-transport-line-pullback identify its coordinates with p, so w is the
source comparison of the statement. The initial comparison is alpha inverse
followed by F_g F_f of w.
2. Expand both traces as F_a(gamma_a) followed by epsilon_a (sk-def-sp-trace).
Naturality of the restricted counit epsilon_f and of gamma_f at gamma_g(K) and
functoriality give E_K followed, in composition order, by F_g F_f(U_K w_K),
where U_K is gamma_f(G_g K) after J_f(gamma_g K) and
E_K is F_g(epsilon_f(G_g K)) followed by epsilon_g(K).
3. Use sk-prop-sp-composition to replace U_K s_K by gamma_h followed by the
counit-preserving exceptional compositor. Naturality of alpha inverse moves gamma_h
outside the support comparison. The specified composite-counit equation leaves
F_h(gamma_h) followed by epsilon_h, which is Tr_h by sk-def-sp-trace. -/
theorem smoothTrace_composition
    (H : CondensedRing.CompactSupportComposition.CoherentData (c.obj.{u} ell) D.k)
    (p : LinePullCoordinates ell c s.map)
    (Rf : CondensedRing.ScalarExceptionalAdjoint (c.bundled.{u} ell) s.compactification)
    (Rg : CondensedRing.ScalarExceptionalAdjoint (c.bundled.{u} ell) cg)
    (Rh : CondensedRing.ScalarExceptionalAdjoint (c.bundled.{u} ell) ch)
    (K : c.ctf ell Z.left) :
    (smoothTrace ell D hEll c (smoothTraceComposite D s Z g e ch) Rh K).hom =
      (smoothTraceSupportComp ell D hEll c s Z g e cg ch H K).hom ≫
        (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) cg).map
          ((CondensedRing.rightDerivedLowerShriekOfCompactification
            (c.obj ell) s.compactification).map
              (smoothTraceSourceComp ell D hEll c s Z g e p K.obj).hom) ≫
        (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) cg).map
          (smoothTrace ell D hEll c s Rf
            ((source ell c g e
              (WeilConjectures.PurityWeil.Condensed.normalizedFamily ell D hEll c
                (smoothTraceSuccessor D s Z g e cg)).source_closed).obj K)).hom ≫
        (smoothTrace ell D hEll c (smoothTraceSuccessor D s Z g e cg) Rg K).hom := by
  let : ∀ x : s.X.left, Invertible (ell : s.X.left.residueField x) :=
    fun x ↦ (by
      simpa using (primeUnit D ell hEll).map
        ((s.X.left ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
          IsUnit (ell : s.X.left.residueField x)).invertible
  let : ∀ y : s.Y.left, Invertible (ell : s.Y.left.residueField y) :=
    fun y ↦ (by
      simpa using (primeUnit D ell hEll).map
        ((s.Y.left ↘ Spec (.of D.k)).residueFieldAlgebraMap y) :
          IsUnit (ell : s.Y.left.residueField y)).invertible
  obtain ⟨q, v, hv, _, w, hw, hγ⟩ :=
    smoothPurity_composition ell D hEll c s Z g e cg ch H Rf Rg Rh
  have hp : p = q := by
    cases p with
    | mk ip hip fp hfp pp hpp =>
      cases q with
      | mk iq hiq fq hfq pq hpq =>
        have hi : ip = iq := (integralComparison ell s.map).unique hip hiq
        subst iq
        have hf : fp = fq := eq_of_heq (hfp.trans hfq.symm)
        subst fq
        have hpow : pp = pq := funext fun d ↦ eq_of_heq ((hpp d).trans (hpq d).symm)
        subst pq
        rfl
  subst q
  let t := spCompositionSecond D s Z g e cg
  let r := spCompositionTotal D s Z g e ch
  let Jg := spCompositionSource ell D hEll c t
  let γf := WeilConjectures.PurityWeil.Condensed.canonicalPurity ell D hEll c s Rf
  let γg := WeilConjectures.PurityWeil.Condensed.canonicalPurity ell D hEll c t Rg
  let γh := WeilConjectures.PurityWeil.Condensed.canonicalPurity ell D hEll c r Rh
  have hγK : γh.hom.app K ≫ v.hom.app K =
      w.hom.app K ≫ (spCompositionSource ell D hEll c s).map (γg.hom.app K) ≫
        γf.hom.app (Rg.upper.obj K) := hγ K
  have htrace :
      Rg.lower.map (Rf.lower.map (w.hom.app K)) ≫
          Rg.lower.map (smoothTrace ell D hEll c s Rf (Jg.obj K)) ≫
          smoothTrace ell D hEll c t Rg K =
        Rg.lower.map (Rf.lower.map (γh.hom.app K ≫ v.hom.app K)) ≫
          Rg.lower.map (Rf.restrictedAdjunction.counit.app (Rg.upper.obj K)) ≫
          Rg.restrictedAdjunction.counit.app K := by
    have he := Rf.restrictedAdjunction.counit.naturality (γg.hom.app K)
    simp only [Functor.comp_map, Functor.id_map] at he
    have hcalc : Rf.lower.map (w.hom.app K) ≫
          smoothTrace ell D hEll c s Rf (Jg.obj K) ≫ γg.hom.app K =
        Rf.lower.map (γh.hom.app K ≫ v.hom.app K) ≫
          Rf.restrictedAdjunction.counit.app (Rg.upper.obj K) := by
      change Rf.lower.map (w.hom.app K) ≫
          (Rf.lower.map (γf.hom.app (Jg.obj K)) ≫
            Rf.restrictedAdjunction.counit.app (Jg.obj K)) ≫ γg.hom.app K = _
      simp only [Category.assoc]
      rw [← he]
      rw [← Rf.lower.map_comp_assoc (γf.hom.app (Jg.obj K))
        (Rf.upper.map (γg.hom.app K))
        (Rf.restrictedAdjunction.counit.app (Rg.upper.obj K)),
        ← γf.hom.naturality (γg.hom.app K)]
      rw [← Rf.lower.map_comp_assoc]
      exact congrArg (fun z ↦ Rf.lower.map z ≫
        Rf.restrictedAdjunction.counit.app (Rg.upper.obj K)) hγK.symm
    simpa only [smoothTrace, Functor.map_comp, Category.assoc] using
      congrArg (fun z ↦ Rg.lower.map z ≫ Rg.restrictedAdjunction.counit.app K) hcalc
  have hc := hv K
  have hs := hw K
  have ht := congrArg (fun z ↦ z.hom) htrace
  let Ff := CondensedRing.rightDerivedLowerShriekOfCompactification
    (c.obj ell) s.compactification
  let Fg := CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) cg
  let Fh := CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) ch
  let α := H.comp
    (SepFinType.homMk (Over.homMk s.map (comp_over s.map (Spec (.of D.k)))))
    (SepFinType.homMk (Over.homMk g (comp_over g (Spec (.of D.k)))))
    s.compactification cg ch
  let M := (inclusion ell c s.X.left).obj
    ((spCompositionSource ell D hEll c r).obj K)
  let N := (inclusion ell c s.X.left).obj (Rh.upper.obj K)
  have hn := α.inv.naturality ((inclusion ell c s.X.left).map (γh.hom.app K))
  change Fh.map (γh.hom.app K).hom ≫ (α.app N).inv =
    (α.app M).inv ≫ Fg.map (Ff.map (γh.hom.app K).hom) at hn
  unfold WeilConjectures.PurityWeil.Condensed.supportComposition at hc
  have hc' := (α.app N).eq_inv_comp.mpr hc
  change (w.hom.app K).hom =
    (smoothTraceSourceComp ell D hEll c s Z g e p K.obj).hom at hs
  change Fg.map (Ff.map (w.hom.app K).hom) ≫
        Fg.map (smoothTrace ell D hEll c s Rf (Jg.obj K)).hom ≫
        (smoothTrace ell D hEll c t Rg K).hom =
      Fg.map (Ff.map ((γh.hom.app K).hom ≫ (v.hom.app K).hom)) ≫
        Fg.map (Rf.restrictedAdjunction.counit.app (Rg.upper.obj K)).hom ≫
        (Rg.restrictedAdjunction.counit.app K).hom at ht
  change Fh.map (γh.hom.app K).hom ≫
      (Rh.restrictedAdjunction.counit.app K).hom =
    (α.app M).inv ≫
      Fg.map (Ff.map (smoothTraceSourceComp ell D hEll c s Z g e p K.obj).hom) ≫
      Fg.map (smoothTrace ell D hEll c s Rf (Jg.obj K)).hom ≫
      (smoothTrace ell D hEll c t Rg K).hom
  rw [← hs, ht, hc']
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rfl

end AlgebraicGeometry.ProEtale.PurityTransport
