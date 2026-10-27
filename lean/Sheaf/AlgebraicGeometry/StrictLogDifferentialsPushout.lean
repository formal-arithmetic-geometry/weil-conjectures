/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleDifferentialPullbackPresentation
public import Sheaf.AlgebraicGeometry.LogMorphismOperations
public import Sheaf.AlgebraicGeometry.LogInfinitesimalLifting
public import Sheaf.AlgebraicGeometry.IntegralChartLogificationThickening
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Sheaf.AlgebraicGeometry.LogDifferentialCanonicalSquare
import Sheaf.AlgebraicGeometry.StrictLogSymbolExtension

/-!
# Logarithmic differentials under a strict morphism

Source: the DAG's agent-formulated symbol-presentation lemma, using ILO VI 1.1,
printed p.69, for the strict comparison of X 1.2, p.138, and XVI 3.6.3, p.252.
ILO does not state the pushout formula verbatim.
(blueprint: lem-per-strict-log-differentials-pushout).

The logarithmic differential sheaves are the existing sheafified symbol quotients.
Ordinary differential and tensor-pullback presentations below are asserted to exist,
with their full normalized universal properties; they are not extra hypotheses.
The cokernel of `(u,-v)` is the quotient by its image in the abelian module category.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The actual cokernel `(B ⊕ C)/im(u,-v)`. A binary coproduct in this abelian
category is the direct sum, and the difference of the two inclusions is `(u,-v)`.
Source: the strict-pushout lemma; Stacks 03DA
(blueprint: lem-per-strict-log-differentials-pushout). -/
noncomputable def strictLogDifferentialQuotient {X : Scheme.{u}}
    {A B C : DifferentialEtaleModules X} (u : A ⟶ B) (v : A ⟶ C) :
    DifferentialEtaleModules X :=
  cokernel (u ≫ (coprod.inl : B ⟶ B ⨿ C) - v ≫ coprod.inr)

/-- The first quotient inclusion `b ↦ [(b,0)]`.
Source: the strict-pushout lemma; Stacks 03DA
(blueprint: lem-per-strict-log-differentials-pushout). -/
noncomputable def strictLogDifferentialInl {X : Scheme.{u}}
    {A B C : DifferentialEtaleModules X} (u : A ⟶ B) (v : A ⟶ C) :
    B ⟶ strictLogDifferentialQuotient u v :=
  coprod.inl ≫ cokernel.π (u ≫ (coprod.inl : B ⟶ B ⨿ C) - v ≫ coprod.inr)

/-- The second quotient inclusion `e ↦ [(0,e)]`.
Source: the strict-pushout lemma; Stacks 03DA
(blueprint: lem-per-strict-log-differentials-pushout). -/
noncomputable def strictLogDifferentialInr {X : Scheme.{u}}
    {A B C : DifferentialEtaleModules X} (u : A ⟶ B) (v : A ⟶ C) :
    C ⟶ strictLogDifferentialQuotient u v :=
  coprod.inr ≫ cokernel.π (u ≫ (coprod.inl : B ⟶ B ⨿ C) - v ≫ coprod.inr)

private theorem ordinary_hom_ext {X S : Scheme.{u}} {f : X ⟶ S}
    (Ω : EtaleOrdinaryDifferentialPresentation f) {T : DifferentialEtaleModules X}
    {a b : Ω.module ⟶ T}
    (h : ∀ (V : X.Etale) (x : Γ(V.left, ⊤)),
      a.val.app (op V) (Ω.derivation.d (X := op V) x) =
        b.val.app (op V) (Ω.derivation.d (X := op V) x)) : a = b := by
  obtain ⟨z, _, hz⟩ := Ω.universal T (Ω.derivation.postcomp a.val)
  exact (hz a (fun _ _ ↦ rfl)).trans (hz b (fun V x ↦ (h V x).symm)).symm

private theorem quotient_pushout {X : Scheme.{u}}
    {A B C : DifferentialEtaleModules X} (u : A ⟶ B) (v : A ⟶ C) :
    IsPushout u v (strictLogDifferentialInl u v) (strictLogDifferentialInr u v) := by
  let d := u ≫ (coprod.inl : B ⟶ B ⨿ C) - v ≫ coprod.inr
  have hw : u ≫ strictLogDifferentialInl u v = v ≫ strictLogDifferentialInr u v := by
    apply sub_eq_zero.mp
    simpa only [d, strictLogDifferentialInl, strictLogDifferentialInr,
      ← Category.assoc, ← Preadditive.sub_comp] using cokernel.condition d
  apply IsPushout.mk' hw
  · intro T a b ha hb
    apply (cancel_epi (cokernel.π d)).1
    apply coprod.hom_ext
    · simpa only [strictLogDifferentialInl, d, Category.assoc] using ha
    · simpa only [strictLogDifferentialInr, d, Category.assoc] using hb
  · intro T a b hab
    have hz : d ≫ coprod.desc a b = 0 := by
      simp only [d, Preadditive.sub_comp, Category.assoc, coprod.inl_desc,
        coprod.inr_desc, hab, sub_self]
    refine ⟨cokernel.desc d (coprod.desc a b) hz, ?_, ?_⟩
    · simp [strictLogDifferentialInl, Category.assoc, d]
    · simp [strictLogDifferentialInr, Category.assoc, d]

/-- Strict logarithmic pullback gives the pushout of ordinary and logarithmic
relative differential sheaves, with its canonical map and all three inverse formulas.
The presentation structures specify the existing ordinary differential sheaves and
actual tensor inverse images up to their unique normalized isomorphisms.

Source: agent-formulated lemma for ILO X 1.2, p.138, and XVI 3.6.3, p.252;
associated-log convention ILO VI 1.1, p.69.
(blueprint: lem-per-strict-log-differentials-pushout).

Proof, following the nine steps of the DAG:
1. Set H=c⁻¹M and beta=c-sharp alpha. Form the monoid presheaf quotient of
   H times O_Z-units by (he,t)=(h,beta(e)t) when beta(e) is a unit, and sheafify
   in commutative monoids (lem-trf-commutative-monoid-sheafification).
2. Local representatives in sheafification give the log axiom and the associated-log
   universal property. Strictness identifies this sheaf with L. Thus sections of L
   are locally c-flat(m)t, with precisely the generated unit relations followed by
   sheafification (lem-weil-pbc-site-sheafification-sections-local and the logification
   convention of lem-per-integral-chart-logification-thickening).
3. Ordinary universal derivations and the symbol maps give j and iota. They agree on
   A by their values on 1 tensor da. The cokernel universal property gives Phi;
   use def-sc-relative-differential-sheaf, def-weil-pbc-kahler-differentials,
   def-pur-sheaf-tensor-product and def-weil-sheaf-of-modules-category.
4. In P put D(a)=q_B(da) and ell(m)=q_C(1 tensor dlog m). The quotient relation
   gives D(beta(m))=beta(m) ell(m). Both maps kill the corresponding base symbols.
5. For a unit t put lambda(t)=t⁻¹D(t). Leibniz makes lambda multiplicative-to-additive.
   If beta(e) is a unit, ell(e)=lambda(beta(e)), so ell(m)+lambda(t) respects every
   generating unit relation, not merely a selected expression.
6. Extend through monoid sheafification to ell_L(c-flat(m)t)=ell(m)+lambda(t).
   Local equality of representatives and the sheaf axiom show independence of all
   expressions, including equalities arising after sheafification; restrictions agree.
7. Compute D(beta(m)t)=t beta(m)ell(m)+beta(m)D(t)=alpha(l)ell_L(l).
   All log relations, including annihilation of N, are satisfied. Hence the actual
   symbol quotient gives Psi with the three displayed formulas.
8. Phi Psi fixes da and dlog(c-flat(m)t); Psi Phi fixes q_B(da) and both types of
   q_C generators, using q_B u=q_C v. Generation and the two sheafification
   universal properties prove that both composites are identities.
9. A pair of maps from B,C agreeing on A kills (u,-v), so factors uniquely through
   its cokernel. This is the pushout property, transported along Phi. No smoothness,
   flatness, finite presentation, saturation or Noetherian hypothesis was used. -/
theorem strictLogDifferentials_pushout {Z W S : Scheme.{u}}
    {L : EtaleLogStructure Z} {M : EtaleLogStructure W} {N : EtaleLogStructure S}
    (c : EtaleLogMap L M) (g : EtaleLogMap M N)
    (hL : L.IsFine) (hM : M.IsFine) (hN : N.IsFine) (hc : c.IsStrict) :
    ∃ (ΩW : EtaleOrdinaryDifferentialPresentation g.base)
      (ΩZ : EtaleOrdinaryDifferentialPresentation (c.base ≫ g.base))
      (A : EtaleDifferentialPullbackPresentation c.base ΩW.module)
      (C : EtaleDifferentialPullbackPresentation c.base g.differentialSheaf)
      (u : A.module ⟶ ΩZ.module) (v : A.module ⟶ C.module)
      (j : ΩZ.module ⟶ (c.comp g).differentialSheaf)
      (iota : C.module ⟶ (c.comp g).differentialSheaf)
      (Φ : strictLogDifferentialQuotient u v ≅ (c.comp g).differentialSheaf),
      (∀ (U : W.Etale) (V : Z.Etale) (k : V.left ⟶ U.left)
        (hk : k ≫ U.hom = V.hom ≫ c.base) (a : Γ(U.left, ⊤)),
        u.val.app (op V) (A.unit.app U V k hk (ΩW.derivation.d (X := op U) a)) =
          ΩZ.derivation.d (X := op V) (k.appTop a)) ∧
      (∀ (U : W.Etale) (V : Z.Etale) (k : V.left ⟶ U.left)
        (hk : k ≫ U.hom = V.hom ≫ c.base) (a : Γ(U.left, ⊤)),
        v.val.app (op V) (A.unit.app U V k hk (ΩW.derivation.d (X := op U) a)) =
          C.unit.app U V k hk (g.sheafD U a)) ∧
      (∀ (V : Z.Etale) (a : Γ(V.left, ⊤)),
        j.val.app (op V) (ΩZ.derivation.d (X := op V) a) = (c.comp g).sheafD V a) ∧
      (∀ (U : W.Etale) (V : Z.Etale) (k : V.left ⟶ U.left)
        (hk : k ≫ U.hom = V.hom ≫ c.base) (a : Γ(U.left, ⊤)),
        iota.val.app (op V) (C.unit.app U V k hk (g.sheafD U a)) =
          (c.comp g).sheafD V (k.appTop a)) ∧
      (∀ (U : W.Etale) (V : Z.Etale) (k : V.left ⟶ U.left)
        (hk : k ≫ U.hom = V.hom ≫ c.base) (m : M.monoidSheaf.obj.obj (op U)),
        iota.val.app (op V) (C.unit.app U V k hk (g.sheafDLog U m)) =
          (c.comp g).sheafDLog V (c.sectionMap U V k hk m)) ∧
      strictLogDifferentialInl u v ≫ Φ.hom = j ∧
      strictLogDifferentialInr u v ≫ Φ.hom = iota ∧
      IsPushout u v j iota ∧
      (∀ (V : Z.Etale) (a : Γ(V.left, ⊤)),
        Φ.inv.val.app (op V) ((c.comp g).sheafD V a) =
          (strictLogDifferentialInl u v).val.app (op V)
            (ΩZ.derivation.d (X := op V) a)) ∧
      (∀ (U : W.Etale) (V : Z.Etale) (k : V.left ⟶ U.left)
        (hk : k ≫ U.hom = V.hom ≫ c.base) (m : M.monoidSheaf.obj.obj (op U)),
        Φ.inv.val.app (op V) ((c.comp g).sheafDLog V (c.sectionMap U V k hk m)) =
          (strictLogDifferentialInr u v).val.app (op V)
            (C.unit.app U V k hk (g.sheafDLog U m))) ∧
      (∀ (V : Z.Etale) (t : Γ(V.left, ⊤)ˣ)
        (l : L.monoidSheaf.obj.obj (op V)), L.alpha.app (op V) l = t.val →
          Φ.inv.val.app (op V) ((c.comp g).sheafDLog V l) =
            (strictLogDifferentialInl u v).val.app (op V)
              ((↑(t⁻¹) : Γ(V.left, ⊤)) • ΩZ.derivation.d (X := op V) t.val)) := by
  obtain ⟨ΩW, ΩZ, A, C, u, v, j, iota, hu, hv, hj, hiD, hiL, hw, hCext⟩ :=
    logDifferential_canonical_square c g
  let qB := strictLogDifferentialInl u v
  let qC := strictLogDifferentialInr u v
  have hQ : IsPushout u v qB qC := quotient_pushout u v
  let φ := hQ.desc j iota hw
  have hBφ : qB ≫ φ = j := hQ.inl_desc j iota hw
  have hCφ : qC ≫ φ = iota := hQ.inr_desc j iota hw
  obtain ⟨ψ, hψD, hψL, hψunit, _⟩ :=
    strictLog_symbol_extension c g hL hM hN hc ΩW ΩZ A C u v hu hv
      (strictLogDifferentialQuotient u v) qB qC hQ.w
  have hjψ : j ≫ ψ = qB := by
    apply ordinary_hom_ext ΩZ
    intro V a
    change ψ.val.app (op V) (j.val.app (op V) _) = _
    rw [hj, hψD]
  have hiψ : iota ≫ ψ = qC := by
    apply hCext
    · intro U V k hk a
      change ψ.val.app (op V) (iota.val.app (op V) _) = _
      rw [hiD, hψD]
      have e := congrArg (fun f : A.module ⟶ strictLogDifferentialQuotient u v ↦
        f.val.app (op V) (A.unit.app U V k hk (ΩW.derivation.d (X := op U) a))) hQ.w
      change qB.val.app (op V) (u.val.app (op V) _) =
        qC.val.app (op V) (v.val.app (op V) _) at e
      rwa [hu, hv] at e
    · intro U V k hk m
      change ψ.val.app (op V) (iota.val.app (op V) _) = _
      rw [hiL, hψL]
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    apply hQ.hom_ext
    · rw [← Category.assoc, hBφ, hjψ, Category.comp_id]
    · rw [← Category.assoc, hCφ, hiψ, Category.comp_id]
  obtain ⟨χ, _, _, _, hχuniq⟩ :=
    strictLog_symbol_extension c g hL hM hN hc ΩW ΩZ A C u v hu hv
      (c.comp g).differentialSheaf j iota hw
  have hid : 𝟙 (c.comp g).differentialSheaf = χ := by
    apply hχuniq
    · intro V a
      exact (hj V a).symm
    · intro U V k hk m
      exact (hiL U V k hk m).symm
  have hψφ : ψ ≫ φ = 𝟙 _ := by
    apply Eq.trans _ hid.symm
    apply hχuniq
    · intro V a
      change φ.val.app (op V) (ψ.val.app (op V) _) = _
      rw [hψD]
      exact congrArg (fun f : ΩZ.module ⟶ (c.comp g).differentialSheaf ↦
        f.val.app (op V) (ΩZ.derivation.d (X := op V) a)) hBφ
    · intro U V k hk m
      change φ.val.app (op V) (ψ.val.app (op V) _) = _
      rw [hψL]
      exact congrArg (fun f : C.module ⟶ (c.comp g).differentialSheaf ↦
        f.val.app (op V) (C.unit.app U V k hk (g.sheafDLog U m))) hCφ
  let Φ : strictLogDifferentialQuotient u v ≅ (c.comp g).differentialSheaf :=
    ⟨φ, ψ, hφψ, hψφ⟩
  have hP : IsPushout u v j iota := by
    exact hQ.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) Φ
      (by simp) (by simp) (by simpa using hBφ) (by simpa using hCφ)
  exact ⟨ΩW, ΩZ, A, C, u, v, j, iota, Φ, hu, hv, hj, hiD, hiL,
    hBφ, hCφ, hP, hψD, hψL, hψunit⟩

end AlgebraicGeometry
