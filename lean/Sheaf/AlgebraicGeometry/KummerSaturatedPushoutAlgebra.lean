/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.LogIdealChartPresentation
public import Sheaf.AlgebraicGeometry.IntegralChartLogificationThickening
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.AssociatedLogArbitraryScheme
import Sheaf.GroupTheory.FineMonoidFiniteSaturation
import Sheaf.TraceFormula.FsFaceSharpening
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Category.Grp.Injective

/-!
# Saturated Kummer pushouts and their monoid algebras

Source: ILO VI 2.1--2.2, pp.71--72; VIII 3.3.5--3.3.11, pp.107--108;
X 1.8, pp.146--147, with the explicit algebraic and arbitrary-scheme refinements
of the DAG (blueprint: lem-per-kummer-saturated-pushout-algebra).

Monoids use multiplicative notation: positive multiples are positive powers.
The quotient and the positive-root subset are actual constructions. The tensor
predicate uses the actual monoid algebras and tensor products, in independent universes.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

namespace KummerPushout

variable {P Q R : Type u} [CommMonoid P] [CommMonoid Q] [CommMonoid R]

/-- The defining congruence of the ordinary commutative monoid pushout.
Source: ILO VI 2.1--2.2, algebraic chart formulation
(blueprint: lem-per-kummer-saturated-pushout-algebra). -/
def relation (h : P →* Q) (a : P →* R) : Con (Q × R) :=
  conGen (fun x y ↦ ∃ p : P, x = (h p, 1) ∧ y = (1, a p))

/-- The ordinary pushout `S₀`, before integralization.
Source: ILO VI 2.1--2.2, algebraic chart formulation
(blueprint: lem-per-kummer-saturated-pushout-algebra). -/
abbrev Raw (h : P →* Q) (a : P →* R) := (relation h a).Quotient

/-- The `Q` leg of the quotient pushout. Source: ILO VI 2.1--2.2
(blueprint: lem-per-kummer-saturated-pushout-algebra). -/
def rawLeft (h : P →* Q) (a : P →* R) : Q →* Raw h a :=
  (relation h a).mk'.comp (MonoidHom.inl Q R)

/-- The `R` leg of the quotient pushout. Source: ILO VI 2.1--2.2
(blueprint: lem-per-kummer-saturated-pushout-algebra). -/
def rawRight (h : P →* Q) (a : P →* R) : R →* Raw h a :=
  (relation h a).mk'.comp (MonoidHom.inr Q R)

/-- Integralization is the image in the actual group completion.
Source: ILO VIII 3.1.17, p.101
(blueprint: lem-per-kummer-saturated-pushout-algebra). -/
noncomputable def integralization (h : P →* Q) (a : P →* R) :
    Submonoid (Algebra.GrothendieckGroup (Raw h a)) :=
  MonoidHom.mrange (Algebra.GrothendieckGroup.of (M := Raw h a))

/-- The positive-root subset of the group completion, with its inherited monoid law.
Source: ILO VIII 3.1.17, p.101; VI 2.1--2.2
(blueprint: lem-per-kummer-saturated-pushout-algebra). -/
noncomputable def saturation (h : P →* Q) (a : P →* R) :
    Submonoid (Algebra.GrothendieckGroup (Raw h a)) where
  carrier := {g | ∃ m : ℕ, 0 < m ∧ g ^ m ∈ integralization h a}
  one_mem' := ⟨1, Nat.zero_lt_one, by simp [integralization]⟩
  mul_mem' := by
    rintro x y ⟨m, hm, hx⟩ ⟨n, hn, hy⟩
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    rw [mul_pow, pow_mul, Nat.mul_comm m n, pow_mul y]
    exact (integralization h a).mul_mem
      ((integralization h a).pow_mem hx n) ((integralization h a).pow_mem hy m)

/-- The actual saturated pushout monoid `S`.
Source: ILO VI 2.1--2.2 and VIII 3.1.17
(blueprint: lem-per-kummer-saturated-pushout-algebra). -/
noncomputable abbrev Sat (h : P →* Q) (a : P →* R) := saturation h a

/-- Integralization followed by saturation, on ordinary pushout representatives.
Source: ILO VI 2.1--2.2 and VIII 3.1.17
(blueprint: lem-per-kummer-saturated-pushout-algebra). -/
noncomputable def toSat (h : P →* Q) (a : P →* R) : Raw h a →* Sat h a :=
  (Algebra.GrothendieckGroup.of (M := Raw h a)).codRestrict _
    (fun x ↦ ⟨1, Nat.zero_lt_one, by
      rw [pow_one]
      exact ⟨x, rfl⟩⟩)

/-- The canonical `Q` leg into the saturation. Source: ILO VI 2.1--2.2
(blueprint: lem-per-kummer-saturated-pushout-algebra). -/
noncomputable def left (h : P →* Q) (a : P →* R) : Q →* Sat h a :=
  (toSat h a).comp (rawLeft h a)

/-- The canonical `R` leg into the saturation. Source: ILO VI 2.1--2.2
(blueprint: lem-per-kummer-saturated-pushout-algebra). -/
noncomputable def right (h : P →* Q) (a : P →* R) : R →* Sat h a :=
  (toSat h a).comp (rawRight h a)

/-- Both displayed monoid-algebra maps are finite and surjective on spectra.
The second map is specified on `A` and every monomial, so it is the canonical
map. Universal quantification over the coefficient algebra includes every further
scalar extension, without flatness or Noetherianness.
Source: ILO VI 2.1--2.2, algebraic chart formulation
(blueprint: lem-per-kummer-saturated-pushout-algebra). -/
def AlgebraRealization (h : P →* Q) (a : P →* R) (n : ℕ) : Prop :=
  ∀ (A : Type v) [CommRing A] [Algebra (MonoidAlgebra ℤ R) A], IsUnit (n : A) →
    letI := (MonoidAlgebra.mapDomainRingHom ℤ (rawRight h a)).toAlgebra
    letI := (MonoidAlgebra.mapDomainRingHom ℤ (right h a)).toAlgebra
    (Algebra.TensorProduct.includeLeftRingHom (R := MonoidAlgebra ℤ R)
      (A := A) (B := MonoidAlgebra ℤ (Sat h a))).Finite ∧
    Function.Surjective (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeLeftRingHom (R := MonoidAlgebra ℤ R)
        (A := A) (B := MonoidAlgebra ℤ (Sat h a)))) ∧
    ∃ t : A ⊗[MonoidAlgebra ℤ R] MonoidAlgebra ℤ (Raw h a) →+*
        A ⊗[MonoidAlgebra ℤ R] MonoidAlgebra ℤ (Sat h a),
      (∀ (b : A) (s : Raw h a),
        t (b ⊗ₜ[MonoidAlgebra ℤ R] MonoidAlgebra.of ℤ (Raw h a) s) =
          b ⊗ₜ[MonoidAlgebra ℤ R] MonoidAlgebra.of ℤ (Sat h a) (toSat h a s)) ∧
      t.Finite ∧ Function.Surjective (PrimeSpectrum.comap t)

/-- The canonical chart scheme `F ×[Spec ℤ[S₀]] Spec ℤ[S]`.
Source: ILO VIII 3.3.5--3.3.11 and X 1.8
(blueprint: lem-per-kummer-saturated-pushout-algebra). -/
noncomputable def ChartScheme (h : P →* Q) (a : P →* R) (F : Scheme.{u})
    (χ : Raw h a →* Γ(F, ⊤)) : Scheme.{u} :=
  pullback (F.toSpecΓ ≫ Spec.map
    (CommRingCat.ofHom (MonoidAlgebra.lift ℤ Γ(F, ⊤) (Raw h a) χ).toRingHom))
    (Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom ℤ (toSat h a))))

/-- Projection of the saturated chart scheme to the ordinary fibre product.
Source: ILO VIII 3.3.5 and X 1.8
(blueprint: lem-per-kummer-saturated-pushout-algebra). -/
noncomputable def chartToBase (h : P →* Q) (a : P →* R) (F : Scheme.{u})
    (χ : Raw h a →* Γ(F, ⊤)) : ChartScheme h a F χ ⟶ F :=
  pullback.fst _ _

/-- Projection to the spectrum of the saturated monoid algebra.
Source: ILO VIII 3.3.5 and X 1.8
(blueprint: lem-per-kummer-saturated-pushout-algebra). -/
noncomputable def chartToSpec (h : P →* Q) (a : P →* R) (F : Scheme.{u})
    (χ : Raw h a →* Γ(F, ⊤)) :
    ChartScheme h a F χ ⟶ Spec (.of (MonoidAlgebra ℤ (Sat h a))) :=
  pullback.snd _ _

/-- Pullbacks of the actual monomials on `Spec ℤ[S]`, defining its prelog chart.
Source: ILO VIII 3.3.5 and X 1.8
(blueprint: lem-per-kummer-saturated-pushout-algebra). -/
noncomputable def chartBeta (h : P →* Q) (a : P →* R) (F : Scheme.{u})
    (χ : Raw h a →* Γ(F, ⊤)) : Sat h a →* Γ(ChartScheme h a F χ, ⊤) :=
  (chartToSpec h a F χ).appTop.hom.toMonoidHom.comp
    ((Scheme.ΓSpecIso (.of (MonoidAlgebra ℤ (Sat h a)))).inv.hom.toMonoidHom.comp
      (MonoidAlgebra.of ℤ (Sat h a)))

/-- Compatible global charts of a cospan of arbitrary fs log schemes. Restricting
an étale chart to its domain gives exactly this formulation.
Source: ILO VI 1.1, VIII 3.3.4--3.3.6
(blueprint: lem-per-kummer-saturated-pushout-algebra). -/
structure ChartCospan (h : P →* Q) (a : P →* R)
    {X Y Y' : Scheme.{u}} {M : EtaleLogStructure X} {N : EtaleLogStructure Y}
    {N' : EtaleLogStructure Y'} (f : EtaleLogMap N M) (g : EtaleLogMap N' M) where
  baseChart : P →* M.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 X)))
  leftChart : Q →* N.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 Y)))
  rightChart : R →* N'.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 Y')))
  baseIsChart : M.IsChart (Scheme.Etale.mk (𝟙 X)) baseChart
  leftIsChart : N.IsChart (Scheme.Etale.mk (𝟙 Y)) leftChart
  rightIsChart : N'.IsChart (Scheme.Etale.mk (𝟙 Y')) rightChart
  leftCompatible :
    (f.sectionMap (Scheme.Etale.mk (𝟙 X)) (Scheme.Etale.mk (𝟙 Y)) f.base
      ((Category.comp_id f.base).trans (Category.id_comp f.base).symm)).comp
      baseChart = leftChart.comp h
  rightCompatible :
    (g.sectionMap (Scheme.Etale.mk (𝟙 X)) (Scheme.Etale.mk (𝟙 Y')) g.base
      ((Category.comp_id g.base).trans (Category.id_comp g.base).symm)).comp
      baseChart = rightChart.comp a

/-- The associated-log chart construction commutes with étale restriction of its
ordinary scheme base. The comparison is fixed by both scheme projections and is
strict, so this is compatibility of the log sheaves as well as the schemes.
Source: ILO VIII 3.3.5--3.3.11; X 1.8
(blueprint: lem-per-kummer-saturated-pushout-algebra). -/
def Restricts (h : P →* Q) (a : P →* R) (F : Scheme.{u})
    (χ : Raw h a →* Γ(F, ⊤)) (L : EtaleLogStructure (ChartScheme h a F χ))
    (η : associatedLogPresheaf (chartBeta h a F χ) ⟶ L.monoidSheaf.obj) : Prop :=
  ∀ U : F.Etale,
    ∃ (LU : EtaleLogStructure
        (ChartScheme h a U.left (U.hom.appTop.hom.toMonoidHom.comp χ)))
      (ηU : associatedLogPresheaf
        (chartBeta h a U.left (U.hom.appTop.hom.toMonoidHom.comp χ)) ⟶ LU.monoidSheaf.obj)
      (b : EtaleLogMap LU L),
      IsAssociatedLogPresentation
        (chartBeta h a U.left (U.hom.appTop.hom.toMonoidHom.comp χ)) LU ηU ∧
      LU.IsFineSaturated ∧ b.IsStrictEtale ∧
      b.base ≫ chartToBase h a F χ =
        chartToBase h a U.left (U.hom.appTop.hom.toMonoidHom.comp χ) ≫ U.hom ∧
      b.base ≫ chartToSpec h a F χ =
        chartToSpec h a U.left (U.hom.appTop.hom.toMonoidHom.comp χ) ∧
      ∀ s : Sat h a,
        b.sectionMap (Scheme.Etale.mk (𝟙 (ChartScheme h a F χ)))
          (Scheme.Etale.mk (𝟙 _)) b.base
          ((Category.comp_id b.base).trans (Category.id_comp b.base).symm)
          (associatedLogIota (chartBeta h a F χ) L η (ULift.up s)) =
            associatedLogIota
              (chartBeta h a U.left (U.hom.appTop.hom.toMonoidHom.comp χ)) LU ηU
              (ULift.up s)

/-- On compatible charts the displayed scheme, with the associated `S` log
structure, is the fs fibre product. The legs are fixed on scheme projections and
on the `Q,R` charts; the cone equality and uniqueness include all log sheaf maps.
The restriction clause identifies the construction on all étale chart domains.
Source: ILO VI 2.1--2.2; VIII 3.3.5--3.3.11; X 1.8
(blueprint: lem-per-kummer-saturated-pushout-algebra). -/
def LogRealization (h : P →* Q) (a : P →* R) : Prop :=
  ∀ (X Y Y' : Scheme.{u}) (M : EtaleLogStructure X) (N : EtaleLogStructure Y)
    (N' : EtaleLogStructure Y'), M.IsFineSaturated → N.IsFineSaturated →
    N'.IsFineSaturated → ∀ (f : EtaleLogMap N M) (g : EtaleLogMap N' M)
    (c : ChartCospan h a f g),
    ∃ χ : Raw h a →* Γ(pullback f.base g.base, ⊤),
      (∀ q : Q, χ (rawLeft h a q) = (pullback.fst f.base g.base).appTop
        (N.alpha.app (op (Scheme.Etale.mk (𝟙 Y))) (c.leftChart q))) ∧
      (∀ r : R, χ (rawRight h a r) = (pullback.snd f.base g.base).appTop
        (N'.alpha.app (op (Scheme.Etale.mk (𝟙 Y'))) (c.rightChart r))) ∧
      ∃ (L : EtaleLogStructure (ChartScheme h a (pullback f.base g.base) χ))
        (η : associatedLogPresheaf (chartBeta h a (pullback f.base g.base) χ) ⟶
          L.monoidSheaf.obj) (p : EtaleLogMap L N) (q : EtaleLogMap L N'),
        IsAssociatedLogPresentation (chartBeta h a (pullback f.base g.base) χ) L η ∧
        L.IsFineSaturated ∧
        p.base = chartToBase h a (pullback f.base g.base) χ ≫
          pullback.fst f.base g.base ∧
        q.base = chartToBase h a (pullback f.base g.base) χ ≫
          pullback.snd f.base g.base ∧
        (∀ x : Q,
          p.sectionMap (Scheme.Etale.mk (𝟙 Y)) (Scheme.Etale.mk
            (𝟙 (ChartScheme h a (pullback f.base g.base) χ))) p.base
              ((Category.comp_id p.base).trans (Category.id_comp p.base).symm) (c.leftChart x) =
            associatedLogIota (chartBeta h a (pullback f.base g.base) χ) L η
              (ULift.up (left h a x))) ∧
        (∀ x : R,
          q.sectionMap (Scheme.Etale.mk (𝟙 Y')) (Scheme.Etale.mk
            (𝟙 (ChartScheme h a (pullback f.base g.base) χ))) q.base
              ((Category.comp_id q.base).trans (Category.id_comp q.base).symm) (c.rightChart x) =
            associatedLogIota (chartBeta h a (pullback f.base g.base) χ) L η
              (ULift.up (right h a x))) ∧
        (∃ d : EtaleLogMap L M, p.CompEq f d ∧ q.CompEq g d) ∧
        (∀ (T : Scheme.{u}) (K : EtaleLogStructure T), K.IsFineSaturated →
          ∀ (i : EtaleLogMap K N) (j : EtaleLogMap K N') (d : EtaleLogMap K M),
            i.CompEq f d → j.CompEq g d →
              ∃! b : EtaleLogMap K L, b.CompEq p i ∧ b.CompEq q j) ∧
        Restricts h a (pullback f.base g.base) χ L η

/-- Compatible local fs charts for an arbitrary log morphism and a prescribed
pointed target chart. Both the point and the given target chart are retained.
Source: ILO VI 1.1; VIII 3.3.4, with the finite-presentation chart argument in
Steps 12--14 of the DAG (blueprint: lem-per-kummer-saturated-pushout-algebra). -/
def CompatibleLocalCharts : Prop :=
  ∀ (X Y : Scheme.{u}) (M : EtaleLogStructure X) (N : EtaleLogStructure Y),
    M.IsFineSaturated → N.IsFineSaturated → ∀ (g : EtaleLogMap N M)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (W : X.Etale) (w : (Scheme.pointSmallEtale (y ≫ g.base)).fiber.obj W)
    (B : Type u) [CommMonoid B], IsFineSaturatedMonoid B →
    ∀ c : B →* M.monoidSheaf.obj.obj (op W), M.IsChart W c →
      ∃ (V : Y.Etale) (v : (Scheme.pointSmallEtale y).fiber.obj V)
        (k : V.left ⟶ W.left) (hk : k ≫ W.hom = V.hom ≫ g.base),
        v.left ≫ k = w.left ∧
        ∃ (D : Type u) (_ : CommMonoid D) (r : D →* N.monoidSheaf.obj.obj (op V))
          (a : B →* D), IsFineSaturatedMonoid D ∧ N.IsChart V r ∧
          (g.sectionMap W V k hk).comp c = r.comp a

end KummerPushout

/-- Saturated Kummer pushouts, their canonical group cokernel, their finite
surjective monoid-algebra realizations over every coefficient algebra, and their
fs logarithmic fibre products and compatible local charts on arbitrary schemes.

Source: ILO VI 2.1--2.2, pp.71--72; VIII 3.3.5--3.3.11, pp.107--108;
X 1.8, pp.146--147, with the algebraic and arbitrary-scheme refinements of this DAG.
(blueprint: lem-per-kummer-saturated-pushout-algebra).

Proof (the DAG's steps, including the finite-presentation local-chart argument):
1. Put $H=(Q^{\rm gp}\oplus R^{\rm gp})/\{(h^{\rm gp}(p),-a^{\rm gp}(p)):p\in P^{\rm gp}\}$. The
   presentations of group completion and of $S_0$ identify $S_0^{\rm gp}=H$: maps from either
   presentation to any abelian group are exactly compatible pairs of maps from $Q,R$. If
   $(0,r)=(h^{\rm gp}(p),-a^{\rm gp}(p))$, injectivity of $h^{\rm gp}$ gives $p=0,r=0$. Thus
   $R^{\rm gp}\to H$ is injective, and quotienting by its image leaves exactly $Q^{\rm gp}/h^{\rm
   gp}(P^{\rm gp})=C$. The image $S_{\rm int}$ is generated by the images of finite generating
   sets of $Q,R$ and generates $H$ as a group.
2. Apply [lem-trf-fine-monoid-finite-saturation] to the integral finitely generated monoid $S_{\rm
   int}\subset H$. Its saturation is the displayed $S$, is fs, and has group completion $H$. The
   injections $R\subset R^{\rm gp}\subset H$ land in $S$. For $s\in S$ choose $m>0$ with $ms=q+r$
   in $H$. Choose $d>0,p\in P$ with $dq=h(p)$. Then $dm s=a(p)+dr\in R$. This proves the positive-
   multiple assertion, including torsion elements, and the first step gives the asserted cokernel.
   Uses: lem-trf-fine-monoid-finite-saturation.
3. If $T$ is fs and $Q\to T$, $R\to T$ agree on $P$, the monoid presentation gives $S_0\to T$.
   Since $T\to T^{\rm gp}$ is injective this factors through $S_{\rm int}$. The induced group map
   $H\to T^{\rm gp}$ sends $s\in S$ into $T$: a positive multiple of its image belongs to $T$ and
   $T$ is saturated. Its restriction $S\to T$ is the required extension. Any extension has that
   group map, because $S_{\rm int}$ generates $H$, so it is unique. This proves the fs monoid
   pushout property.
4. Let $s_1,\ldots,s_t$ generate $S$ and choose $d_i>0$ with $d_i s_i\in R$ by Step 2. Every
   monomial in $\mathbf Z[S]$ is a product of an $R$-monomial and one of the finitely many
   $z^{\sum e_i s_i}$, $0\le e_i<d_i$, by division with remainder of the exponents. These
   monomials span $\mathbf Z[S]$ over $\mathbf Z[R]$ and also over $\mathbf Z[S_0]$ (whose image
   contains $\mathbf Z[R]$). After tensoring with $A$ the same finite spanning formulas prove both
   claimed ring maps finite. This argument does not require flatness, Noetherianity, or
   invertibility of $n$.
5. For use in lifting points, record a face calculation. A face of an additive monoid is a
   submonoid $F$ such that $x+y\in F$ implies $x,y\in F$. If $P\to Q$ is our Kummer injection and
   $F_P=h^{-1}(F_Q)$ for a face $F_Q$ of $Q$, then $q\in F_Q$ exactly when $dq=h(p)$ for some
   $d>0,p\in F_P$: one implication uses a Kummer multiple; the other uses the face property.
   Moreover $(h^{\rm gp})^{-1}(F_Q^{\rm gp})=F_P^{\rm gp}$. Indeed, write $h^{\rm gp}(u)=q_1-q_2$
   with $q_i\in F_Q$, choose a common $d>0$ with $dq_i=h(p_i)$, $p_i\in F_P$, and obtain
   $du=p_1-p_2$. By [lem-trf-fs-face-sharpening], $P^{\rm gp}/F_P^{\rm gp}$ is free abelian, hence
   has no nonzero element killed by $d$. Thus $u\in F_P^{\rm gp}$. Uses: lem-trf-fs-face-
   sharpening.
6. Take compatible monoid maps $\chi_Q:Q\to(k,\cdot)$ and $\chi_R:R\to(k,\cdot)$, where $k$ is
   algebraically closed. Their nonzero loci $F_Q,F_R$ are faces, with common inverse-image face
   $F_P\subset P$. Set $F_S=\{s\in S:ms\in F_R\text{ for some }m>0\}$, interpreting $F_R\subset
   H$. Every $s$ has a positive multiple in $R$. Taking common multiples shows $F_S$ is a face: if
   $s+t$ has a multiple in $F_R$, choose a common multiple also placing $s,t$ in $R$, and apply
   the face property in $R$. Its inverse image in $R$ is $F_R$, since $R\to H$ is injective and
   faces are root-closed inside $R$. Its inverse image in $Q$ is $F_Q$: for $dq=h(p)$, membership
   of the image of $q$ is equivalent successively to $a(p)\in F_R$, $p\in F_P$, and $q\in F_Q$.
7. The group $K=F_Q^{\rm gp}\oplus_{F_P^{\rm gp}}F_R^{\rm gp}$ maps injectively into $H$. To check
   the kernel, if $(q,r)$ in the sum of face groups equals $(h^{\rm gp}(u),-a^{\rm gp}(u))$ in
   $Q^{\rm gp}\oplus R^{\rm gp}$, Step 5 gives $u\in F_P^{\rm gp}$. Thus it was already a defining
   relation for $K$. Its image lies in $F_S^{\rm gp}$. On their nonzero loci the two characters
   extend uniquely to group homomorphisms to $k^\times$; agreement on $F_P$ gives a character
   $K\to k^\times$.
8. The group $k^\times$ is divisible: a root of $X^m-b$, for $m>0,b\ne0$, exists by algebraic
   closedness and is nonzero [def-weil-algebraic-closure]. Apply [lem-per-divisible-group-hom-
   extension] to $K\hookrightarrow F_S^{\rm gp}$, writing the target group multiplicatively, to
   extend that character. Give $s\in F_S$ its character value and $s\notin F_S$ value zero. Since
   $F_S$ is a face this is a monoid homomorphism $S\to(k,\cdot)$, and Step 6 shows its
   restrictions are exactly $\chi_Q,\chi_R$. This proves lifting of every compatible pair, rather
   than assuming that an arbitrary character of $S_0$ factors through integralization. Uses: def-
   weil-algebraic-closure, lem-per-divisible-group-hom-extension.
9. There is also a lift of any single character $\chi_R:R\to(k,\cdot)$. Use its nonzero face $F_R$
   and the face $F_S$ defined in Step 6, whose construction only uses the positive-multiple
   property and $R\hookrightarrow H$. The inclusion $F_R^{\rm gp}\hookrightarrow F_S^{\rm gp}$ is
   injective. Divisibility of $k^\times$ and [lem-per-divisible-group-hom-extension] extend the
   nonzero character to $F_S^{\rm gp}$; extending by zero off the face gives the desired
   $S$-character. Uses: lem-per-divisible-group-hom-extension.
10. For any prime $\mathfrak p$ of $A$, map $A\to k$ into an algebraic closure of its residue
   field [def-weil-algebraic-closure]. Step 9 supplies a compatible $S$-character, hence the
   explicit ring map $A\otimes_{\mathbf Z[R]}\mathbf Z[S]\to k$, $a\otimes z^s\mapsto\bar
   a\chi_S(s)$. Its kernel is a prime over $\mathfrak p$ [def-weil-affine-spectrum]. Likewise, for
   a prime of $A\otimes_{\mathbf Z[R]}\mathbf Z[S_0]$, its residue-field map into an algebraic
   closure gives compatible $Q,R$ characters and the prescribed $A$ map; Step 8 gives a map from
   the target tensor ring whose restriction is that residue-field map. Its kernel lies over the
   original prime. Thus both spectra maps are surjective, including the empty-spectrum case. Uses:
   def-weil-algebraic-closure, def-weil-affine-spectrum.
11. If $A\to A'$ is any further scalar extension, $A'$ is again a $\mathbf Z[R]$-algebra with $n$
   invertible. The maps after base change identify with the same displayed maps for $A'$ by
   $a'\otimes(a\otimes z^s)\mapsto a'a\otimes z^s$ and its inverse $a'\otimes z^s\mapsto
   a'\otimes(1\otimes z^s)$; the same formulas apply with $S_0$. The finite spanning sets and
   prime-lifting arguments above therefore prove the assertions after arbitrary scalar extension.
12. We first produce compatible local charts for an arbitrary fs morphism. Restrict to the
   prescribed target chart and choose some fs source chart $T\to N'$ near $\bar y'$. Put
   $L=N'_{\bar y'}$, $U=\mathcal O_{Y',\bar y'}^\times$, $F=\{t\in T: \alpha(t)\in U\}$. By [lem-
   trf-fs-face-sharpening], $T_F=T-F$ is fs, its units are $F^{\rm gp}$ and $B=T_F/F^{\rm gp}$ is
   fs sharp. By the stalk formula of [lem-per-integral-chart-logification-thickening] for the
   chart $T$, $T\oplus_FU=L$, hence $T_F\oplus_{F^{\rm gp}}U=L$ and $B=L/U$; $L$ is integral by
   [lem-per-associated-log-arbitrary-scheme]. Every image of a generator $p_i$ of $P$ can thus be
   written $t_i+u_i$ in $L$, $t_i\in T_F$, $u_i\in U$ (we use additive notation also for log
   monoids and their unit groups). Let $V\subset U$ be generated as a group by these finitely many
   $u_i$. Let $R$ be the image of $T_F\oplus V$ in the integral monoid $L$. It is finitely
   generated and integral, contains the image of $P$, and maps onto $B$. Uses: lem-trf-fs-face-
   sharpening, lem-per-integral-chart-logification-thickening, lem-per-associated-log-arbitrary-
   scheme.
13. Here $R$ is already saturated. Let $H_R$ be its generated subgroup of $L^{\rm gp}$, and $W$
   the subgroup of $U$ generated by the image of $F^{\rm gp}$ and $V$. The pushout presentation of
   $L$ in Step 12 gives $H_R\cap U=W$: write an element as $t_1-t_2+v$; if it is a unit, $t_1,t_2$
   have the same image in $B$, so their difference lies in the image of $F^{\rm gp}$. Consequently
   $R$ is exactly the inverse image of $B\subset B^{\rm gp}$ under $H_R\to B^{\rm gp}$: choose
   $t\in T_F$ with the prescribed characteristic and subtract it, leaving an element of $W\subset
   R^\times$. Since $B$ is saturated, this inverse image is saturated. Also $R^\times=W$, and
   $R\oplus_W U\to L$ is an isomorphism: it is surjective since $T_F$ and $U$ generate $L$, and
   equality of two images implies that the difference of their $R$ terms lies in $H_R\cap U=W$,
   precisely the pushout relation. Thus $R\to L$ is a stalk chart.
14. Apply [lem-per-prelog-stalk-chart-spreading] to $R\to L$ and its stalk-chart isomorphism. It
   gives an fs chart $R\to N'$ on a pointed etale neighbourhood. The germ of the original $P$-map
   factors through the homomorphism $a:P\to R$ constructed in Step 12. The equality clause of that
   same lemma, applied to the finitely generated $P$, shrinks the neighbourhood so that the two
   $P$-maps agree as sections. Therefore $a$ is compatible with the given morphism and target
   chart. All hypotheses of the spreading lemma concern finite monoids and an fs log structure;
   none require Noetherian schemes. Uses: lem-per-prelog-stalk-chart-spreading.
15. On compatible charts, put $Z=F\times_{\operatorname{Spec}\mathbf
   Z[S_0]}\operatorname{Spec}\mathbf Z[S]$ and give it the associated log structure $L_Z(S,\beta)$
   of [lem-per-integral-chart-logification-thickening], where $\beta(s)$ is the pullback of $z^s$.
   It is fs because $S$ is fs and charts it [lem-per-associated-log-arbitrary-scheme]. For any fs
   test log scheme $(T,M_T)$ with compatible maps to the original factors, their charts give
   compatible maps $Q,R\to\Gamma(T,M_T)$ and an underlying scheme map $v:T\to F$. The section
   monoid is integral saturated by [lem-per-associated-log-arbitrary-scheme]. Step 3's explicit
   extension argument (which uses only integrality and saturation of the target) gives a unique
   $\lambda:S\to\Gamma(T,M_T)$. The ring map $\mathbf Z[S]\to\Gamma(T,\mathcal O_T)$ sends $z^s$
   to $\alpha(\lambda(s))$ and agrees with $v$ on $\mathbf Z[S_0]$. On affine opens of $T$ the
   affine-spectrum correspondence gives the unique lift to $Z$, and uniqueness makes these maps
   agree and glue. The universal property of [lem-per-integral-chart-logification-thickening]
   along this scheme map gives its unique log morphism. Conversely restricting this lift to $Q,R$
   recovers the given pair. Thus this chart scheme satisfies exactly the fs fibre-product
   universal property. Uses: lem-per-associated-log-arbitrary-scheme, lem-per-integral-chart-
   logification-thickening, def-weil-affine-spectrum.
16. On an affine open of $F$ the underlying ring in Step 15 is its tensor product over $\mathbf
   Z[S_0]$ with $\mathbf Z[S]$, by [lem-weil-pbc-fibre-product-affine-spectra], exactly the stated
   chart formula. After etale restriction or replacement of compatible charts, Step 15 again
   describes the same functor of fs test objects, in terms of the three log sheaves. The unique
   comparison maps between two such representatives are inverse, since their composites induce the
   identity on that functor. On triple restrictions their compositions are the unique comparison.
   This proves compatibility with restriction of charts. Step 14 provides compatible charts
   locally at every geometric point, and Step 15 proves that the displayed construction on any
   such charts is the fs fibre product, without a Noetherian or flatness hypothesis. Uses: lem-
   weil-pbc-fibre-product-affine-spectra.
-/
theorem kummer_saturated_pushout_algebra
    (P Q R : Type u) [CommMonoid P] [CommMonoid Q] [CommMonoid R]
    (hP : IsFineSaturatedMonoid P) (hQ : IsFineSaturatedMonoid Q)
    (hR : IsFineSaturatedMonoid R) (h : P →* Q) (a : P →* R)
    (hinj : Function.Injective h)
    (hkum : ∀ q : Q, ∃ (d : ℕ) (p : P), 0 < d ∧ q ^ d = h p)
    (hgp : Function.Injective (Algebra.GrothendieckGroup.lift
      ((Algebra.GrothendieckGroup.of (M := Q)).comp h)))
    (n : ℕ) (hn : 0 < n)
    (hfinite : Finite (Algebra.GrothendieckGroup Q ⧸
      (Algebra.GrothendieckGroup.lift
        ((Algebra.GrothendieckGroup.of (M := Q)).comp h)).range))
    (hann : ∀ c : Algebra.GrothendieckGroup Q ⧸
      (Algebra.GrothendieckGroup.lift
        ((Algebra.GrothendieckGroup.of (M := Q)).comp h)).range, c ^ n = 1) :
    IsFineSaturatedMonoid (KummerPushout.Sat h a) ∧
    Function.Injective (KummerPushout.right h a) ∧
    Function.Injective (Algebra.GrothendieckGroup.lift
      ((Algebra.GrothendieckGroup.of (M := KummerPushout.Sat h a)).comp
        (KummerPushout.right h a))) ∧
    (∀ s : KummerPushout.Sat h a, ∃ (m : ℕ) (r : R),
      0 < m ∧ s ^ m = KummerPushout.right h a r) ∧
    (∃ e : (Algebra.GrothendieckGroup (KummerPushout.Sat h a) ⧸
        (Algebra.GrothendieckGroup.lift
          ((Algebra.GrothendieckGroup.of (M := KummerPushout.Sat h a)).comp
            (KummerPushout.right h a))).range) ≃*
        (Algebra.GrothendieckGroup Q ⧸
          (Algebra.GrothendieckGroup.lift
            ((Algebra.GrothendieckGroup.of (M := Q)).comp h)).range),
      ∀ q : Q, e (QuotientGroup.mk
        (Algebra.GrothendieckGroup.of (KummerPushout.left h a q))) =
          QuotientGroup.mk (Algebra.GrothendieckGroup.of q)) ∧
    (∀ (T : Type v) [CommMonoid T], IsFineSaturatedMonoid T →
      ∀ (f : Q →* T) (g : R →* T), f.comp h = g.comp a →
        ∃! l : KummerPushout.Sat h a →* T,
          l.comp (KummerPushout.left h a) = f ∧ l.comp (KummerPushout.right h a) = g) ∧
    KummerPushout.AlgebraRealization.{u, v} h a n ∧
    KummerPushout.LogRealization h a ∧ KummerPushout.CompatibleLocalCharts.{u} := by
  sorry

end AlgebraicGeometry
