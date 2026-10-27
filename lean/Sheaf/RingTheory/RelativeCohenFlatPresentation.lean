module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Rename
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.FlatCompletion
import WeilConjectures.RingTheory.LocalCompletionQuotient
import WeilConjectures.RingTheory.CompletionRegularLocal
import WeilConjectures.RingTheory.CompletionDimension
import WeilConjectures.RingTheory.CoefficientResidueSection
import Mathlib.RingTheory.Smooth.Field
import WeilConjectures.RingTheory.FormallySmoothAdicLiftIntoComplete
import WeilConjectures.RingTheory.PowerSeriesUniversalPropertyComplete
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import Mathlib.RingTheory.AdicCompletion.Functoriality
import WeilConjectures.RingTheory.FlatClosedFiberKernelRigidity

/-!
# Relative Cohen presentations for flat local maps

Source: Stacks Project, more-algebra.tex, Tag 07NQ, proof of (2) implies (3),
and algebra.tex, Tags 032A, 0322 and 0C0S, coefficient-compatible refinement
(blueprint: lem-trf-relative-cohen-flat-presentation).

The map on completions is specified at every finite quotient. Coefficient linearity
of the two ring equivalences is expressed by their values on constants. The variable
set `Fin e ⊕ Fin s` distinguishes base variables from relative parameters.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

namespace MvPowerSeries

/-- Extend coefficients and include the first block of variables.
Source: Stacks Project, Tag 07NQ, the power-series diagram
(blueprint: lem-trf-relative-cohen-flat-presentation). -/
def coefficientExtensionInl {K : Type u} {L : Type v} [CommRing K] [CommRing L]
    (ι : K →+* L) (e s : ℕ) :
    MvPowerSeries (Fin e) K →+* MvPowerSeries (Fin e ⊕ Fin s) L :=
  (rename (Sum.inl : Fin e → Fin e ⊕ Fin s)).toRingHom.comp (map ι)

end MvPowerSeries

namespace IsLocalRing

/-- Compatible coefficient fields and a relative Cohen presentation.
Source: Stacks Project, Tag 07NQ, proof of (2) implies (3), refined by Tags
032A, 0322, 07NJ and 0C0S as in the DAG proof
(blueprint: lem-trf-relative-cohen-flat-presentation).

Proof:
1. Put $A_0=\widehat A$, $B_0=\widehat B$, and $f_0=\widehat f$. The completion results give
Noetherian local rings with maximal ideals $\mathfrak m_0=\mathfrak m A_0$ and $\mathfrak
n_0=\mathfrak n B_0$, residue fields canonically $K,L$, and completeness for these maximal ideals.
The induced map is local: its reduction is the induced field inclusion $K\hookrightarrow L$, so an
element with nonzero residue has nonzero image residue. By flatness under completion, $f_0$ is
flat. The canonical maps preserve the $\mathbf Q$-algebra structures. Uses: lem-weil-pbc-adic-
completion-noetherian, lem-weil-pbc-local-completion-local-ring, lem-weil-pbc-module-completion-
complete, lem-weil-pbc-flat-completion.
2. Let $C=B/\mathfrak mB$ with maximal ideal the image of $\mathfrak n$. This is a nonzero
Noetherian local ring. Completion of the surjection $B\to C$ gives $B_0/(\mathfrak
mB)B_0\simeq\widehat C$. Since $\mathfrak m_0=\mathfrak m A_0$ and $f_0$ commutes with the
canonical maps, $(\mathfrak mB)B_0=\mathfrak m_0B_0$. Write $C_0=B_0/\mathfrak m_0B_0$. Its
identification with $\widehat C$ preserves residue fields and quotient maps. Completion preserves
regularity and dimension, so $C_0$ is complete regular local of dimension $s$, with residue field
$L$. Uses: lem-weil-pbc-quotient-local-structure, lem-weil-pbc-surjective-image-noetherian, lem-
weil-pbc-local-completion-quotient, lem-weil-pbc-local-completion-local-ring, lem-weil-pbc-
completion-regular-local, lem-weil-pbc-completion-dimension, lem-weil-pbc-module-completion-
complete.
3. Choose a residue section $a:K\to A_0$. Give $B_0$ its $K$-algebra structure $f_0a$. The residue
map $B_0\to L$ is then a $K$-algebra map for the given inclusion $K\hookrightarrow L$. The
arbitrary characteristic-zero extension $L/K$ is formally smooth. Apply the complete-target
lifting lemma to $R=K$, $S=L$, the ideal $0\subset L$, target $B_0$, and $I=J=\mathfrak n_0$,
lifting the identity map $L\to B_0/\mathfrak n_0=L$. Its hypotheses hold with $r=t=1$: the zero
ideal maps into every ideal, $J\subset I$, and $J=\bigcap_{h\ge1}(J+I^h)$ because every summand is
$J$. We obtain a $K$-algebra map $b:L\to B_0$ reducing to the identity. Consequently $b|_K=f_0a$,
with no finiteness assumption on $L/K$. Uses: lem-weil-pbc-coefficient-residue-section, lem-weil-
pbc-char-zero-field-extension-formally-smooth, lem-weil-pbc-fs-adic-lift-into-complete.
4. Choose generators $x_1,\ldots,x_e$ of $\mathfrak m_0$, possible since $A_0$ is Noetherian. Put
$R=K[[X_1,\ldots,X_e]]$. Evaluate coefficients through $a$ and $X_i$ at $x_i$ using the power-
series universal property to obtain $q:R\to A_0$. The source is complete for $\mathfrak
r=(X_1,\ldots,X_e)$, $q(\mathfrak r)A_0=\mathfrak m_0$, and $R\to A_0/\mathfrak m_0=K$ is
surjective by constants. The complete-source surjectivity lemma applies, as $A_0$ is $\mathfrak
m_0$-adically Hausdorff, and proves $q$ surjective. Let $I=\ker q$. Reduction of $q$ is the
constant-coefficient map, so $I\subseteq\mathfrak r$. The quotient isomorphism $R/I\simeq A_0$ is
$K$-linear for $a$. Uses: lem-weil-pbc-power-series-universal-property-complete, lem-weil-pbc-
power-series-field-cohen-regular-complete, lem-weil-pbc-complete-source-surjective-mod-ideal.
5. The section $b$ induces a coefficient map $\bar b:L\to C_0$ whose reduction is the identity of
$L$. By regularity and dimension $s$, choose $\bar t_1,\ldots,\bar t_s$ generating the maximal
ideal of $C_0$. Apply the specified-coefficient coordinate theorem to obtain
$\rho:L[[T_1,\ldots,T_s]]\xrightarrow{\sim}C_0$ with coefficients $\bar b$ and variables $\bar
t_i$. Lift the $\bar t_i$ to $t_i\in\mathfrak n_0$; these lifts exist because the maximal ideal of
the quotient is the image of $\mathfrak n_0$. Uses: lem-trf-regular-complete-coefficient-
coordinates, lem-weil-pbc-quotient-local-structure.
6. Put $S=L[[X_1,\ldots,X_e,T_1,\ldots,T_s]]$ and define $v:S\to B_0$ by coefficients $b$,
$X_i\mapsto f_0(x_i)$, $T_i\mapsto t_i$, using the universal property. The images of the variables
generate $\mathfrak n_0$: the images of the $t_i$ generate its quotient modulo $\mathfrak m_0B_0$,
and the $f_0(x_i)$ generate $\mathfrak m_0B_0$. Thus the complete-source surjectivity lemma
applies to the variable ideal of $S$, since constants surject onto $L$ and $B_0$ is $\mathfrak
n_0$-adically Hausdorff. It gives surjectivity of $v$. The ring $S$ is Noetherian complete local,
with maximal ideal generated by all its variables. Uses: lem-weil-pbc-power-series-universal-
property-complete, lem-weil-pbc-power-series-field-cohen-regular-complete, lem-weil-pbc-complete-
source-surjective-mod-ideal.
7. Let $j:R\to S$ extend coefficients $K\hookrightarrow L$ and retain the $X$ variables. The maps
$vj$ and $f_0q$ agree on constants by $b|_K=f_0a$ and on $X_i$ by construction; uniqueness in the
power-series universal property gives $vj=f_0q$. The map $j$ is local since series of zero
constant term go into the maximal ideal. Setting $X=0$ gives $p:S\twoheadrightarrow L[[T]]$ with
kernel $(X)S$: a series vanishing at $X=0$ is $\sum_{i=1}^eX_iF_i$, grouping each monomial by its
first positive $X$ exponent. Reduction of $v$ to $C_0$ is $\rho p$, by the coefficient and
variable formulas and the same universal-property uniqueness. Since $\rho$ is injective, $\ker
v\subseteq\ker p=(X)S=\mathfrak rS$. Uses: lem-weil-pbc-power-series-universal-property-complete.
8. Apply flat closed-fibre kernel rigidity with presentation $q:R\twoheadrightarrow A_0$, flat map
$f_0:A_0\to B_0$, local map $j:R\to S$ and surjection $v:S\twoheadrightarrow B_0$. Here $R,A_0,S$
are local, $S$ is Noetherian, $vj=f_0q$, and $\ker v\subseteq\mathfrak rS$ by the preceding step.
It yields $\ker v=(\ker q)S=IS$. The quotient isomorphism $S/IS\simeq B_0$ is $L$-linear for $b$,
and the one for $R/I\simeq A_0$ is $K$-linear for $a$. The equation $vj=f_0q$ identifies the
induced map with coefficient extension and inclusion of the $X$ variables. These local
isomorphisms identify maximal ideals and all their powers, hence are isomorphisms of complete
local algebras. Modulo $\mathfrak m_0B_0$, the images of $T_i$ are the chosen $\bar t_i$, which
generate the maximal ideal and number $s=\dim C_0$. This proves every asserted compatibility.
Uses: lem-weil-pbc-flat-closed-fibre-kernel-rigidity.
-/
theorem exists_relative_cohen_flat_presentation
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra ℚ A] [Algebra ℚ B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] (hflat : (algebraMap A B).Flat)
    [IsRegularLocalRing (B ⧸ (maximalIdeal A).map (algebraMap A B))]
    (s : ℕ)
    (hdim : ringKrullDim (B ⧸ (maximalIdeal A).map (algebraMap A B)) =
      (s : WithBot ℕ∞)) :
    ∃ h : AdicCompletion (maximalIdeal A) A →+* AdicCompletion (maximalIdeal B) B,
      (∀ (d : ℕ) (z : AdicCompletion (maximalIdeal A) A) (x : A),
        AdicCompletion.evalₐ (maximalIdeal A) d z =
          Ideal.Quotient.mk ((maximalIdeal A) ^ d) x →
        AdicCompletion.evalₐ (maximalIdeal B) d (h z) =
          Ideal.Quotient.mk ((maximalIdeal B) ^ d) (algebraMap A B x)) ∧
      ∃ (a : ResidueField A →+* AdicCompletion (maximalIdeal A) A)
        (b : ResidueField B →+* AdicCompletion (maximalIdeal B) B),
        (∀ k : ResidueField A, AdicCompletion.evalOneₐ (maximalIdeal A) (a k) = k) ∧
        (∀ l : ResidueField B, AdicCompletion.evalOneₐ (maximalIdeal B) (b l) = l) ∧
        b.comp (ResidueField.map (algebraMap A B)) = h.comp a ∧
        ∃ (e : ℕ) (I : Ideal (MvPowerSeries (Fin e) (ResidueField A))),
          I ≤ Ideal.span (Set.range
            (fun i : Fin e ↦ (MvPowerSeries.X i : MvPowerSeries (Fin e) (ResidueField A)))) ∧
          ∃ (α : (MvPowerSeries (Fin e) (ResidueField A) ⧸ I) ≃+*
              AdicCompletion (maximalIdeal A) A)
            (β : (MvPowerSeries (Fin e ⊕ Fin s) (ResidueField B) ⧸
              I.map (MvPowerSeries.coefficientExtensionInl
                (ResidueField.map (algebraMap A B)) e s)) ≃+*
              AdicCompletion (maximalIdeal B) B),
            (∀ k : ResidueField A, α (Ideal.Quotient.mk I (MvPowerSeries.C k)) = a k) ∧
            (∀ l : ResidueField B, β (Ideal.Quotient.mk _ (MvPowerSeries.C l)) = b l) ∧
            (∀ F : MvPowerSeries (Fin e) (ResidueField A),
              β (Ideal.Quotient.mk _ (MvPowerSeries.coefficientExtensionInl
                (ResidueField.map (algebraMap A B)) e s F)) = h (α (Ideal.Quotient.mk I F))) ∧
            Ideal.span (Set.range (fun j : Fin s ↦
              Ideal.Quotient.mk
                ((maximalIdeal A).map
                  (h.comp (algebraMap A (AdicCompletion (maximalIdeal A) A))))
                (β (Ideal.Quotient.mk _ (MvPowerSeries.X (Sum.inr j)))))) =
              (maximalIdeal (AdicCompletion (maximalIdeal B) B)).map
                (Ideal.Quotient.mk ((maximalIdeal A).map
                  (h.comp (algebraMap A (AdicCompletion (maximalIdeal A) A))))) ∧
            ringKrullDim (AdicCompletion (maximalIdeal B) B ⧸
              (maximalIdeal A).map
                (h.comp (algebraMap A (AdicCompletion (maximalIdeal A) A)))) =
              (s : WithBot ℕ∞) := by
  sorry

end IsLocalRing
