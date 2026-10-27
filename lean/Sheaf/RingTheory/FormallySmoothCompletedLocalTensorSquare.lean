/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q144
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import WeilConjectures.RingTheory.FormallySmoothAdic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.AdicCompletionNoetherianOfQuotient
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Basic
import WeilConjectures.RingTheory.FormallySmoothAdicBaseChange
import WeilConjectures.RingTheory.FormallySmoothAdicCompletion
import WeilConjectures.RingTheory.FormallySmoothAdicFlat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.TensorProduct.Basic
import Sheaf.Algebra.Category.ModuleCat.TowerLimitExactSurjectiveKernels
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.Flat

/-! # The completed local tensor square of an adically formally smooth algebra

Source: EGA 0_I 7.7.1--7.7.7 and 0_IV 19.3.5--19.3.6; the explicit local diagonal
and closed-fibre construction in the DAG proof
(blueprint: lem-sfb-formally-smooth-completed-local-tensor-square).

The abbreviations below expand to Mathlib tensor products, localizations and completions.
The existential maps in the theorem are characterized on the original rings and pure tensors.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v w

namespace RingTheory

/-- Completion of the localization at the kernel of a specified residue homomorphism.
Source: EGA 0_I 7.7.1--7.7.7, local diagonal construction.
(blueprint: lem-sfb-formally-smooth-completed-local-tensor-square). -/
abbrev LocalCompletionAtResidue {P : Type v} [CommRing P]
    {l : Type w} [Field l] (ε : P →+* l) :=
  AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.comap ε ⊥)))
    (Localization.AtPrime (Ideal.comap ε ⊥))

/-- The canonical map from the original ring into its completed residue localization.
Source: EGA 0_I 7.7.1--7.7.7, local diagonal construction.
(blueprint: lem-sfb-formally-smooth-completed-local-tensor-square). -/
noncomputable def toLocalCompletionAtResidue {P : Type v} [CommRing P]
    {l : Type w} [Field l] (ε : P →+* l) : P →+* LocalCompletionAtResidue ε :=
  (algebraMap (Localization.AtPrime (Ideal.comap ε ⊥)) (LocalCompletionAtResidue ε)).comp
    (algebraMap P (Localization.AtPrime (Ideal.comap ε ⊥)))

/-- The tensor-square residue map sends `r ⊗ s` to the product of their residues.
Source: EGA 0_I 7.7.1--7.7.7, local diagonal construction.
(blueprint: lem-sfb-formally-smooth-completed-local-tensor-square). -/
noncomputable def tensorSquareResidue (A : Type u) (R : Type v)
    [CommRing A] [CommRing R] [Algebra A R] [IsLocalRing R] :
    TensorProduct A R R →+* IsLocalRing.ResidueField R :=
  (IsLocalRing.residue R).comp (Algebra.TensorProduct.lmul' A).toRingHom

/-- The completed local tensor square at the multiplication residue point.
Source: EGA 0_I 7.7.1--7.7.7, local diagonal construction.
(blueprint: lem-sfb-formally-smooth-completed-local-tensor-square). -/
abbrev CompletedLocalTensorSquare (A : Type u) (R : Type v)
    [CommRing A] [CommRing R] [Algebra A R] [IsLocalRing R] :=
  LocalCompletionAtResidue (tensorSquareResidue A R)

/-- The first canonical inclusion into the completed local tensor square.
Source: EGA 0_I 7.7.1--7.7.7, local diagonal construction.
(blueprint: lem-sfb-formally-smooth-completed-local-tensor-square). -/
noncomputable def completedTensorLeft (A : Type u) (R : Type v)
    [CommRing A] [CommRing R] [Algebra A R] [IsLocalRing R] :
    R →+* CompletedLocalTensorSquare A R :=
  (toLocalCompletionAtResidue (tensorSquareResidue A R)).comp
    (Algebra.TensorProduct.includeLeft : R →ₐ[A] TensorProduct A R R).toRingHom

/-- The second canonical inclusion into the completed local tensor square.
Source: EGA 0_I 7.7.1--7.7.7, local diagonal construction.
(blueprint: lem-sfb-formally-smooth-completed-local-tensor-square). -/
noncomputable def completedTensorRight (A : Type u) (R : Type v)
    [CommRing A] [CommRing R] [Algebra A R] [IsLocalRing R] :
    R →+* CompletedLocalTensorSquare A R :=
  (toLocalCompletionAtResidue (tensorSquareResidue A R)).comp
    (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A R R).toRingHom

/-- The closed fibre of the local algebra, as the quotient by the extended base maximal ideal.
Source: EGA 0_I 7.7.1--7.7.7, local diagonal construction.
(blueprint: lem-sfb-formally-smooth-completed-local-tensor-square). -/
abbrev LocalClosedFiber (A : Type u) (R : Type v)
    [CommRing A] [CommRing R] [Algebra A R] [IsLocalRing A] :=
  R ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A R)

/-- The canonical residue-field algebra structure on the closed fibre.
Source: EGA 0_I 7.7.1--7.7.7, local diagonal construction.
(blueprint: lem-sfb-formally-smooth-completed-local-tensor-square). -/
noncomputable instance localClosedFiberResidueAlgebra (A : Type u) (R : Type v)
    [CommRing A] [CommRing R] [Algebra A R] [IsLocalRing A] :
    Algebra (IsLocalRing.ResidueField A) (LocalClosedFiber A R) :=
  Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map

/-- Extension of the closed fibre from the base residue field to the target residue field.
Source: EGA 0_I 7.7.1--7.7.7, local diagonal construction.
(blueprint: lem-sfb-formally-smooth-completed-local-tensor-square). -/
abbrev LocalClosedFiberTensor (A : Type u) (R : Type v)
    [CommRing A] [CommRing R] [Algebra A R] [IsLocalRing A] [IsLocalRing R]
    [IsLocalHom (algebraMap A R)] :=
  TensorProduct (IsLocalRing.ResidueField A) (LocalClosedFiber A R)
    (IsLocalRing.ResidueField R)

/-- The ideal generated by the second image of the maximal ideal of the target ring.
Source: EGA 0_I 7.7.1--7.7.7, local diagonal construction.
(blueprint: lem-sfb-formally-smooth-completed-local-tensor-square). -/
noncomputable def completedTensorSecondIdeal (A : Type u) (R : Type v)
    [CommRing A] [CommRing R] [Algebra A R] [IsLocalRing R] :
    Ideal (CompletedLocalTensorSquare A R) :=
  (IsLocalRing.maximalIdeal R).map (completedTensorRight A R)

/-- All structural, splitting, and closed-fibre assertions for the completed local tensor square.
Source: EGA 0_I 7.7.1--7.7.7 and 0_IV 19.3.5--19.3.6, with the DAG local diagonal
and closed-fibre comparison.
(blueprint: lem-sfb-formally-smooth-completed-local-tensor-square).

Proof plan from the accepted DAG split:
1. Write $S=P_{\mathfrak q}$ and $\mathfrak n=\mathfrak qS$. The ideal $H=(\mathfrak
m_R\otimes1,1\otimes\mathfrak m_R)P$ is finitely generated: take generators of $\mathfrak m_R$
in each factor. Applying tensor-quotient base change to each factor gives $P/H\cong l\otimes_k
l$. If $b_1,\ldots,b_d$ is a $k$-basis of $l$, then $1\otimes b_1,\ldots,1\otimes b_d$ span this
ring over its first $l$. A field is Noetherian (its only ideals are zero and the whole field),
so the finite-algebra Noetherian lemma makes $P/H$ Noetherian. Since $H\subset\mathfrak q$,
choose finite ideal generators of $\mathfrak q/H$ and lift them to $\mathfrak q$. Together with
the generators of $H$ they generate $\mathfrak q$: subtract the appropriate lifted combination
from any element of $\mathfrak q$ to obtain an element of $H$. Thus $\mathfrak n$ is finitely
generated. By the fraction description of localization, $S$ is local with maximal ideal
$\mathfrak n$ and $S/\mathfrak n=l$.
Dependencies: def-weil-pbc-noetherian-ring, lem-weil-pbc-tensor-quotient-base-change, lem-weil-
pbc-finite-algebra-noetherian, def-weil-pbc-localization-at-prime.
2. Apply the completion theorem for a finitely generated ideal with Noetherian quotient to
$(S,\mathfrak n)$: its hypotheses hold because $S/\mathfrak n=l$ is a field. It gives that $E$
is Noetherian and complete for $\mathfrak m=\mathfrak nE$. The completion-mod-power lemma gives,
for every $N\ge1$, the canonical compatible surjections $\pi_N:E\to S/\mathfrak n^N$ with kernel
$\mathfrak m^N$. In particular $E/\mathfrak m=l$. This application does not assume that $S$ is
Noetherian.
Dependencies: lem-weil-pbc-completion-noetherian-quotient-noetherian, lem-weil-pbc-adic-
completion-mod-power.
3. The ideal $\mathfrak m$ is the unique maximal ideal of $E$. Indeed, an element
$x\notin\mathfrak m$ has nonzero residue in $l$; each $x_N=\pi_N(x)$ is a unit in the local ring
$S/\mathfrak n^N$. Explicitly a representative of $x_N$ in $S$ lies outside $\mathfrak n$ and
hence has an inverse in $S$. The inverses $x_N^{-1}$ are compatible, since a homomorphism takes
an inverse to an inverse. They form an inverse for $x$ in $E$. Conversely no element of
$\mathfrak m$ is a unit, since its residue is zero. Thus $E$ is complete Noetherian local with
residue $l$. Under this residue identification, each composite $R\to P\to S\to E\to l$ is the
residue map of $R$; consequently $j_i^{-1}(\mathfrak m)=\mathfrak m_R$ and $j_i(\mathfrak
m_R^N)\subset\mathfrak m^N$, proving locality, continuity and the identity residue maps.
Dependencies: def-weil-pbc-localization-at-prime, def-weil-pbc-adic-completion.
4. For the first $R$-algebra structure on $P$, adic formal smoothness is preserved by base
change from $A\to R$ in the second factor. It holds for the ideal $I=(1\otimes\mathfrak m_R)P$.
To verify it on $S$ for $\mathfrak n$, take a square-zero ideal $L\subset D$, an $R$-algebra map
$g:S\to D/L$, and $N\ge1$ with $g(\mathfrak n^N)=0$. The restriction to $P$ kills $I^N$, so
base-change formal smoothness gives an $R$-algebra lift $f:P\to D$. For $t\in
P\setminus\mathfrak q$, $f(t)$ is invertible modulo $L$. Choose $b$ lifting its inverse, so
$f(t)b=1+u$ with $u\in L$; then $b(1-u)$ is an inverse since $u^2=0$. Hence the formula
$p/t\mapsto f(p)f(t)^{-1}$ defines a lift $S\to D$, reducing to $g$. It kills $\mathfrak n^{2N}$
because the image of $\mathfrak n^N$ lies in $L$. This verifies exactly the defining adic
lifting property. Interchanging the two factors repeats the argument with $I=(\mathfrak
m_R\otimes1)P$ and proves it for the second $R$-structure as well.
Dependencies: lem-weil-pbc-fs-adic-base-change, def-weil-pbc-formally-smooth-adic, def-weil-pbc-
localization-at-prime.
5. Since $\mathfrak n$ is finitely generated, preservation of adic formal smoothness by
completion applies to each of the two maps $R\to S$. It makes $E$ formally smooth over $R$ for
the $\mathfrak nE=\mathfrak m$-adic topology. Both $R$ and $E$ are Noetherian local rings and
both $j_i$ are local, as already proved, so the adic-formally-smooth local flatness lemma shows
that each $j_i$ is flat. The flat-local-homomorphism lemma then makes each $j_i$ faithfully
flat.
Dependencies: lem-weil-pbc-fs-adic-completion, lem-weil-pbc-fs-adic-local-flat, lem-weil-pbc-
flat-local-hom-faithfully-flat.
6. The tensor-pushout property gives multiplication $P\to R$, $r\otimes s\mapsto rs$. For
$t\notin\mathfrak q$ its product has nonzero residue in $l$, hence is a unit of $R$.
Multiplication therefore defines $h:S\to R$ by the fraction formula. It sends $\mathfrak n$ into
$\mathfrak m_R$, giving compatible ring maps $S/\mathfrak n^N\to R/\mathfrak m_R^N$. For
$x=(x_N)_N\in E$ their values form a compatible sequence in $\varprojlim_N R/\mathfrak m_R^N$.
Completeness of $R$ identifies that sequence with a unique element $\mu(x)\in R$. Coordinatewise
operations prove that $\mu$ is a ring map, and $\ker\pi_N=\mathfrak m^N$ shows $\mu(\mathfrak
m^N)\subset\mathfrak m_R^N$, so it is continuous. Its residue map is the identity of $l$, hence
$\mu^{-1}(\mathfrak m_R)=\mathfrak m$. On either copy of $R$ its $N$th coordinate is the
original element modulo $\mathfrak m_R^N$; separation of $R$ therefore gives $\mu j_1=\mu
j_2=\mathrm{id}_R$.
Dependencies: lem-weil-pbc-algebra-tensor-pushout-universal-property, def-weil-pbc-localization-
at-prime, def-weil-pbc-adically-complete-ring, lem-weil-pbc-adic-completion-mod-power.
7. Put $B=R/\mathfrak m_AR$ and $K=(1\otimes\mathfrak m_R)S$. Tensor-quotient base change
identifies $P/(1\otimes\mathfrak m_R)P=R\otimes_A l$. This is $F=B\otimes_k l$: the forward map
is $r\otimes a\mapsto[r]\otimes a$, and the inverse is $[r]\otimes a\mapsto r\otimes a$; the
latter is independent of the lift because $\mathfrak m_A$ annihilates $l$. Both maps respect the
balancing relations and are inverse on pure tensors. The map $P\to l$ becomes $F\to l$,
$[r]\otimes a\mapsto\bar r a$, so $\mathfrak q$ is the inverse image of $\mathfrak r$. The map
$S\to F_{\mathfrak r}$ sends $p/t$ to $\bar p/\bar t$ and kills $K$. Conversely $\bar p/\bar
t\mapsto(p/t)\bmod K$ defines its inverse from $F_{\mathfrak r}$ to $S/K$: a lift $t$ of $\bar
t\notin\mathfrak r$ lies outside $\mathfrak q$, and changing either lift by the quotient ideal
changes the fraction by $K$. Thus $S/K\cong F_{\mathfrak r}$, taking $(\mathfrak n+K)/K$ to its
maximal ideal.
Dependencies: lem-weil-pbc-tensor-quotient-base-change, lem-weil-pbc-algebra-tensor-pushout-
universal-property, def-weil-pbc-localization-at-prime.
8. For $N\ge1$ write $K_N=(K+\mathfrak n^N)/\mathfrak n^N$. There are compatible short exact
sequences of $S$-modules $0\to K_N\to S/\mathfrak n^N\to S/(K+\mathfrak n^N)\to0$. The maps
$K_{N+1}\to K_N$ are surjective: represent an element by $k\in K$ and use that same $k$ at level
$N+1$. Inverse-limit exactness for towers with surjective kernel transitions therefore gives a
surjective ring map $\theta:E\to\varprojlim_N S/(K+\mathfrak n^N)$. By the quotient
identification in the previous step, the target is precisely the maximal-ideal-adic completion
of $F_{\mathfrak r}$.
Dependencies: lem-weil-pbc-tower-limit-exact-surjective-kernels, def-weil-pbc-adic-completion.
9. The ideal $J$ of the statement is $KE$. Under $E/\mathfrak m^N\cong S/\mathfrak n^N$, its
image is exactly $K_N$: a sum of products of generators from $K$ and coefficients of $E$ reduces
to one from $S$ because $E\to S/\mathfrak n^N$ is surjective; conversely every $k\in K$ is an
image from $J$. Hence $\ker\theta=\bigcap_{N\ge1}(J+\mathfrak m^N)$. Apply Krull intersection to
the Noetherian ring $E$, the ideal $\mathfrak m$ contained in its Jacobson radical, and the
cyclic $E$-module $E/J$. It gives $\bigcap_N\mathfrak m^N(E/J)=0$, so $\ker\theta=J$. The
resulting ring isomorphism $E/J\cong\widehat{F_{\mathfrak r}}$ sends the class of $j_1(r)$ at
level $N$ to the class of $[r]\otimes1$ modulo the $N$th power of the maximal ideal. It is
therefore canonical and compatible with the map from $B$ claimed in the statement.
Dependencies: lem-weil-pbc-adic-completion-mod-power, lem-weil-pbc-krull-intersection-jacobson.
10. The quotient $B$ of $R$ is Noetherian by the surjective-image lemma; it is local with
maximal ideal $\mathfrak m_B=\mathfrak m_R/\mathfrak m_AR$ (units lift from the local ring $R$)
and residue $l$. The basis $b_1,\ldots,b_d$ of $l/k$ makes $1\otimes b_1,\ldots,1\otimes b_d$ a
finite spanning set for $F=B\otimes_k l$ over $B$. Thus $F$ is Noetherian by the finite-algebra
lemma and $F_{\mathfrak r}$ is Noetherian by the localization lemma. Moreover the composite
$B\to F\to l$ is the residue map of $B$, so the inverse image of $\mathfrak r$ in $B$ is exactly
$\mathfrak m_B$.
Dependencies: lem-weil-pbc-surjective-image-noetherian, lem-weil-pbc-finite-algebra-noetherian,
lem-weil-pbc-localization-noetherian.
11. The field-extension-base-change lemma makes $B\to F=B\otimes_k l$ faithfully flat, in
particular flat. Localizing at $\mathfrak r$, whose contraction is $\mathfrak m_B$, gives a flat
local map $B=B_{\mathfrak m_B}\to F_{\mathfrak r}$. Since $F_{\mathfrak r}$ is Noetherian local,
its completion map is faithfully flat, in particular flat. Composition of flat ring maps
therefore makes $B\to\widehat{F_{\mathfrak r}}$ flat. This composite is local: its residue map
is $B\to l$ by the explicit finite-quotient maps above. Equivalently, via $\theta$, the target
is $E/J$, which is local because $J\subset\mathfrak m$, and its maximal ideal contracts to
$\mathfrak m_B$. The flat-local-homomorphism lemma proves faithful flatness. The compatible
isomorphism of step 9 identifies this map with the map $R/\mathfrak m_AR\to E/J$ induced by
$j_1$, completing all clauses.
Dependencies: lem-weil-pbc-field-extension-base-change-faithfully-flat, def-weil-pbc-faithfully-
flat-ring-map, lem-weil-pbc-flat-local-ring-maps, lem-weil-pbc-local-completion-faithfully-flat,
lem-weil-pbc-flat-ring-map-comp, lem-weil-pbc-flat-local-hom-faithfully-flat.
-/
theorem formallySmoothAdic_completedLocalTensorSquare
    (A : Type u) (R : Type v) [CommRing A] [CommRing R] [Algebra A R]
    [IsNoetherianRing A] [IsNoetherianRing R] [IsLocalRing A] [IsLocalRing R]
    [IsLocalHom (algebraMap A R)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField R)]
    (hfs : Algebra.FormallySmoothAdic A R (IsLocalRing.maximalIdeal R)) :
    IsNoetherianRing (CompletedLocalTensorSquare A R) ∧
    ∃ (_ : IsLocalRing (CompletedLocalTensorSquare A R)),
      IsAdicComplete (IsLocalRing.maximalIdeal (CompletedLocalTensorSquare A R))
        (CompletedLocalTensorSquare A R) ∧
      ∃ ρ : CompletedLocalTensorSquare A R →+* IsLocalRing.ResidueField R,
        Function.Surjective ρ ∧
        RingHom.ker ρ = IsLocalRing.maximalIdeal (CompletedLocalTensorSquare A R) ∧
        (∀ j : R →+* CompletedLocalTensorSquare A R,
          (j = completedTensorLeft A R ∨ j = completedTensorRight A R) →
          IsLocalHom j ∧ ρ.comp j = IsLocalRing.residue R ∧ j.FaithfullyFlat ∧
          @Algebra.FormallySmoothAdic R (CompletedLocalTensorSquare A R) _ _ j.toAlgebra
            (IsLocalRing.maximalIdeal (CompletedLocalTensorSquare A R))) ∧
        (∃ μ : CompletedLocalTensorSquare A R →+* R,
          @Continuous _ _
            (IsLocalRing.maximalIdeal (CompletedLocalTensorSquare A R)).adicTopology
            (IsLocalRing.maximalIdeal R).adicTopology μ ∧
          IsLocalHom μ ∧
          μ.comp (toLocalCompletionAtResidue (tensorSquareResidue A R)) =
            (Algebra.TensorProduct.lmul' A).toRingHom ∧
          μ.comp (completedTensorLeft A R) = RingHom.id R ∧
          μ.comp (completedTensorRight A R) = RingHom.id R) ∧
        ∃ β : LocalClosedFiber A R →+*
            CompletedLocalTensorSquare A R ⧸ completedTensorSecondIdeal A R,
          (∀ r : R, β (Ideal.Quotient.mk _ r) =
            Ideal.Quotient.mk _ (completedTensorLeft A R r)) ∧
          β.FaithfullyFlat ∧
          ∃ ε : LocalClosedFiberTensor A R →+* IsLocalRing.ResidueField R,
            (∀ (r : R) (a : IsLocalRing.ResidueField R),
              ε (TensorProduct.tmul (IsLocalRing.ResidueField A)
                (Ideal.Quotient.mk _ r) a) = IsLocalRing.residue R r * a) ∧
            ∃ e : (CompletedLocalTensorSquare A R ⧸ completedTensorSecondIdeal A R) ≃+*
                LocalCompletionAtResidue ε,
              ∀ r s : R,
                e (Ideal.Quotient.mk _
                  (completedTensorLeft A R r * completedTensorRight A R s)) =
                toLocalCompletionAtResidue ε
                  (TensorProduct.tmul (IsLocalRing.ResidueField A)
                    (Ideal.Quotient.mk _ r) (IsLocalRing.residue R s)) := by
  sorry

end RingTheory
