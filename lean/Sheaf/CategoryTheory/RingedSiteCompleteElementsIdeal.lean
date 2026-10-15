/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.CategoryTheory.RingedSiteCompleteElement
public import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Vanishing localizations form a sheaf of ideals

Source: Stacks Project, algebraization.tex, Tags 0998 and 0997
(blueprint: lem-weil-pbc-ringed-derived-complete-elements-ideal).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

set_option autoImplicit false

namespace CategoryTheory

/-- The sections whose localization has zero derived internal Hom into K form a sheaf
of ideals. The first clause identifies every ideal section with the actual Hom-vanishing
criterion. Ideals encode zero, addition, and multiplication by arbitrary sections. The
next clauses express restriction and descent for every covering sieve. The final clause
is the locally finite-generated ideal consequence, using local finite-span membership.

Source: Stacks Project, algebraization.tex, Tags 0998 and 0997
(blueprint: lem-weil-pbc-ringed-derived-complete-elements-ideal).

Proof (the six steps of the node):
1. On the slice over $U$, write $F_f=R\mathcal Hom_{\mathcal O_U}(\mathcal O_U[1/f],K|_U)$.
   Localization at zero is the zero module, so $F_0=0$ by the Hom-complex formula. Thus $0\in
   S_K(U)$.
2. For $f\in S_K(U)$ and $a\in\mathcal O(U)$ apply the localization internal-Hom identity with
   $P=\mathcal O_U[1/f]$ and localizing section $a$. It gives $F_{af}\cong R\mathcal
   Hom_{\mathcal O_U}(\mathcal O_U[1/a],F_f)=0$. This also applies when either section is zero;
   in particular $a=-1$ proves closure under negatives.
3. For $f,g\in S_K(U)$ put $h=f+g$. For each $V\to U$ take $R=\mathcal O(V)[1/h]$. The images of
   $f,g$ generate its unit ideal because $f/h+g/h=1$. The standard-covering gluing statement
   gives injectivity and middle exactness of $0\to R\to R[1/f]\oplus R[1/g]\to R[1/(fg)]$, with
   diagonal and difference maps. For surjectivity, represent an element of the last term as
   $z/(fg)^n$, increasing $n$ to be positive. The binomial expansion of $(f/h+g/h)^{2n-1}=1$
   gives $u f^n+v g^n=1$ for some $u,v\in R$. The pair $(vz/f^n,-uz/g^n)$ maps to $z/(fg)^n$.
   Sheafifying this sectionwise exact sequence gives $0\to\mathcal O_U[1/h]\to\mathcal
   O_U[1/(fh)]\oplus\mathcal O_U[1/(gh)]\to\mathcal O_U[1/(fgh)]\to0$; iterated localization
   agrees with localization at the product by its universal property.
4. Write $A=\mathcal O_U[1/h]$, $B=\mathcal O_U[1/(fh)]\oplus\mathcal O_U[1/(gh)]$, $D=\mathcal
   O_U[1/(fgh)]$, and let $i:A\to B$ be the injection of step 3. In degree-zero complexes its
   cone $T=C(i)$ is $A\xrightarrow{i}B$ in degrees $-1,0$. The projection $T\to D[0]$ is a
   quasi-isomorphism: its degree $-1$ cohomology is $\ker i=0$, and its degree $0$ cohomology is
   $\operatorname{coker}i=D$. Choose a K-injective representative $I^\bullet$ of $K|_U$, and
   write $H(X)=\mathcal Hom^\bullet(X,I^\bullet)$. The quasi-isomorphism clause of the derived
   internal-Hom definition gives a quasi-isomorphism $H(D)\to H(T)$. Step 2 gives
   $F_{fh}=F_{gh}=F_{fgh}=0$ (multipliers $h,h,gh$ respectively), so $H(T)$ and $H(B)=H(\mathcal
   O_U[1/(fh)])\oplus H(\mathcal O_U[1/(gh)])$ are acyclic. The degreewise split sequence $0\to
   B\to T\to A[1]\to0$ gives $0\to H(A[1])\to H(T)\to H(B)\to0$, also degreewise split:
   restriction to the graded summand $B$ is surjective, with kernel the maps factoring through
   the graded quotient $A[1]$, and the Hom differential preserves this kernel. Its kernel is
   acyclic by the following local boundary chase. For a closed local section $x$ of the kernel,
   acyclicity of $H(T)$ gives locally $y$ with $dy=x$; its image $\bar y$ is closed in $H(B)$,
   so locally $\bar y=dz$. Lift $z$ using the degreewise splitting; then $y-d\widetilde z$ lies
   in the kernel and has differential $x$. Thus $H(A[1])$ has zero cohomology sheaves. Its
   degree $n$ term is $\mathcal Hom(A,I^{n-1})$, with the differential of $I$, so its cohomology
   is that of $H(A)$ shifted by one degree. Therefore $F_h=0$ and $f+g\in S_K(U)$.
5. For any arrow $V\to U$, the restriction identity for localization internal Hom gives
   $F_f|_V\cong F_{f|_V}$. Hence membership is preserved by restriction. Conversely, suppose
   $f|_{U_i}\in S_K(U_i)$ for a covering family of $U$. Then $F_f|_{U_i}=0$ for all $i$. Slice
   restriction is evaluation of module sheaves on objects lying over $U_i$, so preserves kernels
   and the locally defined images; it therefore commutes with cohomology. Every cohomology sheaf
   of $F_f$ restricts to zero on the cover. A section of such a sheaf over any $V\to U$ vanishes
   on the pulled-back covering sieve and is zero by the uniqueness axiom for a sheaf. Thus all
   cohomology sheaves vanish, the representative complex is quasi-isomorphic to zero, and
   $F_f=0$. A compatible family in $S_K$ glues uniquely in $\mathcal O$, and this local
   criterion puts its glued section in $S_K$. Together with steps 1--4 this proves that $S_K$ is
   a sheaf of ideals.
6. On a slice where $b_1,\ldots,b_r$ generate the ideal sheaf and belong to $S_K$, a section of
   the generated ideal is locally a finite sum $\sum_i a_i b_i$. Step 2 puts each summand in
   $S_K$, and repeated application of step 4 puts the sum in $S_K$. Step 5 glues the local
   membership. For $r=0$ the generated ideal is zero and step 1 applies.
-/
theorem ringedSite_complete_elements_ideal
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))]
    (K : DerivedCategory (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) :
    ∃ I : ∀ U : C, Ideal (R.obj.obj (op U)),
      (∀ (U : C) (f : R.obj.obj (op U)),
        f ∈ I U ↔ IsRingedSiteCompleteElement J R K U f) ∧
      (∀ (U V : C) (a : V ⟶ U) (f : R.obj.obj (op U)),
        f ∈ I U → R.obj.map a.op f ∈ I V) ∧
      (∀ (U : C) (S : Sieve U), S ∈ J U → ∀ f : R.obj.obj (op U),
        (∀ (V : C) (a : V ⟶ U), S a → R.obj.map a.op f ∈ I V) → f ∈ I U) ∧
      (∀ (U : C) (S : Sieve U), S ∈ J U → ∀ x : R.obj.obj (op U),
        (∀ (V : C) (a : V ⟶ U), S a →
          ∃ (r : ℕ) (b : Fin r → R.obj.obj (op V)),
            (∀ i : Fin r, IsRingedSiteCompleteElement J R K V (b i)) ∧
            R.obj.map a.op x ∈ Ideal.span (Set.range b)) →
        IsRingedSiteCompleteElement J R K U x) := by
  sorry

end CategoryTheory
