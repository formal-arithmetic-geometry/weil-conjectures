/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.DgAbcData

/-!
# Concrete cone comparisons and homotopy invariance

Source: Stacks Project, `dga.tex`, Tags 09P7, 09QT and 09QU
(blueprint: lem-coef-dg-abc-cone-homotopy).

The theorem records the explicit comparison maps for admissible sequences and cones,
and the cone map induced by a homotopy-commutative square. Equalities of H⁰ classes
are rendered by witnesses in degree `-1`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace CategoryTheory.IntegralDGCategory.ABC

/-- The canonical degree-zero composite in an integral dg category.
Source: Stacks Project, `dga.tex`, Tags 09P7 and 09QU
(blueprint: lem-coef-dg-abc-cone-homotopy). -/
def compZero {A : IntegralDGCategory.{u, v}} {x y z : A.Obj}
    (b : (A.hom y z).X 0) (a : (A.hom x y).X 0) : (A.hom x z).X 0 :=
  (A.hom x z).XIsoOfEq (by omega : (0 : ℤ) + 0 = 0) |>.hom (A.comp 0 0 b a)

/-- Concrete cone comparisons and their homotopy invariance.
Source: Stacks Project, `dga.tex`, Tags 09P7, 09QT and 09QU
(blueprint: lem-coef-dg-abc-cone-homotopy).

Proof step 1. Use the dg-category definition recalled in the statement. For homogeneous maps,
$\partial(vu)=(\partial v)u+(-1)^{|v|}v\partial u$. In particular, for closed degree-zero $a,b$
and degree-minus-one $h$, $b\partial h=\partial(bh)$ and $(\partial h)a=\partial(ha)$. Boundaries
therefore form an ideal among closed degree-zero maps; all subsequent equalities of homotopy
classes can be multiplied and added. A closed map is a homotopy equivalence exactly when its
class has an inverse, by the definition in the statement.
(Source: Tag 09P6, dg Leibniz calculations; Tag 09QT, passage to homotopy classes.)

Proof step 2. For any admissible sequence $(a,b,\pi,s)$ put $D=\pi\partial s\in\mathcal
A(z,x)^1$, the unshifted version of its boundary $\delta$. Differentiating $\pi a=1$ and $bs=1$
gives $(\partial\pi)a=0$ and $b\partial s=0$. Insert $a\pi+sb=1$ to obtain $\partial s=aD$ and,
using $\partial(\pi s)=0$, $\partial\pi=(\partial\pi)sb=-Db$. Finally $a\partial
D=\partial(aD)=\partial^2s=0$, so $\partial D=\pi a\partial D=0$. These identities require only
the displayed splitting equations, not closed splittings. (Source: Tag 09P6, identities (1)-(7).)

Proof step 3. For a chosen cone of $f:x\to y$, write its splitting as $(\rho,\sigma)$ and its
arrows as $(i,p)$. In computations only, use (B) to suppress the source shift in $\sigma:x[1]\to
c(f)$ and the target shift in $p:c(f)\to x[1]$. Denote the resulting maps by $S\in\mathcal
A(x,c(f))^{-1}$ and $P\in\mathcal A(c(f),x)^1$. Composition compatibility gives $\rho i=1$,
$PS=1$, $i\rho+SP=1$, $Pi=0$, $\rho S=0$. Since the boundary is $f[1]$, the identities of step 2
give $\partial S=if$, $\partial\rho=-fP$, $\partial P=0$. Here source shift identifies $\mathcal
A(x[1],c(f))^r$ with $\mathcal A(x,c(f))^{r-1}$, while target shift identifies $\mathcal
A(c(f),x[1])^r$ with $\mathcal A(c(f),x)^{r+1}$; the target-shift differential has the minus
sign stipulated in (B). Thus these formulas keep the Koszul signs and apply to the actual chosen
cone. (Source: Tag 09P7, cone splitting identities; Tag 09QU, proof (1).)

Proof step 4. For (i) specialize step 3 to $f=a$ and retain $D$ from step 2. The maps in the
statement are $e=b\rho$ and $t=is-SD$ in this unshifted notation. Their differentials are
$\partial e=-baP=0$ and $\partial t=i\partial s-(\partial S)D+S\partial D=iaD-iaD=0$. The
splitting identities also give $et=b\rho(is-SD)=bs=1_z$ and $ei=b$.
(Source: Tag 09QU, proof (1), construction and closedness of the comparison maps.)

Proof step 5. Set $H=-S\pi\rho$, a degree-minus-one endomorphism of $c(a)$. By steps 2-3,
$\partial H=-ia\pi\rho-SDb\rho-SP$. On the other hand $te-1=isb\rho-SDb\rho-i\rho-SP=
-ia\pi\rho-SDb\rho-SP$, since $sb=1-a\pi$. Hence $te-1=\partial H$. Moreover
$\partial(\pi\rho)=-Db\rho-P$, so $De+P=-\partial(\pi\rho)$. Under the target-shift isomorphism
(B) this last equality says $[\delta e]=[-p]$: multiplication by the minus sign on the shifted
differential does not change the subgroup of boundaries. Together with $ei=b$ and the homotopy
inverse $t$, this proves the diagram isomorphism in (i).
(Source: Tag 09QU, proof (1), the identity $1=fe+d(\sigma\pi p)$ and the final square.)

Proof step 6. For (ii) choose splittings $(\rho_k,\sigma_k)$ of the two chosen cones, and use
$S_k,P_k$ as in step 3. Define $c=i_2b\rho_1+S_2aP_1+i_2hP_1$. Every summand has degree zero, and
$\partial c=-i_2bf_1P_1+i_2f_2aP_1+i_2(bf_1-f_2a)P_1=0$. Multiplication by the splitting maps
gives $ci_1=i_2b$ and $P_2c=aP_1$ strictly. Restoring the shifts gives $p_2c=a[1]p_1$ strictly,
hence both required equalities of classes. This constructs the cone map for any homotopy square,
including the inverse square used below. (Source: Tag 09P7, proof, the explicit cone map.)

Proof step 7. Here is the elementary null-product calculation needed to show that this cone map
is invertible; keep the shifts on the cone arrows in this step. Let $v$ be a closed degree-zero
endomorphism of any chosen cone $(i,p,\rho,\sigma)$ such that $[vi]=0$ and $[pv]=0$. Choose
degree-minus-one $k,l$ with $vi=\partial k$ and $pv=\partial l$. Set $K=k\rho$, $L=\sigma l$,
$v_L=v-\partial K$ and $v_R=v-\partial L$. Then $v_Li=0$ and $pv_R=0$, since $\rho i=1$,
$p\sigma=1$, and $i,p$ are closed. Thus $v_Lv_R=v_L(i\rho+\sigma p)v_R=0$. The Leibniz identity
gives $v^2=v^2-v_Lv_R=\partial(Kv+v_LL)$, since $v,v_L$ are closed. Consequently, if $u$ is a
closed cone endomorphism with $[ui]=[i]$, $[pu]=[p]$, take $v=u-1$: its class has square zero,
and $[2-u]=[1-v]$ is a two-sided inverse of $[u]=[1+v]$.
(Source: Tag 09QP, null-product computation; Tag 09QT, square-zero argument.)

Proof step 8. Assume now that $a,b$ are homotopy equivalences and choose closed homotopy inverses
$a',b'$. Since $[b][f_1]=[f_2][a]$, multiplication by their inverse classes gives
$[b'][f_2]=[f_1][a']$. The closed difference $b'f_2-f_1a'$ is therefore a boundary, so choose
$h'$ of degree minus one with that differential. Step 6 applied to this square gives a closed
$c':c(f_2)\to c(f_1)$ with $[c'i_2]=[i_1b']$ and $[p_1c']=[a'[1]p_2]$. Hence $u=c'c$ satisfies
$[ui_1]=[i_1]$ and $[p_1u]=[p_1]$; likewise $w=cc'$ satisfies $[wi_2]=[i_2]$ and
$[p_2w]=[p_2]$. The shift is a dg functor, so it preserves the inverse equations on classes.
(Source: Tag 09QT, inverse square and the two composite endomorphisms.)

Proof step 9. By step 7 both $[c'c]$ and $[cc']$ are invertible. Thus $([c'c])^{-1}[c']$ is a
left inverse of $[c]$, and $[c']([cc'])^{-1}$ is a right inverse. They agree: if $L[c]=1$ and
$[c]R=1$ then $L=L([c]R)=(L[c])R=R$. Each class has a closed representative; its two inverse
equations mean precisely that both composites differ from the identities by degree-minus-one
boundaries. Therefore $c$ is a homotopy equivalence. Every construction used only the stipulated
splittings, the dg Leibniz identity and (B),(C), so no triangulated-category axiom or special
model of a cone has entered. (Source: Tag 09QT, conclusion from the two composite isomorphisms.)

In the Lean statement each equality of $H^0$ classes is rendered by an explicit degree `-1`
witness, and each homotopy equivalence by a closed inverse with two such witnesses. -/
theorem dg_abc_cone_homotopy (A : IntegralDGCategory.{u, v}) (S : Shifts A)
    (hA : AxiomA A)
    (hC : ∀ (x y : A.Obj) (f : Closed A x y), Nonempty (Cone S f)) :
    (∀ (x y z : A.Obj) (E : Admissible A x y z)
      (δ : Closed A z (S.obj 1 x))
      (hδ : HEq ((S.homShift 1 z x).hom.f 0 δ.val) (boundary E))
      (K : Cone S E.a),
      ∃ (e : Closed A K.obj z) (t : Closed A z K.obj) (H : (A.hom K.obj K.obj).X (-1)),
        e.val = compZero E.b.val K.sequence.π ∧
        t.val = compZero K.sequence.a.val E.s -
          compZero K.sequence.s δ.val ∧
        compZero e.val t.val = A.unit z ∧
        compZero t.val e.val - A.unit K.obj =
          (A.hom K.obj K.obj).d (-1) 0 H ∧
        compZero e.val K.sequence.a.val = E.b.val ∧
        ∃ (J : (A.hom K.obj (S.obj 1 x)).X (-1)),
          (A.hom K.obj (S.obj 1 x)).d (-1) 0 J =
            compZero δ.val e.val + K.sequence.b.val) ∧
    (∀ (x₁ x₂ y₁ y₂ : A.Obj)
      (f₁ : Closed A x₁ y₁) (f₂ : Closed A x₂ y₂)
      (a : Closed A x₁ x₂) (b : Closed A y₁ y₂)
      (h : (A.hom x₁ y₂).X (-1)),
      (A.hom x₁ y₂).d (-1) 0 h =
        compZero b.val f₁.val - compZero f₂.val a.val →
      ∀ (K₁ : Cone S f₁) (K₂ : Cone S f₂),
      ∃ (c : Closed A K₁.obj K₂.obj),
        (∃ (H₁ : (A.hom y₁ K₂.obj).X (-1)),
          (A.hom y₁ K₂.obj).d (-1) 0 H₁ =
            compZero c.val K₁.sequence.a.val -
              compZero K₂.sequence.a.val b.val) ∧
        (∃ (H₂ : (A.hom K₁.obj (S.obj 1 x₂)).X (-1)),
          (A.hom K₁.obj (S.obj 1 x₂)).d (-1) 0 H₂ =
            compZero K₂.sequence.b.val c.val -
              compZero ((S.map 1 x₁ x₂).f 0 a.val) K₁.sequence.b.val) ∧
        (((∃ (a' : Closed A x₂ x₁) (U : (A.hom x₁ x₁).X (-1))
            (V : (A.hom x₂ x₂).X (-1)),
            (A.hom x₂ x₁).d 0 1 a'.val = 0 ∧
            (A.hom x₁ x₁).d (-1) 0 U =
              compZero a'.val a.val - A.unit x₁ ∧
            (A.hom x₂ x₂).d (-1) 0 V =
              compZero a.val a'.val - A.unit x₂) ∧
          (∃ (b' : Closed A y₂ y₁) (U : (A.hom y₁ y₁).X (-1))
            (V : (A.hom y₂ y₂).X (-1)),
            (A.hom y₂ y₁).d 0 1 b'.val = 0 ∧
            (A.hom y₁ y₁).d (-1) 0 U =
              compZero b'.val b.val - A.unit y₁ ∧
            (A.hom y₂ y₂).d (-1) 0 V =
              compZero b.val b'.val - A.unit y₂)) →
          ∃ (c' : Closed A K₂.obj K₁.obj) (U : (A.hom K₁.obj K₁.obj).X (-1))
            (V : (A.hom K₂.obj K₂.obj).X (-1)),
            (A.hom K₂.obj K₁.obj).d 0 1 c'.val = 0 ∧
            (A.hom K₁.obj K₁.obj).d (-1) 0 U =
              compZero c'.val c.val - A.unit K₁.obj ∧
            (A.hom K₂.obj K₂.obj).d (-1) 0 V =
              compZero c.val c'.val - A.unit K₂.obj)) := by
  sorry

end CategoryTheory.IntegralDGCategory.ABC
