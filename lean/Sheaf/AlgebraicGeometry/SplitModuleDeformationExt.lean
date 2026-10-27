module

public import Sheaf.AlgebraicGeometry.MarkedSplitModuleDeformations
public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.RingTheory.RingHom.Flat
import Sheaf.CategoryTheory.ExtOneExtensionClassification
import Sheaf.CategoryTheory.YonedaDerivedExtComparison
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Sheaf.RingTheory.FlatModuleFibreProductPatching
import Mathlib.RingTheory.Etale.Field
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # Split module deformations and derived Ext

Source: Stacks Project, defos.tex, Tags 08VW and 0CYE; quot.tex, Tag 08W8;
more-algebra.tex, Tag 0D2I (blueprint: lem-sfb-space-module-split-deformation-ext).
The equivalences preserve the geometric operations explicitly. This states linearity
without requiring an independently chosen vector-space structure on deformation classes.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace.SplitModule

/-- Marked flat lifts over the dual numbers and infinitesimal automorphisms of the trivial
lift are naturally identified with degree-one and degree-zero derived Ext. Origin,
scalar pullback, unique gluing followed by the addition map, and composition are all
specified below. Naturality is relabelling the fixed module by any isomorphism.
There is no quasi-coherence, finiteness, Noetherian, or properness assumption.

Source: Stacks Project, defos.tex, Tags 08VW and 0CYE; quot.tex, Tag 08W8;
more-algebra.tex, Tag 0D2I (blueprint: lem-sfb-space-module-split-deformation-ext).

Proof:
1. Apply [lem-sfb-space-first-order-ringed-description] to the square-zero inclusion $X\subset
X_D$. Identify their small etale sites by reduction. Its inverse sends a chart $U\to X$ to
$U_D=U\times_k\operatorname{Spec}D\to X_D$, etale by
[lem-trf-space-fibre-products-etale-covers]. On an affine chart with ring $A$, the structure
ring is $A\otimes_kD=A\oplus\epsilon A$, with $(a,b)(c,d)=(ac,ad+bc)$. These formulas commute
with restriction and therefore identify the transported structure sheaf with $\mathcal
O_X\oplus\epsilon\mathcal O_X$. Thus a module on $X_D$ is an $\mathcal O_X$-module $E$ with an
$\mathcal O_X$-linear endomorphism $t$, $t^2=0$, representing multiplication by $\epsilon$;
reduction is $E/tE$. The same calculation for the base gives geometric local rings
$K[\epsilon]$, with $K$ a field: an affine etale $k$-algebra is a finite product of finite
separable fields by [lem-weil-pbc-etale-algebra-over-field-product], and a pointed neighbourhood
selects a field factor; the filtered colimit of these fields is $K$. Hence the flatness in the
statement is flatness over these $K[\epsilon]$, not a quasi-coherence test. The stalk
construction and its exactness are [lem-sfb-space-etale-conservative-geometric-points].

2. For a $K[\epsilon]$-module $V$, the canonical map $(\epsilon)\otimes_{K[\epsilon]}V\to V$
identifies with $V/\epsilon V\to V$, $\bar v\mapsto\epsilon v$. Indeed $(\epsilon)\cong K$ as
quotient-ring modules, and [lem-weil-pbc-tensor-over-quotient-ring] gives this tensor
identification. If $V$ is flat the map is injective by the definition of flatness, applied to
$(\epsilon)\hookrightarrow K[\epsilon]$. Conversely, if it is injective, $V/\epsilon V$ is flat
over $K$ by [lem-weil-pbc-module-over-field-flat], and [lem-sfb-nilpotent-ideal-module-flatness]
applies with $I=(\epsilon)$ and $I^2=0$. Thus flatness is equivalent to $\ker(\epsilon:V\to
V)=\epsilon V$. Apply this at every geometric point of $X$ and use
[lem-sfb-space-etale-conservative-geometric-points] to conclude that $E$ represents a flat lift
precisely when $E/tE\to tE$, $\bar e\mapsto t(e)$, is an isomorphism of module sheaves. No
finite presentation is used.

3. Given a marked flat lift, let $q:E\twoheadrightarrow M$ be its reduction followed by the
marking. Define $i:M\to E$ by $i(m)=t(e)$ for any local lift $e$ of $m$. This is independent of
the lift since $t^2=0$, and local formulas glue. Step 2 says that $i$ identifies $M$ with $tE$,
so $0\to M\xrightarrow{i}E\xrightarrow{q}M\to0$ is exact and $t=iq$. Conversely, for any such
short exact sequence define $t=iq$. Then $t^2=0$, $tE=i(M)=\ker q$, and the induced $E/tE\to tE$
is $i$ under the quotient identification with $M$. Step 2 proves flatness. These constructions
are inverse: the original $t$, quotient marking, and injection are recovered. A marked module
isomorphism commutes with $t$ and $q$, hence also with $i$; an isomorphism of the extensions
commutes with $i,q$, hence with $t=iq$. Thus this is a bijection on the required isomorphism
classes, not merely on underlying modules.

4. The module category is abelian by [def-weil-sheaf-of-modules-category]. Apply
[lem-weil-pbc-ext-one-extension-classification] in this category with $P=Q=M$ to the exact
sequences of step 3. This gives the asserted bijection to the degree-one Hom group in the
derived category, with both endpoints fixed. The trivial lift is $\mathcal
O_{X_D}\otimes_{\mathcal O_X}M=M\oplus M$, with $t(m,n)=(0,m)$, $i(n)=(0,n)$, and $q(m,n)=m$.
Its extension is split. By [lem-coef-yoneda-derived-ext-comparison] this is the zero Ext class.
This constructs the pointed identification without making a choice of a point in a torsor.

5. For $a\in k$, pullback along $\epsilon\mapsto a\epsilon$ has the following explicit
presentation as an $\mathcal O_X$-module: $$E_a=(E\oplus M)/\{(i(m),-am):m\in M\},\quad
q_a[e,m]=q(e),\quad i_a(m)=[0,m].$$ The tensor isomorphism sends $e\otimes1$ to $[e,0]$ and
$e\otimes\epsilon$ to $[0,q(e)]$. Its inverse sends $[e,m]$ to $e\otimes1+\widetilde
m\otimes\epsilon$, where $q(\widetilde m)=m$ locally. This is independent of the lift because
$i(n)\otimes\epsilon=0$; that relation follows by multiplying $i(n)\otimes1=a\widetilde
n\otimes\epsilon$ by $\epsilon$. These formulas respect the tensor relations in both directions.
The map $i_a$ is injective: a relation with first coordinate zero has $i(m)=0$, hence $m=0$.
Also $\ker q_a=\operatorname{im}i_a$ since $[i(n),m]=[0,an+m]$. Multiplication by the new
$\epsilon$ is $i_aq_a$, so step 2 proves flatness, including $a=0$. This exact sequence is the
pushout of the old extension along $a\,\mathrm{id}_M$. Naturality in the second variable in
[lem-coef-yoneda-derived-ext-comparison], and the postcomposition formula in [def-pc-ext], show
that its class is $a$ times the old class. This proves the scalar assertion without using
obstruction functoriality as a theorem about tangent classes.

6. Let the two lifts correspond to $(E_1,i_1,q_1)$ and $(E_2,i_2,q_2)$. Put
$R=D\times_kD=k\oplus k\epsilon_1\oplus k\epsilon_2$, with all products of the $\epsilon_j$
zero. Reduction identifies the small etale sites of $X_R$ and $X$ as in step 1. On this site
form $P=E_1\times_M E_2$. It is an $\mathcal O_X\otimes_kR$-module by coordinatewise
multiplication. Its projections are locally surjective. The kernel of $P\to E_1$ is
$\{(0,i_2m)\}$ and is precisely $\epsilon_2P$; the analogous kernel for the other projection is
$\epsilon_1P$. Hence its two tensor restrictions are the given marked modules. At a geometric
point the base rings are $K[\epsilon_1,\epsilon_2]/(\epsilon_1,\epsilon_2)^2=K[\epsilon]\times_K
K[\epsilon]$, and the stalk of $P$ is the fibre product of the two stalks by
[lem-sfb-space-etale-conservative-geometric-points]. Both factors are flat over $K[\epsilon]$.
Apply the flatness assertion of [lem-sfb-flat-module-fibre-product-patching] with $A=K$,
$A'=B=K[\epsilon]$ and the marking as $\varphi$. Thus $P$ is a flat gluing over
$\operatorname{Spec}R$.

7. For any other flat gluing $L$ with its specified identifications on the two copies of $D$,
the tensor unit maps give a canonical marked map $L\to E_1\times_M E_2=P$. At each geometric
point this map is the reconstruction isomorphism of
[lem-sfb-flat-module-fibre-product-patching], part (2), for the same rings as in step 6. By
[lem-sfb-space-etale-conservative-geometric-points] the sheaf map is an isomorphism. Its formula
uses only the restriction maps and the given marking, so compatible marked isomorphisms of
either input induce the corresponding isomorphism of gluings. This proves existence and
uniqueness up to marked isomorphism in the sense needed for the addition operation.

8. The ring map $R\to D$, $(a+b\epsilon,a+c\epsilon)\mapsto a+(b+c)\epsilon$, is surjective with
kernel generated by $\epsilon_1-\epsilon_2$. Consequently the tensor pullback of $P$ is
$$Q=P/\{(i_1(m),-i_2(m)):m\in M\}.$$ Here $(\epsilon_1-\epsilon_2)(e_1,e_2)=(i_1(m),-i_2(m))$
for $m=q_1(e_1)=q_2(e_2)$, and every $m$ has such local lifts. The quotient map to $M$ has
kernel $(M\oplus M)/\{(m,-m)\}\cong M$, identified by addition. Multiplication by the new
$\epsilon$ is injection after quotient: $[(e_1,e_2)]\mapsto[(i_1(m),0)]=[(0,i_2(m))]$. Thus step
2 again proves flatness. The resulting extension is the pullback of $E_1\oplus E_2$ along the
diagonal on the quotient, followed by pushout along addition on the kernel. This is exactly the
Baer sum in [lem-coef-yoneda-derived-ext-comparison], whose class is the sum of the two classes.
All formulas hold in characteristic two as well. Hence the prescribed addition and scalar
operations make the pointed bijection of step 4 $k$-linear; their vector-space identities follow
from the bijection.

9. For the trivial lift $E=M\oplus M$, every marked automorphism $g$ satisfies $qg=q$ and
$gt=tg$. Since $i(m)=t(e)$ for local lifts, $gi=i$ also. Thus $g-1$ vanishes on $i(M)$ and has
image in $i(M)$, and there is a unique module endomorphism $f:M\to M$ with $g=1+ifq$. Conversely
every such map is an automorphism with inverse $1-ifq$, since $qi=0$. Moreover
$(1+ifq)(1+ihq)=1+i(f+h)q$. Scalar pullback sends $ifq$ to $aifq$ under the canonical
identification of the pullback of the trivial lift with itself: in the tensor formula of step 5,
$i(m)\otimes1=a\,\widetilde m\otimes\epsilon$. Thus this is an identification of
$\operatorname{Aut}^0_M$, with its stated operations, with $\operatorname{End}_{\mathcal
O_X}(M)$ as a $k$-vector space.

10. Apply [lem-weil-pbc-derived-single-fully-faithful] to the abelian category of module
sheaves. It identifies $\operatorname{End}_{\mathcal O_X}(M)$ with
$\operatorname{Hom}_{D(\mathcal O_X)}(M[0],M[0])=\operatorname{Ext}^0(M,M)$. The map sends a
module morphism to the same degree-zero map of complexes, so it preserves addition and
multiplication by $a\in k$ termwise. Composing with step 9 proves the second $k$-linear
identification. The constructions in steps 1--9 use only the specified maps, kernels, tensor
products and quotients. Relabelling $M$ by an isomorphism relabels these formulas, and
isomorphisms of extensions are exactly marked isomorphisms by step 3. This gives the claimed
natural identifications. Empty $X$ or zero $M$ give singleton deformation sets and zero Ext
spaces by the same construction.
-/
theorem split_module_deformation_ext {k : Type u} [Field k]
    (X : AlgebraicSpace (Spec (.of k))) [HasDerivedCategory.{w} X.SmallModules] :
    ∃ (deformation : ∀ M : X.Modules, Classes X (V := k) M ≃ Ext X M 1)
      (automorphism : ∀ M : X.Modules, AutZero X (V := k) M ≃ Ext X M 0),
      (∀ M : X.Modules, ∃ T : Marked X (V := k) M, IsTrivial X T) ∧
      (∀ (M : X.Modules) (T : Marked X (V := k) M),
        IsTrivial X T → deformation M (classOf X T) = 0) ∧
      (∀ (M : X.Modules) (a : k) (N : Marked X (V := k) M),
        (∃ N' : Marked X (V := k) M, PullsBack X (a • LinearMap.id) N N') ∧
        ∀ N' : Marked X (V := k) M, PullsBack X (a • LinearMap.id) N N' →
          deformation M (classOf X N') = extScalar X 1 a (deformation M (classOf X N))) ∧
      (∀ (M : X.Modules) (N₁ N₂ : Marked X (V := k) M),
        (∃ L : Marked X (V := k × k) M, IsGluing X L N₁ N₂) ∧
        (∀ L L' : Marked X (V := k × k) M,
          IsGluing X L N₁ N₂ → IsGluing X L' N₁ N₂ → Related X L L') ∧
        ∀ L : Marked X (V := k × k) M, IsGluing X L N₁ N₂ →
          (∃ N : Marked X (V := k) M,
            PullsBack X (LinearMap.fst k k k + LinearMap.snd k k k) L N) ∧
          ∀ N : Marked X (V := k) M,
            PullsBack X (LinearMap.fst k k k + LinearMap.snd k k k) L N →
              deformation M (classOf X N) =
                deformation M (classOf X N₁) + deformation M (classOf X N₂)) ∧
      (∀ (M : X.Modules) (g : AutZero X (V := k) M),
        g.val = Iso.refl _ → automorphism M g = 0) ∧
      (∀ (M : X.Modules) (g h : AutZero X (V := k) M),
        (∃ t : AutZero X (V := k) M, t.val = g.val ≪≫ h.val) ∧
        ∀ t : AutZero X (V := k) M, t.val = g.val ≪≫ h.val →
          automorphism M t = automorphism M g + automorphism M h) ∧
      (∀ (M : X.Modules) (a : k) (g : AutZero X (V := k) M),
        (∃ t : AutZero X (V := k) M, t.val = changeAut X (a • LinearMap.id) g) ∧
        ∀ t : AutZero X (V := k) M, t.val = changeAut X (a • LinearMap.id) g →
          automorphism M t = extScalar X 0 a (automorphism M g)) ∧
      (∀ (M M' : X.Modules) (e : M ≅ M') (N : Marked X (V := k) M),
        deformation M' (classOf X (relabel X e N)) =
          extRelabel X e 1 (deformation M (classOf X N))) ∧
      (∀ (M M' : X.Modules) (e : M ≅ M') (g : AutZero X (V := k) M),
        (∃ g' : AutZero X (V := k) M',
          g'.val = ((moduleTensorPullback (projection X k)).mapIso e).symm ≪≫
            g.val ≪≫ (moduleTensorPullback (projection X k)).mapIso e) ∧
        ∀ g' : AutZero X (V := k) M',
          g'.val = ((moduleTensorPullback (projection X k)).mapIso e).symm ≪≫
            g.val ≪≫ (moduleTensorPullback (projection X k)).mapIso e →
          automorphism M' g' = extRelabel X e 0 (automorphism M g)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace.SplitModule
