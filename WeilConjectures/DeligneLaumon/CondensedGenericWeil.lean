/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CondensedGenericWeilData
import WeilConjectures.DeligneLaumon.CondensedWeilComponent
import WeilConjectures.DeligneLaumon.ComponentArithmeticInclusion
import WeilConjectures.DeligneLaumon.WeilKernelCoordinates
import WeilConjectures.DeligneLaumon.NormalizedWeilFibreConstruction
import WeilConjectures.DeligneLaumon.NormalizedWeilFibreDescent
import WeilConjectures.DeligneLaumon.NormalizedWeilAssertions

/-! # Generic fibres of condensed lisse Weil modules

The original actual-fibre definitions are exposed by CondensedGenericWeilData. The proof
constructs the component and its canonical group inclusion, then combines normalized
fibre construction and descent. No geometric connectedness hypothesis is imposed on U0.
Source: Weil II (1.1.10)--(1.1.12), latest rem-dl-a1-conventions.
(blueprint: lem-dl-a1-condensed-weil-generic-representation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale.CondensedGenericWeil

variable (D : WeilConjectures.FiniteFieldDatum.{u})
  (U₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
  [ConnectedSpace U₀.left]

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (t : Spec (.of Ω) ⟶ (D.geometricFiber U₀).left)
  (G : ProfiniteGrp.{u})
  [∀ Q, MulAction G ((FiniteEtale.fiber (t ≫ projection D U₀)).obj Q)]
  [PreGaloisCategory.IsFundamentalGroup (FiniteEtale.fiber (t ≫ projection D U₀)) G]

variable (ell : ℕ) [Fact ell.Prime]


/-- The generic-fibre exact tensor equivalence for all nonempty connected normal models,
including models whose geometric fibre has several components.

Source: latest blueprint, rem-dl-a1-conventions, irreducible-lisse and geometric-constancy
paragraphs; Deligne, Weil II (1.1.10)--(1.1.12).
(blueprint: lem-dl-a1-condensed-weil-generic-representation).

Proof plan (the construction and descent steps are named intermediate theorems):

1. Apply [lem-dl-a1-normal-constant-field-components]. Write $L=\mathbf F_{q^d}$ for the
constant field embedded through $\bar\eta$, $C=U_0\times_Lk$ for its component, and
$\Phi=\operatorname{Fr}_U$. Thus $U=\coprod_{i=0}^{d-1}\Phi^iC$, each component is normal
connected Noetherian, and $f=\Phi^d|_C$ is geometric Galois Frobenius for $U_0/L$. These are
precisely the hypotheses needed for the normal, rather than merely regular, clause of the
condensed lisse correspondence.

2. Restriction to $C$ takes a pair $(F,\theta)$ to $(M,a)=(F|_C,\theta^{(d)}|_C)$, where
$a:f^*M\to M$ is the composite of the $d$ successive pullbacks of $\theta$. This loses no data.
Put $C_i=\Phi^iC$ and $h_i=\Phi^i|_C:C\to C_i$. For a given $(M,a)$ put $F_i=(h_i^{-1})^*M$.
Under $h_i^*F_i=M$, define the arrow $(\Phi|_{C_i})^*F_{i+1}\to F_i$ to be the identity for
$i<d-1$; for $i=d-1$ its pullback to $C$ is $a:f^*M\to M$. Assemble the $F_i$ into a sheaf on
the finite disjoint union: sections over $T\to U$ are the product of sections over $T\times_U
C_i$. The sheaf and module axioms hold componentwise. For an arbitrary pair, successive
$\theta_i$ identify its components with this reconstruction, with its last arrow equal to $a$.
The same equations on arrows show full faithfulness. These identifications are natural.
Restriction, this reconstruction, and their inverse identifications commute with tensor products
and exact sequences componentwise. This is the explicit cyclic-descent reduction, including
$d=1$.

3. The structure map $U_0\to\operatorname{Spec}L$ is separated by [lem-weil-pbc-separated-
cancellation] (b), since $U_0\to\operatorname{Spec}k_0$ is; it is of finite type by [lemma-
nagata-finite-type-to-separated-target] (b), since
$\operatorname{Spec}L\to\operatorname{Spec}k_0$ is a morphism of affine schemes, hence separated
(its diagonal is the closed immersion given by the surjective multiplication $L\otimes_{k_0}L\to
L$). Apply [lem-wf-arithmetic-lift-fibre-path] to the perfect finite field $L$, its algebraic
closure $k$ (through the embedding of Step 1), the separated finite-type scheme $U_0/L$, and its
connected geometric fibre $C$. It gives $1\to P=\pi_1(C,\bar\eta)\to
G=\pi_1(U_0,\bar\eta)\xrightarrow{r_L}\operatorname{Gal}(k/L)\to1$. The original constants map
is the composite of $r_L$ with the inclusion in $\operatorname{Gal}(k/k_0)$: on finite constant
covers both act on embeddings by the same field automorphism. Hence the original Weil group is
$r_L^{-1}(\langle\gamma^d\rangle)$, where $\gamma(z)=z^{1/q}$; its degree image is $d\mathbf Z$,
not necessarily $\mathbf Z$. Choose $s\in G$ mapping to $\gamma^d$. Every $w\in W$ is uniquely
$hs^n$, $h\in P$, with original degree $dn$. Thus $W=P\rtimes\langle s\rangle$, with $s$
conjugating $P$ by $h\mapsto shs^{-1}$. The topology is the disjoint union of the profinite
cosets $Ps^n$.

4. For the return pair $(M,a)$, [thm-lisse-qlbar-representations] (3)-(5) gives its finite-
dimensional fibre $V$, continuous geometric action $\rho:P\to\operatorname{GL}(V)$ and a finite
coefficient model. Use the specified arithmetic path for $s$ and [lem-real-condensed-fibre-
functoriality] to obtain $L_s:(f^*M)_{\bar\eta}\to V$, with $L_s\rho_f(g)=\rho(s^{-1}gs)L_s$.
The fibre of $a$ satisfies $a_{\bar\eta}\rho_f(g)=\rho(g)a_{\bar\eta}$. Set
$T=a_{\bar\eta}L_s^{-1}$. Substitution of $g=shs^{-1}$ gives $T\rho(h)T^{-1}=\rho(shs^{-1})$.
Define $R(hs^n)=\rho(h)T^n$. Indeed $(hs^n)(h's^m)=h(s^nh's^{-n})s^{n+m}$, and the conjugation
identity makes $R$ multiplicative, also for negative $n$. It is continuous on the open subgroup
$P$. Adjoin to the geometric coefficient field the finitely many matrix entries of $T$ and
$T^{-1}$: this is a finite extension since $\Lambda$ is algebraic over $\mathbf Q_\ell$, and it
defines the entire action. No integrality condition is imposed on $T$.

5. The lisse dictionary is fully faithful. Thus a $P$-equivariant linear map $u:V_M\to V_N$
lifts uniquely to a sheaf morphism $b:M\to N$. It commutes with the return Weil structures
exactly when $uT_M=T_Nu$: the fibre of $b a_M=a_N f^*b$ is $u
a_{M,\bar\eta}=a_{N,\bar\eta}(f^*b)_{\bar\eta}$, and path naturality says
$L_{s,N}(f^*b)_{\bar\eta}=uL_{s,M}$. Cancel the invertible path maps. Since $W$ is generated by
$P$ and $s$, these are exactly the $W$-equivariant linear maps. Faithfulness of the geometric
fibre turns this equality of fibres back into equality of sheaf arrows. Together with cyclic
descent this proves full faithfulness of the asserted functor.

6. Conversely let $R$ be an allowed $W$-representation, put $\rho=R|_P$ and $T=R(s)$. Its
geometric restriction is defined over a finite field by hypothesis. The normal condensed lisse
correspondence reconstructs $M$ on $C$ with fibre $(V,\rho)$. In the specified path coordinates
the fibre of $f^*M$ has action $\rho(s^{-1}gs)$. The linear map $T L_s:(f^*M)_{\bar\eta}\to V$
is equivariant because $T\rho(s^{-1}gs)=\rho(g)T$. Fullness reconstructs an arrow $a:f^*M\to M$,
and fullness applied to its inverse matrix, followed by faithfulness, shows it is an
isomorphism. The representation constructed in Step 4 now has restriction $\rho$ and value $T$
on $s$, hence equals $R$ on every $hs^n$. Reconstruct the original pair by Step 2. This proves
essential surjectivity without assuming the full action preserves a lattice.

7. The construction uses the arithmetic path normalized by $s^{-1}$ on finite arithmetic fibres.
If $s$ is replaced by $bs$, $b\in P$, the arithmetic-path identity and its condensed extension
give $L_{bs}=L_s\rho_f(b^{-1})$. Consequently $T_{bs}=a_{\bar\eta}\rho_f(b)L_s^{-1}=\rho(b)T_s$,
so the formula on $hs^n$ defines the same action of the same group $W$. On a geometrically
connected regular scheme $d=1$. The formula $T_s=\theta_{\bar\eta}L_s^{-1}$ and its finite
reduction are exactly the normalization in [def-wf-fundamental-representation]. Here that node
is used solely to check the convention: the condensed action and the adic action agree at finite
reductions and hence after the inverse limit and scalar extensions stipulated by the two fibre
constructions; no equivalence of their entire coefficient categories is assumed.

8. By [det-lem-coefficient-heart-closure], kernels and cokernels of maps of lisse
$\Lambda_U$-modules are lisse. The exact Frobenius pullback in [sk-def-sf-weil-complexes]
carries their kernel and cokernel diagrams to such diagrams; the invertible structures therefore
induce invertible structures on these kernels and cokernels. Thus the lisse Weil category is
abelian with exactness inherited from module sheaves. The geometric fibre in [lem-real-
condensed-fibre-functoriality] is exact, so the fully faithful equivalence above is exact. Its
tensor comparison is the canonical fibre comparison $V_{F\otimes G}=V_F\otimes_\Lambda V_G$ and
its unit is $\Lambda$ with trivial action. Path compatibility with tensors and naturality imply
$T_{F\otimes G}=T_F\otimes T_G$; the geometric action has the same tensor rule. Hence the
comparison is $W$-equivariant. Associativity, symmetry and unit diagrams are those of the
canonical tensor fibre functor (on pure tensors each route gives the same tensor). This proves
the exact tensor assertion.

9. Finally any $W$-stable subspace $V'\subset V$ is an allowed representation. To check the
finite-field clause, take a finite geometric field of definition for $V$, choose a
$\Lambda$-basis of $V'$ extended to a basis of $V$, and adjoin the finitely many entries of this
change-of-basis matrix and its inverse. In this enlarged finite field, invariance says that the
lower-left matrix blocks vanish, so the span of the chosen $V'$-basis is a stable finite-field
model and the restricted action is continuous. The quotient has the corresponding quotient
model. Essential surjectivity reconstructs both, and fullness lifts $V'\hookrightarrow V$.
Exactness and faithfulness show this lift is a monomorphism: its kernel has zero fibre and is
zero. Conversely a lisse Weil monomorphism has an injective fibre map, with $W$-stable image.
Two such subobjects have the same subspace exactly when their inclusions are uniquely
isomorphic, by full faithfulness. The zero sheaf has zero fibre; if a fibre is zero, the
equivalence on $C$ and cyclic reconstruction make the whole pair zero. This proves all the
remaining clauses.
-/
theorem generic_fibre_equivalence (hEll : ell ≠ D.p)
    [IsSeparated U₀.hom]
    (hNormal : ∀ x : U₀.left, IsDomain (U₀.left.presheaf.stalk x) ∧
      IsIntegrallyClosed (U₀.left.presheaf.stalk x))
    (hGeneric : ∃ Z ∈ irreducibleComponents (D.geometricFiber U₀).left,
      IsGenericPoint (t (IsLocalRing.closedPoint Ω)) Z) :
    ∃ (A : Geometry D U₀ t G) (S : RealCondensedFibre.System.{u} ell),
      Nonempty (Assertions D U₀ t G ell A S) := by
  obtain ⟨C, j, x, hj, himage, hx⟩ :=
    component_context_exists D U₀ t hNormal hGeneric
  obtain ⟨P, hact, hFund⟩ := FiniteEtale.exists_isFundamentalGroup x
  let := hact
  let := hFund
  let π := FiniteEtale.constantCoverAction U₀.hom (t ≫ projection D U₀) G
  let Φ := FiniteEtale.geometricFrobenius U₀.hom (t ≫ projection D U₀)
  let i := componentArithmeticInclusion D U₀ t G C j x hx P
  obtain ⟨hi, hr⟩ :=
    component_arithmetic_exactness D U₀ t G C j x hx P hj himage hNormal hGeneric
  have hk : ∀ a, π (i a) = 1 := by
    intro a
    change i a ∈ π.ker
    rw [← hr]
    exact ⟨a, rfl⟩
  let geom := WeilKernel.lift π Φ i hk
  obtain ⟨hgi, hgr, hgo⟩ := WeilKernel.coordinates π Φ i hk hi hr
    (componentArithmeticInclusion_continuous D U₀ t G C j x hx P)
  let A : Geometry D U₀ t G := {
    component := C
    inclusion := j
    openImmersion := hj
    image := himage
    point := x
    point_eq := hx
    P := P
    action := hact
    fundamental := hFund
    geometric := geom
    geometric_degree := fun _ ↦ rfl
    geometric_arithmetic :=
      componentArithmeticInclusion_normalized D U₀ t G C j x hx P
    injective := hgi
    geometric_image := hgr
    topology := hgo }
  obtain ⟨S⟩ := RealCondensedFibre.real_condensed_fibre_functoriality ell
  obtain ⟨M⟩ := normalized_weil_fibre_construction D U₀ t G ell hEll hNormal hGeneric A S
  obtain ⟨hf, hfaith, hes⟩ :=
    normalized_weil_fibre_descent D U₀ t G ell hEll hNormal hGeneric A S M
  let := hf
  let := hfaith
  let := hes
  have : IsNoetherian (D.geometricFiber U₀).left := {
    toIsLocallyNoetherian := by
      change IsLocallyNoetherian (pullback U₀.hom _)
      infer_instance
    toCompactSpace := by
      change CompactSpace ↥(pullback U₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) : Scheme.{u})
      infer_instance }
  exact ⟨A, S, normalized_functor_assertions D U₀ t G ell A S M⟩

end AlgebraicGeometry.ProEtale.CondensedGenericWeil
