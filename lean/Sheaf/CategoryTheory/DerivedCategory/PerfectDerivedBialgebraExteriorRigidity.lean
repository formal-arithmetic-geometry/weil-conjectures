module

public import Sheaf.CategoryTheory.DerivedCategory.ExteriorCohomology
public import Sheaf.CategoryTheory.DerivedCategory.PerfectScalarTensorCoherence
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import Mathlib.CategoryTheory.Monoidal.Bimon_

import WeilConjectures.RingTheory.FiniteProjectivePrimeLocalFree
import WeilConjectures.RingTheory.RingPseudoCoherent
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import WeilConjectures.RingTheory.MinimalFreeModel
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import WeilConjectures.RingTheory.FiniteFreeMapResidueLocalization
import Sheaf.RingTheory.KrullIntersectionLocalization
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-! # Rigidity of a perfect derived bialgebra with exterior residue cohomology

Source: the agent-stated rigidity argument based on Stacks Project, More on Algebra,
Tags 0BCC and 00IP. (blueprint: lem-sfb-perfect-derived-bialgebra-exterior-rigidity).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

namespace DerivedCategory.ExteriorCohomology

/-- Perfect derived bialgebra rigidity over a Noetherian local ring.

Source: the agent-stated rigidity argument based on Stacks Project, More on Algebra,
Tags 0BCC and 00IP, with the signed derived tensor conventions of Tags 064K and 064B.
(blueprint: lem-sfb-perfect-derived-bialgebra-exterior-rigidity).

Proof:
1. Choose a bounded cochain complex of finitely generated projective $R$-modules representing
$K$, using [def-pc-perfect-ring-complex]. Apply [lem-weil-pbc-finite-projective-prime-local-
free] to each of its finitely many nonzero terms $M$ at the prime $\mathfrak m$: there is
$f\notin\mathfrak m$ with $M_f\cong R_f^{\oplus r}$. Since $R$ is local, $f$ is a unit, so $R\to
R_f$ and $M\to M_f$ are isomorphisms and $M\cong R^{\oplus r}$ is finite free. Thus this is a
bounded finite-free representative, in particular a bounded-above one, so $K$ is pseudo-coherent
by [def-pc-ring-pseudo-coherent-complex]. Uses: def-pc-perfect-ring-complex, lem-weil-pbc-
finite-projective-prime-local-free, def-pc-ring-pseudo-coherent-complex.

2. Put $d_i=\dim_k H^i(\overline K)$. The exterior-basis statement [lem-weil-pbc-exterior-power-
free-basis] gives $d_i=\binom gi$ for $0\leq i\leq g$ and zero otherwise. Apply [lem-sc-perfect-
local-pseudocoherent-free-model]: there is a representative $P$ of $K$ with $P^i=R^{d_i}$ in
every degree. It is therefore bounded and supported in $[0,g]$. It is minimal: for the residue
complex $E=k\otimes_R P$, the equality $\dim_k E^i=\dim_k H^i(E)=d_i$ and the formula $\dim
H^i(E)=\dim E^i-\operatorname{rank}(\overline d^{i-1})-\operatorname{rank}(\overline d^i)$ force
all residue differentials to vanish. Hence $d(P)\subseteq\mathfrak mP$. Uses: lem-weil-pbc-
exterior-power-free-basis, lem-sc-perfect-local-pseudocoherent-free-model.

3. The bounded free complexes $R[0]$, $P$ and all finite tensor powers of $P$ are K-flat by
[lem-pc-module-bounded-flat-kflat]; freeness makes tensoring termwise a finite direct sum, hence
exact. By [lem-pc-derived-tensor-second-factor-functor] their ordinary signed total tensors
compute the derived tensors. Use [lem-pc-ring-derived-map-representative] to represent
$u,\mu,\varepsilon,\Delta$ by chain maps on these complexes. The same bijectivity says that each
bialgebra identity holds up to chain homotopy, since its source is bounded projective. On
reducing modulo $\mathfrak m$, all terms $dh+hd$ vanish. Thus $E$ is a strict graded bialgebra
with underlying graded algebra $H^*(\overline K)$ and with the given exterior product. Uses:
lem-pc-module-bounded-flat-kflat, lem-pc-derived-tensor-second-factor-functor, lem-pc-ring-
derived-map-representative.

4. The residue of $u^0:R\to P^0$ is an isomorphism by the hypothesis on $H^0(\overline K)$.
Apply [lem-pc-finite-free-map-residue-localization] at $\mathfrak m$. Its $f\notin\mathfrak m$
is a unit, so $u^0$ itself is an isomorphism. Identify $P^0$ with $R$ by this map. The chain-map
equation $d^0u^0=0$ gives $d^0=0$. In particular the unit is an actual cycle, and its leading
differential in every maximal-ideal order is zero. Uses: lem-pc-finite-free-map-residue-
localization.

5. Write $V=E^1$. Since $E$ has no negative degrees, $E^0=k$ via the unit, and the counit is
zero in positive degrees, its two counit equations imply $\overline\Delta(v)=v\otimes1+1\otimes
v$ for $v\in V$. Multiplicativity of $\overline\Delta$, with the signed tensor product, gives
the $(1,1)$-component $c(vw)=v\otimes w-w\otimes v$. Choose a basis $e_1,\ldots,e_g$ of $V$. By
[lem-weil-pbc-exterior-power-free-basis], the $e_ie_j$ with $i<j$ form a basis of $E^2$. Define
$\rho:V\otimes_kV\to E^2$ by $\rho(e_i\otimes e_j)=e_ie_j$ for $i<j$ and zero for $i\geq j$.
Then $\rho c=1$. Consequently $c$ is split injective and every primitive element of $E^2$ is
zero. This includes characteristic two, and $E^2=0$ when $g<2$. Uses: lem-weil-pbc-exterior-
power-free-basis.

6. We prove by induction on $n\geq1$ that every entry of $d$ lies in $\mathfrak m^n$; step 2 is
the base case. Suppose this holds for $n$, and put $I_n=\mathfrak m^n/\mathfrak m^{n+1}$. The
differential induces a degree-one $k$-linear map $\delta:E^i\to I_n\otimes_k E^{i+1}$: for $a\in
P^i$, take $da$ in $\mathfrak m^nP^{i+1}/\mathfrak m^{n+1}P^{i+1}$ and use the identification
with $I_n\otimes_k E^{i+1}$ given by a free basis of $P^{i+1}$. Changing $a$ by an element of
$\mathfrak mP^i$ changes $da$ by an element of $\mathfrak m^{n+1}P^{i+1}$, proving independence
of the lift. Step 4 gives $\delta(1)=0$. Uses: .

7. The chain-map equations for the chosen representatives are
$d\mu=\mu(d\otimes1+(-1)^{\deg}1\otimes d)$ and $\Delta d=(d\otimes1+(-1)^{\deg}1\otimes
d)\Delta$. Take their coefficients in $\mathfrak m^n/\mathfrak m^{n+1}$. Every occurrence of $d$
contributes its leading coefficient $\delta$; every adjacent coefficient of $\mu$ or $\Delta$
can be reduced modulo $\mathfrak m$, since its error times $\mathfrak m^n$ lies in $\mathfrak
m^{n+1}$. We obtain $\delta(ab)=\delta(a)b+(-1)^{\deg a}a\delta(b)$ and
$\overline\Delta\delta=(\delta\otimes1+(-1)^{\deg}1\otimes\delta)\overline\Delta$, with the
coefficient factor $I_n$ placed first on both sides. These are identities of $k$-linear maps
with values in $I_n$ tensored with the indicated graded modules. Uses: .

8. For $v\in E^1$, substitute $\overline\Delta(v)=v\otimes1+1\otimes v$ and $\delta(1)=0$ into
the second equation of step 7. It says $\overline\Delta(\delta v)=\delta
v\otimes1+1\otimes\delta v$. Its $(1,1)$-component is $(1_{I_n}\otimes c)(\delta v)=0$. Tensor
the explicit retraction $\rho$ of step 5 with $I_n$ to conclude $\delta v=0$; no flatness of
$I_n$ is needed. The first equation of step 7 now gives $\delta(v_1\cdots v_r)=0$ by induction
on $r$, since $E$ is generated by $E^1$ and the unit. Thus $\delta=0$, so every entry of $d$
lies in $\mathfrak m^{n+1}$. This completes the induction for all $n$. Uses: .

9. Every matrix entry of $d$ belongs to $N=\bigcap_{n\geq0}\mathfrak m^nR$. Apply [lem-weil-pbc-
krull-intersection-localization] with the Noetherian ring $R$, ideal $\mathfrak m$, finite
module $R$, and prime $\mathfrak m$. It gives $f\notin\mathfrak m$ with $N_f=0$. Because $f$ is
a unit, this says $N=0$ already over $R$. Therefore $d=0$. We have proved the asserted derived
isomorphism to a bounded finite-free zero-differential complex supported in $[0,g]$, without
completing $R$. Uses: lem-weil-pbc-krull-intersection-localization.

10. Put $A^i=P^i=H^i(K)$. All tensor powers of $P$ now have zero differential. Consequently
every chain homotopy between their maps has boundary $dh+hd=0$, so the bialgebra laws from step
3 hold as exact graded-module identities on $A$. By step 4, $A^0=R$ via $H^0(u)$; by step 2,
$A^1$ is free of rank $g$. The counit equations, degree by degree, imply
$\Delta(x)=x\otimes1+1\otimes x$ for every $x\in A^1$, just as in step 5. Uses: .

11. Let $c_R:A^2\to A^1\otimes_R A^1$ be the $(1,1)$-component of $\Delta$. Its residue is the
split injection $c$ of step 5. Both source and target are finite free, so [lem-pc-finite-free-
map-residue-localization] and the fact that $R$ is local make $c_R$ injective. For $x\in A^1$,
multiplicativity and the signed tensor product give $\Delta(x^2)=(x\otimes1+1\otimes
x)^2=x^2\otimes1+x\otimes x-x\otimes x+1\otimes x^2$. Hence $c_R(x^2)=0$, so $x^2=0$. This is
the required square-zero assertion, even when $2$ is not a unit. Uses: lem-pc-finite-free-map-
residue-localization.

12. Associativity, signed commutativity and step 11 make $(x_1,\ldots,x_r)\mapsto x_1\cdots x_r$
multilinear and alternating: move two equal factors next to one another using the signs, then
their square is zero. By [lem-trf-exterior-power-universal-property] it induces
$\phi_r:\bigwedge_R^r A^1\to A^r$ with the stated value on pure wedges. The source is finite
free by [lem-weil-pbc-exterior-power-free-basis]; the target is finite free by step 2. Its
residue is the exterior-product isomorphism in the hypothesis: exterior basis vectors reduce to
the corresponding exterior basis vectors over $k$, and the product maps reduce to the given
product. Apply [lem-pc-finite-free-map-residue-localization] at $\mathfrak m$ to obtain that
each $\phi_r$ is an isomorphism. Both sides vanish for $r>g$ (and negative degrees); for $r=0$
the map is $H^0(u)$. On pure wedges concatenation and associativity give
$\phi_{r+s}(\alpha\wedge\beta)=\phi_r(\alpha)\phi_s(\beta)$, so the direct sum of the $\phi_r$
is the required graded-algebra isomorphism. Uses: lem-trf-exterior-power-universal-property,
lem-weil-pbc-exterior-power-free-basis, lem-pc-finite-free-map-residue-localization.
-/
theorem perfect_derived_bialgebra_exterior_rigidity
    [∀ A : CommRingCat.{u}, HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (R : CommRingCat.{u}) [IsNoetherianRing R] [IsLocalRing R]
    (K : PerfectScalar.D.{u, w} R)
    (hK : IsPerfectRingComplex K)
    (hB : @CategoryTheory.BimonObj (DerivedCategory (ModuleCat.{u} R)) _ _
      (DerivedMonoidal.braidedCategory' (Qh (C := ModuleCat.{u} R))
        (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))) K)
    (hC : @CategoryTheory.IsCommMonObj (DerivedCategory (ModuleCat.{u} R)) _ _
      (DerivedMonoidal.braidedCategory' (Qh (C := ModuleCat.{u} R))
        (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))) K hB.toMonObj)
    (hFinite : Module.Finite (IsLocalRing.ResidueField R)
      ((homologyFunctor.{w} (ModuleCat.{u} (CommRingCat.of (IsLocalRing.ResidueField R))) 1).obj
        ((PerfectScalar.B.{u, w}
          (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))).obj K)))
    (hResidue : IsExterior
      (scalarUnit.{u, w} (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))
        (@CategoryTheory.MonObj.one (DerivedCategory (ModuleCat.{u} R)) _ _ K hB.toMonObj))
      (scalarMul.{u, w} (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))) hK
        (@CategoryTheory.MonObj.mul (DerivedCategory (ModuleCat.{u} R)) _ _ K hB.toMonObj))) :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (∀ i : ℤ, i < 0 ∨ ((Module.finrank (IsLocalRing.ResidueField R)
        ((homologyFunctor.{w} (ModuleCat.{u} (CommRingCat.of (IsLocalRing.ResidueField R))) 1).obj
          ((PerfectScalar.B.{u, w}
            (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))).obj K))) : ℤ) < i →
        IsZero (P.X i)) ∧
      (∀ i : ℤ, P.d i (i + 1) = 0) ∧
      (∀ i : ℤ, Module.Free R (P.X i) ∧ Module.Finite R (P.X i)) ∧
      Nonempty (K ≅ DerivedCategory.Q.obj P) ∧
      IsIso ((homologyFunctor.{w} (ModuleCat.{u} R) 0).map
        (@CategoryTheory.MonObj.one (DerivedCategory (ModuleCat.{u} R)) _ _ K hB.toMonObj)) ∧
      Nonempty ((homologyFunctor.{w} (ModuleCat.{u} R) 1).obj K ≅
        ModuleCat.of R (Fin (Module.finrank (IsLocalRing.ResidueField R)
        ((homologyFunctor.{w} (ModuleCat.{u} (CommRingCat.of (IsLocalRing.ResidueField R))) 1).obj
          ((PerfectScalar.B.{u, w}
            (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))).obj K))) → R)) ∧
      (∀ x : (homologyFunctor.{w} (ModuleCat.{u} R) 1).obj K,
          cup (@CategoryTheory.MonObj.mul (DerivedCategory (ModuleCat.{u} R)) _ _ K hB.toMonObj)
            1 1 x x = 0) ∧
      IsExterior
        (@CategoryTheory.MonObj.one (DerivedCategory (ModuleCat.{u} R)) _ _ K hB.toMonObj)
        (@CategoryTheory.MonObj.mul (DerivedCategory (ModuleCat.{u} R)) _ _ K hB.toMonObj) := by
  sorry

end DerivedCategory.ExteriorCohomology
