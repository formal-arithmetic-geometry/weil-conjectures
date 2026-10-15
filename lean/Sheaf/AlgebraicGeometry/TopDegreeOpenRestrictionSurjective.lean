/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.Topology.KrullDimension
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.ZeroDimensionalNoetherianFiniteDiscrete
import Sheaf.Paper.PQFCohomology
import Sheaf.Topology.RingedSpaceModuleEnoughInjectives
import Sheaf.Topology.RestrictInjectiveResolution
import Sheaf.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Topology.Spectral.Basic
import Sheaf.Topology.NoetherianTopologicalCohomologyVanishing
import Mathlib.CategoryTheory.Limits.HasLimits
import Sheaf.Topology.ModuleMayerVietoris

/-! # Surjectivity of top-degree cohomology restriction

Source: Stacks Project, Cohomology, Tag 0A3G (2), and Tag 01F1
(blueprint: lem-weil-pbc-top-degree-open-restriction-surjective).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- On a Noetherian k-scheme of dimension d, restriction to a quasi-compact open
immersion is a surjective k-linear map, for every module sheaf. The scalar actions
are the canonical restrictions along k → Γ(X, O_X) and k → Γ(V, O_V).
The equality with the canonical cohomology map fixes the underlying function of L.
No coherence, separatedness or properness assumption is imposed.

Source: Stacks Project, Cohomology, Tag 0A3G (2), and Tag 01F1
(blueprint: lem-weil-pbc-top-degree-open-restriction-surjective).

Proof:
1. Identify the open immersion with its image $U\subseteq |X|$. The Noetherian-scheme
minimal-closed-subset theorem gives a Noetherian underlying topological space $T=|X|$. Local
Noetherianity gives quasi-separatedness; since $X$ is quasi-compact, the qcqs-scheme spectral
theorem gives that $T$ is spectral. Thus, in particular, $T$ is sober. No separatedness or
properness hypothesis is used. Dependencies:
lem-weil-pbc-noetherian-scheme-closed-subsets-minimal,
lem-weil-pbc-locally-noetherian-quasi-separated, lem-weil-pbc-qcqs-scheme-spectral,
def-weil-open-immersion.

2. If $d=0$, the zero-dimensional Noetherian-scheme theorem makes $T$ finite discrete. Hence $U$
and its complement are disjoint open subsets. Given any section of $\mathcal F|_U$, glue it with
the zero section on $T\setminus U$. Its restriction is the given section. Since $H^0=\Gamma$,
restriction in degree zero is surjective. This includes $U=\varnothing$ and $U=T$. Henceforth
assume $d\geq1$. Dependencies: lem-sc-zero-dim-noetherian-finite-discrete, pqf-def-cohomology.

3. Write $A=\mathcal F_{ab}$. Choose a module-injective resolution $\mathcal F\to I^\bullet$,
which exists because module sheaves have enough injectives. For each open $B\subseteq T$, its
restriction is module-injective. The underlying abelian sheaves of these terms are acyclic for
global sections on $B$, by injective-module abelian acyclicity applied to the ringed site of opens
of $B$. By the module-sheaf category definition, kernels are sectionwise kernels and cokernels are
sheafifications of sectionwise cokernels. Forgetting scalars leaves these kernel and cokernel
abelian groups unchanged (the induced scalar action descends to the quotient and its
sheafification). Thus forgetting preserves kernels and cokernels, hence exactness, so the
underlying augmented abelian complex is still a resolution. Leray acyclicity therefore computes
$H^p(B,A|_B)$ by the underlying abelian complex $\Gamma(B,I^\bullet|_B)$, the very complex
computing module cohomology. Consequently there are canonical isomorphisms $c_B:H^p(B,\mathcal
F|_B)\cong H^p(B,A|_B)$. For inclusions $B\subseteq B\prime$, both restriction maps are induced by
the identical chain map $\Gamma(B\prime,I^\bullet)\to\Gamma(B,I^\bullet)$, so
$c_B\circ\mathrm{res}_{mod}=\mathrm{res}_{ab}\circ c_{B\prime}$. This verifies restriction
compatibility, not just an objectwise comparison. Dependencies:
lem-sc-ringed-space-module-sheaves-enough-injectives,
lem-sc-ringed-space-restrict-injective-resolution,
lem-sc-injective-module-abelian-acyclic-zariski, lemma-weil-pbc-leray-acyclicity,
def-weil-sheaf-of-modules-category, def-sc-topological-abelian-cohomology.

4. Set $Z=T\setminus U$, $W=\{x\in T:\overline{\{x\}}\cap Z\ne\varnothing\}$ and $S=W\setminus Z$.
The space $S$ is Noetherian: for any ascending chain of opens $O_i$ of $S$, choose ambient opens
$P_i$ with $O_i=S\cap P_i$ and replace $P_i$ by $\bigcup_{j\leq i}P_j$. These ambient opens form
an ascending chain and therefore stabilize in $T$; intersecting with $S$ stabilizes the original
chain. Moreover $S$ is stable under generalization: if $x$ specializes to $z\in Z$ and $y$
generalizes $x$, then $y$ specializes to $z$; if $x\in U$, then $y\in U$ because $U$ is open.
Dependencies: .

5. We have $\dim S\leq d-1$. Indeed, take a chain $C_0\subsetneq\cdots\subsetneq C_r$ of
irreducible closed subsets of $S$. Their ambient closures $D_i=\overline{C_i}^{\,T}$ are
irreducible closed and strictly nested, since $S\cap D_i=C_i$. By sobriety choose the generic
point $y$ of $D_0$. It generalizes any point of $C_0$, so the preceding generalization-stability
gives $y\in S$. Choose $z\in Z\cap\overline{\{y\}}$. Then $\overline{\{z\}}$ is nonempty
irreducible closed and lies in $D_0$; it is strictly smaller because it lies in closed $Z$ whereas
$y\notin Z$. Thus $\overline{\{z\}}\subsetneq D_0\subsetneq\cdots\subsetneq D_r$ is an ambient
chain of length $r+1$, so $r+1\leq d$. If $S$ is empty the bound holds by the definition of
dimension. This is a direct chain argument, with no additional dimension theorem needed.
Dependencies: def-weil-spectral-space, def-kun-topological-krull-dimension.

6. Apply Noetherian topological cohomology vanishing to $S$, the abelian sheaf $A|_S$, and the
nonnegative bound $d-1$. The hypotheses were verified in the preceding two steps. Since $d>d-1$,
it gives $H^d(S,A|_S)=0$, including when $S=\varnothing$. This replaces the lower-dimensional
spectral induction in the source by the existing Noetherian vanishing theorem; no quasi-coherence
is needed. Dependencies: lem-sc-noetherian-topological-cohomology-vanishing.

7. Let $\xi\in H^d(U,\mathcal F|_U)$ and write $\alpha=c_U(\xi)$. The punctured-neighborhood
comparison applies to spectral $T$, closed $Z$ and quasi-compact open complement $U$. It
identifies $H^d(S,A|_S)$ with the filtered colimit of $H^d(N\setminus Z,A|_{N\setminus Z})$ over
quasi-compact open neighborhoods $N$ of $Z$, using precisely restriction maps. The image of
$\alpha$ from the initial stage $N=T$ is therefore zero in that colimit. Dependencies:
lem-weil-pbc-punctured-neighborhood-cohomology-colimit.

8. For completeness the eventual-zero inference is elementary: construct the directed colimit of
groups as classes of pairs $(N,a)$, with $(N,a)\sim(N\prime,a\prime)$ exactly when their
restrictions agree at a common smaller neighborhood. Addition is defined after passing to a common
smaller neighborhood; this gives the colimit universal property. Equality of the class of
$(T,\alpha)$ with the zero class thus gives a quasi-compact open $N\supseteq Z$ with
$\alpha|_{N\setminus Z}=0$. Since $N\setminus Z=N\cap U$, the restriction-compatible isomorphisms
$c_B$ of step 3 imply $\xi|_{N\cap U}=0$ in module cohomology. Dependencies:
def-weil-pbc-category-colimit.

9. The opens $U,N$ cover $T$ since $N$ contains $Z$. Use the Mayer--Vietoris sequence for the
ringed space $X$ and the arbitrary module $\mathcal F$. Its exact segment is $H^d(X,\mathcal F)\to
H^d(U,\mathcal F|_U)\oplus H^d(N,\mathcal F|_N)\to H^d(U\cap N,\mathcal F|_{U\cap N})$, with the
last map the difference of restrictions. The pair $(\xi,0)$ maps to zero by step 8. Exactness
gives $\widetilde\xi\in H^d(X,\mathcal F)$ restricting to $(\xi,0)$, in particular restricting to
$\xi$ on $U$. This proves surjectivity for $d\geq1$. Dependencies:
lem-sc-mayer-vietoris-ringed-space.

10. Finally the $k$-scheme structure supplies compatible maps $k\to\mathcal O_X(B)$ for all opens
$B$. On the module-resolution complexes used in step 3, restriction obeys $\mathrm{res}(a
s)=a\mathrm{res}(s)$ for $a\in k$ in every degree, and the differentials are module-linear.
Passing to kernels modulo images gives $\mathrm{res}(a[ s])=a\mathrm{res}([ s])$ on cohomology. In
degree zero the same formula holds for sections. Thus the surjective canonical restriction map
just proved is $k$-linear, as asserted. Dependencies: def-weil-scheme-over-base,
pqf-def-cohomology, def-weil-sheaf-of-modules-category. -/
theorem top_degree_open_restriction_surjective
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsLocallyNoetherian X] [CompactSpace X]
    (d : ℕ) (hdim : topologicalKrullDim X = (d : WithBot ℕ∞))
    (V : Scheme.{u}) (j : V ⟶ X) [IsOpenImmersion j] [CompactSpace V]
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    ∃ L :
      (ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          (X ↘ Spec (.of k)).appTop).hom).obj
        ((RingedSpace.moduleCohomology X.toRingedSpace d).obj F) ⟶
      (ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          (j ≫ (X ↘ Spec (.of k))).appTop).hom).obj
        ((RingedSpace.moduleCohomology V.toRingedSpace d).obj
          ((restrictFunctor j).obj F)),
      (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}).map L =
        moduleCohomologyFMap j ((restrictAdjunction j).unit.app F) d ∧
      Function.Surjective L := by
  sorry

end AlgebraicGeometry.Scheme.Modules
