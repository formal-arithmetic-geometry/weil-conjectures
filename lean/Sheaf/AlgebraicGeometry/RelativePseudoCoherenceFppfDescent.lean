module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.FinitePushforwardLocallyFree
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.AlgebraicGeometry.AffinePushforwardResolutionQuasiIso
import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import Sheaf.AlgebraicGeometry.FppfLocalFiniteFreeRefinement
import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition

/-! # Fppf descent of relative fixed-degree pseudo-coherence

Source: Stacks Project, More on Morphisms, Tag 0CSN,
`lemma-relative-pseudo-coherent-descends-fppf`
(blueprint: lem-sfb-relative-pseudocoherence-fppf-descent).

The three conditions defining the fppf covering are written explicitly. The base
morphism is only locally of finite type; the complex need not be globally bounded.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Relative `m`-pseudo-coherence of a complex with quasi-coherent cohomology is
local for an fppf covering of its source, with the same integer `m` throughout.
Source: Stacks Project, More on Morphisms, Tag 0CSN,
`lemma-relative-pseudo-coherent-descends-fppf`
(blueprint: lem-sfb-relative-pseudocoherence-fppf-descent).

Proof (the eight steps of the node; the refinement is over `X`, not over `B`):
1. Assume $E$ is $m$-pseudo-coherent relative to $B$. Each $p_j$ is flat and locally of finite
   presentation, so $\mathcal O_{X_j}[0]$ is pseudo-coherent relative to $X$ by the flat-lfp
   structure lemma. Local finite presentation implies local finite type directly from the affine
   finite-presentation definition, and local finite type is closed under composition. Apply the
   relative pullback lemma to $X_j\to X\to B$, for this same $m$, to obtain the forward
   implication.

   Inputs: lem-sfb-flat-lfp-structure-relative-pseudocoherence,
   lem-sfb-relative-pseudocoherent-pullback, def-sbc-locally-finite-presentation,
   lem-weil-pbc-proper-fp-permanence.

2. We first prepare the converse for a surjective finite locally free $\pi:Y\to Z$, where $Z\to
   B$ is locally of finite type. By the definition of finite locally free morphisms, $\pi$ is
   finite, flat and locally of finite presentation, so its algebra $A=\pi_*\mathcal O_Y$ is
   finite locally free. Locally trivialize it near $z\in Z$, and write the section $1$ as
   $(a_1,\ldots,a_d)$. Affine pushforward base change identifies $A\otimes\kappa(z)$, as a
   unital algebra, with the coordinate ring of the fibre. The image of $1$ is nonzero: the fibre
   of the surjective map $\pi$ is a nonempty affine scheme, hence its coordinate ring has
   $1\ne0$. Thus some $a_i$ is a unit in $\mathcal O_{Z,z}$. Shrink so it is invertible and
   define $r:A\to\mathcal O_Z$ by $r(b_1,\ldots,b_d)=a_i^{-1}b_i$. Then $r(1)=1$, and the
   explicit maps $b\mapsto(r(b),b-r(b)1)$ and $(c,q)\mapsto c1+q$ identify $A$ with $\mathcal
   O_Z\oplus\ker r$. This argument uses no division by the rank; it also applies in residue
   characteristic dividing $d$.

   Inputs: lem-sc-finite-pushforward-locally-free, def-weil-finite-integral-morphism,
   lem-weil-pbc-affine-pushforward-base-change, def-pc-finite-locally-free.

3. Let $F\in D_{\mathrm{QCoh}}(\mathcal O_Z)$ and assume $L\pi^*F$ is $m$-pseudo-coherent
   relative to $B$. Derived pullback preserves quasi-coherent cohomology. Hence the
   finite-pushforward lemma makes $R\pi_*L\pi^*F$ $m$-pseudo-coherent relative to $B$. The
   source $Y\to B$ is locally of finite type by composition. The map $\pi$ is finite, hence
   proper, thus quasi-compact and separated by definition and quasi-separated by the
   separatedness lemma. It is affine by the definition of finite. Apply the projection formula
   with $\mathcal O_Y[0]$ and $F$. For this affine map, termwise pushforward of a K-injective
   resolution of the quasi-coherent complex $\mathcal O_Y[0]$ is a quasi-isomorphism from
   $\pi_*\mathcal O_Y[0]=A[0]$ by the affine resolution comparison, so $R\pi_*\mathcal O_Y\cong
   A[0]$ by the definition of derived direct image. With the unit isomorphism $\mathcal
   O_Y\otimes^{\mathbf L}L\pi^*F\cong L\pi^*F$ and the symmetry of the derived tensor structure,
   the formula gives an isomorphism in $D(\mathcal O_Z)$: $$R\pi_*L\pi^*F\cong F\otimes^{\mathbf
   L}_{\mathcal O_Z} A[0].$$

   Inputs: lem-pc-derived-pullback-tensor-qcoh,
   lem-sfb-finite-relative-pseudocoherent-pushforward, lem-weil-pbc-proper-fp-permanence,
   def-weil-finite-integral-morphism, lem-pc-projection-formula,
   lem-pc-affine-pushforward-resolution-quasi-iso, lem-weil-pbc-finite-proper,
   def-weil-proper-morphism, lem-pc-separated-quasi-separated, def-pc-derived-direct-image,
   def-pc-scheme-derived-tensor-structure.

4. On each neighbourhood of step 2, the displayed splitting of $A$ induces $$F\otimes^{\mathbf
   L}A[0]\cong F\oplus(F\otimes^{\mathbf L}(\ker r)[0]).$$ Indeed tensor a K-flat representative
   of $F$ with the two inverse module maps of step 2: additivity of the total tensor gives the
   two inverse complex maps, and localization gives this isomorphism. By step 3,
   $F\otimes^{\mathbf L}A[0]$ is $m$-pseudo-coherent relative to $B$ on $Z$; by the
   all-affine-charts criterion (every affine chart of the open neighbourhood is a chart of $Z$,
   and such charts exist), its restriction to each neighbourhood is $m$-pseudo-coherent relative
   to $B$. Relative $m$-pseudo-coherence is invariant under isomorphism by its definition, so
   the relative direct-summand lemma gives it for $F$ on these neighbourhoods. Source locality
   glues them. We have therefore proved descent along each surjective finite locally free map,
   keeping the fixed $m$.

   Inputs: lem-sfb-relative-m-pseudocoherent-summands, def-pc-scheme-derived-tensor-structure,
   def-sfb-relative-pseudo-coherent-complex, lem-sfb-relative-pseudocoherence-local-on-source,
   lem-sfb-relative-pseudocoherence-all-affine-charts.

5. Now assume every $Lp_j^*E$ is $m$-pseudo-coherent relative to $B$. Apply the fppf refinement
   lemma to the scheme $X$ and the covering $\{X_j\to X\}$. It supplies opens $X=\bigcup_a U_a$,
   surjective finite locally free $W_a\to U_a$, opens $W_a=\bigcup_b W_{ab}$, surjective finite
   locally free $T_{ab}\to W_{ab}$, indices $j(a,b)$, and $X$-morphisms $\alpha_{ab}:T_{ab}\to
   X_{j(a,b)}$. Write $q_{ab}:T_{ab}\to X$ for the whole composite; then
   $p_{j(a,b)}\alpha_{ab}=q_{ab}$. The refinement is on $X$, not on $B$.

   Inputs: lem-trf-fppf-local-finite-free-refinement.

6. Each $q_{ab}$ is flat and locally of finite presentation: its factors are open immersions or
   finite locally free maps. For flatness, on local rings use composition of flat maps; for
   local finite presentation use its composition lemma. The open-immersion factors are
   localizations and thus flat and locally of finite presentation. Hence $\mathcal
   O_{T_{ab}}[0]$ is pseudo-coherent relative to $X$, as is $\mathcal O_{X_{j(a,b)}}[0]$. The
   maps to $X$ are locally of finite type, and $\alpha_{ab}$ is locally of finite type by
   cancellation from $p_{j(a,b)}\alpha_{ab}=q_{ab}$. Apply relative-composition invariance to
   $T_{ab}\xrightarrow{\alpha_{ab}}X_{j(a,b)}\to X$, with the object $\mathcal O_{T_{ab}}[0]$,
   for every integer degree. It is therefore pseudo-coherent relative to $X_{j(a,b)}$. No
   flatness of $\alpha_{ab}$ is needed.

   Inputs: def-pc-finite-locally-free, def-weil-flat-morphism,
   def-sbc-locally-finite-presentation, lem-weil-pbc-flat-ring-map-comp,
   lem-sbc-locally-finite-presentation-composition,
   lem-sfb-flat-lfp-structure-relative-pseudocoherence, lem-weil-pbc-proper-fp-permanence,
   lem-sfb-relative-pseudocoherence-composition.

7. Apply relative pullback to $\alpha_{ab}$ and $Lp_{j(a,b)}^*E$. All three morphisms in
   $T_{ab}\to X_{j(a,b)}\to B$ are locally of finite type by step 6 and composition with $X\to
   B$. The result and the composition isomorphism for derived pullback give $$Lq_{ab}^*E\cong
   L\alpha_{ab}^*Lp_{j(a,b)}^*E$$ $m$-pseudo-coherent relative to $B$. Every pulled-back complex
   that occurs in the refinement has quasi-coherent cohomology by preservation under derived
   pullback.

   Inputs: lem-sfb-relative-pseudocoherent-pullback,
   lem-pc-ringed-spaces-derived-pullback-composition, lem-weil-pbc-proper-fp-permanence,
   lem-pc-derived-pullback-tensor-qcoh.

8. Use the finite locally free descent proved in steps 2--4 on $T_{ab}\to W_{ab}$. It gives
   $m$-pseudo-coherence relative to $B$ for the pullback of $E$ to each $W_{ab}$. Source
   locality glues this on $W_a$. Use steps 2--4 again on $W_a\to U_a$, and source locality again
   on $X=\bigcup_a U_a$. The result is $m$-pseudo-coherence of $E$ relative to $B$. All
   intermediate structure maps to $B$ are locally of finite type, and all intermediate objects
   have quasi-coherent cohomology, as checked above. If $X$ is empty, the definition is vacuous
   and the same empty-cover assembly applies. No finite subcover or uniform cohomological bound
   is used.

   Inputs: lem-sfb-relative-pseudocoherence-local-on-source,
   def-sfb-relative-pseudo-coherent-complex.
-/
theorem isMPseudoCoherentRelativeTo_iff_fppf
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X B : Scheme.{u}} (f : X ⟶ B) [LocallyOfFiniteType f]
    (m : ℤ) (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E)
    {J : Type v} (Xj : J → Scheme.{u}) (p : ∀ j : J, Xj j ⟶ X)
    [∀ j : J, Flat (p j)] [∀ j : J, LocallyOfFinitePresentation (p j)]
    (hcover : ∀ x : X, ∃ (j : J) (y : Xj j), p j y = x) :
    IsMPseudoCoherentRelativeTo f m E ↔
      ∀ j : J, IsMPseudoCoherentRelativeTo (p j ≫ f) m ((derivedPullback (p j)).obj E) := by
  sorry

end AlgebraicGeometry.Scheme
