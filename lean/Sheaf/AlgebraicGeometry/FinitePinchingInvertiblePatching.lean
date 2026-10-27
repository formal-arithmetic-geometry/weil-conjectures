module

public import Sheaf.AlgebraicGeometry.PinchingLineData
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.AlgebraicGeometry.AffineCapSectionOpenDictionary
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.RingTheory.FiniteProjectivePrimeLocalFree
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.Topology.GlueSheavesOfModules
import Mathlib.RingTheory.Flat.Basic

/-! # Invertible sheaves on finite pinching squares

Source: Stacks Project, More on Algebra, Tags 0D2J and 07RU, applied to
rank-one finite projectives and glued on the stated affine cover
(blueprint: lem-sfb-finite-pinching-invertible-patching).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback is an equivalence on line-bundle triples and all their morphisms;
tensor products and allowed base changes use the specified canonical comparisons.
Flat base changes preserve the affine hypothesis. No nonemptiness assumption is imposed.

Source: Stacks Project, More on Algebra, Tags 0D2J and 07RU; Modules, Tag 01CT
(blueprint: lem-sfb-finite-pinching-invertible-patching).

Proof plan (the reviewed seven-step split):
1. Fix a chart $U=\operatorname{Spec}R$ in the assumed cover. Write $M_A=\Gamma(v^{-1}U,M)$ and
$N_B=\Gamma(Z\times_XU,N)$. The affine invertible-sheaf dictionary makes these finite projectives
of rank one, and the affine pullback formula turns $\alpha$ into $F\otimes_A M_A\simeq F\otimes_B
N_B$. Apply finite-projective patching to construct the actual module $P_U=\{(m,n):\alpha(1\otimes
m)=1\otimes n\}$. It is finite projective over $R$, and its two scalar extensions, with their
specified comparison on $F$, are precisely the given modules and comparison. On morphisms the
construction sends $(a,b)$ to the restriction of $a\oplus b$ to this kernel. The affine tilde
equivalence turns module homomorphisms into all morphisms of the associated quasi-coherent
sheaves. The general patched-module comparison gives these projection counits even before imposing
finite projectivity.
Uses: lem-sc-affine-cap-section-open-dictionary, lem-weil-pbc-module-pullback-affine-sections,
lem-sfb-fibre-product-finite-projective-patching, lem-weil-pbc-affine-tilde-gamma-adjunction,
lem-sfb-patched-module-base-change.
2. The finite projective $P_U$ has rank one at every prime. Indeed put $J=\ker(R\to B)$;
surjectivity of $A\to F$ shows $R\to B$ is surjective and identifies $J$ with $\ker(A\to F)$. If
$\mathfrak p\supseteq J$, let $\mathfrak q=\mathfrak p/J\in\operatorname{Spec}B$. A standard-open
free neighbourhood of $\mathfrak p$ for $P_U$ has some rank $d$. After tensoring its fibre with
$\kappa(\mathfrak q)=\kappa(\mathfrak p)$, the projection comparison identifies it with the
rank-one fibre of $N_B$, so $d=1$. If $\mathfrak p\not\supseteq J$, choose $r\in
J\setminus\mathfrak p$. Localizing $0\to R\to A\oplus B\to F\to0$ at $r$ gives $R_r=A_r$, since
$B_r=F_r=0$. Hence $\mathfrak p$ corresponds to a prime of $A_r$; the same free-neighbourhood and
fibre calculation, now with $M_A$, gives rank one. Principal-open sections of $\widetilde {P_U}$
are these localizations, so these rank-one free neighbourhoods trivialize $L_U=\widetilde {P_U}$.
Thus $L_U$ is invertible. Conversely an invertible sheaf on $U$ has finite projective rank-one
sections by the affine dictionary, and the unit of patching recovers those sections. Consequently
pullback on this chart is fully faithful on all module maps and essentially surjective on
line-bundle triples.
Uses: lem-sfb-fibre-product-finite-projective-patching,
lem-weil-pbc-finite-projective-prime-local-free, lem-weil-pbc-localization-module-exact,
lem-weil-pbc-spec-module-tilde-sections, lem-sc-affine-cap-section-open-dictionary.
3. These constructions commute with principal-open restriction. For $r\in R$, exactness of
localization applied to the two kernels $R=\ker(A\oplus B\to F)$ and $P_U=\ker(M_A\oplus N_B\to
F\otimes_BN_B)$ identifies $R_r=A_r\times_{F_r}B_r$ and
$(P_U)_r=\{(m,n)\in(M_A)_r\oplus(N_B)_r:\alpha_r(1\otimes m)=1\otimes n\}$. The ring map $A_r\to
F_r$ remains surjective: a preimage of a fraction is obtained by lifting its numerator. The
principal-open descriptions of tilde sections identify the localized projection maps with the
restricted projection maps. Therefore the fully faithful affine equivalence of steps 1--2 also
holds on every such principal open.
Uses: lem-weil-pbc-localization-module-exact, lem-weil-pbc-spec-module-tilde-sections.
4. For charts $U_i,U_j$, their intersection has a cover by opens principal in both affine charts.
On each such open, step 3 and affine full faithfulness give a unique isomorphism $L_{U_i}\simeq
L_{U_j}$ inducing the identity on the prescribed triple. On smaller opens the maps agree, because
they agree on a principal-open basis and affine full faithfulness is faithful there. Glue these
maps over the intersection. On triple intersections their two possible composites induce the same
identity triple, and equality can again be checked on a principal-open basis inside one chart.
Thus the transition maps satisfy the cocycle condition. Gluing modules produces $L$ on $X$,
invertible because this is local on $X$, with the desired pullback identifications. The same
argument glues the unique local lift of any morphism of triples. It also proves uniqueness of that
lift globally. Thus pullback is an equivalence of the categories stated in the item. Applying the
bijection on Hom sets to invertible endomorphisms identifies automorphisms as well: lifts of an
inverse are inverse by faithfulness.
Uses: lem-sc-affine-inter-principal-both, lem-weil-pbc-spec-localization-away-basic-open,
lem-weil-pbc-glue-sheaves-of-modules.
5. For two triples take their tensor product componentwise and tensor their overlap
identifications. The sheaf $L_1\otimes L_2$ is invertible, and the canonical pullback comparisons
identify its triple with that tensor-product triple: on simple tensors the comparison is
$(1\otimes x)\otimes(1\otimes y)\mapsto1\otimes(x\otimes y)$. Full faithfulness yields the unique
comparison between $L_1\otimes L_2$ and the sheaf reconstructed from the tensor-product triple.
Its inverse lifts the inverse triple map. The unit comparison uses the diagonal identification
$R=A\times_FB$ on each chart. The associativity, symmetry and unit diagrams commute because their
pullbacks act identically on the displayed simple tensors, and pullback is faithful. This proves
tensor compatibility.
Uses: lem-weil-pbc-invertible-pullback-tensor.
6. Let $T\to S$ be a base change satisfying the stated affine hypothesis. Pullback of the
reconstructed $L$ to $X_T$ is invertible. Its restrictions to $X^{\prime}_T$ and $Z_T$ identify
with the pulled-back $M,N$ by the canonical composition comparison for pullback; on $Z^{\prime}_T$
the overlap comparison is the pullback of $\alpha$. Apply the equivalence already proved on the
new square: full faithfulness gives a unique isomorphism from the reconstruction of this new
triple to $L|_{X_T}$ inducing those identifications. This is natural in triple morphisms by
faithfulness. For two successive allowed base changes the composite comparison and the direct
comparison induce the same maps on both components, by the pullback composition formula, so are
equal. The identity base change likewise gives the identity. This establishes the asserted
naturality without claiming that tensoring an arbitrary kernel is exact.
Uses: lem-weil-pbc-invertible-pullback-tensor.
7. Finally suppose $T\to S$ is flat. The map $X_T\to X$ is flat by flat base change; on an affine
open $\operatorname{Spec}C\subseteq X_T$ mapping into a chosen $U=\operatorname{Spec}R$, the
affine criterion makes $C$ flat over $R$. The three inverse-image charts have rings $A\otimes_R
C$, $B\otimes_R C$, $F\otimes_R C$ by the affine fibre-product formula. Tensoring $0\to R\to
A\oplus B\to F\to0$ with $C$ preserves its kernel, so $C\cong(A\otimes_R C)\times_{F\otimes_R
C}(B\otimes_R C)$. Surjectivity of the first map to $F\otimes_R C$ follows by lifting numerators
of simple tensors. Finite generation of $A$ over $R$ persists by tensoring a finite list of
generators, and $R\to B$ being a quotient remains a quotient after tensoring. Thus the
base-changed square satisfies all the hypotheses on an affine cover, and step 6 applies. If $Z$ is
empty, then $B=F=0$ on every chart, $R=A$ and $P_U=M_A$. There is a unique module on the empty
scheme and a unique overlap identification, so the same construction gives precisely the asserted
equivalence, including automorphisms and tensor products.
Uses: lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-flat-morphism-affine-criterion,
lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-flat-tensor-exact.
-/
theorem finite_pinching_invertible_patching
    {S X A B : Scheme.{u}} (p : X ⟶ S) (v : A ⟶ X) (j : B ⟶ X)
    [IsFinite v] [IsClosedImmersion j] (h : HasAffinePinchingCover v j) :
    PinchingLineEquivalence v j ∧
    (pinchingUnitTriple v j).IsLift (𝟙_ X.Modules) (pinchingUnitIso v) (pinchingUnitIso j) ∧
    (∀ (D E : PinchingLineTriple v j) (P : PinchingLineLift D) (Q : PinchingLineLift E),
      (D.tensor E).IsLift (P.line ⊗ Q.line)
        ((Classical.choose (module_pullback_tensor v)) P.line Q.line ≪≫ (P.left ⊗ᵢ Q.left))
        ((Classical.choose (module_pullback_tensor j)) P.line Q.line ≪≫
          (P.right ⊗ᵢ Q.right))) ∧
    (∀ (T : Scheme.{u}) (t : T ⟶ S),
      HasAffinePinchingCover (pinchingBaseMap p v t) (pinchingBaseMap p j t) →
      PinchingLineEquivalence (pinchingBaseMap p v t) (pinchingBaseMap p j t) ∧
      ∀ (D : PinchingLineTriple v j) (P : PinchingLineLift D),
        (D.baseChange p t).IsLift ((tensorPullback (pullback.fst p t)).obj P.line)
          (pinchingBaseProjection p v t P.line ≪≫
            (tensorPullback (pullback.fst (v ≫ p) t)).mapIso P.left)
          (pinchingBaseProjection p j t P.line ≪≫
            (tensorPullback (pullback.fst (j ≫ p) t)).mapIso P.right)) ∧
    (∀ (T : Scheme.{u}) (t : T ⟶ S) [Flat t],
      HasAffinePinchingCover (pinchingBaseMap p v t) (pinchingBaseMap p j t)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
