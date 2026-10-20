/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Paper.CoefficientRingedTensorHomModel
import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import Sheaf.CategoryTheory.RingedSiteDualityMaps
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.CategoryTheory.TruncationTriangle
import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import Sheaf.Paper.IntegralTensorShriek
import Sheaf.SixFunctors.IntTensorProjection
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison
import WeilConjectures.ConstructibleSheaf.Pullback
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.IntegralTensorPullback
import Sheaf.Paper.IntegralConstructibleHeart
import Sheaf.Paper.IntegralModels

/-!
# The ordinary integral derived tensor product

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-int-tensor,
`det-lem-int-tensor-product.md` and its proof (blueprint: det-lem-int-tensor-product).

All tensors use the ambient K-flat derived monoidal structure over the pulled-back
continuous condensed valuation ring. Constructibility uses finite constant scalar models.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The point inverse image is a left adjoint, by its point adjunction and the scheme
inverse-image adjunction. This supplies additivity for termwise scalar extension.
Source: blueprint det-lem-int-tensor-product, local model P tensor R_S
(blueprint: det-lem-int-tensor-product). -/
noncomputable instance integralTensorProduct_point_isLeftAdjoint (X : Scheme.{u}) :
    (upperStarFromPoint X).IsLeftAdjoint :=
  letI : pointUpperStar.{u}.IsLeftAdjoint := pointUpperStarLowerStarAdjunction.isLeftAdjoint
  inferInstanceAs ((pointUpperStar ⋙ upperStar Ab.{u + 1} (toSpecZ X)).IsLeftAdjoint)

/-- The uncompleted integral tensor preserves bounded constructibility, and local bounded
finite free scalar complexes are dualizable and preserve products, sequential derived limits
and derived completeness.

Source: blueprint main-20261015, det-lem-int-tensor-product
(blueprint: det-lem-int-tensor-product).

Proof (the DAG steps, in order):
1. Use a small skeleton of each pro-étale site. The internal-module category can be treated as
sheaves of modules over its reconstructed section ring, by
[def-weil-pbc-internal-abelian-sheaf-module-equivalence]. Its hypotheses hold here: abelian
sheafification and monoidality of its local equivalences are supplied by
[lem-weil-pbc-sheaf-tensor-closed]. This equivalence is identity on the underlying abelian
sheaves, hence exact. The coequalizer defining relative module tensor in
[def-sfb-modobj-relative-tensor] represents bilinear maps balanced for the section-ring action, so
under this equivalence it is exactly sheaf tensor over that ring. Consequently the equivalence
identifies the K-flat derived tensors and their internal-Hom right adjoints. All tensors below are
these ambient tensors, without completion.  They are exact in each variable: represent a fixed
argument by a K-flat resolution with flat terms, available on a ringed site by
[lem-pc-kflat-resolution]. The K-flat tensor functor is triangulated by
[lem-sc-source-kflat-tensor-left-triangulated]; the derived tensor of
[sk-def-sfb-derived-tensor-hom] is this functor. Symmetry gives exactness in the other variable.
The hypotheses apply both to $R_S$-module sheaves and to constant residue-field module sheaves.
2. First compute the dual on a chart, over any small ringed site $(\mathcal C,R)$. Let $T$ be a
bounded complex of finite free $R$-modules and put $D_T=\mathcal Hom^\bullet_R(T,R[0])$. Each
$\mathcal Hom_R(T^i,-)$ is exact and is a finite sum of the identity functor by
[lem-sc-finite-free-internal-hom-exact]. Therefore [lem-pc-bounded-exact-term-hom-quasi-iso],
applied to a K-injective replacement of an arbitrary complex $F$, shows that $\mathcal
Hom^\bullet_R(T,F)$ computes $R\mathcal Hom_R(T,F)$ as defined in [def-pur-derived-internal-hom].
The complex $D_T$ is bounded finite free, hence K-flat by [lem-pc-bounded-above-flat-kflat-site].
For each degree $n$, the evaluation map $$\bigoplus_{a+b=n}
F^a\otimes_R(D_T)^b\longrightarrow\prod_i\mathcal Hom_R(T^i,F^{i+n})$$ is an isomorphism: only
finitely many $i$ occur, and for $i=-b$ the summand map sends $y\otimes\phi$ to $(x\mapsto
y\phi(x))$. In a basis its inverse sends $f:T^i\to F^{i+n}$ to $\sum_j f(e_j)\otimes e_j^*$. It is
a chain map: the dual differential is $d\phi=(-1)^{b+1}\phi d_T$, so the second
tensor-differential term has sign $(-1)^{a+b+1}$, exactly the second term of $df=d_Ff-(-1)^nf d_T$
in [def-pur-hom-complex] and [def-pc-tensor-complex-sheaves]. Thus the canonical comparison
$F\otimes_R^{\mathbf L}D_T\to R\mathcal Hom_R(T,F)$ is an isomorphism for every $F$, not merely
for bounded or constructible $F$.
3. Now let $M$ have the local models of the statement and set $D=R\mathcal Hom_{R_S}(M,R_S)$. For
a covering chart $W\to S$, [lem-weil-proetale-weakly-etale-localization] identifies its pro-étale
site with the slice; Apply the untwisted clause (1) of [sk-prop-sfb-cartesian-coefficients] to
$f:W\to S$ and the admissible condensed ring $\Lambda=\underline{\mathcal O_E}$: its canonical
ring isomorphism $f^{-1}R_S\simeq R_W$ identifies the restricted ring with $R_W$. This clause
applies to arbitrary schemes and morphisms; it imposes no invertibility condition on $S$, and
neither its Tate-twist clause nor its finite-extension clause is used. On each chart, derived
internal Hom restricts to internal Hom on the slice by
[lem-weil-pbc-ringed-internal-hom-exact-restriction]. Tensor restricts to tensor by
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback], applied to the slice morphism with its
restricted coefficient ring. Thus for every $N$ the canonical global evaluation comparison
$$u_N:N\otimes_{R_S}^{\mathbf L}D\longrightarrow R\mathcal Hom_{R_S}(M,N)$$ restricts to the
isomorphism in step 2, since $P\otimes_{\mathcal O_E}R$ is a bounded finite free complex. It
follows that $u_N$ is an isomorphism globally. Here only detection of isomorphisms is local: slice
restriction is exact by [lem-pur-site-restriction-module-adjunction-exact], so kernels and
cokernels of each $H^q(u_N)$ restrict to zero. Every section of either sheaf is locally zero on
the given covering, hence zero by the sheaf axiom. Apply
[lem-weil-pbc-unbounded-derived-iso-cohomology] to conclude. This argument uses a small skeleton
of the pro-étale site as in [def-weil-pbc-proetale-site].
4. The closed adjunction of [sk-def-sfb-derived-tensor-hom], followed by $u_B^{-1}$, gives natural
bijections $$\operatorname{Hom}(M\otimes^{\mathbf L}A,B)\simeq\operatorname{Hom}(A,R\mathcal
Hom(M,B))\simeq\operatorname{Hom}(A,B\otimes^{\mathbf L}D).$$ Suppress associators and the
symmetry that moves $B$ past $M,D$. Write $e:D\otimes^{\mathbf L}M\to R_S$ for evaluation. Since
$u_B$ is the canonical evaluation comparison, the inverse bijection takes $h:A\to
B\otimes^{\mathbf L}D$ to the contraction of $M\otimes^{\mathbf L}h$ by $e$. Let $c:R_S\to
M\otimes^{\mathbf L}D$ correspond to $1_M$ at $(A,B)=(R_S,M)$. Transposing this defining equality
gives $(1_M\otimes e)(c\otimes1_M)=1_M$. Tensoring this equality with $1_A$ shows that
$c\otimes1_A$ transposes to $1_{M\otimes A}$, so it is the adjunction unit at $A$. The
inverse-bijection formula gives the counit at $B$ as contraction with $e$. The other adjunction
triangle, on the right-adjoint image of $R_S$, is therefore $(e\otimes1_D)(1_D\otimes c)=1_D$.
Thus $e,c$ satisfy both duality identities globally. Symmetry interchanges the two dual objects
and gives also $D\otimes^{\mathbf L}-\dashv M\otimes^{\mathbf L}-$.
5. Write $T_M=M\otimes^{\mathbf L}-$. The adjunction $D\otimes^{\mathbf L}-\dashv T_M$ implies
product preservation directly: for any $A$ and family $(N_i)$,
$$\operatorname{Hom}(A,T_M\prod_iN_i)\simeq\operatorname{Hom}(D\otimes^{\mathbf
L}A,\prod_iN_i)\simeq\prod_i\operatorname{Hom}(A,T_MN_i).$$ The bijections respect projections, so
they identify the canonical product comparison. Step 1 gives exactness, and
[lem-pc-homotopy-limit-map] then identifies $T_M(R\varprojlim_nN_n)$ with
$R\varprojlim_nT_M(N_n)$. For $B_n=(\mathcal O_E/\pi_E^n)_S$, associativity gives
$(T_MN)\otimes^{\mathbf L}_{R_S}B_n\simeq T_M(N\otimes^{\mathbf L}_{R_S}B_n)$ as $R_S$-complexes.
These are the canonical associations of the same threefold tensor, so they commute with
$B_{n+1}\to B_n$ and with $N\to N\otimes^{\mathbf L}B_n$. If $N$ is complete, apply $T_M$ to its
completion isomorphism and the preceding limit comparison. The result is exactly the canonical
completion map for $T_MN$, hence an isomorphism by [sk-def-pe-derived-completion]. This proves
every assertion in the second paragraph of the imported statement.
6. We next verify tensor closure with the residue field $\kappa=\mathcal O_E/\pi_E$, which is a
field by [def-weil-l-adic-coefficient-extension]. Every sheaf $F$ of $\kappa_S$-modules is flat.
To apply [lem-pc-sites-modules-sheafification-flat], view $F$ as a presheaf of modules over the
constant presheaf $\kappa$. Each $F(U)$ is a vector space, so tensoring with it preserves finite
limits of vector spaces (choose a basis, so this is a direct sum of copies of the identity).
Finite limits of presheaves are sectionwise; the hypotheses of that lemma hold. The ring
sheafification is $\kappa_S$ and the module sheafification is $F$ with its original action, by
[lem-pc-sites-module-sheafification-interface]. This proves finite-limit preservation of sheaf
tensor with $F$; sheaf tensor is also a left adjoint by [lem-pc-sheaf-modules-tensor-closed], so
it preserves cokernels and is exact. In particular $F[0]$ is K-flat by
[lem-pc-bounded-above-flat-kflat-site], and $F[0]\otimes^{\mathbf L}G[0]=(F\otimes G)[0]$ for
module sheaves.
7. For constructible $\kappa_S$-module sheaves $F,G$ on the Noetherian scheme $S$, intersect the
strata of their two finite stratifications: base-changing the stratification of $G$ along each
stratum immersion $Z_a\to S$ of $F$ gives, by [lemma-constructible-pullback-stratification], a
stratification of $Z_a$ with strata $Z_a\times_S Z'_b$, and the composites $Z_a\times_SZ'_b\to S$
form a finite stratification of $S$ refining both; its strata are constructible since $S$ is
Noetherian. Restriction to a stratum or to an object of a pro-étale cover is module inverse image
along a morphism $g$; by clause (1) of [sk-prop-sfb-cartesian-coefficients] for the finite
admissible ring $\kappa$, $g^{-1}\kappa_S\simeq\kappa_T$, so restrictions of $\kappa_S$-modules
are $\kappa_T$-modules and the restriction of a local model $\kappa_U\otimes_\kappa P$ is again
$\kappa\otimes_\kappa P$ over the new coefficient sheaf. On each intersection refine a
trivializing cover for $F$ by the pullbacks of a trivializing cover for $G$; the covering axiom
makes this a common cover. The finite constant local models in [sk-def-sfb-constructible] are
finitely presented, hence finite-dimensional, $\kappa$-vector spaces, so choose bases giving
$F|_V\simeq\kappa_V^r$, $G|_V\simeq\kappa_V^s$ on each covering object $V$. Since $F$ and $G$ are
flat (step 6), their tensor is the derived tensor, and
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback] (applied to the restriction morphism with the
ring isomorphism above) gives $(F\otimes G)|_V\simeq F|_V\otimes G|_V$. The basis $e_i\otimes f_j$
identifies this with $\kappa_V^{rs}$. It is therefore a finite constant local model on each
stratum, and $F\otimes G$ is constructible. This includes rank zero and the empty stratum.
8. Let $A,B\in\Dbc(S,\kappa)$ with $S$ a standing scheme. The truncation triangles of
[lem-weil-pbc-truncation-triangle] express each bounded object as finitely many extensions of
shifts of its constructible cohomology sheaves. Steps 6 and 7 compute the tensor of any pair of
these sheaves as a constructible sheaf. By step 1 tensor is exact in both variables, and
[sk-def-sfb-bounded-constructible] says that the bounded constructible category is triangulated on
this Noetherian $S$. Induct first through the finitely many truncation triangles for $A$ and then
those for $B$ to obtain $A\otimes^{\mathbf L}_{\kappa_S}B\in\Dbc(S,\kappa)$. A cohomological bound
is $[a+c,b+d]$ when the input bounds are $[a,b]$, $[c,d]$, since the tensor of $H^i(A)[-i]$ and
$H^j(B)[-j]$ is concentrated in degree $i+j$.
9. Fix $L\in\Dbc(X,\mathcal O_E)$. By step 1 and the triangulatedness assertion (1) of
[sk-lem-int-integral-heart], the full class of $K$ for which $K\otimes^{\mathbf L}_{R_X}L$ is
bounded constructible is closed under isomorphisms, shifts and extensions. Clause (2) of
[det-lem-int-tensor-shriek] therefore reduces the claim to $K=a_!M$, where $a:S\hookrightarrow X$
is a stratum inclusion and $M\in\Dbc(S,\mathcal O_E)$ has the finite-free local models in the
statement. A locally closed subscheme of a standing scheme is again separated finite type over
$k$. The projection isomorphism in [det-lem-int-tensor-projection] gives $$(a_!M)\otimes^{\mathbf
L}_{R_X}L\simeq a_!(M\otimes^{\mathbf L}_{R_S}a^*L).$$ Clause (1) of [det-lem-int-tensor-shriek]
says that $a_!$ preserves the integral category, so it remains to treat the inside tensor.
10. By clause (1) of [det-lem-int-tensor-pullback], $N=a^*L$ lies in $\Dbc(S,\mathcal O_E)$.
Clause (2) of [sk-lem-integral-models] says precisely that $M$ and $N$ are derived complete and
their reductions $\bar M,\bar N$ modulo $\pi_E$ are bounded constructible complexes over the
constant field $\kappa_S$. Step 5 shows that $M\otimes^{\mathbf L}_{R_S}N$ is derived complete.
Apply [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] to the identity topos with ring map
$R_S\to\kappa_S$. Its monoidal scalar-extension isomorphism gives $$(M\otimes^{\mathbf
L}_{R_S}N)\otimes^{\mathbf L}_{R_S}\kappa_S\simeq\bar M\otimes^{\mathbf L}_{\kappa_S}\bar N.$$ The
right side is bounded constructible by step 8. It is pulled back from the étale site by
[sk-thm-pe-constructible-comparison], applicable because $S$ is Noetherian and hence qcqs and
$\kappa$ is a discrete Noetherian ring. The two conditions of clause (2) of
[sk-lem-integral-models] now imply $M\otimes^{\mathbf L}_{R_S}N\in\Dbc(S,\mathcal O_E)$. This uses
that node's actual residue criterion, replacing the nonexistent node sk-prop-integral-criterion in
the imported proof.
11. Apply $a_!$ to the membership established in step 10 and use step 9's projection isomorphism.
This proves the claim for every generator $a_!M$. Induction through the finite extension
construction supplied in step 9 proves it for every $K\in\Dbc(X,\mathcal O_E)$. Throughout, the
tensor was the ambient uncompleted tensor; completeness was proved, not imposed by replacing it
with a completed tensor.
-/
theorem integralTensorProduct
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpl : p ≠ l) :
    (∀ (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
      [QuasiCompact (X ↘ Spec (.of k))]
      (K L : DerivedCategory (AdicCompletion.Modules l E X)),
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K →
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X L →
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X (K ⊗ L)) ∧
    (∀ (S : Scheme.{u}) (M : DerivedCategory (AdicCompletion.Modules l E S)),
      (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage S, ∀ i : C.I₀,
        ∃ P : CochainComplex (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
          (DerivedNakayama.integerRing l E)) ℤ,
          (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
          (∀ n : ℤ, Mod.IsFree (DerivedNakayama.integerRing l E) (P.X n)) ∧
          Nonempty
            ((CondensedRing.upperStar (DerivedNakayama.integerRing l E)
                (C.f i)).mapDerivedCategory.obj M ≅
              DerivedCategory.Q.obj
                (((DerivedNakayama.pullback l E (C.X i)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj P))) →
      IsDualizable M ∧
        (∀ I : Type w, PreservesLimitsOfShape (Discrete I) (tensorLeft M)) ∧
        (∀ (F : ℕᵒᵖ ⥤ DerivedCategory (AdicCompletion.Modules l E S)) (c : Cone F),
          IsHomotopyLimit c → IsHomotopyLimit ((tensorLeft M).mapCone c)) ∧
        (∀ N : DerivedCategory (AdicCompletion.Modules l E S),
          IsDerivedComplete l E S N → IsDerivedComplete l E S (M ⊗ N))) := by
  sorry

end AlgebraicGeometry.ProEtale
