/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.SupportCohomology
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.Paper.SupportedSectionsHom
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import Sheaf.CategoryTheory.Abelian.RHomDerivedRoof

/-!
# Supported cohomology as morphisms

Source: blueprint sec-smooth-purity/sk-prop-a1-kummer/lem-pur-supported-hom.md,
order 1940 (blueprint: lem-pur-supported-hom).

The coefficient sheaf is pushed forward before being placed in degree zero.
The derived category is the ambient category of all module sheaves. The natural
isomorphism is between additive-group-valued functors on its bounded-below subcategory.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

private noncomputable def exactPostcompositionDerivedIso.{uC, uD, uE, vC, vD, vE, wC, wD, wE}
    {C : Type uC} {D : Type uD} {E : Type uE}
    [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    [HasDerivedCategory.{wE} E]
    [EnoughInjectives C] (F : C ⥤ D) [F.Additive]
    (G : D ⥤ E) [G.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits G]
    [CategoryTheory.Limits.PreservesFiniteColimits G] :
    (F ⋙ G).rightDerivedFunctorPlus ≅
      F.rightDerivedFunctorPlus ⋙ G.mapDerivedCategoryPlus := by
  let e : (F ⋙ G).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙ G.mapDerivedCategoryPlus :=
    Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ G.mapDerivedCategoryPlusFactorsh.symm
  exact Functor.rightDerivedNatIso _ _
    (F ⋙ G).rightDerivedFunctorPlusUnit
    (Functor.whiskerRight F.rightDerivedFunctorPlusUnit G.mapDerivedCategoryPlus ≫
      (Functor.associator _ _ _).hom)
    (HomotopyCategory.Plus.quasiIso C) e

namespace AlgebraicGeometry.ProEtale

/-- Supported cohomology is naturally the group of morphisms from the underived
closed direct image of the coefficient unit, placed in degree zero.
Source: blueprint sec-smooth-purity/sk-prop-a1-kummer/lem-pur-supported-hom.md,
order 1940 (blueprint: lem-pur-supported-hom).

Proof, following the six recorded DAG steps:

1. First identify the sections of the coefficient sheaf on every scheme $T$. Degree-zero
comparison [lem-cbc-abelian-etale-proetale-cohomology-comparison], with the constant-ring
identification [lem-sf-comparison-pullback-exact], identifies $A_T(T)$ on the pro-etale site with
the sections of the constant etale coefficient sheaf. The underlying set of a constant ring sheaf
is the constant set sheaf [lem-weil-pbc-ring-sheafification-underlying-sets]; the same
sheafification of the constant additive group identifies its additive structure. Thus
[lem-weil-pbc-constant-sheaf-sections-locally-constant] gives $A_T(T)=\operatorname{LC}(|T|,A)$.
Addition and multiplication are pointwise: on the open fibres both sections are constant and their
operations are the operations of $A$. Pullback along a scheme morphism sends a function to its
composite with the underlying continuous map: restrict to the open fibres, where the section is
the indicated constant and the comparison maps preserve that constant, then glue. For a weakly
etale $W\to X$, [lem-weil-proetale-weakly-etale-localization] identifies $A_X(W)$ with $A_W(W)$,
and also identifies $A_Z(W\times_XZ)$ with $A_{W\times_XZ}(W\times_XZ)$. These identifications
therefore describe restrictions as restrictions of locally constant functions. Uses:
lem-cbc-abelian-etale-proetale-cohomology-comparison, lem-sf-comparison-pullback-exact,
lem-weil-pbc-ring-sheafification-underlying-sets,
lem-weil-pbc-constant-sheaf-sections-locally-constant,
lem-weil-proetale-weakly-etale-localization.

2. Put $P=i_*A_Z$ and let $\rho:A_X\to P$ be the constant-coefficient structure map. By
[def-weil-proetale-module-direct-image] and step 1, its component at $W\to X$ restricts locally
constant functions from $|W|$ to the closed subspace $|W_Z|$, where $W_Z=W\times_XZ$. The
projection $W_Z\to W$ is a closed immersion by [lem-weil-pbc-closed-immersion-base-change], so its
underlying space is indeed the closed subspace used here. It is locally surjective. Indeed, given
$s:|W_Z|\to A$ locally constant and $z\in|W_Z|$, choose an open neighbourhood $V_z\subset W$ whose
intersection with $W_Z$ lies in the fibre of $s(z)$; the constant section $s(z)$ on $V_z$ lifts
$s$ there. On $W\setminus W_Z$ the target section is zero and lifts to zero. These opens cover
$W$. This Zariski cover is a pro-etale cover by [def-weil-pbc-proetale-site]. For each affine open
$B\subset W$, choose affine open neighbourhoods of its points contained in intersections of $B$
with members of the displayed cover; these exist since schemes are locally affine.
Quasi-compactness of $B$ [lem-weil-pbc-affine-scheme-qcqs] selects finitely many of these affine
neighbourhoods covering $B$, exactly as required in the covering definition. The
local-surjectivity criterion [lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective] makes the
underlying abelian map epic; it is also epic among module sheaves since equality of module maps is
equality of their underlying maps. This proves that $\rho$ is epic without imposing
quasi-compactness on $j$. Uses: def-weil-proetale-module-direct-image, def-weil-pbc-proetale-site,
lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective, lem-weil-pbc-affine-scheme-qcqs,
lem-weil-pbc-closed-immersion-base-change.

3. By [lem-pur-site-restriction-module-adjunction-exact], $j_!A_U$ is the sheafification of the
extension presheaf [def-weil-extension-by-zero-presheaf]. Construct $\epsilon:j_!A_U\to A_X$ as
follows. By clause (4) of [lem-weil-proetale-weakly-etale-localization], an object $W$ has at most
one map to $U$. When it has one, send its extension-presheaf section to the same section of
$A_X(W)$ under the coefficient identification of clause (2); otherwise use the zero map from the
zero presheaf value. These maps are module-linear and commute with restrictions by the presheaf
restriction formula, including the case of an arrow from an object mapping to $U$ to an object not
mapping to $U$, where the source restriction starts at zero. The universal property of
[def-weil-presheaf-modules-sheafification] gives $\epsilon$. The composite $\rho\epsilon$ is zero:
on every nonzero presheaf summand $W\to U$ one has $W_Z=\varnothing$ and $P(W)=0$, so the
composite is zero before sheafification and hence after it by
[def-weil-presheaf-modules-sheafification]. Conversely, for $f\in\ker(\rho_W)$, step 1 makes $f$ a
locally constant function vanishing on $W_Z$. Its nonzero locus $O\subset W$ is open and closed
and lies in $W\times_XU$. On $O$ the section $f|_O$ supplies a section of the extension presheaf
and thus of $j_!A_U$; on $W\setminus O$ take zero. They agree on the empty overlap and glue to a
section of $j_!A_U(W)$ mapping to $f$. Thus $\operatorname{im}(\epsilon)=\ker(\rho)$. Together
with the epimorphism of step 2 this proves that $P$ is the cokernel of $\epsilon$ in the abelian
category of module sheaves. Uses: lem-pur-site-restriction-module-adjunction-exact,
lem-weil-proetale-weakly-etale-localization, def-weil-extension-by-zero-presheaf,
def-weil-presheaf-modules-sheafification.

4. The cokernel universal property from step 3 gives
$\operatorname{Hom}(P,M)=\ker(\operatorname{Hom}(A_X,M)\to\operatorname{Hom}(j_!A_U,M))$. For any
module sheaf $N$ over a constant coefficient ring, evaluation on $1$ identifies
$\operatorname{Hom}(A_T,N)$ with $N(T)$: the inverse sends $s\in N(T)$ to the map $a\mapsto
a\,s|_V$ on each site object $V$. These are inverse module maps and commute with restrictions by
[def-weil-sheaf-of-modules-category]. Compute the other Hom group explicitly. By
[def-weil-presheaf-modules-sheafification], a map $\beta:j_!A_U\to M$ is uniquely a
module-presheaf map from the extension presheaf of [def-weil-extension-by-zero-presheaf] to $M$.
The site and coefficient identifications of [lem-weil-proetale-weakly-etale-localization] give
$\beta\mapsto\beta_U(1)\in M(U)$, where $1$ is taken in the unique $U\to U$ summand before
sheafification. Conversely, for $s\in M(U)$, on an object $V$ mapping to $U$ send $a\in
A_U(V)=A_X(V)$ to $a\,s|_V$; on an object not mapping to $U$ use the zero map from the zero
presheaf value. These maps commute with restrictions: when $V$ maps to $U$, semilinearity gives
$(a\,s|_V)|_{V'}=a|_{V'}\,s|_{V'}$; otherwise the source value is zero, including when $V'$ maps
to $U$. Sheafification gives the required map $\beta$. Evaluation returns $s$, and conversely
naturality along $V\to U$ gives $\beta_V(1)=\beta_U(1)|_V$, so linearity recovers
$\beta_V(a)=a\,\beta_U(1)|_V$ on every summand. Thus these constructions are inverse additive
identifications $\operatorname{Hom}(j_!A_U,M)\cong M(U)$. Under them precomposition with the
explicitly constructed $\epsilon$ is restriction $M(X)\to M(U)$, since its $U$-summand sends $1$
to $1$. Hence the displayed kernel is $\ker(M(X)\to M(U))=\Gamma_Z(X,M)$ by
[def-pur-support-cohomology]. We obtain an additive natural isomorphism
$v(M):=\operatorname{Hom}(P,M)\cong\Gamma_Z(X,M)$. Naturality holds because a module map $M\to N$
applies its section map to the same supported section on both sides. Uses:
def-weil-sheaf-of-modules-category, def-weil-presheaf-modules-sheafification,
def-weil-extension-by-zero-presheaf, lem-weil-proetale-weakly-etale-localization,
def-pur-support-cohomology.

5. Use the chosen small skeleton of $X_{\mathrm{proet}}$ and the module universe specified by
[def-weil-pbc-proetale-site]. Thus the small-site hypothesis of
[prop-pur-kinjective-resolutions-exist] holds, and the category $\mathcal A$ of all $A_X$-module
sheaves is Grothendieck. It has enough injectives: apply the termwise monic resolution of
[lem-pur-kinjective-degreewise-existence] to $M[0]$; its degree-zero component embeds each $M$
into an injective object. Put $w=\Gamma_Z(X,-)$ and let $\theta:v\xrightarrow{\sim}w$ be the
additive natural isomorphism of step 4. Applying $\theta$ termwise gives an isomorphism of
functors on bounded-below homotopy categories: its compatibility with each differential and with
homotopies is the naturality of $\theta$ and its additivity. The universal property in
[lem-weil-pbc-right-derived-plus-injective] derives this isomorphism without an additional
geometric hypothesis. Explicitly, let $\alpha_v:QK(v)\to RvQ$ and $\alpha_w:QK(w)\to RwQ$ be the
derived units. Apply clause (1) to $\alpha_w\circ QK(\theta)$ to obtain $\gamma:Rv\to Rw$, and to
$\alpha_v\circ QK(\theta^{-1})$ to obtain $\delta:Rw\to Rv$. Their composites satisfy
$(\delta\gamma)Q\circ\alpha_v=\alpha_v$ and $(\gamma\delta)Q\circ\alpha_w=\alpha_w$, since
$\theta^{-1}\theta$ and $\theta\theta^{-1}$ are identities. The uniqueness in clause (1) forces
both composites to be identities. By [def-pur-support-cohomology], $Rw=R\Gamma_Z(X,-)$, so
degree-$a$ cohomology gives $H_Z^a(X,F)\cong H^a(Rv(F))$, naturally in $F$. Uses:
def-weil-pbc-proetale-site, prop-pur-kinjective-resolutions-exist,
lem-pur-kinjective-degreewise-existence, lem-weil-pbc-right-derived-plus-injective,
def-pur-support-cohomology.

6. Apply [lem-sc-p1-rhom-hom-derived-roof] to the abelian category $\mathcal A$ from step 5, the
object $M=P=i_*A_Z$, the bounded-below object $F$, and $n=a$. Its statement gives
$H^a(Rv(F))\cong\operatorname{Hom}_{D(\mathcal A)}(P[0],F[a])$, natural in $F$, with no condition
on $P$ being projective or locally free. Concretely a cocycle $f:P\to I^a$ becomes the complex map
$P[0]\to I[a]$ and then is composed with the inverse of the shifted resolution isomorphism
$F[a]\to I[a]$. A boundary $d_I^{a-1}h$ gives the homotopy with sole component $(-1)^a h:P\to
I^{a-1}$ for the shifted differential, so the formula respects cohomology classes. Compose with
step 5. This is the displayed identification with the underived $i_*A_Z$ in degree zero, and
proves naturality for every integer $a$. Uses: lem-sc-p1-rhom-hom-derived-roof. -/
theorem supported_cohomology_hom (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (a : ℤ) :
    Nonempty
      ((derivedSupportSections i P.Coefficient ⋙
          DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) a ⋙
          forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}) ≅
        (DerivedCategory.Plus.ι ⋙
          shiftFunctor (ModuleDerivedCategory X P.Coefficient) a ⋙
          preadditiveCoyoneda.obj
            (op ((DerivedCategory.singleFunctor
              (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) 0).obj
                ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z)))))) := by
  classical
  let C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)
  let B : C := (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z)
  let G : ModuleCat.{u + 1} P.Coefficient ⥤ AddCommGrpCat.{u + 1} :=
    forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}
  let : CategoryTheory.Limits.PreservesFiniteLimits G := inferInstance
  let : CategoryTheory.Limits.PreservesColimitsOfSize.{u + 1, u + 1} G :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1, u + 1} P.Coefficient
  let : CategoryTheory.Limits.PreservesFiniteColimits G :=
    CategoryTheory.Limits.PreservesColimitsOfSize.preservesFiniteColimits.{u + 1, u + 1} G
  let V := preadditiveCoyoneda.obj (op B)
  let H := DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} a
  obtain ⟨θ⟩ := supported_sections_hom P i
  let eD : derivedSupportSections i P.Coefficient ⋙ G.mapDerivedCategoryPlus ≅
      V.rightDerivedFunctorPlus :=
    (exactPostcompositionDerivedIso (supportSections i P.Coefficient) G).symm ≪≫
      Functor.rightDerivedFunctorPlusNatIso θ
  let eH : derivedSupportSections i P.Coefficient ⋙
      DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) a ⋙ G ≅
        V.rightDerivedFunctorPlus ⋙ H :=
    Functor.isoWhiskerLeft (derivedSupportSections i P.Coefficient)
        (G.mapDerivedCategoryPlusHomologyFunctorIso a) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eD H
  obtain ⟨ψ, hnat, _⟩ := Functor.exists_rhom_hom_derived_roof B
  let eR : V.rightDerivedFunctorPlus ⋙ H ≅
      DerivedCategory.Plus.ι ⋙ shiftFunctor (ModuleDerivedCategory X P.Coefficient) a ⋙
        preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor C 0).obj B)) :=
    NatIso.ofComponents (fun F ↦ (ψ F a).toAddCommGrpIso)
      (by
        intro F F' g
        ext x
        exact hnat F F' g a x)
  exact ⟨eH ≪≫ eR⟩

end AlgebraicGeometry.ProEtale
