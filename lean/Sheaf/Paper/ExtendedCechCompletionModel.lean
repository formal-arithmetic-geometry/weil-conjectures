/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import Sheaf.CategoryTheory.LocalExtendedCechDescription
public import Sheaf.CategoryTheory.RingedCompletionUnit
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.Algebra.Homology.RhomGlobalSections

/-!
# Global extended Cech model and its derived completion unit

Source: Stacks Project, algebraization.tex, Tags 099E and 099F
(blueprint: lem-weil-pbc-extended-cech-completion-model).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A finite type ideal sheaf has a global augmented extended Cech model. For every such
model, internal Hom gives the reflection into the locally derived complete objects,
with the canonical augmentation-induced unit.

Source: Stacks Project, algebraization.tex, Tags 099E and 099F.
(blueprint: lem-weil-pbc-extended-cech-completion-model).

Proof:
1. Give the full subcategory $\mathcal C'$ of objects with finitely many generators the induced
coverings. Every object has a covering by these objects, by local finite generation. If $V\to U$
and $U\in\mathcal C\prime$, the restrictions of a finite generating list on $U$ generate $\mathcal
J|_V$, so $V\in\mathcal C\prime$. Consequently every covering of an object of $\mathcal C\prime$,
and every covering fibre product over that object, already lies in this full subcategory. Give it
exactly these coverings. The inclusion preserves coverings and their fibre products, which is
continuity as defined in [def-weil-pbc-sites-and-cohomology](3); the same covering itself supplies
the refinement required for cocontinuity. Faithfulness and fullness hold without refinement
because the subcategory is full; cover-density is the first observation. Apply
[lem-weil-pbc-special-cocontinuous-sheaf-equivalence]. Its equivalence preserves finite products,
so ring operations, module operations, and their equations extend uniquely under its
quasi-inverse; this gives an additive equivalence from modules over $\mathcal O$ to modules over
its restricted sheaf $u^*\mathcal O$. Equivalences preserve kernels and cokernels, hence
complexes, quasi-isomorphisms and augmentations. We may construct $K$ on $\mathcal C'$.

2. On $\mathcal C'/U$, choose a finitely generated $I\subset\mathcal J(U)$ generating $\mathcal
J|_U$. Define the presheaf complex at $V\to U$ to be $K(\mathcal O(V),I\mathcal O(V))$, with
restriction maps and augmentation supplied by [lem-weil-pbc-ring-complex-functorial]. Sheafify
degreewise; the differential still squares to zero and the augmentation remains a chain map
because sheafification is a functor.

3. For two such ideals $I=(a_1,\ldots,a_s)$ and $I'=(b_1,\ldots,b_t)$, each $a_i$ is locally a sum
$\sum_j c_{ij}b_j$ because $I'$ generates the ideal sheaf. Refine the finitely many covers for the
$a_i$, and then those expressing each $b_j$ in the $a_i$. On the resulting cover $U_k\to U$ both
inclusions of section ideals hold, hence $I\mathcal O(U_k)=I'\mathcal O(U_k)$. On every object
over $U_k$ the ring construction has identical inputs and identical maps, so the two presheaf
complexes agree there. Their sheafifications are canonically identified by these identities; any
two choices agree after the combined refinement, so the identification is unique with this local
identity property and satisfies the cocycle identity.

4. For $V\to U$, the restriction of the presheaf constructed with $I$ is literally the presheaf
constructed with $I\mathcal O(V)$. Step 3 identifies its sheafification with the choice for $V$.
Both successive restrictions and their composite are locally the identity on the same ring
construction, so the identifications satisfy the cocycle condition. Define
$K^n(U)=K_U^n(U\xrightarrow{1}U)$ and use these identifications for restriction maps. On a
covering the sheaf condition is exactly that of the sheaf $K_U^n$ on $\mathcal C'/U$. The
differentials and augmentations agree under restriction and therefore define $K^\bullet\to\mathcal
O[0]$. For a chosen list generating $I$, clause (d) of [lem-weil-pbc-ring-complex-functorial]
supplies an augmented derived isomorphism over $\mathcal O(U)$. Extend scalars to $\mathcal O_U$:
its localization terms become the specified sheafified localizations. The functorial chain maps
give a map from this derived scalar extension of $K(\mathcal O(U),I)$ to $K_U$; clause (c),
evaluated on every $V\to U$, makes it a quasi-isomorphism after sheafification, using exactness of
[lem-weil-pbc-ringed-site-module-sheafification-exact]. Thus the desired local Čech isomorphism
follows without selecting nonfunctorial isomorphisms independently at every $V$. Return along the
module equivalence of Step 1.

5. For any augmented model as in the statement put $F(E)=R\mathcal Hom(K,E)$ and
$\eta_E=\epsilon^*$. On a generating slice, [lem-weil-pbc-ringed-internal-hom-exact-restriction]
identifies this with $R\mathcal Hom(C_f,E|_U)$ and its augmentation unit. For a generator $f_i$,
[lem-weil-pbc-ringed-localization-rhom-calculus] identifies its derived internal Hom from
$\mathcal O_U[1/f_i]$ with $R\mathcal Hom((C_f)_{f_i},E|_U)$. Here $(C_f)_{f_i}$ is contractible:
for components indexed by sorted subsets $S$, set $(hx)_S=0$ if $i\in S$, and
$(hx)_S=(-1)^{|\{j\in S:j<i\}|}x_{S\cup\{i\}}$ otherwise, using invertibility of $f_i$ to identify
the localizations. In $dh+hd$ the term deleting $i$ is $x_S$; terms deleting any other index
cancel in pairs with opposite signs. Thus $dh+hd=1$, including degree zero. The internal Hom
vanishes for each generator on every further slice. By
[lem-weil-pbc-ringed-derived-complete-elements-ideal] its vanishing sections form an ideal sheaf,
hence contain every section of $\mathcal J$. This proves completeness of $F(E)$. For the empty
list the complex and unit are the identity, and localization at zero is zero.

6. If $L$ is complete, each nonempty product $g=\prod_{i\in S}f_i$ belongs to $\mathcal J(U)$, so
$R\mathcal Hom(\mathcal O_U[1/g],L|_U)=0$. The kernel $A_f$ of $C_f\to\mathcal O_U[0]$ has only
the positive-degree localization terms. Explicitly, let $F^pA_f$ be the subcomplex with the terms
of $A_f$ in degrees $\geq p$ and zero below $p$, for $1\leq p\leq r+1$. Then $F^1A_f=A_f$,
$F^{r+1}A_f=0$, and $F^pA_f/F^{p+1}A_f=A_f^p[-p]$, a finite sum of localizations shifted by $-p$.
The degreewise split short exact sequences give distinguished triangles. Exactness of internal Hom
[lem-weil-pbc-ringed-internal-hom-exact-restriction] applied successively to this filtration gives
$R\mathcal Hom(A_f,L|_U)=0$. Applying it to $A_f\to C_f\to\mathcal O_U$ proves that $\eta_L|_U$ is
an isomorphism. The cone of $\eta_L$ has zero cohomology on a generating cover, so its cohomology
sheaves vanish globally and $\eta_L$ is an isomorphism.

7. Let $Z_E$ be the cone of $\eta_E$. On a generating slice the triangle in Step 6 gives
$Z_E|_U\cong R\mathcal Hom(A_f,E|_U)$. Applying contravariant internal Hom to the successive
triangles of the explicit filtration in Step 6 expresses this object by finitely many
distinguished triangles whose other terms are shifts of $M_g=R\mathcal Hom(\mathcal
O_U[1/g],E|_U)$ for nonempty products $g$. A Hom-complex representative $\mathcal
Hom^\bullet(\mathcal O_U[1/g],I^\bullet)$, with $I^\bullet$ K-injective, has a termwise $\mathcal
O_U[1/g]$-action by precomposition; hence localization tensoring fixes it. Localization is flat
(sectionwise localization preserves exact sequences and sheafification is exact by
[lem-weil-pbc-ringed-site-module-sheafification-exact]), so also $M_g\otimes^{\mathbf L}\mathcal
O_U[1/g]\cong M_g$. For complete $L$, the tensor/internal-Hom identity of
[lem-weil-pbc-ringed-internal-hom-exact-restriction] gives $$R\mathcal Hom(M_g,L|_U)\cong
R\mathcal Hom(M_g\otimes^{\mathbf L}\mathcal O_U[1/g],L|_U)\cong R\mathcal Hom(M_g,R\mathcal
Hom(\mathcal O_U[1/g],L|_U))=0.$$ Applying internal Hom into $L|_U$ to those triangles and
inducting from the zero end implies $R\mathcal Hom(Z_E|_U,L|_U)=0$. Slice compatibility of the
same calculus node makes this the restriction of $R\mathcal Hom(Z_E,L)$; its cohomology sheaves
vanish on a cover and hence globally. Applying internal Hom into $L$ to $E\to F(E)\to Z_E$ now
gives an isomorphism $R\mathcal Hom(F(E),L)\to R\mathcal Hom(E,L)$. Taking zeroth derived global
sections using [lem-pur-rhom-global-sections] gives the required bijection
$\operatorname{Hom}(F(E),L)\to\operatorname{Hom}(E,L)$, induced by composition with $\eta_E$.
Naturality follows from the internal-Hom functor and the fixed augmentation. Together with Step 5
this proves the left adjoint for every augmented model with the stated local description. -/
theorem exists_ringedExtendedCech_completion_model
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [Mono ι] [I.IsFiniteType] :
    (∃ (K : ringedSiteComplex O) (ε : K ⟶ ringedSiteRingComplex O),
      HasLocalExtendedCechDescription O I ι K ε) ∧
    ∀ (K : ringedSiteComplex O) (ε : K ⟶ ringedSiteRingComplex O),
      HasLocalExtendedCechDescription O I ι K ε →
        (∀ E : ringedSiteDerived O,
          IsLocallyDerivedRingedIdealComplete O I ι ((ringedCechCompletionFunctor O K).obj E)) ∧
        (∀ (E E' : ringedSiteDerived O) (g : E ⟶ E'),
          ringedCechCompletionUnit O K ε E ≫ (ringedCechCompletionFunctor O K).map g =
            g ≫ ringedCechCompletionUnit O K ε E') ∧
        (∀ (E L : ringedSiteDerived O), IsLocallyDerivedRingedIdealComplete O I ι L →
          Function.Bijective
            (fun h : (ringedCechCompletionFunctor O K).obj E ⟶ L ↦
              ringedCechCompletionUnit O K ε E ≫ h)) ∧
        (∀ E : ringedSiteDerived O, IsLocallyDerivedRingedIdealComplete O I ι E →
          IsIso (ringedCechCompletionUnit O K ε E)) := by
  sorry

end CategoryTheory
