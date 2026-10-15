/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Sheaf.Paper.SiteSheafificationSectionsLocal
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.Paper.SiteRestrictionExact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Sheaf.AlgebraicGeometry.ProEtaleQcqsSiteLimits

/-!
# Finite-presentation section calculus on the qcqs pro-etale site

Source: Stacks Project, Tags 0738 (4), 0GMZ, 0GN0 and 098D
(blueprint: lem-weil-pbc-proetale-qcqs-fp-section-calculus).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry


/-- Source: Stacks Project, Tags 0738 (4), 0GMZ, 0GN0 and 098D
(blueprint: lem-weil-pbc-proetale-qcqs-fp-section-calculus).
Sections over a qcqs scheme and Hom from a locally finitely presented module commute
with filtered sheaf colimits. Both comparisons use the chosen colimit coprojections;
equality of representatives is witnessed at a common stage.

Proof plan from the DAG:
1. Work throughout in `\mathcal C=V_{\mathrm{proet}}`. Every covering of a qcqs object `T` has a
finite affine refinement: choose a finite affine open cover of `T`, and over each open use the
finite list of affine source opens in the definition of a pro-etale covering. Their union is
finite, still covers, and refines the original covering. The opens and composites are arrows of
the site by its definition. For two members `U_a,U_b`, the map `U_a\to T` is qcqs by qcqs
morphism permanence (1); base change (3) and composition with the qcqs scheme `U_b` in (2) show
that `U_a\times_TU_b` is qcqs. Its fibre product exists in the site by the qcqs-site-limits
node. Thus every qcqs `T` has finite affine covering refinements with qcqs overlaps; no
intersection is assumed affine.
2. For a small filtered diagram of abelian groups `B_i`, use the set of pairs `(i,b)` modulo
`(i,b)\sim(j,c)` when there are arrows `i\to k\leftarrow j` giving equal images. Filteredness
makes this transitive: take a common target of two equality witnesses and equalize the two
arrows from their shared middle index. Define addition by sending two representatives to a
common stage and adding there; further common targets and equalization show independence of the
choices. Zero and negatives are represented by zero and negatives at a stage. Every compatible
cocone induces exactly one homomorphism on these classes, so this is the abelian-group colimit
by the colimit universal property. The same construction with scalar multiplication is the
colimit of modules over a fixed ring. Consequently every element has a stage representative,
equality is witnessed by arrows to a common stage, and any finite collection of representatives
and equality witnesses can be moved to one stage. The last assertion follows by repeatedly
taking common targets and equalizing the finitely many parallel arrows; it does not require the
filtered category to be a poset.
3. Let `(F_i)` be the abelian-sheaf diagram and put `F=\varinjlim_iF_i`. Its colimit is the
sheafification of the presheaf `Q(T)=\varinjlim_iF_i(T)` by the site-abelian-colimits node. The
underlying set sheafification agrees with abelian sheafification by the underlying-sets node.
Thus the local-sections node applies: sections of `F` are locally images of elements of `Q`, and
two elements of `Q(T)` with the same image are equal after a covering of `T`. By step 2 these
local elements lift to actual stage sections and these local equalities are eventual equalities.
All these assertions use the supplied coprojections: the identification of the sheafification
with `F` is the unique isomorphism respecting them. Enlarge the working set universe, as allowed
by the size convention, to contain the site and diagram data; this satisfies the local-sections
node's universe hypothesis. Abelian sheaves satisfy the cited module-sheaf sheaf axiom by their
canonical integer action `n x=x+\cdots+x` (and negatives), so steps 4 and 5 may use that
definition for them.
4. For any qcqs object `T`, suppose `s\in F_i(T)` and `s'\in F_j(T)` have the same image in
`F(T)`. By step 3 they become equal in `Q` on a covering. Refine it to the finite affine
covering of step 1. On each member step 2 supplies arrows to a stage where the restricted
sections agree. Choose a common target and equalize the finitely many arrows from `i` and `j` so
that there is one chosen arrow from each of these indices. At that stage the two sections agree
on the finite covering and hence on `T` by the sheaf separation axiom. This proves injectivity
of `\varinjlim_iF_i(T)\to F(T)`, including its eventual-equality form.
5. For `t\in F(T)` with `T` qcqs, step 3 and then step 1 give a finite affine cover `(U_a\to T)`
and stage sections `s_a` representing `t|_{U_a}`. Move them to one stage `i` by step 2. Their
restrictions to each qcqs overlap `W_{ab}=U_a\times_TU_b` have equal images in `F(W_{ab})`; step
4 supplies eventual equality there. For the finitely many overlaps, take a common target of the
witnesses and equalize the finitely many arrows from `i`. The transported sections now agree on
every overlap, so the sheaf axiom glues them to a section at that stage over `T`. Its image is
`t` by separation. If the cover is empty, `T` is empty and both groups of sections are zero;
choose any index, which exists by filteredness. This proves section bijectivity for every qcqs
object of `\mathcal C`, and in particular for `T=V`.
6. Now fix the ring sheaf `A` and the module diagram `(N_i)` with colimit `N`. Forgetting to
abelian sheaves preserves the colimit by the module-sheaves-colimits-forgetful node, so steps 4
and 5 give `\varinjlim_iN_i(T)\cong N(T)` for every qcqs `T`, compatibly with `A(T)`-actions.
Refine a presentation covering for `P` by step 1 to a finite affine cover `(U_a\to V)`, with
`A^{m_a}\xrightarrow{r_a}A^{n_a}\xrightarrow{b_a}P\to0` on `\mathcal C/U_a`. Presentations
remain presentations after further slice restriction: underlying abelian restriction is exact by
the site-restriction-exact node, and the module forgetful functor computes kernels and
cokernels. In particular it reflects exactness, since zero underlying kernel or cokernel is the
zero module sheaf. Finite free sheaves restrict to finite free sheaves by their sectionwise
description. This checks the presentations on every qcqs `W\to U_a`, including the overlaps.
7. On `\mathcal C/U_a` write `r_a(e_\ell)=\sum_{k=1}^{n_a}a_{k\ell}e_k`, with `a_{k\ell}\in
A(U_a)`. For each qcqs `W\to U_a` and any module sheaf `M`, a map `A|_W\to M|_W` is uniquely
determined by the image of `1` in `M(W)`: on an object `Z\to W` it sends `f` to `f` times the
restriction of that image. Consequently the cokernel universal property gives the natural
identification
``\operatorname{Hom}_{A|_W}(P|_W,M|_W)=\ker\left(M(W)^{n_a}\longrightarrow
M(W)^{m_a}\right),\qquad (x_k)\longmapsto\left(\sum_k a_{k\ell}|_W x_k\right)_\ell.``
No surjectivity of `A(W)^{n_a}\to P(W)` is being asserted: the universal property is in sheaves.
Apply filtered-colimits-commute-finite-limits to this finite-product and kernel diagram of
abelian groups. Step 6 identifies the colimits of the `N_i(W)` with `N(W)`, and the matrix maps
correspond because the coprojections are `A`-linear. Therefore
`\varinjlim_i\operatorname{Hom}_{A|_W}(P|_W,N_i|_W)\to\operatorname{Hom}_{A|_W}(P|_W,N|_W)` is
bijective for every such `W`. Its two representative assertions are exactly those of step 2.
Ranks `m_a=0` or `n_a=0` use empty products, so are included.
8. Given `h:P\to N`, step 7 with `W=U_a` lifts every `h|_{U_a}` to a morphism `h_a:P|_{U_a}\to
N_i|_{U_a}` at one common stage after transporting finitely many lifts. On each qcqs `W_{ab}`,
the two restricted morphisms have equal images in `\operatorname{Hom}(P|_{W_{ab}},N|_{W_{ab}})`.
Use step 7 with the presentation restricted from `U_a` to witness equality at a later stage.
Step 2 makes all the finitely many witnesses hold with one arrow from `i`. Since the sheaf Hom
of the defining node is a sheaf, the resulting morphisms glue to `g:P\to N_j`. Its image equals
`h` on the cover and hence globally. Conversely, if two global morphisms at stages `i,i'` have
equal images, step 7 on each `U_a` witnesses their equality at a later stage; step 2 makes one
pair of arrows `i\to j\leftarrow i'` work for the whole finite cover. Sheaf Hom separation then
gives equality globally. This proves both surjectivity and injectivity of the canonical Hom map
and the claimed common-stage equality. On the empty scheme, sheaf Hom has its unique empty-cover
section, so the same conclusion holds. Every comparison just used is postcomposition with the
supplied coprojections, as the formula in step 7 and gluing show. -/
theorem proetale_qcqs_fp_section_calculus
    (X : Scheme.{u}) (V : X.ProEt)
    [CompactSpace V.left] [QuasiSeparatedSpace V.left]
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] :
    (∀ F : I ⥤ Sheaf (Scheme.ProEt.topology V.left) AddCommGrpCat.{u + 1},
      Function.Bijective (colimit.post F
        ((sheafSections (Scheme.ProEt.topology V.left) AddCommGrpCat.{u + 1}).obj
          (op (Scheme.ProEt.mk (𝟙 V.left))))) ∧
      (∀ (i j : I)
        (s : (F.obj i).obj.obj (op (Scheme.ProEt.mk (𝟙 V.left))))
        (t : (F.obj j).obj.obj (op (Scheme.ProEt.mk (𝟙 V.left)))),
        ((colimit.ι F i).hom.app (op (Scheme.ProEt.mk (𝟙 V.left)))) s =
            ((colimit.ι F j).hom.app (op (Scheme.ProEt.mk (𝟙 V.left)))) t ↔
          ∃ (k : I) (a : i ⟶ k) (b : j ⟶ k),
            ((F.map a).hom.app (op (Scheme.ProEt.mk (𝟙 V.left)))) s =
              ((F.map b).hom.app (op (Scheme.ProEt.mk (𝟙 V.left)))) t)) ∧
    (∀ (A : Sheaf (Scheme.ProEt.topology V.left) CommRingCat.{u + 1})
      (P : ringedSiteModules.{u + 1}
        ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A))
      [SheafOfModules.IsFinitePresentation.{u + 1, u, u + 1} P]
      (N : I ⥤ ringedSiteModules.{u + 1}
        ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)),
      Function.Bijective (colimit.post N (coyoneda.obj (op P))) ∧
        (∀ (i j : I) (f : P ⟶ N.obj i) (g : P ⟶ N.obj j),
          f ≫ colimit.ι N i = g ≫ colimit.ι N j ↔
            ∃ (k : I) (a : i ⟶ k) (b : j ⟶ k), f ≫ N.map a = g ≫ N.map b)) := by
  sorry

end AlgebraicGeometry
