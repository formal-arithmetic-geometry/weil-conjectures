module

public import Sheaf.AlgebraicGeometry.SmoothAtlasAlgebraDatum
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties

import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.SchemeBigFppfQuasicoherentEquivalence
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.AlgebraicGeometry.FlatModulePullbackExact
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-! # Quasi-coherent algebra descent along a general smooth scheme atlas

Source: Stacks Project, stacks-sheaves.tex, Tags 06WT and 06WV(1),(5);
stacks-cohomology.tex, Tag 0GQF (blueprint: lem-sfb-smooth-atlas-algebra-descent).

The equivalence is normalized as actual restriction on all atlas scheme tests, scalar
maps, algebra maps and vertical relation isomorphisms. The datum uses scheme points of
the algebraic-space relation, rather than requiring that relation to be a scheme.
Tensor products of commutative algebras are categorical coproducts, and their unit is
the initial algebra; preservation of finite coproducts includes the canonical structural
maps. The coordinate isomorphisms are ring isomorphisms, so preserve multiplication and one.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace CategoryTheory

/-- A regular function on a test, transported by the equality over Sch/S and ULift.
Source: Stacks 06TV, 06WT (blueprint: lem-sfb-smooth-atlas-algebra-descent). -/
def atlasDescentScalar {S : Scheme.{u}} {F : BasedCategory.{v, w} (Over S)} {U : Over S}
    (a : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    {T : Over S} (f : T ⟶ U) (r : Scheme.Γ.obj (op T.left)) :
    (moduliStructurePresheaf F).obj (op (a.obj (atlasAlgebraTest f))) :=
  ULift.up ((eqToHom (congrArg (fun Q : Over S ↦ Scheme.Γ.obj (op Q.left))
    (a.w_obj (atlasAlgebraTest f)).symm)) r)

/-- A restriction-normalized algebra equivalence, including tensor/unit compatibility
and precisely the smooth-site injectivity criterion.
Source: Stacks 06WT, 06WV(1),(5), 0GQF
(blueprint: lem-sfb-smooth-atlas-algebra-descent). -/
structure SmoothAtlasAlgebraDescent {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) (U : Over S)
    (a : BasedFunctor (discreteModuli (yoneda.obj U)) F) where
  /-- An equivalence on objects and all algebra maps, with its unit and counit. -/
  equivalence :
    ObjectProperty.FullSubcategory (IsQuasicoherentModuliAlgebra (F := F) (hF := hF)) ≌
      SmoothAtlasAlgebraDatum a
  /-- Normalization as actual restriction on every atlas test. -/
  coordinates
      (A : ObjectProperty.FullSubcategory
        (IsQuasicoherentModuliAlgebra (F := F) (hF := hF)))
      {T : Over S} (f : T ⟶ U) :
    (equivalence.functor.obj A).algebra.obj.right.obj.obj (op (atlasAlgebraTest f)) ≅
      A.obj.right.obj.obj (op (a.obj (atlasAlgebraTest f)))
  /-- The structure morphism is the original pullback of regular functions. -/
  coordinates_scalars
      (A : ObjectProperty.FullSubcategory
        (IsQuasicoherentModuliAlgebra (F := F) (hF := hF)))
      {T : Over S} (f : T ⟶ U) (r : Scheme.Γ.obj (op T.left)) :
    (coordinates A f).hom
        ((equivalence.functor.obj A).algebra.obj.hom.hom.app
          (op (atlasAlgebraTest f)) (ULift.up (ULift.up r))) =
      A.obj.hom.hom.app (op (a.obj (atlasAlgebraTest f))) (atlasDescentScalar a f r)
  /-- Restriction along all scheme-test arrows, in particular smooth further tests. -/
  coordinates_restriction
      (A : ObjectProperty.FullSubcategory
        (IsQuasicoherentModuliAlgebra (F := F) (hF := hF)))
      {T T' : Over S} (b : T' ⟶ T) (f : T ⟶ U) :
    (equivalence.functor.obj A).algebra.obj.right.obj.map (atlasAlgebraTestMap b f).op ≫
        (coordinates A (b ≫ f)).hom =
      (coordinates A f).hom ≫ A.obj.right.obj.map (a.map (atlasAlgebraTestMap b f)).op
  /-- Naturality for every algebra morphism, including noninvertible maps. -/
  coordinates_maps
      {A B : ObjectProperty.FullSubcategory
        (IsQuasicoherentModuliAlgebra (F := F) (hF := hF))} (b : A ⟶ B)
      {T : Over S} (f : T ⟶ U) :
    (equivalence.functor.map b).hom.hom.right.hom.app (op (atlasAlgebraTest f)) ≫
        (coordinates B f).hom =
      (coordinates A f).hom ≫ b.hom.right.hom.app (op (a.obj (atlasAlgebraTest f)))
  /-- The actual relation arrow determines the transition, with p1-to-p2 orientation. -/
  coordinates_relation
      (A : ObjectProperty.FullSubcategory
        (IsQuasicoherentModuliAlgebra (F := F) (hF := hF)))
      {T : Over S} (f g : T ⟶ U) (i : AtlasAlgebraRelation a f g) :
    ((equivalence.functor.obj A).delta f g i).hom ≫ (coordinates A g).hom =
      (coordinates A f).hom ≫ A.obj.right.obj.map i.val.inv.op
  /-- The tensor product and unit algebra exist on both sides. -/
  tensor_unit_exists :
    HasFiniteCoproducts (ObjectProperty.FullSubcategory
      (IsQuasicoherentModuliAlgebra (F := F) (hF := hF))) ∧
      HasFiniteCoproducts (SmoothAtlasAlgebraDatum a)
  /-- Tensor products and the unit algebra, with their canonical coproduct maps. -/
  tensor_unit : PreservesFiniteCoproducts equivalence.functor
  /-- Injectivity on smooth-etale tests iff injectivity of the ordinary atlas sheaf.
  Open immersions into U give exactly the Zariski section tests; nonflat big-site
  tests are not included on the left. -/
  injective_iff
      {A B : ObjectProperty.FullSubcategory
        (IsQuasicoherentModuliAlgebra (F := F) (hF := hF))} (b : A ⟶ B) :
    (∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) F),
      ModuliSpaceTest (@Smooth) t → Function.Injective
        (b.hom.right.hom.app (op (t.obj (atlasAlgebraTest (𝟙 T)))))) ↔
      ∀ (T : Over S) (f : T ⟶ U), IsOpenImmersion f.left → Function.Injective
        ((equivalence.functor.map b).hom.hom.right.hom.app (op (atlasAlgebraTest f)))

/-- Comparison on an arbitrary smooth scheme test after a specified common atlas lift.
Its formula uses only actual restriction and the supplied two-isomorphism, so it
preserves the unit, multiplication and all algebra maps. Such common lifts cover the
test by base change of the smooth surjective atlas; no nonflat injectivity follows.
Source: Stacks 06WK, 06WT (blueprint: lem-sfb-smooth-atlas-algebra-descent). -/
def SmoothAtlasAlgebraDescent.testComparison {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} {hF : IsFibredInGroupoids F} {U : Over S}
    {a : BasedFunctor (discreteModuli (yoneda.obj U)) F}
    (D : SmoothAtlasAlgebraDescent F hF U a)
    (A : ObjectProperty.FullSubcategory
      (IsQuasicoherentModuliAlgebra (F := F) (hF := hF)))
    {T W : Over S} (t : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (f : W ⟶ U) (g : W ⟶ T)
    (i : a.obj (atlasAlgebraTest f) ≅ t.obj (atlasAlgebraTest g)) :
    (D.equivalence.functor.obj A).algebra.obj.right.obj.obj (op (atlasAlgebraTest f)) ≅
      A.obj.right.obj.obj (op (t.obj (atlasAlgebraTest g))) :=
  D.coordinates A f ≪≫ A.obj.right.obj.mapIso i.symm.op

/-- Restriction along any smooth surjective scheme atlas gives algebra descent, tensor
and unit compatibility and the equivalence of injectivity on the smooth-etale site
with injectivity on the atlas.

Source: Stacks 06WT, 06WV(1),(5) and 0GQF
(blueprint: lem-sfb-smooth-atlas-algebra-descent).

Proof:
1. Put $s=p_1,t=p_2$. Smoothness implies flatness and local finite presentation by
[lem-sfb-stack-chartwise-smooth-etale-calculus]. Thus
[lem-sfb-fppf-groupoid-stack-presentations](2) applies to the given smooth surjective scheme
atlas: its self-relation is an algebraic space, with groupoid operations given by composition of
the specified isomorphisms, and $[U/R]\simeq\mathcal X$ compatibly with $U$. Let $\mathcal P$ be
the groupoid prestack with objects $u:T\to U$ and arrows $(f,r):(T,u)\to(T',u')$, where $f:T\to
T'$, $r:T\to R$, $sr=u$ and $tr=u'f$. Its stackification is $[U/R]$. For an algebra on $\mathcal
X$, [lem-sfb-stack-quasi-coherent-scheme-restriction] gives the quasi-coherent algebra on each
scheme test; the arrow $(u,v,\alpha)$ in the self-relation induces its pullback isomorphism.
Identity and composition of these arrows give exactly the displayed unit and triple-cocycle
equations. This constructs restriction, including its action on all algebra maps.
2. Conversely, fix $(C,\delta)$ on $U$. On $\mathcal P$ set $H(T,u)=\Gamma(T,u^*C)$, with its
usual algebra structure. For $(f,r)$ define restriction as section pullback along $f$ followed by
$r^*\delta^{-1}:(u'f)^*C\to u^*C$. The scheme section pullbacks and their composition comparisons
are those of [lem-sfb-scheme-big-fppf-quasicoherent-equivalence]. Two successive arrows have
transition $r_1^*\delta^{-1}\circ
r_2^*\delta^{-1}=(\delta_{r_2}\circ\delta_{r_1})^{-1}=\delta_{r_2r_1}^{-1}$ under these
comparisons. This is the single restriction for their composite, by the given cocycle; the
identity restriction is the identity by $e^*\delta=1$. All restrictions are ring maps over
pullback of functions, since $\delta$ is an algebra isomorphism. These formulas therefore define a
presheaf of commutative algebras, not just its values on objects.
3. For $x=(T,u)$, its slice in $\mathcal P$ is equivalent to schemes over $T$: an arrow to $x$ is
uniquely isomorphic over $x$ to the chosen cartesian arrow over its base map, because all vertical
arrows are invertible. Under this equivalence the restriction of $H$ is $A_T(u^*C)$, using the
transition isomorphism in step 2. By [lem-sfb-scheme-big-fppf-quasicoherent-equivalence] this is
an fppf sheaf with local free presentations. Hence $H$ is a sheaf: every covering and its matching
sections lie in such a slice. It is quasi-coherent as defined in
[def-trf-space-quasi-coherent-module]: the local free presentations on each slice give precisely a
covering and presentation locally at every object of $\mathcal P$. No descent theorem on a
nonexistent scheme representing $R$ is used here; a map $T\to R$ suffices for the restriction
formula.
4. Let $q:\mathcal P\to[U/R]\simeq\mathcal X$. By [lem-sfb-stackification-module-equivalence],
precomposition gives an equivalence on all module sheaves, restricting to quasi-coherent ones. It
therefore descends the underlying module of $H$ to a quasi-coherent module $F$, with $q^*F\simeq
H$. We also need its actual tensor comparison. For quasi-coherent $F,G$ on $\mathcal X$,
[lem-sfb-stack-qcoh-flat-atlas-exactness] ensures that $F\otimes G$ and the unit are
quasi-coherent. On the slice of $x\in\mathcal P(T)$,
[lem-sfb-stack-quasi-coherent-scheme-restriction] identifies the restrictions with $A_T(F_{qx})$
and $A_T(G_{qx})$. Apply [lem-sfb-localized-site-tensor-restriction] on both sites and the tensor
comparison of [lem-sfb-scheme-big-fppf-quasicoherent-equivalence]. Both $q^*(F\otimes G)$ and
$q^*F\otimes q^*G$ then identify with $A_T(F_{qx}\otimes G_{qx})$. The canonical comparison sends
each local pure tensor to that same tensor, so it is this isomorphism on every slice, hence
globally. The unit comparison is the identity on $\Gamma(T,\mathcal O_T)$. Associativity, symmetry
and unit compatibility follow on local pure tensors: either composite sends $(a\otimes b)\otimes
c$ to $a\otimes(b\otimes c)$, or exchanges the same factors, or multiplies the same scalar. Such
sections locally generate the sheaf tensor.
5. The multiplication of $H$ is bilinear and thus a module map $H\otimes H\to H$ by
[lem-pc-sites-sheaf-tensor-bilinear-universal]. Using step 4's tensor and unit comparisons, full
faithfulness of [lem-sfb-stackification-module-equivalence] gives unique maps $\mu:F\otimes F\to
F$ and $\eta:\mathcal O_{\mathcal X}\to F$ restricting to multiplication and unit of $H$. The two
associativity maps from $F^{\otimes3}$, the two unit diagrams and the commutativity diagram become
the corresponding equalities for $H$ after $q^*$. Faithfulness makes these equalities hold on
$\mathcal X$. The same bilinear universal property interprets $\mu$ as a sheaf multiplication;
with $\eta$ it makes $F$ a commutative algebra in exactly the sense of
[def-sfb-stack-quasi-coherent-algebra]. Thus the construction descends its algebra operations as
well as its module.
6. A compatible map $h:C\to D$ gives $H_C(T,u)\to H_D(T,u)$ by $\Gamma(T,u^*h)$; compatibility
with $\delta$ is precisely commutation with the restriction along every $(f,r)$. Conversely a
module map $H_C\to H_D$ restricts on the slice of $(U,1)$, identified with
$(\mathit{Sch}/U)_{fppf}$, to a unique module map $h:C\to D$ by
[lem-sfb-scheme-big-fppf-quasicoherent-equivalence]. Naturality along $(f,e)$ forces its
components to be $\Gamma(T,u^*h)$; naturality along $(1,r)$ forces the descent equation. This
tests the equation on all scheme maps to $R$, in particular on its etale scheme charts, so it is
an equation on $R$. The map is an algebra map exactly when it preserves multiplication and unit on
every slice, equivalently when $h$ does, by the tensor comparison and faithfulness of that scheme
equivalence. Finally [lem-sfb-stackification-module-equivalence] descends these module maps
uniquely; faithfulness and step 4 show that the descended maps preserve the operations of step 5.
This proves full faithfulness on all algebra maps, not only isomorphisms.
7. Restriction of the constructed algebra to $U$ is $C$: on the slice $(U,1)$ the sheaf is
$A_U(C)$, whose inverse comparison is the identity on Zariski opens by
[lem-sfb-scheme-big-fppf-quasicoherent-equivalence]; the arrows $r$ recover $\delta$ by the
formula in step 2. Starting instead with an algebra $B$ on $\mathcal X$,
[lem-sfb-stack-quasi-coherent-scheme-restriction] identifies its value at every $(T,u)$ with
$\Gamma(T,u^*B_U)$, and its restrictions with the same $r^*\delta^{-1}$ formula. Thus the presheaf
constructed from its datum is canonically $q^*B$, on maps and operations. Full faithfulness of
[lem-sfb-stackification-module-equivalence] descends this identification to the unique compatible
algebra isomorphism with $B$. These identifications are natural by their section formulas, so the
two constructions are quasi-inverse.
8. For a scheme test $a:T\to\mathcal X$, [lem-sfb-stack-quasi-coherent-scheme-restriction]
identifies restriction with tensor pullback and gives its natural identity and composition
comparisons, preserving the structure module and tensors. Thus the restriction functor of step 1
carries an algebra tensor product to the tensor product of its two restrictions, with transition
$\delta_C\otimes\delta_D$, and carries the unit to the canonical unit datum. Multiplication on
$C\otimes D$ sends $(c\otimes d)(c'\otimes d')$ to $cc'\otimes dd'$, and its unit is $1\otimes1$;
these are exactly the restrictions of the same structural maps on the descended algebras. The
comparisons in step 4 respect these formulas. The composition comparisons for test pullback
therefore show compatibility after every further smooth test and for every algebra map. No
arbitrary ring of global sections is being asserted to commute with tensor: all these comparisons
are sheaf tensors on the test sites.
9. Let $b:B\to D$ be the descended map, and suppose $b_U$ is injective. Fix a smooth scheme test
$a:T\to\mathcal X$. Choose a surjective etale scheme chart $W\to Z=U\times_{\mathcal X}T$,
possible by the atlas condition of [def-sfb-algebraic-moduli-stack] and [def-trf-algebraic-space].
The projections $W\to T$ and $W\to U$ are smooth, and the former is surjective, by
[lem-sfb-stack-chartwise-smooth-etale-calculus]; for $W\to U$ use the smoothness of $a$. In
particular both scheme maps are flat. By [lem-sfb-stack-quasi-coherent-scheme-restriction] the two
pullbacks of $b_T$ and $b_U$ to $W$ coincide. Exact flat pullback from
[lem-weil-pbc-flat-module-pullback-exact-pushforward-injective] makes this map injective. Put
$K=\ker b_T$, a quasi-coherent Zariski module by [lem-weil-pbc-quasi-coherent-module-kernel].
Exactness gives $K|_W=0$. Apply [lem-sc-flat-cover-module-isomorphism-reflection] to $0\to K$ and
the flat surjective scheme cover $W\to T$: it is an isomorphism after pullback, hence before
pullback. Therefore $K=0$ and $b_T$ is injective. This uses the reflection lemma only for
isomorphisms, its stated conclusion.
10. The smooth-etale site here has objects smooth scheme maps $T\to\mathcal X$ and coverings etale
covering families over each such object. By [lem-sfb-stack-quasi-coherent-scheme-restriction] its
values are the sections of the quasi-coherent scheme modules $B_T,D_T$. Step 9 makes every section
map on every smooth test injective; hence the restricted sheaf map is injective. Conversely,
injectivity on this site gives injectivity on every open subscheme of $U$, since these remain
smooth tests; therefore $b_U$ is injective. Equivalently one can use
[lem-sfb-scheme-etale-module-exact-finiteness-comparison] to express the test injections on the
small etale site. In step 9 both projections were flat because both $U$ and $T$ were smooth over
$\mathcal X$; no assertion about an arbitrary nonflat big-site test follows, or is needed.
-/
theorem exists_smoothAtlasAlgebraDescent {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsAlgebraicModuliStack F) (U : Over S)
    (a : BasedFunctor (discreteModuli (yoneda.obj U)) F) (ha : IsSmoothModuliAtlas F U a) :
    Nonempty (SmoothAtlasAlgebraDescent F hF.1.1 U a) := by
  sorry

end CategoryTheory
