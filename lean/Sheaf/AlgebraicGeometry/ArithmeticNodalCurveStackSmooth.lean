module

public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.CurveModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.FiniteOfIsClosedOfClosedPoints
import Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts
import Sheaf.AlgebraicGeometry.ArtinRepresentableDiagonalCriterion
import Sheaf.AlgebraicGeometry.CurveDescentIsomSpaces
import Sheaf.AlgebraicGeometry.CurveInfinitesimalPushout
import Sheaf.AlgebraicGeometry.CurveLimitPreservation
import Sheaf.AlgebraicGeometry.ProperCurveOpennessVersality
import Sheaf.AlgebraicGeometry.CurveTangentFiniteness
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatLfpUniversallyOpen
import Sheaf.AlgebraicGeometry.IsolatedLCICurveSmoothOpen
import Sheaf.AlgebraicGeometry.SeparatedSpaceDimensionOneScheme
import Sheaf.AlgebraicGeometry.SpaceNodalLocusBaseChange
import Sheaf.AlgebraicGeometry.StackSmoothAtlasBaseChange
import Sheaf.AlgebraicGeometry.DthFittingSmoothLocus
import Sheaf.AlgebraicGeometry.NodalCurveLCICriterion
import Sheaf.AlgebraicGeometry.UnramifiedOverFieldLocalCriterion
import Mathlib.AlgebraicGeometry.Noetherian

/-! # The arithmetic nodal curve stack

Source: Stacks Project, quot.tex, Tag 0D5A; moduli-curves.tex, Tags 0DSY, 0E00
and 0DZZ; stacks-morphisms.tex, Tags 06FM, 075U and 075W
(blueprint: lem-sfb-arithmetic-nodal-curve-stack-smooth).

The base is an arbitrary scheme. The smooth-family open is characterized on every
scheme base change, and its inverse image is the corresponding smooth-family open.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The full subcategory of proper curve families with nonempty nodal geometric fibres,
with the original cartesian arrows and projection to schemes over the base.
Source: Stacks, moduli-curves.tex, Tag 0DSY
(blueprint: lem-sfb-arithmetic-nodal-curve-stack-smooth). -/
def ProperCurveModuli.nodalCategory (S : Scheme.{u}) : BasedCategory (Over S) :=
  fullModuliSubcategory (ProperCurveModuli.category S)
    (fun X ↦ X.family.HasNonemptyNodalGeometricFibres)

/-- Smoothness of the actual presheaf pullback family, tested on every representable
etale scheme chart, with its specified projection to the new base scheme.
Source: Stacks, moduli-curves.tex, Tag 0DZZ; Morphisms of Spaces, smooth morphisms
(blueprint: lem-sfb-arithmetic-nodal-curve-stack-smooth). -/
def ProperCurveFamily.IsSmoothAfterBaseChange {S : Scheme.{u}} {T : Over S}
    (X : ProperCurveFamily T) {T' : Over S} (a : T' ⟶ T) : Prop :=
  ∀ (U : Over S) (b : yoneda.obj U ⟶ pullback X.projection (yoneda.map a)),
    AlgebraicSpace.IsEtale b →
      Smooth (yoneda.preimage (b ≫ pullback.snd X.projection (yoneda.map a))).left

/-- Proper curves form an algebraic stack over any scheme; the nonempty nodal
families form an open algebraic substack smooth over that scheme. Every representable
smooth scheme map has smooth composite, with no surjectivity hypothesis. The smooth
families form an open substack, with the stated universal smooth-family locus and
arbitrary-base-change compatibility.
Source: Stacks, quot.tex, Tag 0D5A; moduli-curves.tex, Tags 0DSY, 0E00 and 0DZZ;
stacks-morphisms.tex, Tags 06FM, 075U and 075W
(blueprint: lem-sfb-arithmetic-nodal-curve-stack-smooth).

Proof plan:
1. Write $\mathcal C$ for the absolute proper-curve groupoid over $\operatorname{Spec}\mathbf Z$.
By [lem-sfb-curve-descent-isom-spaces] it is an fppf stack, hence an etale stack, and each Isom
sheaf is an algebraic space; this is exactly representability of its diagonal. The size convention
[def-weil-size-convention] supplies the size bound in Artin's criterion: a finite-type field over
$\mathbf Z$ is countable, and finite-presentation proper algebraic spaces have presentations by
finitely many affine charts and finitely many overlap charts with finitely presented algebras and
structure maps. These are finite lists of countable algebraic data; isomorphisms are bounded by
maps between such presentations. A single infinite cardinal in the chosen larger universe bounds
these presentations uniformly in the finite-type field. This checks the size premise, without
asserting existence of an atlas. Uses: lem-sfb-curve-descent-isom-spaces,
def-weil-size-convention.

2. Apply [lem-sfb-artin-representable-diagonal-criterion] over $\mathbf Z$. Step 1 gives its
stack, diagonal and size premises. [lem-sfb-curve-limit-preservation] gives precisely its small
directed affine-limit equivalence, including arrows and eventual equality.
[lem-sfb-curve-infinitesimal-pushout] gives the pushout equivalence, in particular for its
Artinian local tests. [lem-sfb-curve-tangent-finiteness] gives both required finite-dimensional
spaces over every finite-type field. [lem-sfb-curve-formal-effectivity] gives effectivity over the
complete Noetherian local rings in the criterion, without restricting the residue field.
[lem-sfb-curve-openness-versality] gives its Artinian lifting form of openness at finite-type
points. Thus $\mathcal C$ is algebraic. Uses: lem-sfb-artin-representable-diagonal-criterion,
lem-sfb-curve-limit-preservation, lem-sfb-curve-infinitesimal-pushout,
lem-sfb-curve-tangent-finiteness, lem-sfb-curve-formal-effectivity,
lem-sfb-curve-openness-versality.

3. For any scheme $S$, an object of $\mathcal C\times_{\operatorname{Spec}\mathbf Z}S$ over $T$ is
exactly a proper curve family over $T$ and a map $T\to S$; arrows are exactly the cartesian arrows
preserving that map. This identifies this 2-fibre product with $\mathfrak C_S$ of
[def-sfb-proper-curve-moduli]. Apply [lem-sfb-algebraic-stack-fibre-products] to $\mathcal C$, $S$
and $\operatorname{Spec}\mathbf Z$, viewing schemes as their representable stacks. Hence
$\mathfrak C_S$ is algebraic for arbitrary $S$. Uses: def-sfb-proper-curve-moduli,
lem-sfb-algebraic-stack-fibre-products.

4. For a family $f:X\to T$ let $V\subseteq X$ be the nodal relative-dimension-one open supplied by
[lem-sfb-space-nodal-locus-base-change], and put $B=|X|\setminus|V|$. Set $T_{\rm nod}=T\setminus
|f|(B)$. Properness makes $|f|(B)$ closed. The nodal-locus statement says precisely that every
geometric fibre over $T_{\rm nod}$ is either empty or pure one-dimensional with only smooth points
and ordinary nodes, with the etale-chart interpretation in [def-sfb-curve-moduli-groupoids].
Formation of this open commutes with arbitrary base change: $V$ pulls back by the cited lemma;
over a point $t'$ above $t$, the bad fibre is empty exactly when the original bad fibre is empty.
Indeed a field-valued point in a nonempty bad fibre remains nonempty after a field extension,
since the tensor product of two field extensions of $\kappa(t)$ is nonzero; a prime of that tensor
product supplies a point. Thus the inverse image of $|f|(B)$ is the bad-image subset for the
pulled-back family. This also proves the universal factorization criterion, testing the bad locus
on geometric points. Uses: lem-sfb-space-nodal-locus-base-change, def-sfb-curve-moduli-groupoids.

5. The nonempty-fibre locus $T_{\ne\varnothing}=|f|(|X|)$ is open by
[lem-sfb-flat-lfp-space-universally-open] and closed by properness. It commutes with arbitrary
base change by the same field-tensor-product argument as in step 4. Therefore $T_N=T_{\rm nod}\cap
T_{\ne\varnothing}$ is open and compatible with every base change, and $T'\to T$ factors through
it if and only if its family has nonempty nodal geometric fibres. These compatible opens show that
the full groupoid $\mathfrak N_S\subseteq\mathfrak C_S$ is an open substack. Descent is the
restriction of descent in $\mathfrak C_S$ because these opens pull back. Its diagonal has the same
Isom spaces, and pulling back a scheme atlas of $\mathfrak C_S$ restricts that atlas to an open
scheme. This gives a smooth surjective atlas of $\mathfrak N_S$, hence its algebraicity.
Smoothness of the atlas projection is unchanged on an open source: in the local
finite-presentation and infinitesimal lifting definition [def-sbc-smooth-morphisms], localization
preserves finite presentation and a nilpotent thickening has the same underlying points, so any
local lift remains in that open. Uses: lem-sfb-flat-lfp-space-universally-open,
def-sbc-smooth-morphisms.

6. Work again over $\operatorname{Spec}\mathbf Z$ and let $C/\Omega$ be a geometric fibre
belonging to $\mathfrak N_{\mathbf Z}$, with $\Omega$ algebraically closed. Properness gives
separatedness and finite type, and the dimension is one, so
[lem-sfb-separated-space-dimension-one-scheme] makes $C$ a scheme. Its identity etale chart in
[def-sfb-curve-moduli-groupoids] is pure one-dimensional and every closed point is smooth or an
ordinary node. [lem-trf-nodal-curve-lci-criterion] therefore gives that $C$ is a local complete
intersection and that its first-Fitting singular subscheme $Z_C$ is unramified over $\Omega$.
Apply [lem-trf-dth-fitting-smooth-locus] with $d=1$: flatness holds over the field, local finite
presentation holds for the family, and geometric purity is part of the nodal predicate, including
its algebraically closed extensions. Thus $|Z_C|$ is exactly the nonsmooth locus. Uses:
lem-sfb-separated-space-dimension-one-scheme, def-sfb-curve-moduli-groupoids,
lem-trf-nodal-curve-lci-criterion, lem-trf-dth-fitting-smooth-locus.

7. The field $\Omega$ is Noetherian. By [pqf-lem-locnoeth-lft], $C$ is locally Noetherian, and
finite type over the field makes it quasi-compact, hence Noetherian. The closed subscheme $Z_C$ is
locally of finite type over $\Omega$, since locally its algebra is a quotient of a finite-type
$\Omega$-algebra. By [lem-trf-unramified-over-field-local-criterion], every point of $Z_C$ is
closed. A closed immersion carries it to a closed point of $C$. Now
[lem-sc-noetherian-closed-points-finite] applies to the closed subset $|Z_C|$ of $C$, proving
finiteness. Hence $C$ is lci and smooth except at finitely many points. Uses:
pqf-lem-locnoeth-lft, lem-trf-unramified-over-field-local-criterion,
lem-sc-noetherian-closed-points-finite.

8. Apply [lem-sfb-isolated-lci-curve-smooth-open] to the absolute algebraic stack $\mathcal C$
proved algebraic in step 2. It gives an open $\mathcal L\subseteq\mathcal C$ smooth over $\mathbf
Z$. Steps 6 and 7 verify its field-point characterization for every geometric point of $\mathfrak
N_{\mathbf Z}$. For any family over $T$ in this nodal stack, the pullback of $\mathcal L$ is
therefore an open of $T$ containing all its geometric points, so equals $T$. Thus $\mathfrak
N_{\mathbf Z}$ factors through $\mathcal L$ and is an open substack of it. Restrict a smooth
scheme atlas $A\to\mathcal L$ with smooth composite $A\to\operatorname{Spec}\mathbf Z$ to this
open. Its restriction remains a smooth surjective atlas and its composite remains smooth by the
open-restriction lifting argument of step 5. This proves $\mathfrak N_{\mathbf Z}$ smooth over
$\mathbf Z$. Uses: lem-sfb-isolated-lci-curve-smooth-open.

9. The object-and-arrow identification of step 3 identifies $\mathfrak N_S$ with $\mathfrak
N_{\mathbf Z}\times_{\operatorname{Spec}\mathbf Z}S$: the nodal predicate tests the same geometric
fibres. Apply [lem-sfb-stack-smooth-atlas-base-change] to this base change, with no restriction on
$S\to\operatorname{Spec}\mathbf Z$. It gives smoothness over $S$. The same lemma gives exactly the
asserted test by every representable smooth $W\to\mathfrak N_S$, including nonsurjective charts.
Conversely that test applies to a smooth surjective scheme atlas, so implies smoothness in the
atlas sense. Uses: lem-sfb-stack-smooth-atlas-base-change.

10. Finally, for $f:X\to T$ in $\mathfrak N_S$, use [lem-sfb-flat-space-smooth-locus] to form the
maximal smooth open $U\subseteq X$, which commutes with arbitrary base change because $f$ is flat
and locally finitely presented. Put $T^{\rm sm}=T\setminus|f|(|X|\setminus|U|)$. It is open by
properness. Under $T'\to T$, the complement $|X|\setminus|U|$ pulls back to the nonsmooth locus,
and its image pulls back by the field-tensor-product argument of step 4. Consequently $X_{T'}\to
T'$ is smooth exactly when this pulled-back complement is empty, equivalently when $T'\to T$
factors through $T^{\rm sm}$. This proves both the full-subcategory openness and its
arbitrary-base-change clause. No genus or connectedness bound, and no field or Noetherian
condition on the base, has been used. Uses: lem-sfb-flat-space-smooth-locus.
-/
theorem arithmetic_nodal_curve_stack_smooth (S : Scheme.{u}) :
    IsAlgebraicModuliStack (ProperCurveModuli.category S) ∧
    (∃ N : OpenModuliSubstack (ProperCurveModuli.category S),
      N.property = fun X ↦ X.family.HasNonemptyNodalGeometricFibres) ∧
    IsAlgebraicModuliStack (ProperCurveModuli.nodalCategory S) ∧
    IsSmoothModuliStack (ProperCurveModuli.nodalCategory S) ∧
    (IsSmoothModuliStack (ProperCurveModuli.nodalCategory S) ↔
      ∀ (W : Over S)
          (p : BasedFunctor (discreteModuli (yoneda.obj W)) (ProperCurveModuli.nodalCategory S)),
        (∀ (T : Over S)
            (t : BasedFunctor (discreteModuli (yoneda.obj T))
              (ProperCurveModuli.nodalCategory S)),
          ∃ (Z : AlgebraicSpace S) (a : Z.obj.obj ⟶ yoneda.obj T),
            HasSpaceBaseChange p T t Z a ∧ SpaceMapIsSmooth Z T a) → Smooth W.hom) ∧
    (∃ M : OpenModuliSubstack (ProperCurveModuli.nodalCategory S),
      M.property = fun X ↦ AlgebraicSpace.MapToSchemeIsLocally (@Smooth)
        X.obj.family.space X.obj.base X.obj.family.projection) ∧
    ∀ (T : Over S) (X : ProperCurveFamily T), X.HasNonemptyNodalGeometricFibres →
      ∃ U : T.left.Opens,
        (∀ (T' : Over S) (a : T' ⟶ T),
          X.IsSmoothAfterBaseChange a ↔
            ∃ b : T'.left ⟶ U.toScheme, b ≫ U.ι = a.left) ∧
        ∀ (T' : Over S) (a : T' ⟶ T),
          ∃ V : T'.left.Opens, V = a.left ⁻¹ᵁ U ∧
            ∀ (T'' : Over S) (b : T'' ⟶ T'),
              X.IsSmoothAfterBaseChange (b ≫ a) ↔
                ∃ c : T''.left ⟶ V.toScheme, c ≫ V.ι = b.left := by
  sorry

end AlgebraicGeometry
