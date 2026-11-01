/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

import WeilConjectures.Compactification.Dense
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientSectionsLocalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.Right.RightDerivedExactRestrictionNormalization
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
import WeilConjectures.Compactification.RefinementPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
import WeilConjectures.Compactification.CommonDenseRefinement
import WeilConjectures.Compactification.CompactificationCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartTriangulated
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty

/-! # Condensed compact support over quasi-separated finite-type bases

Source: latest blueprint, sk-thm-sf-ctf-stability-direct-images (3), and
lem-zl-composition-weight-bound, proof paragraph 1; the DAG supplies the extension
from separated standing schemes to quasi-separated finite-type schemes
(blueprint: lem-zl-condensed-shriek-bounded-qcqs).

The coefficient is the finite-subextension-valued condensed algebraic closure.
The compactification models are the existing ordinary module-object derived functors.
The comparisons use the existing normalized proper-refinement transformations.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open CompactificationReindexing

/-- Compactification existence, exact triangulated compact support, coherent normalized
comparisons, preservation of bounded constructibility and every lower cohomological
bound. The two triangulated structures and the preservation proof are existential
proof data; the restricted functor itself is the actual `ObjectProperty.lift`.

Source: latest blueprint, sk-thm-sf-ctf-stability-direct-images (3), and
lem-zl-composition-weight-bound, proof paragraph 1; the qcqs extension is the present
DAG node (blueprint: lem-zl-condensed-shriek-bounded-qcqs).

Proof plan (the accepted DAG proof, including its normalized comparisons):

1. All schemes in the assertion, including the ambient schemes of compactifications, are
Noetherian: apply [lem-weil-pbc-finite-type-over-noetherian] to their finite-type maps to the
spectrum of the field. In particular they have finite affine covers. The target is qcqs, so [sk-
thm-nagata-compactification] gives a compactification. Its open part is quasi-compact by [lemma-
nagata-open-immersion-qc-over-separated-target], applied over the point. Its ambient scheme is
finite type over $k$ since proper morphisms are finite type. Base changes and compositions used
below retain properness, separatedness and finite type by [lem-weil-pbc-proper-fp-permanence] and
[lem-weil-pbc-qcqs-morphism-permanence]. No structure morphism is assumed separated.

2. Use small pro-étale sites throughout. The module categories are Grothendieck abelian: [lem-
weil-pbc-sheaf-tensor-closed] supplies the closed monoidal Grothendieck category of abelian
sheaves and [lem-sfb-modobj-grothendieck] applies to its coefficient ring object. Thus they have
enough injectives by [lem-sp-grothendieck-enough-injectives] and K-injective resolutions by [lem-
sfb-grothendieck-k-injective]. Form $T_c=Rp_*D(j_!)$ exactly as in [def-sfb-module-derived-lower-
shriek-compactification]. Its factors are triangulated by [lem-sf-exact-functor-derived-
triangulated], [sk-def-sfb-module-lower-shriek] and [lem-pc-right-derived-functor-triangulated].
We use the unital associative composition comparisons of actual condensed-module derived direct
images [lem-weil-derived-direct-image-composition].

3. Here is the open-restriction calculation needed below, for an arbitrary morphism $r:P\to Q$ and
open $v:V\hookrightarrow Q$, with $b:P_V\hookrightarrow P$ and $r_V:P_V\to V$. By [lem-weil-
proetale-weakly-etale-localization](1),(4), restriction is localization of the small site, and the
abelian inverse image along an object of the small pro-étale site is restriction to that localized
site [lem-sfb-coefficient-sections-localization]. On an object $W\to V$, the underived identity
$v^*r_*M=(r_V)_*b^*M$ evaluates both sides on $P\times_QW$, with identical coefficient action;
pulled-back coefficients and their composition are [sk-def-sfb-module-pushforward-pullback].
Restrictions are exact by [det-prop-sfb-module-pullback-exact-main]. Moreover $b^*$ preserves
K-injectives by [lem-weil-pbc-right-adjoint-preserves-kinjective], since its left adjoint $b_!$ is
exact [sk-def-sfb-module-lower-shriek]. Apply this identity to a K-injective resolution $I$: both
sides compute $v^*Rr_*K\simeq R(r_V)_*b^*K$. This is the canonical derived square, with its full
units, by [lem-right-derived-exact-restriction-normalization]. Successive restrictions and direct-
image composition give the same maps because they give the same section identities on these
representatives. Restriction of open extension is extension on the restricted open: the two
sheaves have the identical extension-by-zero sections and action. Open units are unchanged by
these identifications. Finally restrictions to an open cover detect zero sheaves by
the sheaf axiom; exactness therefore makes them detect zero cohomology and isomorphisms of derived
objects
by taking cones.

4. Fix $K\in D^b_c(X,\Lambda)$ and a finite affine open cover $Y=\bigcup_iV_i$. Then
$X_i=f^{-1}V_i$ and $\overline X_i=p^{-1}V_i$ are separated finite-type $k$-schemes: their maps to
$V_i$ are separated, $V_i$ is affine, and separated maps compose [lem-weil-pbc-proper-fp-
permanence]. Restrict $K$ to $X_i$. It remains bounded constructible directly from the local-
model/stratification definition [sk-def-sfb-constructible]. Extension by zero is exact [sk-def-
sfb-module-lower-shriek], so its cohomology is extension of the cohomology [lem-weil-pbc-exact-
functor-bounded-below]; the restriction of $j_{i!}$ to the closed complement $\overline
X_i\setminus X_i$ vanishes, since applying the triangle $j_!j^*\to\mathrm{id}\to i_*i^*$ and
$i^*i_*\cong\mathrm{id}$ of [lem-weil-pbc-condensed-open-closed-recollement] to $j_{i!}$ (with
$j^*j_!\cong\mathrm{id}$) gives $i^*j_{i!}=0$, so adjoining the zero stratum $\overline
X_i\setminus X_i$ proves constructibility of $j_{i!}K|_{X_i}$. Proper direct image preserves
bounded constructibility here by the $\Qlb$ clause of [sk-thm-sf-ctf-stability], applied only to
the separated schemes $\overline X_i,V_i$. Step 3 identifies this output with $(T_cK)|_{V_i}$.
Take the minimum and maximum of the finitely many cohomological bounds. The sheaf axiom then gives
the same global bound. In each degree, finite local stratifications give a global finite
stratification by intersecting their strata with the disjoint pieces
$V_i\setminus\bigcup_{j<i}V_j$ and refining. These are locally closed constructible pieces on a
Noetherian scheme. Their finite constant models restrict, so [sk-def-sfb-constructible] gives
constructibility of $\mathcal H^n(T_cK)$. Thus every $T_c$ preserves $D^b_c$, including
nonseparated bases.

5. We first compare a compactification $c$ with its dense replacement $c^d$. The closure
construction [sk-lem-nagata-sketch-closure] gives a closed immersion $a:Z^d\hookrightarrow Z$ and
open $j_d:X\hookrightarrow Z^d$. The square over $j:X\hookrightarrow Z$ is cartesian, since the
closure restricts to $X$ on this open. Step 3 gives $j^*Ra_*j_{d!}K\simeq K$. By the derived open
adjunction [lem-weil-pbc-condensed-open-closed-recollement], define $e_a:j_!K\to Ra_*j_{d!}K$ as
the unique map with this restriction the identity. On each affine open $V\subset Z$, the closure
commutes with restriction [lemma-nagata-scheme-image-restrict-open]. All schemes of the restricted
factorization are separated and finite type over $k$. The canonical density normalization [sk-lem-
nagata-density-normalization], with target $V$ and proper map $\mathrm{id}_V$, gives an
isomorphism $\psi:j_!K|_{X\cap V}\xrightarrow{\sim}(Ra_*j_{d!}K)|_V$ (Step 3 identifies its target
with the restriction). Its restriction to $X\cap V$ is some automorphism $\alpha$ of $K|_{X\cap
V}$; then $\psi\circ j_!(\alpha^{-1})$ is an isomorphism restricting to the identity, so
uniqueness under $j_!\dashv j^*$ identifies it with the restriction of $e_a$. No claim that $\psi$
itself restricts to the identity is used. Consequently $e_a$ is an isomorphism by Step 3. Applying
$Rp_*$ and its composition comparison gives $T_c\simeq T_{c^d}$.

6. Let $h:Z'\to Z$ be a proper refinement whose source compactification is dense. The square on
$X$ is cartesian by [lem-nagata-dense-refinement-cartesian], even if the target compactification
is not dense. Step 3 gives $\theta_h:j^*Rh_*j'_!K\simeq K$. Define $e_h:j_!K\to Rh_*j'_!K$ to be
the adjunct of $\theta_h^{-1}$ under the open adjunction [lem-weil-pbc-condensed-open-closed-
recollement]. This gives a natural map uniquely characterized by identity on $X$. If both
compactifications are dense, restrict to any affine $V\subset Z$. Properness makes $h^{-1}V$
separated finite type over $k$, and $X\cap V$ is an open subscheme of $V$. Density persists under
this restriction, since the injection $\mathcal O\to j_*\mathcal O_X$ remains an injection. The
restricted comparison is exactly that of [det-sf-comp-coherence-refinement](1),(2), for
compactifications of $X\cap V\to V$. Its constructible input has finite Tor amplitude by [lem-
integral-ctf-equals-bc], so the cited isomorphism applies. Step 3 detects invertibility globally.
For a nondense target, $h$ factors through its schematic closure of $X$: the closure ideal pulls
back to functions vanishing on the schematically dense open $X$ of $Z'$, hence to zero. The factor
is proper by base change of $h$ along the closed immersion [lem-weil-pbc-proper-fp-permanence].
Compose its dense-target comparison with the closure comparison of Step 5. Its restriction is the
identity, so uniqueness identifies it with $e_h$. Thus $e_h$ is invertible also in this case.

7. For composable refinements $Z''\xrightarrow{a}Z'\xrightarrow{h}Z$, with $Z''$ and $Z'$ dense,
use the canonical identification $R(ha)_*\simeq Rh_*Ra_*$ of [lem-weil-derived-direct-image-
composition]. Both $e_{ha}$ and $Rh_*(e_a)\circ e_h$ start at $j_!K$. Under $j_!\dashv j^*$, their
adjuncts are the same map: after the identifications of Step 3 they are respectively $1_K$ and
$1_K\circ1_K$. Hence they agree by adjunction bijectivity. The same argument gives
$e_{\mathrm{id}}=1$. Applying $Rp_*$ and its unital associative compositor defines
$\rho_h:T_c\xrightarrow{\sim}T_{c'}$ for a dense-source refinement $h:c'\to c$, with
$\rho_{ha}=\rho_a\rho_h$ whenever the intermediate source is dense. This proves equality of the
globally constructed maps; open-cover detection was used only for invertibility, not for equality
of derived morphisms.

8. For arbitrary $c_1,c_2$, choose a common dense refinement $d\xrightarrow{u_i}c_i$, which exists
by [det-nagata-refinement-common-dense], and put $\phi_{2,1}=\rho_{u_2}^{-1}\rho_{u_1}:T_{c_1}\to
T_{c_2}$. Given two choices $d,e$, cofilteredness [prop-nagata-compactification-category] supplies
a common refinement and equalizes the finitely many parallel composites to $c_1,c_2$; take a
further dense refinement. Step 7 then inserts the same invertible factor into numerator and
denominator, which cancels. Thus $\phi$ is choice-independent. Using a single common dense
refinement of three compactifications gives
$\phi_{3,2}\phi_{2,1}=\rho_3^{-1}\rho_2\rho_2^{-1}\rho_1=\phi_{3,1}$ and $\phi_{c,c}=1$. For an
arbitrary proper refinement $h:c'\to c$, choose dense $d\to c'$ and use its composite to $c$; its
comparison is $\rho_{d\to c'}^{-1}\rho_{d\to c}$. Independence and the displayed cancellation
prove identity and composition also for these refinements, and agree with the direct normalized
construction whenever its source is dense. Choose one $c$ to define $Rf_!=T_c$ on $D^b_c$; the
$\phi$ provide the asserted coherent comparisons with every other $T_d$.

9. For $K\in D^b_c(X,\Lambda)$ with $\mathcal H^i(K)=0$ for $i<a$, exact $j_!$ gives $D(j_!)K\in
D^{\ge a}$ by [lem-weil-pbc-exact-functor-bounded-below]. The module category on $Z$ has enough
injectives by Step 2. Apply [lem-weil-pbc-dplus-injective-representative] to represent this object
by a K-injective complex $I$ of injectives with $I^i=0$ for $i<a$. By the total-module-derived
convention [sk-def-sfb-module-derived-pushpull], $Rp_*D(j_!)K$ is represented by $p_*I$.
Additivity of $p_*$ [sk-def-sfb-module-pushforward-pullback] gives $(p_*I)^i=p_*0=0$ for $i<a$.
Hence the same cohomological lower bound holds for $T_cK$, and therefore for $Rf_!K$ through the
comparisons. Taking $a=0$ and $K=F[0]$ proves the asserted negative-degree vanishing. This
calculation uses no exactness claim about $p_*$ beyond its stated additive left exactness.

10. The Noetherian-scheme conclusion of [det-lem-coefficient-heart-closure] says precisely that
constructible $\Lambda$-modules are closed under kernels, cokernels and extensions in the ambient
module category. In a triangle whose two vertices have bounded constructible cohomology, the long
exact cohomology sequence expresses the third vertex's cohomology as extensions of such kernels
and cokernels; outside a finite range all these objects vanish. Thus $D^b_c$ is a full
triangulated subcategory. Standard truncations merely retain the cohomology in the indicated half-
line, so they stay in $D^b_c$; their degree-zero intersection is exactly degree-zero constructible
modules [sk-def-sfb-constructible]. The standard ambient t-structure therefore restricts and its
heart is $\operatorname{Cons}(T,\Lambda)$ with its exact inclusion, including for the nonseparated
schemes considered here. Step 2's triangulated functor restricts to these full subcategories by
Step 4, which completes all clauses. On separated schemes its preservation assertion is exactly
the $\Qlb$ instance of [sk-thm-sf-ctf-stability].
-/
theorem condensedShriekBoundedQcqs
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [QuasiSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left]
    [QuasiCompact f.left] :
    HasCompactification f.left ∧
    Exists fun
      [(constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X.left).IsTriangulated] ↦
    Exists fun
      [(constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) Y.left).IsTriangulated] ↦
    ∃ hpres : ∀ (c : Compactification f.left)
        (K : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X.left),
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) Y.left
        ((F (Profinite.padicAlgClRingObj ℓ) c).obj K.obj),
    (∀ c : Compactification f.left,
      ((constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) Y.left).lift
        ((constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X.left).ι ⋙
          F (Profinite.padicAlgClRingObj ℓ) c)
        (hpres c)).IsTriangulated) ∧
    (∀ c : Compactification f.left,
      PreservesFiniteLimits (openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) c.i) ∧
      PreservesFiniteColimits (openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) c.i)) ∧
    (∃ τ : ∀ c d : Compactification f.left,
        (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X.left).ι ⋙
          F (Profinite.padicAlgClRingObj ℓ) c ≅
          (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X.left).ι ⋙
            F (Profinite.padicAlgClRingObj ℓ) d,
      (∀ (c d : Compactification f.left) (r : d.Refinement c)
          (K : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X.left),
        (τ c d).hom.app K = (refinement (Profinite.padicAlgClRingObj ℓ) r).app K.obj) ∧
      (∀ c : Compactification f.left, τ c c = Iso.refl _) ∧
      (∀ c d e : Compactification f.left, τ c d ≪≫ τ d e = τ c e)) ∧
    (∀ (c : Compactification f.left)
        (K : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X.left) (a : ℤ),
      (∀ i : ℤ, i < a → IsZero ((DerivedCategory.homologyFunctor _ i).obj K.obj)) →
      ∀ i : ℤ, i < a →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj
          ((F (Profinite.padicAlgClRingObj ℓ) c).obj K.obj))) ∧
    (∀ (c : Compactification f.left)
        (M : ConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X.left) (b : ℤ), b < 0 →
      IsZero ((DerivedCategory.homologyFunctor _ b).obj
        ((F (Profinite.padicAlgClRingObj ℓ) c).obj
          ((DerivedCategory.singleFunctor _ 0).obj M.obj)))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
