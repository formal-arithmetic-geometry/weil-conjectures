/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Topology.SpectralSpace.ConnectedComponentsProfinite
public import Sheaf.AlgebraicGeometry.CondensedScalarRealization
import Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality
import Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation
import Sheaf.RingTheory.HenselianWStrictLocalInvariance
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent

/-!
# Henselian rigidity of lisse condensed-coefficient complexes

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Corollary 4.4(1)--(2)
(blueprint: lem-zl-condensed-henselian-lisse-rigidity).

## Main definitions and statement

* `discreteScalarExtensionPullbackIso` constructs the canonical comparison on all
  unbounded complexes over the discrete ring Γ(*, Λ), using the recorded constant functor.
* `henselian_lisse_rigidity` states the component homeomorphism, invariance of
  w-contractibility, and the exact symmetric monoidal lisse equivalence. Symmetric
  monoidality is `Functor.Braided` for the published Koszul braiding
  `DerivedCategory.braidedCategory'` of the derived tensor, passed explicitly in source
  and target.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Left exactness of inverse image from the profinite point, reused on module objects.
Source: HRS, Section 3, pullback paragraph
(blueprint: lem-zl-condensed-henselian-lisse-rigidity). -/
instance henselianPoint_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (upperStarFromPoint X) :=
  by
    unfold upperStarFromPoint pointUpperStar
    infer_instance

/-- Right exactness of inverse image from the profinite point.
Source: HRS, Section 3, pullback paragraph
(blueprint: lem-zl-condensed-henselian-lisse-rigidity). -/
instance henselianPoint_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (upperStarFromPoint X) :=
  by
    let : pointUpperStar.{u}.IsLeftAdjoint :=
      pointUpperStarLowerStarAdjunction.isLeftAdjoint
    unfold upperStarFromPoint
    infer_instance

/-- Additivity of the canonical module inverse image from the profinite point.
Source: HRS, Section 3, pullback paragraph
(blueprint: lem-zl-condensed-henselian-lisse-rigidity). -/
instance henselianPoint_mapMod_additive
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) : ((upperStarFromPoint X).mapMod Λ).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The ordinary unbounded derived inverse image of condensed modules from the point.
In particular it sends a discrete scalar complex extended to Λ to its scalar extension
on X. This is the existing inverse image, applied levelwise, with no completeness condition.
Source: HRS, Section 3, pullback paragraph before (3.1)
(blueprint: lem-zl-condensed-henselian-lisse-rigidity). -/
def derivedFromCondensed
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) :
    DerivedCategory (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) ⥤
      DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  ((upperStarFromPoint X).mapMod Λ).mapDerivedCategory

/-- The canonical coefficient-compatible comparison on module inverse images from the
point. It is induced by upperStarFromPointComp, followed by cancellation of restriction
and extension along the SAME coefficient isomorphism condensedPullbackHom.
Source: HRS, Section 3, pullback paragraph before (3.1)
(blueprint: lem-zl-condensed-henselian-lisse-rigidity). -/
def fromCondensedPullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStarFromPoint Y).mapMod Λ ⋙ upperStar Λ f ≅
      (upperStarFromPoint X).mapMod Λ :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapModCompIso (upperStarFromPoint Y) (ProEtale.upperStar Ab.{u + 1} f)
        (upperStarFromPointComp f).hom Λ) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _
        (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)) ≪≫
        (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ f)).unitIso.symm) ≪≫
    Functor.rightUnitor _

/-- The derived canonical point comparison. Whiskering it with the realization of
constant discrete scalar complexes gives the scalar-extension compatibility in the
rigidity statement. It is the derived image of the specified coefficient comparison,
not a chosen unrelated isomorphism.
Source: HRS, Section 3, pullback paragraph before (3.1)
(blueprint: lem-zl-condensed-henselian-lisse-rigidity). -/
def derivedFromCondensedPullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    derivedFromCondensed Λ Y ⋙ (upperStar Λ f).mapDerivedCategory ≅
      derivedFromCondensed Λ X :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (fromCondensedPullbackIso Λ f)

/-- The canonical scalar comparison for every unbounded discrete scalar complex.
It is obtained by whiskering the canonical coefficient-compatible point comparison,
so its coefficient map is exactly condensedPullbackHom, including for identities.
Source: HRS, Section 3, pullback paragraph before (3.1); Corollary 4.4
(blueprint: lem-zl-condensed-henselian-lisse-rigidity). -/
def discreteScalarExtensionPullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    condensedScalarRealization Λ Y ⋙ (upperStar Λ f).mapDerivedCategory ≅
      condensedScalarRealization Λ X :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _
          (Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft _ (derivedFromCondensedPullbackIso Λ f)))

/-- Henselian rigidity, including the canonical inverse-image functor on the full
subcategories of dualizable objects.

Source: HRS, Corollary 4.4(1)--(2)
(blueprint: lem-zl-condensed-henselian-lisse-rigidity).

The exact symmetric monoidal clause is `Functor.IsTriangulated` together with a
`Functor.Braided` structure: a strong monoidal structure (invertible unit and tensor
comparisons with their coherence laws) whose tensor comparison commutes with the derived
Koszul braidings `DerivedCategory.braidedCategory'` of source and target. These braidings
are `DerivedMonoidal.braiding'` for `DerivedCategory.Qh` and quasi-isomorphisms, over the
same derived tensor `Mod.derivedMonoidalCategory` as the dualizable subcategories.

Proof:
1. Apply the henselian-pair definition [def-weil-pbc-henselian-terminology] to the finite
   $A$-algebra $A$ itself. It gives a bijection
   $\operatorname{Idem}(A)\to\operatorname{Idem}(A/I)$. Under
   [lem-weil-pbc-spec-clopen-idempotent], the clopen corresponding to $e$ is $D(e)$, and
   $i^{-1}D(e)=D(\overline e)$. Thus inverse image is a bijection between the clopens of $T$ and
   those of $Z$.
2. Put $P=\pi_0(T)$, $Q=\pi_0(Z)$ and $h=\pi_0(i):Q\to P$. By [sk-def-pe-wlocal] the underlying
   spaces of these affine schemes are spectral; [lem-pe-spectral-components-profinite] makes $P,Q$
   compact Hausdorff. Every clopen of a space is a union of components, and hence descends to a
   clopen of its component quotient. Therefore Step 1 says that $h^{-1}$ is a bijection on
   clopens. The formula of [lem-weil-pbc-quasicompact-components-clopen-intersection], applied to
   $T$ and $Z$, separates distinct components by clopens. If $q_1\ne q_2$ in $Q$, choose a
   separating clopen in $Q$ and lift it along $h^{-1}$; this separates $h(q_1),h(q_2)$, proving
   injectivity. The image $K=h(Q)$ is compact, hence closed in $P$. If $p\notin K$, for each $k\in
   K$ choose a clopen containing $p$ and excluding $k$. Compactness of $K$ gives finitely many
   whose intersection $V$ misses $K$. Then $h^{-1}V=\varnothing=h^{-1}\varnothing$, contradicting
   injectivity on clopens since $p\in V$. So $h$ is surjective. A continuous bijection from
   compact to Hausdorff is a homeomorphism: it sends closed sets to compact, thus closed, sets.
3. By [lem-zl-henselian-wstrict-local-invariance], $A$ is w-strictly local exactly when $A/I$ is.
   By Step 2, $P$ is extremally disconnected exactly when $Q$ is: a homeomorphism preserves open
   sets, their closures, and openness of those closures. The definition [sk-def-pe-wlocal] of
   w-contractibility is the conjunction of these two conditions, so $T$ is w-contractible if and
   only if $Z$ is.
4. Assume these equivalent conditions. Apply [lem-zl-condensed-wcontractible-lisse-evaluation] to
   the two w-contractible affine schemes $T$ and $Z$. The coefficient-compatible component maps
   give equivalences $\pi_T^*:D_{\mathrm{lis}}(P,\Lambda)\simeq D_{\mathrm{lis}}(T,\Lambda)$ and
   $\pi_Z^*:D_{\mathrm{lis}}(Q,\Lambda)\simeq D_{\mathrm{lis}}(Z,\Lambda)$. Also
   [lem-zl-condensed-lisse-proetale-locality], for the scheme morphism $i$, gives the exact
   symmetric monoidal functor $i^*$, its restriction to dualizable objects, and its canonical
   coefficient identification.
5. The square of component maps commutes with $i$ and $h$. Here this includes the maps of sites,
   not only the point maps: the component-site construction in
   [lem-zl-condensed-wcontractible-lisse-evaluation] starts with finite clopen subdivisions. A
   clopen $U\subseteq P$ gives the open-and-closed part $T_U\subseteq T$; pulling back gives
   $Z\times_TT_U=Z_{h^{-1}U}$. Thus the two composite constructions agree on every finite
   subdivision and on their inverse-limit construction of a profinite set over $P$. Functoriality
   of inverse image gives $i^*\pi_T^*\cong\pi_Z^*h^*$, compatibly with coefficients, since each
   coefficient ring is pulled back from the same condensed ring $\Lambda$.
6. Since $h$ is a homeomorphism, relabelling profinite sets over $P$ by $h$ gives an inverse to
   $h^*$, also on the dualizable subcategories. By Steps 4 and 5, $i^*$ is conjugate by
   $\pi_T^*,\pi_Z^*$ to this equivalence. Hence $i^*$ is an equivalence and in particular gives
   bijections on all morphism sets between dualizable objects. Finally
   [lem-zl-condensed-lisse-proetale-locality] identifies $i^*(\Lambda_T\otimes^L_{\underline
   R}\underline C)$ with $\Lambda_Z\otimes^L_{\underline R}\underline C$ for every constant
   discrete scalar complex $C\in D(R)$, $R=\Gamma(*,\Lambda)$; this is the required canonical
   scalar-extension compatibility. -/
theorem henselian_lisse_rigidity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (A : Type u) [CommRing A] (I : Ideal A) [HenselianRing A I] :
    IsHomeomorph (PrimeSpectrum.continuous_comap (Ideal.Quotient.mk I)).connectedComponentsMap ∧
      (IsWContractibleRing A ↔ IsWContractibleRing (A ⧸ I)) ∧
      (IsWContractibleRing A →
        (upperStar Λ (Spec.map
          (CommRingCat.ofHom (Ideal.Quotient.mk I)))).mapDerivedCategory.IsTriangulated ∧
        Nonempty (@Functor.Braided _ _ _ (DerivedCategory.braidedCategory' _) _ _ _
          (DerivedCategory.braidedCategory' _)
          (upperStar Λ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).mapDerivedCategory) ∧
        ∃ e :
          (ObjectProperty.FullSubcategory
            (IsDualizable (C := DerivedCategory
              (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of A))) Ab.{u + 1})
                (condensedRingObj Λ (Spec (.of A))))))) ≌
          (ObjectProperty.FullSubcategory
            (IsDualizable (C := DerivedCategory
              (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of (A ⧸ I)))) Ab.{u + 1})
                (condensedRingObj Λ (Spec (.of (A ⧸ I)))))))),
          Nonempty (e.functor ⋙ ObjectProperty.ι _ ≅
            ObjectProperty.ι _ ⋙
              (upperStar Λ (Spec.map
                (CommRingCat.ofHom (Ideal.Quotient.mk I)))).mapDerivedCategory)) :=
  by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
