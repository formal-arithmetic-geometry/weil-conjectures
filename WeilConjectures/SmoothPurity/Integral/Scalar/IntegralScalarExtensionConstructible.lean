/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
public import WeilConjectures.SmoothPurity.Integral.IntegralConstructibleLinear

import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarFiniteLevelBounds
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTowerEffectivity
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
public import WeilConjectures.AlgebraicGeometry.IntegralScalarExtensionExactModel
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible

/-! # Constructibility under completed integral scalar extension

Source: Weil conjectures blueprint, sec-smooth-purity/sk-def-sf-operations,
order 1460 (blueprint: lem-weil-integral-scalar-extension-constructible).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 1024

universe d u

open CategoryTheory

namespace WeilConjectures

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

private theorem finiteLevel_property_of_iso
    (n : ℕ) {A B : AlgebraicGeometry.Scheme.proEtaleDerivedCategory Y
      (Padic.coefficientExtensionRing l L (n + 1))} (e : A ≅ B)
    (r s : ℤ)
    (hA : AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible l L (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) Y A)
    (hb : ∀ i : ℤ, i ∈ AlgebraicGeometry.Scheme.proEtaleCohomologicalSupport A →
      r ≤ i ∧ i ≤ s) :
    AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible l L (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) Y B ∧
    ∀ i : ℤ, i ∈ AlgebraicGeometry.Scheme.proEtaleCohomologicalSupport B →
      r ≤ i ∧ i ≤ s := by
  let : Finite (Padic.coefficientExtensionRing l L (n + 1)) :=
    Padic.finite_coefficientExtensionRing l L (n + 1) (by omega)
  let P := AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible l L (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)) Y
  have : P.IsClosedUnderIsomorphisms :=
    (AlgebraicGeometry.Scheme.proEtale_bounded_constructible_isTriangulated Y
      (Padic.coefficientExtensionRing l L (n + 1))).1
  refine ⟨P.prop_of_iso e hA, ?_⟩
  intro i hi
  apply hb i
  exact fun hz ↦ hi (((DerivedCategory.homologyFunctor _ i).mapIso e).isZero_iff.mp hz)

/-- Completed integral extension preserves the actual integral constructible property.
Source: blueprint order 1460 (blueprint: lem-weil-integral-scalar-extension-constructible).
Proof: the strict quotient tower is normalized by the balanced tensor associator.
Its first layer is scalar extension to the finite residue field. Filter each
higher target quotient by powers of its uniformizer, with that residue field
as each layer. Extension closure preserves constructibility and the same
cohomological interval through this finite filtration. Normalized DVR effectivity
identifies all these levels with reductions of the completed extension and gives
its derived completeness. The constant-section balancing identity gives linearity.

Complete DAG proof plan:
1. Write $R=\mathcal O_E$, $S=\mathcal O_L$, $k_E=R/(\varpi_E)$ and $k_L=S/(\varpi_L)$, with
completed coefficient sheaf $\widehat R_Y$. By [lem-weil-l-adic-extension-integers-dvr] the
residue fields are finite and both valuation rings are DVRs. The maps of
[def-weil-integral-scalar-extension] induce $k_E\to k_L$: $\varpi_E\in\varpi_L S$. This is a
unital map of fields, hence injective. Since $k_L$ is a finite set, successively adjoining a
vector outside the span of the vectors already chosen terminates and gives a finite $k_E$-basis,
say of length $d$. By [def-weil-derived-complete-integral-detailed] choose $r\le s$ bounding the
cohomology of all reductions of $K$, in particular $K_1=K\otimes^L_R k_E$; its cohomology sheaves
are constructible. Only this first reduction and its bound will be used in the finite-level
argument.
2. Choose one K-flat resolution $P\to K$ with flat terms as in
[def-weil-integral-scalar-extension]. For $m\ge1$ put $B_m=S/(\varpi_L^m)$ and
$M_m=P\otimes_{\widehat R_Y}(B_m)_Y$, with the strict quotient transition maps. By
[lem-pur-derived-change-of-rings] these complexes compute $K\otimes^L_R B_m$. By
[lem-pur-kflat-change-of-rings], $M_m$ is K-flat with flat terms over $(B_m)_Y$. Consequently,
for $m\ge n$, derived reduction of $M_m$ to $B_n$ is computed by its ordinary tensor, and the map
$$(P\otimes_{\widehat R_Y}(B_m)_Y)\otimes_{(B_m)_Y}(B_n)_Y\longrightarrow P\otimes_{\widehat
R_Y}(B_n)_Y$$ is an isomorphism of complexes. Its local tensor formula is $(p\otimes b)\otimes
c\mapsto p\otimes bc$, with inverse $p\otimes c\mapsto(p\otimes1)\otimes c$; balancing makes the
maps inverse. The maps commute with differentials, and for $m\ge n\ge a$ both composites send
$(p\otimes b)\otimes c\otimes z$ to $p\otimes bcz$. Thus the adjoints of the specified transition
maps are these isomorphisms and satisfy the quotient cocycle. The strict system is a normalized
DVR tower in the sense of [def-coef-normalized-dvr-tower]; this establishes normalization rather
than assuming it.
3. First treat the common layer $Q=P\otimes_{\widehat R_Y}(k_L)_Y$. Put $P_1=P\otimes_{\widehat
R_Y}(k_E)_Y$, representing $K_1$. By [lem-pur-kflat-change-of-rings], $P_1$ is K-flat over
$(k_E)_Y$, so $P_1\otimes_{(k_E)_Y}(k_L)_Y$ computes $K_1\otimes^L_{k_E} k_L$. The coefficient
map $\widehat R_Y\to(k_L)_Y$ factors through $(k_E)_Y$ by the residue map of step 1. The balanced
maps $(p\otimes a)\otimes b\mapsto p\otimes ab$ and $p\otimes b\mapsto(p\otimes1)\otimes b$ are
inverse chain maps identifying this complex with $Q$. The chosen $k_E$-basis identifies $(k_L)_Y$
with $(k_E)_Y^{\oplus d}$, so tensoring with it is a finite direct sum of the identity functor.
It is exact, and $\mathcal H^i(Q)=\mathcal H^i(K_1)\otimes_{k_E}k_L$; this also follows by
computing cycles and boundaries in the finite direct sum. For the finitely many degrees $r\le
i\le s$, take a common finite refinement of their constructible stratifications: its members are
intersections of the locally closed constructible members, so remain locally closed constructible
and partition $Y$. Pullback to such a stratum is exact and commutes with constants and tensor, by
[def-weil-proetale-inverse-image] and [lem-weil-pbc-left-exact-site-inverse-image-tensor]. On a
cover trivializing $\mathcal H^i(K_1)$ to the constant sheaf of a finite $k_E$-module $V$, the
displayed cohomology of $Q$ is the constant sheaf of $V\otimes_{k_E}k_L$, with its actual
$k_L$-action. For clarity, inverse image takes each constant coefficient ring to the same
constant ring: the constant set sheaf is the copower of the terminal sheaf indexed by the ring,
and the cited inverse-image theorem preserves both terminal objects and colimits; addition and
multiplication are transported because it preserves finite products. Thus module pullback here is
the exact inverse image, not tensor along an unknown ring comparison. The constant tensor
identification is induced by $v\otimes c\mapsto v\otimes c$ in the sheafified tensor
presentation. Exact sheafification [lem-weil-pbc-site-module-presheaf-sheafification-exact]
justifies the constant tensor and cohomology calculation. This module is finite, as a quotient of
the finite set $V\otimes_{k_E}k_E^{\oplus d}\cong V^{\oplus d}$. Therefore $Q$ has constructible
$k_L$-cohomology and support in $[r,s]$. For each $m$, regard $Q$ as a $(B_m)_Y$-complex via
$B_m\to k_L$; the same constant models show constructibility as $B_m$-modules, with the same
support.
4. Fix $m$. Filter the $B_m$-module $B_m$ by the ideals $J_j=\varpi_L^j S/\varpi_L^m S$ for $0\le
j\le m$. Thus $J_0=B_m$, $J_m=0$, and multiplication by $\varpi_L^j$ induces a $B_m$-linear
isomorphism $k_L\cong J_j/J_{j+1}$ for $j<m$. It is surjective by the definition of $J_j$; its
kernel is $(\varpi_L)$ since $S$ is a domain and $\varpi_L^m S\subseteq\varpi_L^{j+1}S$, so
cancellation of $\varpi_L^j$ reduces the kernel assertion to membership in $\varpi_L S$
[lem-weil-l-adic-extension-integers-dvr]. In particular each $J_j/J_{j+1}$ is a finite set.
Descending induction using the fibers of $J_j\to J_j/J_{j+1}$ (each a coset of $J_{j+1}$) shows
that $J_j$ is finite, starting with $J_m=0$. Thus $B_m=J_0$ is indeed a finite commutative ring,
as required for the constructible-subcategory theorem below. Exact constant sheafification
[lem-weil-pbc-site-module-presheaf-sheafification-exact] gives short exact coefficient sheaf
sequences $0\to(J_{j+1})_Y\to(J_j)_Y\to(k_L)_Y\to0$. They are sequences of $\widehat R_Y$-modules
as well, through the compatible coefficient maps. Because each $P^q$ is flat, tensoring produces
degreewise short exact sequences of $B_m$-complexes $$0\to P\otimes_{\widehat R_Y}(J_{j+1})_Y\to
P\otimes_{\widehat R_Y}(J_j)_Y\to Q\to0.$$ They yield distinguished triangles by
[lem-weil-pbc-complex-ses-triangle]. Descending induction from $j=m$ now proves that every middle
complex has constructible cohomology and support in $[r,s]$: the base is the zero complex; the
induction step uses the constructible layer $Q$ from step 3 and extension closure
[lem-weil-proetale-dbc-triangulated] for the finite ring $B_m$. For a degree $i$ outside $[r,s]$,
the two outer cohomology objects vanish, so the middle one vanishes by
[lem-sf-derived-homology-long-exact]. At $j=0$ this complex is $M_m$. The interval never changes
during the induction and is independent of $m$; no flatness of $B_m$ over $A_{E,m}$, no finite
Tor hypothesis and no Noetherian hypothesis on $Y$ were used.
5. Let $N=K\otimes_R S$ be the object defined by [def-weil-integral-scalar-extension]. It is the
fixed cone $\operatorname{Cone}(1-s)[-1]$ of the strict tower $\operatorname{Res}^L_mM_m$, and is
a derived limit of that tower by [lem-weil-integral-scalar-extension-well-defined]. Step 2
verified precisely the normalized-tower hypothesis of [lem-coef-normalized-dvr-effectivity], with
the DVR $S$ and quotient rings $B_m=A_{L,m}$. Apply that theorem to obtain compatible
isomorphisms $N\otimes^L_S B_m\cong M_m$ and derived completeness of $N$. This is the same
derived limit as the normalized-tower theorem: the strict tower theorem
[lem-weil-pbc-ringed-strict-tower-homotopy-limit] computes total derived inverse limit by its
Roos triangle. Countable products of completed-coefficient module sheaves are exact by
[lem-weil-proetale-countable-products-exact], so [lem-weil-derived-limit-products-core]
identifies the derived products in that triangle with the termwise products used here. To make
the comparison explicit, take the strict tower resolution $X_\bullet\to I_\bullet$ used by the
strict-tower theorem, where $X_m=\operatorname{Res}^L_mM_m$. Its maps are termwise
quasi-isomorphisms and commute with the transitions. Exact countable products imply that
$\prod_mX_m\to\prod_mI_m$ is a quasi-isomorphism: cohomology of these products is the product of
the cohomologies by [lem-weil-derived-limit-products-core]. The commuting square with $1-s$
therefore induces a quasi-isomorphism of the shifted mapping-cone complexes. On each evaluation
it commutes with projection to the corresponding tower member, since the square came from a
strict tower map. The Roos model of the strict-tower theorem is consequently identified with the
fixed cone defining $N$, with its evaluations. This supplies the comparison needed for the
canonical counit isomorphisms of the effectivity theorem, without asserting uniqueness of
arbitrary cone maps. The finite-level statement of step 4 therefore supplies constructibility and
the single interval $[r,s]$ for all derived reductions of $N$. These are exactly the conditions
of [def-weil-derived-complete-integral-detailed] for $L$, so $N\in D^b_c(Y,S)$. Finally the
ambient functor is $R$-linear by clause 3 of [lem-weil-integral-scalar-extension-well-defined].
Restricting its objects and morphisms to the full subcategories just proved preserved leaves the
equality $T(af)=aT(f)$ intact, and gives the asserted $R$-linear functor.
-/
theorem integralScalarExtension_constructible
    (K : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) :
    boundedConstructibleDerivedCompleteIntegral D l hl L Y
      ((integralScalarExtension l E L ι Y).obj K.obj) := by
  classical
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0} _
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{u + 1} := integralCoefficientAbSheafify.{u, u} Y
  let : (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} := integralCoefficientAbLocallyBijective.{u, u} Y
  let X := (DerivedCategory.Q (C := integralTowerModules l E Y)).objPreimage K.obj
  let eX := (DerivedCategory.Q (C := integralTowerModules l E Y)).objObjPreimageIso K.obj
  obtain ⟨V, f, hV, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) X
  have hgood : integralOperationsGoodComplex l E Y V := by
    refine ⟨hV, fun i ↦ ?_⟩
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso
        (completedIntegralCommRingSheafUnrestricted l E Y) (V.X i)).symm (hf i)
  let P : (integralOperationsGoodComplex l E Y).FullSubcategory := ⟨V, hgood⟩
  let : QuasiIso f := hq
  let e : DerivedCategory.Q.obj P.obj ≅ K.obj := asIso (DerivedCategory.Q.map f) ≪≫ eX
  have hP := (boundedConstructibleDerivedCompleteIntegral D l hl E Y).prop_of_iso
    e.symm K.property
  obtain ⟨_, r, s, hrs, hlevels⟩ := hP
  have hfinite := integralScalarFiniteLevel_bounds D l hl E L ι Y P r s hrs
    (hlevels 0).1 (hlevels 0).2
  obtain ⟨hc, he⟩ := integralScalarTower_effectivity D l hl E L ι Y P
  have hresult : boundedConstructibleDerivedCompleteIntegral D l hl L Y
      ((integralScalarExtension l E L ι Y).obj (DerivedCategory.Q.obj P.obj)) := by
    refine ⟨hc, r, s, hrs, ?_⟩
    intro n
    obtain ⟨en⟩ := he n
    exact finiteLevel_property_of_iso l L Y n en.symm r s (hfinite n).1 (hfinite n).2
  exact (boundedConstructibleDerivedCompleteIntegral D l hl L Y).prop_of_iso
    ((integralScalarExtension l E L ι Y).mapIso e) hresult

/-- The restricted functor uses the original completed extension on objects and maps.
Source: blueprint order 1460 (blueprint: lem-weil-integral-scalar-extension-constructible). -/
noncomputable def constructibleIntegralScalarExtension :
    boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y ⥤
      boundedConstructibleDerivedCompleteIntegralCategory D l hl L Y :=
  (boundedConstructibleDerivedCompleteIntegral D l hl L Y).lift
    ((boundedConstructibleDerivedCompleteIntegral D l hl E Y).ι ⋙
      integralScalarExtension l E L ι Y)
    (integralScalarExtension_constructible D l hl E L ι Y)

set_option backward.isDefEq.respectTransparency.types false in
/-- Integer-linearity of the restricted completed coefficient functor.
Source: blueprint order 1460 (blueprint: lem-weil-integral-scalar-extension-constructible).
Proof: the ambient integralScalarExtensionWellDefined equality is the balancing
identity for the actual constant sections. Restriction to full subcategories
preserves that equality and their inherited Hom module structures. -/
theorem constructibleIntegralScalarExtension_smul
    (K K' : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y)
    (f : K ⟶ K') (a : Padic.coefficientExtensionIntegers l E) :
    (constructibleIntegralScalarExtension D l hl E L ι Y).map (a • f) =
      integralScalarIntegerInclusion l E L ι a •
        (constructibleIntegralScalarExtension D l hl E L ι Y).map f := by
  let : Linear (Padic.coefficientExtensionIntegers l E)
      (completedIntegralDerivedCategory l E Y D hl) := integralCoefficientLinear l E Y
  let : Linear (Padic.coefficientExtensionIntegers l L)
      (completedIntegralDerivedCategory l L Y D hl) := integralCoefficientLinear l L Y
  apply ObjectProperty.hom_ext
  change (integralScalarExtension l E L ι Y).map (a • f.hom) =
    integralScalarIntegerInclusion l E L ι a •
      (integralScalarExtension l E L ι Y).map f.hom
  rw [(integralCoefficientLinear_existsUnique l E Y).exists.choose_spec,
    (integralCoefficientLinear_existsUnique l L Y).exists.choose_spec]
  exact (integralScalarExtensionWellDefined l E L ι Y).2.choose_spec.choose_spec.2.2.2.2
    a K.obj K'.obj f.hom

end WeilConjectures

namespace WeilConjectures

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

private local instance scalarSiteSmall : EssentiallySmall.{u + 1} Y.ProEt :=
  essentiallySmallSelf.{0} _

private noncomputable local instance scalarSheafify :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} Y

private local instance scalarLocallyBijective :
    (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} := integralCoefficientAbLocallyBijective.{u, u} Y

private theorem scalarMap_eq_completed :
    integralCompletedScalarMap l E L ι Y = completedCoefficientMap l E L ι Y := by
  apply (completedCoefficientMap_existsUnique l E L ι Y).unique
  · exact (integralCompletedScalarMap_existsUnique l E L ι Y).exists.choose_spec
  · exact (completedCoefficientMap_existsUnique l E L ι Y).exists.choose_spec

attribute [local irreducible] integralCompletedScalarMap completedCoefficientMap
  completedScalarChangeData

set_option backward.isDefEq.respectTransparency false in
private theorem tensorPresentation_hom_ext
    {R S : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (A B : SheafOfModules.{u + 1}
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (hA : A = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M) (f g : A ⟶ B)
    (h : ∀ (U : Y.ProEtᵒᵖ) (a : S.obj.obj U) (x : M.val.obj U),
      f.val.app U ((eqToHom hA.symm).val.app U
        ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x))) =
      g.val.app U ((eqToHom hA.symm).val.app U
        ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x)))) : f = g := by
  subst A
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 _)).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => exact h U a x
  | add z z' hz hz' => simp only [map_add, hz, hz']

private theorem tensorPresentation_transport
    {R S : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{u + 1}}
    (φ ψ : R ⟶ S) (hφ : φ = ψ)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (A B : SheafOfModules.{u + 1}
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (hA : A = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M)
    (hB : B = SheafOfModules.changeOfRings.{u, u + 1, u + 1} ψ M)
    (U : Y.ProEtᵒᵖ) (a : S.obj.obj U) (x : M.val.obj U) :
    (eqToHom ((hA.trans (congrArg
      (fun φ : R ⟶ S ↦ SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M) hφ)).trans
        hB.symm)).val.app U
      ((eqToHom hA.symm).val.app U
        ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x))) =
      (eqToHom hB.symm).val.app U
        ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} ψ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(ψ.hom.app U).hom] x)) := by
  subst ψ
  subst A
  subst B
  rfl

private theorem tensorPresentation_natural
    {R S : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{u + 1}}
    (φ ψ : R ⟶ S) (hφ : φ = ψ)
    (M N : SheafOfModules.{u + 1}
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) (f : M ⟶ N)
    (A B C F : SheafOfModules.{u + 1}
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (hA : A = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M)
    (hB : B = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ N)
    (hC : C = SheafOfModules.changeOfRings.{u, u + 1, u + 1} ψ M)
    (hF : F = SheafOfModules.changeOfRings.{u, u + 1, u + 1} ψ N)
    (a : A ⟶ B) (b : C ⟶ F)
    (ha : a = eqToHom hA ≫
      SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} φ M f ≫ eqToHom hB.symm)
    (hb : b = eqToHom hC ≫
      SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} ψ M f ≫ eqToHom hF.symm) :
    a ≫ eqToHom ((hB.trans (congrArg
      (fun φ : R ⟶ S ↦ SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ N) hφ)).trans
        hF.symm) =
      eqToHom ((hA.trans (congrArg
        (fun φ : R ⟶ S ↦ SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M) hφ)).trans
          hC.symm) ≫ b := by
  subst ψ
  subst A
  subst B
  subst C
  subst F
  simpa using ha.trans hb.symm

attribute [local irreducible] SheafOfModules.changeOfRings SheafOfModules.changeOfRingsHom

private noncomputable def ordinaryScalarModelIso :
    integralOrdinaryScalar l E L ι Y ≅ completedOrdinaryScalarExtension l E L ι Y := by
  have hF : ∀ M, (integralOrdinaryScalar l E L ι Y).obj M =
      SheafOfModules.changeOfRings.{u, u + 1, u + 1} (integralCompletedScalarMap l E L ι Y) M :=
    by
      simpa only [integralOrdinaryScalar] using
        (integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose
  have hG : ∀ M, (completedOrdinaryScalarExtension l E L ι Y).obj M =
      SheafOfModules.changeOfRings.{u, u + 1, u + 1} (completedCoefficientMap l E L ι Y) M :=
    by
      simpa only [completedOrdinaryScalarExtension] using
        (completedScalarChangeData l E L ι Y).choose_spec.choose
  have hφ := scalarMap_eq_completed l E L ι Y
  have hobj (M : integralTowerModules l E Y) := ((hF M).trans (congrArg
    (fun φ ↦ SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M) hφ)).trans (hG M).symm
  refine NatIso.ofComponents (fun M ↦ eqToIso (hobj M)) ?_
  intro M N f
  exact tensorPresentation_natural Y _ _ hφ M N f _ _ _ _ (hF M) (hF N)
    (hG M) (hG N) _ _
    (by simpa only [integralOrdinaryScalar] using
      (integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose_spec.choose f)
    (by simpa only [completedOrdinaryScalarExtension] using
      (completedScalarChangeData l E L ι Y).choose_spec.choose_spec.choose f)

private theorem ordinaryScalarModelIso_hom_app (M : integralTowerModules l E Y) :
    (ordinaryScalarModelIso l E L ι Y).hom.app M =
      eqToHom ((((integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose M).trans
        (congrArg (fun φ ↦ SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M)
          (scalarMap_eq_completed l E L ι Y))).trans
        ((completedScalarChangeData l E L ι Y).choose_spec.choose M).symm) := by
  rfl

attribute [local irreducible] ordinaryScalarModelIso
attribute [local semireducible] SheafOfModules.changeOfRings SheafOfModules.changeOfRingsHom

private theorem ordinaryScalarModelIso_transport
    (M : integralTowerModules l E Y) (U : Y.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U)
    (x : M.val.obj U) :
    ((ordinaryScalarModelIso l E L ι Y).hom.app M).val.app U
      ((eqToHom ((integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose M).symm).val.app U
        ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (SheafOfModules.changeOfRingsPresheaf
            (integralCompletedScalarMap l E L ι Y) M).presheaf).app U
              (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
                ((integralCompletedScalarMap l E L ι Y).hom.app U).hom] x))) =
      completedScalarTensorSection l E L ι Y M U s x := by
  rw [ordinaryScalarModelIso_hom_app]
  exact tensorPresentation_transport Y _ _ (scalarMap_eq_completed l E L ι Y)
    M _ _ ((integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose M)
    ((completedScalarChangeData l E L ι Y).choose_spec.choose M) U s x

attribute [local irreducible] completedScalarTensorSection

attribute [local irreducible] integralScalarReductionWitness integralScalarReduction
  integralScalarTensorSection

private theorem complexProduct_hom_ext
    {D : Type*} [Category* D] [Preadditive D] [HasCountableProducts D]
    (X : ℕ → CochainComplex D ℤ) (i : ℤ) {M : D}
    (f g : M ⟶ (∏ᶜ X).X i)
    (h : ∀ n, f ≫ (Pi.π X n).f i = g ≫ (Pi.π X n).f i) : f = g := by
  apply (isLimitOfPreserves (HomologicalComplex.eval D (.up ℤ) i)
    (limit.isLimit (Discrete.functor X))).hom_ext
  intro n
  exact h n.as

attribute [local irreducible] limit

private theorem cocone_degree_ext
    {D : Type*} [Category* D] [Preadditive D] [HasBinaryBiproducts D]
    {P K L₀ : CochainComplex D ℤ} (φ : K ⟶ L₀)
    (f g : P ⟶ CochainComplex.mappingCocone φ) (i : ℤ)
    (hf : f.f i ≫ (CochainComplex.mappingCocone.fst φ).f i =
      g.f i ≫ (CochainComplex.mappingCocone.fst φ).f i)
    (hs : f.f i ≫ (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega) =
      g.f i ≫ (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega)) :
    f.f i = g.f i := by
  have hi := CochainComplex.mappingCocone.id_X φ i (i - 1) (by omega)
  calc
    f.f i = f.f i ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = f.f i ≫ _ := congrArg (f.f i ≫ ·) hi.symm
    _ = g.f i ≫ _ := by
      rw [Preadditive.comp_add, Preadditive.comp_add, reassoc_of% hf, reassoc_of% hs]
    _ = g.f i := by rw [hi, Category.comp_id]

/-- Finite free completed extension preserves bounded constructibility and completeness.
Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: lem-weil-integral-scalar-extension-constructible).
Proof: finite freeness makes termwise tensor exact and commutes with all products in
the reduction Roos complex. Tensor associativity identifies the target reductions with
the extended source reductions after cofinal reindexing of the two uniformizer powers.
Thus completeness and the uniform support interval are preserved. At residue level,
finite coefficient extension preserves finite locally constant stalks on each stratum;
induction over the uniformizer filtration gives every finite target level. -/
theorem integralOrdinaryDerivedScalar_constructible
    (K : completedIntegralDerivedCategory l E Y D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E Y K) :
    boundedConstructibleDerivedCompleteIntegral D l hl L Y
      ((integralOrdinaryDerivedScalar l E L ι Y).obj K) := by
  obtain ⟨χ, hχ, _⟩ := archivedIntegralScalarCompletion l E L ι Y
  let : IsIso (χ.app K) := hχ.2 K
    ((sfDerivedComplete_iff_legacy l E Y D hl K).mpr hK.1)
  exact (boundedConstructibleDerivedCompleteIntegral D l hl L Y).prop_of_iso
    (asIso (χ.app K)).symm
    (integralScalarExtension_constructible D l hl E L ι Y ⟨K, hK⟩)

/-- Restriction of finite free completed tensor to the integral full subcategories.
On complete objects its ordinary exact tensor model computes completed derived tensor.
Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: lem-weil-integral-scalar-extension-constructible). -/
noncomputable def integralConstructibleScalarExtension :
    boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y ⥤
      boundedConstructibleDerivedCompleteIntegralCategory D l hl L Y :=
  (boundedConstructibleDerivedCompleteIntegral D l hl L Y).lift
    ((boundedConstructibleDerivedCompleteIntegral D l hl E Y).ι ⋙
      integralOrdinaryDerivedScalar l E L ι Y)
    (fun K ↦ integralOrdinaryDerivedScalar_constructible D l hl E L ι Y K.obj K.property)

/-- The actual boundary 1-s of the fixed scalar tower, used for both cone coordinates.
Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: lem-weil-integral-scalar-extension-constructible). -/
noncomputable abbrev integralScalarRoosBoundary
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :=
  towerTransitionEndomorphism
    (K := fun n ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n))
    (integralOperationsTowerStep ((integralScalarTowerFunctor l E L ι Y).obj P))

attribute [local irreducible] completedScalarChainComparison

private theorem integralScalarCompletionChain_model_spec :
    let e := NatIso.mapHomologicalComplex (ordinaryScalarModelIso l E L ι Y) (.up ℤ);
    let b := e.hom ≫ completedScalarChainComparison l E L ι Y;
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (n : ℕ)
        (U : Y.ProEtᵒᵖ)
        (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U)
        (x : (P.X i).val.obj U),
        (((b.app P ≫ CochainComplex.mappingCocone.fst
          (integralScalarRoosBoundary l E L ι Y P) ≫
          Pi.π (fun n ↦ (integralScalarLevel l E L ι Y n).obj P) n).f i).val.app U)
            ((eqToHom ((integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose
              (P.X i)).symm).val.app U
              ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
                (SheafOfModules.changeOfRingsPresheaf
                  (integralCompletedScalarMap l E L ι Y) (P.X i)).presheaf).app U
                (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
                  ((integralCompletedScalarMap l E L ι Y).hom.app U).hom] x))) =
          integralScalarTensorSection l E L ι Y n (P.X i) U
            ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app U s) x) ∧
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i j : ℤ)
        (h : i + -1 = j),
        (b.app P).f i ≫ (CochainComplex.mappingCocone.snd
          (integralScalarRoosBoundary l E L ι Y P)).v i j h = 0) := by
  let e := NatIso.mapHomologicalComplex (ordinaryScalarModelIso l E L ι Y) (.up ℤ)
  let b := e.hom ≫ completedScalarChainComparison l E L ι Y
  change _ ∧ _
  constructor
  · intro P i n U s x
    dsimp only [NatTrans.comp_app, HomologicalComplex.comp_f,
      NatTrans.mapHomologicalComplex_app_f]
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
    change (((completedScalarChainComparison l E L ι Y).app P).f i ≫
      (CochainComplex.mappingCocone.fst
        (completedScalarRoosEndomorphism l E L ι Y P)).f i ≫
      (Pi.π (fun n ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n)) n).f i
      ).val.app U
        (((ordinaryScalarModelIso l E L ι Y).hom.app (P.X i)).val.app U
          ((eqToHom ((integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose
            (P.X i)).symm).val.app U
            ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
              (SheafOfModules.changeOfRingsPresheaf
                (integralCompletedScalarMap l E L ι Y) (P.X i)).presheaf).app U
                  (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
                    ((integralCompletedScalarMap l E L ι Y).hom.app U).hom] x)))) = _
    exact (congrArg (fun z ↦
      (((completedScalarChainComparison l E L ι Y).app P).f i ≫
        (CochainComplex.mappingCocone.fst
          (completedScalarRoosEndomorphism l E L ι Y P)).f i ≫
        (Pi.π (fun n ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n)) n).f i
        ).val.app U z) (ordinaryScalarModelIso_transport l E L ι Y (P.X i) U s x)).trans
      (by
        simpa only [completedScalarChainComparison] using
          (completedScalarChainComparison_existsUnique l E L ι Y).exists.choose_spec.1
            P i n U s x)
  · intro P i j hij
    have hj : j = i - 1 := by omega
    subst j
    change (e.hom.app P).f i ≫
      (((completedScalarChainComparison l E L ι Y).app P).f i ≫
        (CochainComplex.mappingCocone.snd
          (completedScalarRoosEndomorphism l E L ι Y P)).v i (i - 1) (by omega)) = 0
    have h : ((completedScalarChainComparison l E L ι Y).app P).f i ≫
        (CochainComplex.mappingCocone.snd
          (completedScalarRoosEndomorphism l E L ι Y P)).v i (i - 1) (by omega) = 0 := by
      simpa only [completedScalarChainComparison] using
        (completedScalarChainComparison_existsUnique l E L ι Y).exists.choose_spec.2 P i
    dsimp only [completedOrdinaryScalarComplex] at h ⊢
    exact (congrArg ((e.hom.app P).f i ≫ ·) h).trans
      (Preadditive.leftComp _ ((e.hom.app P).f i)).map_zero

/-- The completion chain map is fixed by the quotient maps and zero shifted coordinate.
Source: Bhatt--Scholze, Proposition 3.5.1; blueprint finite-free comparison
(blueprint: lem-weil-integral-scalar-extension-constructible).
Proof: the quotient tensor maps commute with the tower transitions. Their product is
therefore killed by 1-s. Lift this map to the mapping cocone with zero degree-minus-one
coordinate. The two displayed cone coordinates determine every component uniquely.
Balanced tensor generation proves naturality in P and the quotient formula on sections. -/
theorem integralScalarCompletionChain_existsUnique :
    ∃! χ : (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
        integralScalarComplexFunctor l E L ι Y,
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (n : ℕ)
        (U : Y.ProEtᵒᵖ)
        (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U)
        (x : (P.X i).val.obj U),
        (((χ.app P ≫ CochainComplex.mappingCocone.fst
          (integralScalarRoosBoundary l E L ι Y P) ≫
          Pi.π (fun n ↦ (integralScalarLevel l E L ι Y n).obj P) n).f i).val.app U)
            ((eqToHom ((integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose
              (P.X i)).symm).val.app U
              ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
                (SheafOfModules.changeOfRingsPresheaf
                  (integralCompletedScalarMap l E L ι Y) (P.X i)).presheaf).app U
                (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
                  ((integralCompletedScalarMap l E L ι Y).hom.app U).hom] x))) =
          integralScalarTensorSection l E L ι Y n (P.X i) U
            ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app U s) x) ∧
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i j : ℤ)
        (h : i + -1 = j),
        (χ.app P).f i ≫ (CochainComplex.mappingCocone.snd
          (integralScalarRoosBoundary l E L ι Y P)).v i j h = 0) := by
  refine existsUnique_of_exists_of_unique ?_ ?_
  · let e := NatIso.mapHomologicalComplex
      (ordinaryScalarModelIso l E L ι Y) (.up ℤ)
    let b := e.hom ≫ completedScalarChainComparison l E L ι Y
    exact ⟨b, integralScalarCompletionChain_model_spec l E L ι Y⟩
  · intro b₁ b₂ hb₁ hb₂
    apply NatTrans.ext
    funext P
    ext i : 1
    let φ := integralScalarRoosBoundary l E L ι Y P
    have hf : (b₁.app P).f i ≫ (CochainComplex.mappingCocone.fst φ).f i =
        (b₂.app P).f i ≫ (CochainComplex.mappingCocone.fst φ).f i := by
      apply complexProduct_hom_ext
      intro n
      change ((b₁.app P).f i ≫ (CochainComplex.mappingCocone.fst φ).f i ≫ _) =
        ((b₂.app P).f i ≫ (CochainComplex.mappingCocone.fst φ).f i ≫ _)
      apply tensorPresentation_hom_ext Y (integralCompletedScalarMap l E L ι Y)
        (P.X i) ((integralOrdinaryScalar l E L ι Y).obj (P.X i)) _
        ((integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose (P.X i))
      intro U s x
      exact (hb₁.1 P i n U s x).trans (hb₂.1 P i n U s x).symm
    have hs := (hb₁.2 P i (i - 1) (by omega)).trans
      (hb₂.2 P i (i - 1) (by omega)).symm
    exact cocone_degree_ext φ (b₁.app P) (b₂.app P) i hf hs

/-- The quotient completion map, with both cone coordinates specified.
Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: lem-weil-integral-scalar-extension-constructible). -/
noncomputable def integralScalarCompletionChain :=
  (integralScalarCompletionChain_existsUnique l E L ι Y).exists.choose

private theorem integralScalarCompletionChain_model :
    integralScalarCompletionChain l E L ι Y =
      (NatIso.mapHomologicalComplex (ordinaryScalarModelIso l E L ι Y) (.up ℤ)).hom ≫
        completedScalarChainComparison l E L ι Y := by
  exact (integralScalarCompletionChain_existsUnique l E L ι Y).unique
    (integralScalarCompletionChain_existsUnique l E L ι Y).exists.choose_spec
    (integralScalarCompletionChain_model_spec l E L ι Y)

/-- The canonical finite-free comparison is uniquely fixed on good representatives.
Source: Bhatt--Scholze, Proposition 3.5.1 and Lemma 6.8.2
(blueprint: lem-weil-integral-scalar-extension-constructible).
Proof: finite freeness identifies ordinary extension with a finite sum on underlying
source modules. It commutes with products and the signed Roos differential. The source
completeness unit is invertible, and cofinality of the two uniformizer filtrations gives
invertibility of exactly the displayed quotient completion map. Its zero shifted
coordinate is retained. The localization of good complexes gives naturality and uniqueness
on the full complete constructible subcategory. No arbitrary lift to a cone is used. -/
theorem integralConstructibleScalarComparison_existsUnique :
    ∃! c : integralConstructibleScalarExtension D l hl E L ι Y ≅
        constructibleIntegralScalarExtension D l hl E L ι Y,
      ∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (hP : boundedConstructibleDerivedCompleteIntegral D l hl E Y
          (DerivedCategory.Q.obj P.obj)),
        (c.hom.app ⟨DerivedCategory.Q.obj P.obj, hP⟩).hom ≫
            (integralScalarExtensionComparison l E L ι Y).hom.app P =
          (integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.app P.obj ≫
            DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι Y).app P.obj) := by
  classical
  obtain ⟨χ, hχ, _⟩ := archivedIntegralScalarCompletion l E L ι Y
  let e : integralConstructibleScalarExtension D l hl E L ι Y ≅
      constructibleIntegralScalarExtension D l hl E L ι Y :=
    NatIso.ofComponents
      (fun K ↦ by
        let : IsIso (χ.app K.obj) := hχ.2 K.obj
          ((sfDerivedComplete_iff_legacy l E Y D hl K.obj).mpr K.property.1)
        let eK : (integralOrdinaryDerivedScalar l E L ι Y).obj K.obj ≅
            (integralScalarExtension l E L ι Y).obj K.obj := asIso (χ.app K.obj)
        exact (boundedConstructibleDerivedCompleteIntegral D l hl L Y).isoMk eK)
      (by
        intro K M f
        apply ObjectProperty.hom_ext
        exact χ.naturality f.hom)
  refine ⟨e, ?_, ?_⟩
  · intro P hP
    exact hχ.1 P
  · intro c hc
    apply Iso.ext
    apply NatTrans.ext
    funext K
    let X := (DerivedCategory.Q (C := integralTowerModules l E Y)).objPreimage K.obj
    let eX := (DerivedCategory.Q (C := integralTowerModules l E Y)).objObjPreimageIso K.obj
    obtain ⟨V, f, hV, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := completedIntegralCommRingSheafUnrestricted l E Y) X
    have hgood : integralOperationsGoodComplex l E Y V := by
      refine ⟨hV, fun i ↦ ?_⟩
      exact (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso
          (completedIntegralCommRingSheafUnrestricted l E Y) (V.X i)).symm (hf i)
    let P : (integralOperationsGoodComplex l E Y).FullSubcategory := ⟨V, hgood⟩
    let : QuasiIso f := hq
    let eP : DerivedCategory.Q.obj P.obj ≅ K.obj :=
      asIso (DerivedCategory.Q.map f) ≪≫ eX
    have hP := (boundedConstructibleDerivedCompleteIntegral D l hl E Y).prop_of_iso
      eP.symm K.property
    let K₀ : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y :=
      ⟨DerivedCategory.Q.obj P.obj, hP⟩
    let e₀ : K₀ ≅ K :=
      (boundedConstructibleDerivedCompleteIntegral D l hl E Y).isoMk eP
    apply (cancel_epi
      ((integralConstructibleScalarExtension D l hl E L ι Y).map e₀.hom)).mp
    rw [c.hom.naturality, e.hom.naturality]
    congr 1
    apply ObjectProperty.hom_ext
    apply (cancel_mono ((integralScalarExtensionComparison l E L ι Y).hom.app P)).mp
    exact (hc P hP).trans (hχ.1 P).symm

/-- The finite-free comparison with the canonical quotient completion normalization.
Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: lem-weil-integral-scalar-extension-constructible). -/
noncomputable def integralConstructibleScalarComparison :=
  (integralConstructibleScalarComparison_existsUnique D l hl E L ι Y).exists.choose

end WeilConjectures

namespace AlgebraicGeometry.ProEtale

/-- Constant integral sections of the condensed coefficient ring.
Source: `det-def-sfb-pulled-back-coefficients`; the constants in the continuous-function
presentation. This is the same construction as the point-fibre constant map, placed
here without importing point-fibre theorems.
(blueprint: lem-route-integral-ordinary-derived-scalar-constructible) -/
noncomputable def integralScalarConstants
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    PadicAlgCl.integers ℓ E.1 →+* Γ (Profinite.padicIntegersRingObj.{u} ℓ E.1) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  Profinite.continuousMapConstRingHom (PadicAlgCl.integers ℓ E.1)

/-- The restricted functor is linear for `O_E`. The source action is induced by the
constant-section map `O_E → Γ(R)`. The target action is induced by the composite
`O_E → O_L → Γ(S)`, so it is exactly the coefficient action required by the
statement.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-qlbar-two-colimit/
det-def-sf-operations.md, clause (i), direct derived tensor restricted to the preserved full
subcategories (blueprint: lem-weil-integral-scalar-extension-constructible).

Proof (node step 3): the coefficient point map sends the constant section `r` to the constant
section of its image in `O_L` (sectionwise postcomposition on continuous functions), and
naturality of global sections under `upperStarFromPoint Y` gives `Γ(a_Y) ∘ φE = φF`. Hence
restriction `Mod.comap a_Y` is `O_E`-linear (`Mod.linear_comap`), so is its left adjoint
`Mod.extendScalars a_Y` (`sk-def-sfb-change-of-scalars`); the exact functor induces an
`O_E`-linear functor on derived categories, transported to `T` by
`leftDerivedFunctorIsoMapDerivedCategory` (`det-def-sfb-derived-extension-of-scalars`). The
full-subcategory maps on Hom groups are the ambient ones, so `T(c f) = c T(f)` there.
-/
theorem integralScalarExtensionFunctor_linear
    (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (Y : Scheme.{u}) :
    let φE := (MonObj.Γ.mapFunctor (upperStarFromPoint Y)).comp
      (integralScalarConstants ℓ E)
    let φF := (MonObj.Γ.mapFunctor (upperStarFromPoint Y)).comp
      ((integralScalarConstants ℓ F).comp
        (finiteCoefficientIntegersMap ℓ h))
    letI := CategoryTheory.Mod.linearOfRingHom φE
    letI := CategoryTheory.Mod.linearOfRingHom φF
    (integralScalarExtensionFunctor ℓ h Y).Linear (PadicAlgCl.integers ℓ E.1) := by
  dsimp only
  let φE := (MonObj.Γ.mapFunctor (upperStarFromPoint Y)).comp
    (integralScalarConstants ℓ E)
  let φF := (MonObj.Γ.mapFunctor (upperStarFromPoint Y)).comp
    ((integralScalarConstants ℓ F).comp
      (finiteCoefficientIntegersMap ℓ h))
  let := Mod.linearOfRingHom φE
  let := Mod.linearOfRingHom φF
  let a := coefficientMap (finiteCoefficientIntegersPointMap ℓ h) Y
  have hc (r : PadicAlgCl.integers ℓ E.1) : Γ.map a (φE r) = φF r := by
    have hp : Γ.map (finiteCoefficientIntegersPointMap ℓ h)
        (integralScalarConstants ℓ E r) =
        integralScalarConstants ℓ F (finiteCoefficientIntegersMap ℓ h r) := by
      exact Sheaf.Γ_map_ringHomΓSheafCompose _
        (Profinite.continuousMapRingSheafMap (finiteCoefficientIntegersMap ℓ h)
          ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ |>.subtype_mk _))
        (Profinite.continuousMapConstSectionRingHom _) (fun _ _ ↦ rfl)
        (Profinite.continuousMapConstSectionRingHom _) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    change Γ.map ((upperStarFromPoint Y).map (finiteCoefficientIntegersPointMap ℓ h))
        (Γ.mapFunctor (upperStarFromPoint Y)
          (integralScalarConstants ℓ E r)) = _
    have hn (s : Γ (Profinite.padicIntegersRingObj.{u} ℓ E.1)) :
        Γ.map ((upperStarFromPoint Y).map (finiteCoefficientIntegersPointMap ℓ h))
            (Γ.mapFunctor (upperStarFromPoint Y) s) =
          Γ.mapFunctor (upperStarFromPoint Y)
            (Γ.map (finiteCoefficientIntegersPointMap ℓ h) s) := by
      ext1
      rw [Γ.map_hom, Γ.mapFunctor_hom, Γ.mapFunctor_hom, Γ.map_hom,
        Category.assoc, Functor.map_comp]
    rw [hn, hp]
    rfl
  have : (Mod.comap a).Linear (PadicAlgCl.integers ℓ E.1) :=
    Mod.linear_comap a φE φF hc
  have : (Mod.extendScalars a).Linear (PadicAlgCl.integers ℓ E.1) :=
    (Mod.extendRestrictAdjunction a).left_adjoint_linear
  have : PreservesFiniteLimits (Mod.extendScalars a) :=
    ((cartesianCoefficients_finiteFree ℓ h).2.2 Y).1
  have : (Mod.extendScalars a).mapDerivedCategory.Linear (PadicAlgCl.integers ℓ E.1) :=
    inferInstance
  have : (integralScalarExtension ℓ h Y).Linear (PadicAlgCl.integers ℓ E.1) :=
    Functor.linear_of_iso _ (Mod.extendScalars a).leftDerivedFunctorIsoMapDerivedCategory.symm
  constructor
  intro K L f r
  apply ObjectProperty.hom_ext
  exact (integralScalarExtension ℓ h Y).map_smul r f.hom

/-- Ordinary exact scalar extension preserves bounded constructibility for condensed
integral coefficients. Source: `lem-coef-integral-finite-extension`, first paragraph.
Proof: direct derived tensor preserves bounded constructibility by finite freeness and
preservation of finite presentations. Transport that result through the canonical
comparison with the exact functor on complexes. This includes zero complexes, empty
schemes, the identity extension, and ramified finite extensions.
(blueprint: lem-route-integral-ordinary-derived-scalar-constructible) -/
theorem integralOrdinaryDerivedScalar_constructible
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y)))
    (hK : boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y) K) :
    boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ F.1) Y)
      ((integralOrdinaryDerivedScalar ℓ h Y).obj K) := by
  exact (boundedConstructible _).prop_of_iso
    ((integralScalarExactDerivedComparison ℓ h Y).app K)
    (integralScalarExtension_constructible ℓ h Y K hK)

/-- Restriction of ordinary exact tensor to the bounded constructible categories.
Source: `lem-coef-integral-finite-extension`, preservation clause.
(blueprint: lem-route-integral-ordinary-derived-scalar-constructible) -/
noncomputable def integralConstructibleScalarExtension :
    (boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y)).FullSubcategory ⥤
    (boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ F.1) Y)).FullSubcategory :=
  ObjectProperty.lift _
    ((boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y)).ι ⋙
        integralOrdinaryDerivedScalar ℓ h Y)
    (fun K ↦ integralOrdinaryDerivedScalar_constructible ℓ h Y K.obj K.property)

/-- The comparison restricted to bounded constructible objects. Its underlying components
are those of the canonical exact-derived comparison.
Source: `lem-coef-integral-finite-extension`, first proof paragraph.
Proof: fullness lifts both components; their inverse and naturality identities are the
ambient identities.
(blueprint: lem-route-integral-constructible-scalar-comparison-exists-unique) -/
noncomputable def integralConstructibleScalarComparison :
    integralScalarExtensionFunctor ℓ h Y ≅ integralConstructibleScalarExtension ℓ h Y :=
  NatIso.ofComponents
    (fun K ↦
      { hom := ObjectProperty.homMk ((integralScalarExactDerivedComparison ℓ h Y).hom.app K.obj)
        inv := ObjectProperty.homMk ((integralScalarExactDerivedComparison ℓ h Y).inv.app K.obj)
        hom_inv_id := by
          apply ObjectProperty.hom_ext
          exact (integralScalarExactDerivedComparison ℓ h Y).hom_inv_id_app K.obj
        inv_hom_id := by
          apply ObjectProperty.hom_ext
          exact (integralScalarExactDerivedComparison ℓ h Y).inv_hom_id_app K.obj })
    (by
      intro K M f
      apply ObjectProperty.hom_ext
      exact (integralScalarExactDerivedComparison ℓ h Y).hom.naturality f.hom)

private theorem natTrans_ext_of_representatives
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (S : C → Prop) (α β : F ⟶ G)
    (hS : ∀ X, ∃ Y, S Y ∧ Nonempty (Y ≅ X))
    (h : ∀ Y, S Y → α.app Y = β.app Y) : α = β := by
  apply NatTrans.ext
  funext X
  obtain ⟨Y, hY, ⟨e⟩⟩ := hS X
  apply (cancel_epi (F.map e.hom)).mp
  rw [α.naturality, β.naturality, h Y hY]

/-- The comparison is uniquely fixed by the total-derived counit on representatives.
Source: `lem-coef-integral-finite-extension`, first proof paragraph.
Proof: the canonical exact-derived comparison satisfies its defining counit equation.
The exact model's representative comparison is invertible, so the equation determines
our comparison on representatives. Every constructible object has such a representative;
transport along its isomorphism and use naturality to obtain uniqueness everywhere.
(blueprint: lem-route-integral-constructible-scalar-comparison-exists-unique) -/
theorem integralConstructibleScalarComparison_existsUnique :
    letI : PreservesFiniteLimits
        (Mod.extendScalars (integralConstructibleCoefficientMap ℓ h Y)) :=
      ((cartesianCoefficients_finiteFree ℓ h).2.2 Y).1
    ∃! c : integralScalarExtensionFunctor ℓ h Y ≅ integralConstructibleScalarExtension ℓ h Y,
      ∀ (P : HomotopyCategory
          (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
            (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y)) (.up ℤ))
        (hP : boundedConstructible
          (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y)
          (DerivedCategory.Qh.obj P)),
        (c.hom.app ⟨DerivedCategory.Qh.obj P, hP⟩).hom ≫
            (Mod.extendScalars
              (integralConstructibleCoefficientMap ℓ h Y)).mapDerivedCategoryFactorsh.hom.app P =
          (Mod.extendScalars
            (integralConstructibleCoefficientMap ℓ h Y)).leftDerivedFunctorCounit.app P := by
  let : PreservesFiniteLimits
      (Mod.extendScalars (integralConstructibleCoefficientMap ℓ h Y)) :=
    ((cartesianCoefficients_finiteFree ℓ h).2.2 Y).1
  let T := Mod.extendScalars (integralConstructibleCoefficientMap ℓ h Y)
  have he P hP :
      ((integralConstructibleScalarComparison ℓ h Y).hom.app
          ⟨DerivedCategory.Qh.obj P, hP⟩).hom ≫
            T.mapDerivedCategoryFactorsh.hom.app P = T.leftDerivedFunctorCounit.app P := by
    exact NatTrans.congr_app T.leftDerivedFunctorIsoMapDerivedCategory_hom_fac P
  refine ⟨integralConstructibleScalarComparison ℓ h Y, he, ?_⟩
  intro c hc
  apply Iso.ext
  let S := fun K ↦ ∃ P hP, K =
    (⟨DerivedCategory.Qh.obj P, hP⟩ :
      (boundedConstructible
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y)).FullSubcategory)
  apply natTrans_ext_of_representatives S c.hom
    (integralConstructibleScalarComparison ℓ h Y).hom
  · intro K
    let P := (DerivedCategory.Qh (C :=
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y))).objPreimage K.obj
    let eP : DerivedCategory.Qh.obj P ≅ K.obj := DerivedCategory.Qh.objObjPreimageIso K.obj
    have hP := (boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y)).prop_of_iso
        eP.symm K.property
    refine ⟨⟨DerivedCategory.Qh.obj P, hP⟩, ⟨P, hP, rfl⟩, ?_⟩
    exact ⟨(boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y)).isoMk eP⟩
  · rintro K ⟨P, hP, rfl⟩
    apply ObjectProperty.hom_ext
    apply (cancel_mono (T.mapDerivedCategoryFactorsh.app P).hom).mp
    exact (hc P hP).trans (he P hP).symm

end AlgebraicGeometry.ProEtale
