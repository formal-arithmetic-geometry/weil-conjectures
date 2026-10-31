/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.DerivedInternalHomMixedUniverses
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Algebra.Homology.HomComplexComponents
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! # Lower bound for derived internal Hom on an etale site

Source: Stacks Project, sites-cohomology.tex, Sections 0A8X and 08J7;
Bhatt--Scholze, *The pro-etale topology for schemes*, Lemma 6.3.16, pp. 47--48
(blueprint: lem-weil-pbc-etale-internal-hom-lower-bound).
The Bhatt--Scholze proof supplies the continuity context; the general ring-sheaf
estimate is the elementary support calculation for the Stacks Hom complex.
-/

@[expose] public section
set_option autoImplicit false
attribute [instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
universe u r w
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry.Etale

private theorem homObj_zero_left (T : Scheme.{u})
    (R : Sheaf T.smallEtaleTopology CommRingCat.{r})
    (L M : SheafOfModules.{max (u + 1) r}
      ((sheafCompose T.smallEtaleTopology
        (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (hL : IsZero L) :
    IsZero (SheafOfModules.homObj (R := R) L M) := by
  rw [IsZero.iff_id_eq_zero,
    ← SheafOfModules.homObjMap_id (R := R) (M := L) (N := M),
    hL.eq_of_src (𝟙 L) 0]
  apply SheafOfModules.hom_ext
  ext U φ : 3
  change (PresheafOfModules.restrictOver R.obj U.unop).map 0 ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj U.unop).map (𝟙 M.val) = 0
  ext W x
  change ((φ.app W).hom) 0 = 0
  exact map_zero _

private theorem homObj_zero_right (T : Scheme.{u})
    (R : Sheaf T.smallEtaleTopology CommRingCat.{r})
    (L M : SheafOfModules.{max (u + 1) r}
      ((sheafCompose T.smallEtaleTopology
        (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (hM : IsZero M) :
    IsZero (SheafOfModules.homObj (R := R) L M) := by
  rw [IsZero.iff_id_eq_zero,
    ← SheafOfModules.homObjMap_id (R := R) (M := L) (N := M),
    hM.eq_of_tgt (𝟙 M) 0]
  apply SheafOfModules.hom_ext
  ext U φ : 3
  rfl

/-- For an arbitrary commutative ring sheaf on the small etale site, derived
internal Hom sends an object bounded above by `b` and an object bounded below
by `N` to an object bounded below by `N - b`.
Source: Stacks Project, sites-cohomology.tex, Sections 0A8X and 08J7;
Bhatt--Scholze, Lemma 6.3.16 proof, pp. 47--48
(blueprint: lem-weil-pbc-etale-internal-hom-lower-bound).

Proof:
1. Work in the module universe containing the small etale site. The category of
   modules over the given ring sheaf is Grothendieck abelian by
   prop-pur-kinjective-resolutions-exist, and has enough injectives by
   lem-sp-grothendieck-enough-injectives (Stacks 079H). Keep the ring sheaf `R`.
2. The standard t-structure (def-sbc-standard-tstructure-derived-category) gives
   a representative `L` of `K` with `L.X p = 0` for `b < p`.
   By lem-weil-pbc-dplus-injective-representative (Stacks 013K), represent `M`
   by a complex `I` of injectives vanishing below `N`. It is K-injective by
   lem-weil-pbc-acyclic-map-to-injective-nullhomotopy (Stacks 070J): every map
   from an acyclic complex to `I` is null-homotopic. The localization and
   cohomology are those of def-weil-abstract-derived-category, so the
   representing isomorphisms also hold in the ordinary unbounded category.
3. The representative comparison in def-pur-derived-internal-hom,
   `derivedInternalHomMixedUniverses_obj_iso` (Stacks 0A95), identifies derived
   internal Hom with `Q` of `homComplex L I` (def-pur-hom-complex). Its degree
   `n` term is the product over integers `p` of the sheaves Hom(L^p, I^(p+n)).
4. For `n < N - b`, either `b < p`, and the source is zero, or `p <= b`,
   whence `p + n <= b + n < N`, and the target is zero. Sheaf Hom from or to
   zero has only its zero section on every localized site
   (def-pur-sheaf-hom). Hence every factor and the sectionwise product are
   zero. The Hom complex therefore vanishes below `N - b`; its cohomology
   does too. Transport along the isomorphism of Step 3 and apply the standard
   t-structure's cohomological characterization. -/
theorem derivedInternalHom_etale_isGE_sub
    (T : Scheme.{u})
    (R : Sheaf T.smallEtaleTopology CommRingCat.{r})
    [HasDerivedCategory.{w} (SheafOfModules.{max (u + 1) r}
      ((sheafCompose T.smallEtaleTopology
        (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]
    (K M : DerivedCategory (SheafOfModules.{max (u + 1) r}
      ((sheafCompose T.smallEtaleTopology
        (forget₂ CommRingCat.{r} RingCat.{r})).obj R)))
    (b N : ℤ)
    (hK : K.IsLE b)
    (hM : M.IsGE N) :
    ((derivedInternalHomMixedUniverses.{u + 1, u, r, w}
      T.smallEtaleTopology R).obj (op K, M)).IsGE (N - b) := by
  let C := SheafOfModules.{max (u + 1) r}
    ((sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
  let : IsGrothendieckAbelian C :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsMixedUniverses
      T.smallEtaleTopology R).1
  let : K.IsLE b := hK
  let : M.IsGE N := hM
  obtain ⟨L, hL, ⟨eL⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE K b
  obtain ⟨P, hP, ⟨eP⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE M N
  obtain ⟨I, f, hf, hI, hIN⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective P N
  have : QuasiIso f := hf
  have : I.IsStrictlyGE N := hIN
  have : ∀ n, Injective (I.X n) := hI
  have : I.IsKInjective := CochainComplex.isKInjective_of_injective I N
  obtain ⟨e⟩ := derivedInternalHomMixedUniverses_obj_iso.{u + 1, u, r, w}
    T.smallEtaleTopology R K M L I eL.symm
      ((asIso (DerivedCategory.Q.map f)).symm ≪≫ eP.symm)
  have : (homComplex (R := R) L I).IsStrictlyGE (N - b) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    apply (homComplexIsLimit (R := R) L I n).isZero_pt
    apply Functor.isZero
    intro p
    by_cases hp : b < p.as
    · exact homObj_zero_left T R _ _ (L.isZero_of_isStrictlyLE b p.as hp)
    · exact homObj_zero_right T R _ _
        (I.isZero_of_isStrictlyGE N (p.as + n) (by omega))
  exact DerivedCategory.TStructure.t.isGE_of_iso e.symm (N - b)

end AlgebraicGeometry.Etale
