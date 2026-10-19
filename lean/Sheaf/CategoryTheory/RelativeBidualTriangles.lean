/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RingedSiteDualityMaps
public import Sheaf.Algebra.Homology.SignedDoubleHomCone
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Algebra.Homology.HomComplex
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.HomComplexGlobalHomotopy
import Sheaf.Algebra.Homology.HomTensorTotal
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import Sheaf.Algebra.Homology.HomComplexGlobalHomotopyOfUniverses

/-! # Relative evaluation biduality and distinguished triangles

Source: Stacks Project, sites-cohomology.tex, Tags 08JC and 0A97, with the signed
cone and evaluation calculations in the DAG proof
(blueprint: lem-per-relative-bidual-triangles).

The target of internal Hom is an arbitrary derived object. The closed structure
is the existing normalized ringed-site structure, and the evaluation transpose is
its existing canonical map, with no assumption of reflexivity or constructibility.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory.RelativeBidualTriangles

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (O : Sheaf J CommRingCat.{max c v r})

/-- The existing module category, with the site small in the module universe.
Source: Stacks 08J7 (blueprint: lem-per-relative-bidual-triangles). -/
abbrev Modules := ringedSiteModules.{max c v r}
  ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O)

/-- The existing category of unbounded cochain complexes.
Source: Stacks 0A8X (blueprint: lem-per-relative-bidual-triangles). -/
abbrev Complex := CochainComplex (Modules.{c, v, r} J O) ℤ

/-- The existing unbounded derived category, in the chosen morphism universe.
Source: Stacks 08J7 (blueprint: lem-per-relative-bidual-triangles). -/
abbrev D [HasDerivedCategory.{w} (Modules.{c, v, r} J O)] :=
  DerivedCategory (Modules.{c, v, r} J O)

variable [HasDerivedCategory.{w} (Modules.{c, v, r} J O)]

/-- Internal Hom into the arbitrary fixed derived target K.
Source: Stacks 08JC (blueprint: lem-per-relative-bidual-triangles). -/
def dual (K : D.{c, v, r, w} J O) : (D.{c, v, r, w} J O)ᵒᵖ ⥤ D.{c, v, r, w} J O :=
  Prod.sectL _ K ⋙ derivedInternalHomOfUniverses.{c, v, r, w} J O

/-- The covariant relative double dual, on the same objects and morphisms.
Source: Stacks 0A97 (blueprint: lem-per-relative-bidual-triangles). -/
def bidual (K : D.{c, v, r, w} J O) : D.{c, v, r, w} J O ⥤ D.{c, v, r, w} J O :=
  (dual.{c, v, r, w} J O K).rightOp ⋙ dual.{c, v, r, w} J O K

/-- The existing transpose of evaluation after the normalized Koszul symmetry.
Source: Stacks 0A97 (blueprint: lem-per-relative-bidual-triangles). -/
def bidualMap (K : D.{c, v, r, w} J O) (M : RingedSiteDualityModel.{c, v, r, w} J O) :
    𝟭 _ ⟶ bidual.{c, v, r, w} J O K where
  app P := ringedSiteBidual M.closed M.symmetric K P
  naturality _ _ f := ringedSiteBidual_naturality M.closed M.symmetric K f

/-- The fixed functorial K-injective resolution of a target representative.
Source: Stacks 079P (blueprint: lem-per-relative-bidual-triangles). -/
abbrev targetResolution (B : Complex.{c, v, r} J O) : Complex.{c, v, r} J O :=
  (WeilConjectures.coefficientHomResolution.{r, c, v} J O).obj B

/-- The actual factorization comparison from double Hom into the same resolution.
The last map transports both occurrences of the target along eK. No K-injectivity
of the first Hom complex is needed: both Hom targets are the fixed resolution.
Source: Stacks 0A95 (blueprint: lem-per-relative-bidual-triangles). -/
def modelMap (K : D.{c, v, r, w} J O) (B : Complex.{c, v, r} J O)
    (eK : DerivedCategory.Q.obj B ≅ K) (E : Complex.{c, v, r} J O) :
    DerivedCategory.Q.obj
      ((SignedDoubleHomCone.doubleDual.{c, v, r, max c v r} (R := O)
        (targetResolution.{c, v, r} J O B)).obj E) ⟶
      (bidual.{c, v, r, w} J O K).obj (DerivedCategory.Q.obj E) :=
  (WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J O
    (homComplex.{c, v, max c v r, max c v r} (R := O) E
      (targetResolution.{c, v, r} J O B)) B).inv ≫
  (derivedInternalHomOfUniverses.{c, v, r, w} J O).map
    (Prod.mkHom (WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J O E B).hom.op
      (𝟙 _)) ≫
  (derivedInternalHomOfUniverses.{c, v, r, w} J O).map
    (Prod.mkHom ((derivedInternalHomOfUniverses.{c, v, r, w} J O).map
      (Prod.mkHom (𝟙 _) eK.inv)).op eK.hom)

/-- The ordinary Hom shift fixed by the product formula (-1)^(m*q).
The comparison theorem determines this map componentwise, so this is a choice
of the uniquely specified signed comparison, not of an unspecified isomorphism.
Source: Stacks 08JC (blueprint: lem-per-relative-bidual-triangles). -/
def signedHomShift (B E : Complex.{c, v, r} J O) (m : ℤ) :=
  (SignedDoubleHomCone.comparison.{c, v, r, max c v r} (R := O)
    (targetResolution.{c, v, r} J O B)).choose E m

/-- The signed double-Hom shift, retaining the leading minus in the cone calculation:
chi = -s_(T(E),-1) composed with T(s_(E,1)) inverse.
Source: Stacks 08JC (blueprint: lem-per-relative-bidual-triangles). -/
def signedModelShift (B E : Complex.{c, v, r} J O) :=
  -((SignedDoubleHomCone.dual.{c, v, r, max c v r} (R := O)
      (targetResolution.{c, v, r} J O B)).mapIso
      (signedHomShift.{c, v, r} J O B E 1).symm.op ≪≫
    signedHomShift.{c, v, r} J O B
      (homComplex.{c, v, max c v r, max c v r} (R := O) E
        (targetResolution.{c, v, r} J O B)) (-1))

/-- The full locus where the specified relative evaluation map is invertible.
Source: Stacks 08JC and 0A97 (blueprint: lem-per-relative-bidual-triangles). -/
def reflexive (K : D.{c, v, r, w} J O) (M : RingedSiteDualityModel.{c, v, r, w} J O) :
    ObjectProperty (D.{c, v, r, w} J O) :=
  fun E ↦ IsIso ((bidualMap.{c, v, r, w} J O K M).app E)

/-- Relative evaluation respects the signed shifts and all distinguished triangles.
Source: Stacks 08JC and 0A97, with the signed double-Hom cone calculation
(blueprint: lem-per-relative-bidual-triangles).

Proof (the node's nine steps):
1. Resolve any representative B of K by a K-injective I. Hom(-,I) inverts
   quasi-isomorphisms by lem-pur-rhom-well-defined; applying it twice gives the
   double dual. First-variable exactness (08JC) makes dual contravariantly exact.
2. On homogeneous x of degree p and f of degree q put b(x)(f)=(-1)^(p*q)f(x).
   Expanding the Hom differential gives d(b(x))(f)=(-1)^((p+1)*q)f(dx).
   Thus b is a chain map, natural in the source, and descends to the localization.
3. Compute tensor-Hom transposition using K-flat flat-term sources and a
   K-injective target. Hom from a K-flat to I is K-injective. Hom into these
   representatives computes derived maps; global Hom H^0 is homotopy classes.
   Currying g(x tensor y)=g(x)(y) has no extra sign and commutes with differentials.
4. Resolve Hom(P,I) by a K-flat L with r:L -> Hom(P,I). Evaluation after Koszul
   symmetry is x tensor ell -> (-1)^(p*q)r(ell)(x). Its curry is T(r)b_P.
   T(r) is a quasi-isomorphism, so the existing evaluation transpose is Q(b_P),
   and naturality extends this identification to every representative E.
5. Apply lem-sf-double-hom-cone-comparison: chi=-s_(T(E),-1)T(s_(E,1)) inverse.
   Its cone comparison respects inclusion and the actual connecting map -pi.
   Localize these comparisons. Every distinguished triangle is a localized cone
   triangle up to isomorphism, hence the normalized bidual functor is exact.
6. On degree-p g and degree-t y the chi formula multiplies by (-1)^(p+t).
   On b(x), the exponent is p+t+p*(t+1), equal modulo two to (p+1)*t.
   Consequently chi b_(E[1])=b_E[1], and the derived evaluation commutes with shift.
7. Iterate for positive shifts, invert for negative shifts, and use the identity
   for zero. These signed comparisons satisfy integer-addition coherence.
8. Apply lem-weil-pbc-commshift-nattrans-triangle-morphism. Naturality gives the
   first two squares; on w the last square is F(w) eta followed by psi equal to
   w followed by shifted eta. This uses the precise shift equality from step 6.
9. Apply lem-sf-triangle-two-out-of-three. The isomorphism locus is closed under
   triangles, all shifts and isomorphisms. At zero both Hom complexes vanish;
   additivity gives finite biproduct closure. Thus the full locus is triangulated.
   Throughout K was arbitrary; no constructibility or universal reflexivity is used. -/
theorem compatibility (K : D.{c, v, r, w} J O)
    (M : RingedSiteDualityModel.{c, v, r, w} J O) :
    (∃ _ : (dual.{c, v, r, w} J O K).CommShift ℤ,
      (dual.{c, v, r, w} J O K).IsTriangulated) ∧
    ∃ cs : (bidual.{c, v, r, w} J O K).CommShift ℤ,
      (fun [comm : (bidual.{c, v, r, w} J O K).CommShift ℤ] ↦
        (bidual.{c, v, r, w} J O K).IsTriangulated ∧
        NatTrans.CommShift (bidualMap.{c, v, r, w} J O K M) ℤ ∧
        (∀ (B : Complex.{c, v, r} J O) (eK : DerivedCategory.Q.obj B ≅ K)
          (E : Complex.{c, v, r} J O),
          DerivedCategory.Q.map (signedModelShift.{c, v, r} J O B E).hom ≫
              ((DerivedCategory.Q).commShiftIso (1 : ℤ)).hom.app _ ≫
              (modelMap.{c, v, r, w} J O K B eK E)⟦(1 : ℤ)⟧' =
            modelMap.{c, v, r, w} J O K B eK (E⟦(1 : ℤ)⟧) ≫
              (bidual.{c, v, r, w} J O K).map
                (((DerivedCategory.Q).commShiftIso (1 : ℤ)).hom.app E) ≫
              ((bidual.{c, v, r, w} J O K).commShiftIso (1 : ℤ)).hom.app
                (DerivedCategory.Q.obj E)) ∧
        (∀ T : Triangle (D.{c, v, r, w} J O), T ∈ distTriang _ →
          ∃ f : T ⟶ (bidual.{c, v, r, w} J O K).mapTriangle.obj T,
            f.hom₁ = (bidualMap.{c, v, r, w} J O K M).app T.obj₁ ∧
            f.hom₂ = (bidualMap.{c, v, r, w} J O K M).app T.obj₂ ∧
            f.hom₃ = (bidualMap.{c, v, r, w} J O K M).app T.obj₃) ∧
        (reflexive.{c, v, r, w} J O K M).IsTriangulated ∧
        (reflexive.{c, v, r, w} J O K M).IsClosedUnderIsomorphisms) (comm := cs) := by
  sorry

end CategoryTheory.RelativeBidualTriangles
