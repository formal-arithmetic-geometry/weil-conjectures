/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PrincipalTorsorComparisons.PrincipalTorsorSignTypes
import WeilConjectures.AlgebraicGeometry.Principal.PrincipalTorsorNormalizedComparison
import WeilConjectures.AlgebraicGeometry.Principal.PrincipalTorsorConnectingComparison
import WeilConjectures.AlgebraicGeometry.Principal.PrincipalTorsorFramedComparison
import WeilConjectures.AlgebraicGeometry.Principal.PrincipalTorsorNormalizedNatural
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.CategoryTheory.Sites.RelativeTorsorExtension
public import WeilConjectures.CategoryTheory.Sites.TorsorExtensionPresentation
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.CategoryTheory.Abelian.Exact
public import WeilConjectures.CategoryTheory.Sites.EtaleTorsorExtensionPresentationExists
public import WeilConjectures.CategoryTheory.Sites.ExtensionPresentationShortExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeEtaleCohomology
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.DivisorTorsorBoundarySigns
public import WeilConjectures.AlgebraicGeometry.RelativeCone.PurityRelativeCone
public import WeilConjectures.Algebra.Homology.SmoothPurity.ClosedSupportHom
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSupportedSections
public import WeilConjectures.SixFunctors.OpenClosed.Exact

/-! The signed torsor formula from normalized comparisons and Yoneda compatibility. -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite HomologicalComplex
namespace AlgebraicGeometry.Etale
private lemma principal_section_rep_unique
    (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) (q : ℕ)
    (b : (I.X q).obj.obj (op U)) (x y : (relativeSections U I).homology q)
    (hx : TorsorSectionRepresents U I q b x)
    (hy : TorsorSectionRepresents U I q b y) : x = y := by
  obtain ⟨z, hz, rfl⟩ := hx
  obtain ⟨z', hz', rfl⟩ := hy
  congr 1
  apply (AddCommGrpCat.mono_iff_injective ((relativeSections U I).iCycles q)).1
    inferInstance
  apply (ConcreteCategory.bijective_of_isIso
    ((((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).obj I).extendXIso
      ComplexShape.embeddingUpNat rfl).hom).1
  exact hz.trans hz'.symm

private theorem principal_torsor_yoneda_sign_formula
    (C : PrincipalTorsorComparisons.{u}) (hC : C.Normalized) : C.Formula := by
  classical
  intro T Z i hi W h G P e s g hs E a b hab hE F hF hbF hFs
  obtain ⟨hpush, hframe⟩ := principalTorsorFramedComparison C hC T Z i W h G P e s g hs
    E a b hab hE F hF hbF hFs
  constructor
  · exact hpush
  · intro H K aK bK habK hK I J L α β hαβ hα hβ hsplit
    let U := Scheme.Etale.mk W.ι
    obtain ⟨e', he', hsign⟩ := divisor_torsor_boundary_signs.{u}
    obtain ⟨x₀, hx₀, hy₀, _⟩ := hsign.trivial T W G L g
    have hbclass := hframe L _ hy₀
    obtain ⟨hOpen, hop⟩ := hsign.coefficients T W (ShortComplex.mk aK bK habK) hK I J L
      α β hαβ hα hβ hsplit
    obtain ⟨x₁, hx₁, hδ, _⟩ := hop g
    refine ⟨hOpen, ?_⟩
    intro x hx
    have hxx := principal_section_rep_unique T U L.cocomplex 0
      ((L.ι.f 0).hom.app (op U) g) x x₁ hx hx₁
    rw [hxx]
    have hcomp := principalTorsorConnectingComparison C hC T Z i W h
      (ShortComplex.mk aK bK habK) hK I J L α β hαβ hα hβ hsplit hE.extClass
    rw [hbclass, map_neg, hδ] at hcomp
    rw [hcomp, map_neg]

/-- A globally framed relative torsor is the inverse-section localization pushout;
its coefficient Yoneda splice is minus the supported localization boundary.
All identifications are supplied with their cocycle normalization and naturality.
Source: Stacks Tags 03AJ and 06XU; blueprint lemma-cycle-class-cartier-divisor, clause (a)
(blueprint: lem-pur-principal-torsor-yoneda-sign).

Proof:
1. The open-closed short exact sequence and extension-by-zero adjunction identify
   Hom(j_! Z_W,A) with A(W), taking the inclusion to one. Push it out along -g.
   The published pushout-short-exact-sequence theorem gives its Ext class.
2. In the quotient (G plus Z_T)/im(-g,-t), put F(a+e)=[a,1]. The relation
   [-g,-1]=0 gives F(s)=[g,1]=0. Uniqueness of relative_extension_existsUnique
   identifies this extension with the specified extension, not only its H1 image.
3. Extend G into an injective resolution over E by h. Write dh=c b. The cone
   boundary convention represents the extension by -c, by the homotopy -h.
4. With u=hF(e), one has res(u)=-g and du=c p(1). Thus (-du,0)+D(u)=(0,-g).
   This is the positive localization boundary of g in the stipulated signed model.
5. Degreewise split horseshoe resolutions give short exact section complexes.
   The normalized supported-Hom maps commute strictly with these sequences;
   naturality of homology boundaries and extMk_resolution_connecting_eq_triangle
   identify the coefficient connecting map with the Yoneda splice k[1] after beta.
6. If r lifts g, the lift (0,-r) has differential (0,dr), the negative of the
   localization representative (0,-dr). Kernel-to-cone realization gives the formula
   in right-derived kernel-of-restriction cohomology.
7. The equations on cocycles commute with coefficient lifts and etale section
   transfers; the relative pushout is preserved by uniqueness. For G_m, negation
   in the abelian sheaf is multiplication inverse, so -g means g inverse. -/
theorem principal_torsor_yoneda_sign :
    ∃ C : PrincipalTorsorComparisons.{u}, C.Normalized ∧ C.Natural ∧ C.Formula := by
  obtain ⟨C, hC⟩ := principalTorsorNormalizedComparison.{u}
  exact ⟨C, hC, principalTorsorNormalizedNatural C hC,
    principal_torsor_yoneda_sign_formula C hC⟩

end AlgebraicGeometry.Etale
