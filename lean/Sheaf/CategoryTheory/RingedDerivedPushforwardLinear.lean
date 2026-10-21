/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.Sites.RGammaDerivedLimit
public import Sheaf.CategoryTheory.KInjectiveDerivedMapComputation
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective

/-! # Central scalar linearity of the unbounded ringed-topos direct image

Source: Stacks Project, Derived Categories, Tags 070K and 070Y; Modules on Sites,
Tag 03D6; Differential Graded Algebra, Tags 09MJ and 09MK
(blueprint: lem-pur-ringed-derived-pushforward-linear).

Global sections are compatible families, using Mathlib's `RingCat.sectionsSubring`.
Scalar compatibility is tested on generalized elements, as in `RingedToposMorphism`;
no functor between the presenting sites or exactness of module direct image is imposed.
The existential linear structures are characterized on every section of every Hom.
The derived functor is the existing universal K-injective construction, whose unit and
resolution comparisons are those of `rightDerivedFunctorOfQuasiIsoResolutions`.
-/

@[expose] public section

set_option autoImplicit false

universe u v wA wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Compatible locally central sections give the prescribed scalar structures, and the
canonical unbounded right derived module direct image is additive and linear for their
induced derived structures. In particular its value on scalar multiplication is scalar
multiplication by the actual target section, as stated by the final identity.

Source: Stacks Tags 070K and 070Y, with the module action of Tag 03D6 and the definitions
of Tags 09MJ and 09MK (blueprint: lem-pur-ringed-derived-pushforward-linear).

Proof plan:
1. On each module Hom set set (r f)_U(x) = s(r)_U f_U(x). Local centrality makes this
   sectionwise module-linear; compatibility of the global section with restrictions makes
   it natural. The ring-map and module axioms give the module and bilinear-composition
   axioms, hence the two claimed `Linear` structures.
2. Transpose generalized elements using the adjunction of `u`. Its `module_linear`
   identity and scalar compatibility identify s_A(r)x with s_B(r) times the transpose.
   Naturality then gives u_*(r f) = r u_*(f). Additivity is part of the module direct image.
3. `lem-weil-pbc-ring-sheaves-grothendieck` and
   `lem-pur-kinjective-degreewise-existence` supply the K-injective resolution hypothesis.
   Additivity preserves homotopies, shifts and cone triangles, so
   `lem-weil-pbc-kinjective-total-derived` supplies the existing universal derived pair.
4. For resolutions a:N→I and b:N'→J use
   `lem-sf-kinjective-derived-map-computation`: a derived morphism h is represented by
   the unique homotopy class g with Qg = Qb h (Qa)⁻¹, and its derived image, conjugated
   by the specified comparison isomorphisms c_a,c_b, is Q(u_*g).
5. The linearity of Q from `lem-weil-linear-abelian-derived-category` shows that rg
   represents rh and g+t represents h+k. Step 2 gives Q(u_*(rg)) = r Q(u_*g), and
   additivity gives Q(u_*(g+t)) = Q(u_*g)+Q(u_*t). Cancel the fixed comparison
   isomorphisms, using bilinearity, to get both equalities on all derived morphisms.
   Transport along presentation isomorphisms covers every derived object.
6. For h = id the scalar map is multiplication by the actual section s_B(r) on a
   representative. Linearity and preservation of identity identify its image with
   multiplication by s_A(r) on the direct-image representative. -/
theorem ringedDerivedPushforward_linear
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J RingCat.{u}) (B : Sheaf K RingCat.{u})
    [HasDerivedCategory.{wA} (ringedSiteModules.{u} A)]
    [HasDerivedCategory.{wB} (ringedSiteModules.{u} B)]
    (u : RingedToposMorphism B A) (R : Type v) [CommRing R]
    (sA : R →+* RingCat.sectionsSubring A.obj)
    (sB : R →+* RingCat.sectionsSubring B.obj)
    (centralA : ∀ (r : R) (U : Cᵒᵖ) (a : A.obj.obj U),
      (sA r).val U * a = a * (sA r).val U)
    (centralB : ∀ (r : R) (V : Dᵒᵖ) (b : B.obj.obj V),
      (sB r).val V * b = b * (sB r).val V)
    (compatible : ∀ (r : R) (T : Sheaf J (Type u))
      (z : T ⟶ (sheafCompose J (forget RingCat)).obj A),
      (∀ (U : Cᵒᵖ) (t : T.obj.obj U), z.hom.app U t = (sA r).val U) →
      ∀ (V : Dᵒᵖ) (t : (u.inverse.obj T).obj.obj V),
        ((u.inverse.map z) ≫ u.ringMap).hom.app V t = (sB r).val V) :
    ∃ (LA : Linear R (ringedSiteModules.{u} A))
      (LB : Linear R (ringedSiteModules.{u} B))
      (enough : ∀ N : CochainComplex (ringedSiteModules.{u} B) ℤ,
        ∃ (I : CochainComplex (ringedSiteModules.{u} B) ℤ) (a : N ⟶ I),
          I.IsKInjective ∧ QuasiIso a),
      (fun [_iA : Linear R (ringedSiteModules.{u} A)]
        [_iB : Linear R (ringedSiteModules.{u} B)] ↦
        (∀ (M N : ringedSiteModules.{u} A) (f : M ⟶ N) (r : R)
          (U : Cᵒᵖ) (x : M.val.obj U),
          (r • f).val.app U x = (sA r).val U • f.val.app U x) ∧
        (∀ (M N : ringedSiteModules.{u} B) (f : M ⟶ N) (r : R)
          (V : Dᵒᵖ) (x : M.val.obj V),
          (r • f).val.app V x = (sB r).val V • f.val.app V x) ∧
        (u.modules.rightDerivedFunctorOfQuasiIsoResolutions enough).Additive ∧
        Functor.Linear R (u.modules.rightDerivedFunctorOfQuasiIsoResolutions enough) ∧
        (∀ (N : DerivedCategory (ringedSiteModules.{u} B)) (r : R),
          (u.modules.rightDerivedFunctorOfQuasiIsoResolutions enough).map (r • 𝟙 N) =
            r • 𝟙 ((u.modules.rightDerivedFunctorOfQuasiIsoResolutions enough).obj N)))
        (_iA := LA) (_iB := LB) := by
  sorry

end CategoryTheory
