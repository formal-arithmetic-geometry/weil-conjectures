module

public import Sheaf.RingTheory.CotangentResolutionCoherence
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Category.Ring.Colimits
public import Sheaf.TraceFormula.OnePointDerivedRingIdentification
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction

/-! # The cotangent base-change adjunct on polynomial resolutions

Source: Stacks Project, cotangent.tex, Tags 08QL and 08QQ
(blueprint: lem-trf-cotangent-base-change-adjunct-formula).

Ring tensor products are pushouts, computed pointwise for simplicial rings.
The ordinary module tensor is Mathlib's scalar extension (with the symmetric
order of factors). The derived extension is any universal pair, retaining
its natural computation map, and the adjunction is normalized by its unit.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped ChangeOfRings

namespace Algebra.CotangentResolution

/-- Base change of an augmentation along the specified square, with target `C'`.
Source: Stacks, Tags 08QL and 08QQ
(blueprint: lem-trf-cotangent-base-change-adjunct-formula). -/
def squareTensorAugmentation {f g : Arrow CommRingCat.{u}} (q : f ⟶ g)
    (P : Augmentation f) : Augmentation g where
  algebra := pushout P.base ((SimplicialObject.const CommRingCat).map q.left)
  base := pushout.inr P.base ((SimplicialObject.const CommRingCat).map q.left)
  augmentation := pushout.desc
    (P.augmentation ≫ (SimplicialObject.const CommRingCat).map q.right)
    ((SimplicialObject.const CommRingCat).map g.hom) (by
      apply NatTrans.ext
      funext n
      obtain ⟨n⟩ := n
      obtain ⟨n⟩ := n
      change P.base.app (op ⦋n⦌) ≫ (P.augmentation.app (op ⦋n⦌) ≫ q.right) =
        q.left ≫ g.hom
      rw [← Category.assoc, P.triangle n, q.w])
  triangle := by
    intro n
    change ((pushout.inr P.base ((SimplicialObject.const CommRingCat).map q.left)) ≫
      pushout.desc _ _ _).app (op ⦋n⦌) = _
    rw [pushout.inr_desc]
    rfl

/-- The canonical inclusion `p ↦ p ⊗ 1` of augmented simplicial algebras.
Source: Stacks, Tag 08QL
(blueprint: lem-trf-cotangent-base-change-adjunct-formula). -/
def squareTensorInclusion {f g : Arrow CommRingCat.{u}} (q : f ⟶ g)
    (P : Augmentation f) : AugmentedMap q P (squareTensorAugmentation q P) where
  map := pushout.inl _ _
  base := by
    intro n
    exact congrArg (fun t ↦ t.app (op ⦋n⦌)) (pushout.condition (f := P.base)
      (g := (SimplicialObject.const CommRingCat).map q.left))
  augmentation := by
    intro n
    change ((pushout.inl P.base ((SimplicialObject.const CommRingCat).map q.left)) ≫
      (squareTensorAugmentation q P).augmentation).app (op ⦋n⦌) = _
    dsimp only [squareTensorAugmentation]
    rw [pushout.inl_desc]
    rfl

/-- The balanced map `h(p ⊗ a') = t(p)a'`, as the pushout descender.
Source: Stacks, Tags 08QL and 08QQ
(blueprint: lem-trf-cotangent-base-change-adjunct-formula). -/
def squareTensorToTarget {f g : Arrow CommRingCat.{u}} {q : f ⟶ g}
    {P : Augmentation f} {R : Augmentation g} (t : AugmentedMap q P R) :
    AugmentedMap (𝟙 g) (squareTensorAugmentation q P) R where
  map := pushout.desc t.map R.base (by
    apply NatTrans.ext
    funext n
    obtain ⟨n⟩ := n
    obtain ⟨n⟩ := n
    exact t.base n)
  base := by
    intro n
    change ((pushout.inr P.base ((SimplicialObject.const CommRingCat).map q.left)) ≫
      pushout.desc _ _ _).app (op ⦋n⦌) = _
    rw [pushout.inr_desc]
    exact (Category.id_comp _).symm
  augmentation := by
    have ht : P.base ≫ t.map =
        (SimplicialObject.const CommRingCat).map q.left ≫ R.base := by
      apply NatTrans.ext
      funext n
      obtain ⟨n⟩ := n
      obtain ⟨n⟩ := n
      exact t.base n
    have hh : (pushout.desc t.map R.base ht) ≫ R.augmentation =
        (squareTensorAugmentation q P).augmentation := by
      apply pushout.hom_ext
      · rw [← Category.assoc, pushout.inl_desc]
        change t.map ≫ R.augmentation =
          pushout.inl P.base ((SimplicialObject.const CommRingCat).map q.left) ≫
          pushout.desc _ _ _
        rw [pushout.inl_desc]
        apply NatTrans.ext
        funext n
        obtain ⟨n⟩ := n
        obtain ⟨n⟩ := n
        exact t.augmentation n
      · rw [← Category.assoc, pushout.inr_desc]
        change R.base ≫ R.augmentation =
          pushout.inr P.base ((SimplicialObject.const CommRingCat).map q.left) ≫
          pushout.desc _ _ _
        rw [pushout.inr_desc]
        apply NatTrans.ext
        funext n
        obtain ⟨n⟩ := n
        obtain ⟨n⟩ := n
        exact R.triangle n
    intro n
    change ((pushout.desc t.map R.base ht) ≫ R.augmentation).app (op ⦋n⦌) = _
    rw [hh]
    exact (Category.comp_id _).symm

variable [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]

/-- The differential complex after ordinary scalar extension, `K ⊗_C C'`.
Source: Stacks, Tags 08QL and 08QQ
(blueprint: lem-trf-cotangent-base-change-adjunct-formula). -/
def squareTensorComplex (C : Coherence.{u}) {f g : Arrow CommRingCat.{u}}
    (q : f ⟶ g) : CochainComplex (ModuleCat.{u} g.right) ℤ :=
  ((ModuleCat.extendScalars q.right.hom).mapHomologicalComplex (.up ℤ)).obj
    (differentialComplex (C.differentials (C.standard f)))

/-- The differential base-change map `theta`, obtained by the ordinary tensor
adjunction from the differential of `p ↦ p ⊗ 1`. Thus it sends
`(dp ⊗ c) ⊗ b'` to `d(p ⊗ 1) ⊗ f(c)b'`.
Source: Stacks, Tags 08QL and 08QQ
(blueprint: lem-trf-cotangent-base-change-adjunct-formula). -/
def squareTensorTheta (C : Coherence.{u}) {f g : Arrow CommRingCat.{u}} (q : f ⟶ g) :
    squareTensorComplex C q ⟶
      differentialComplex (C.differentials (squareTensorAugmentation q (C.standard f))) :=
  (((ModuleCat.extendRestrictScalarsAdj q.right.hom).mapHomologicalComplex (.up ℤ)).homEquiv
    _ _).symm (C.differentialMap (squareTensorInclusion q (C.standard f))).map

/-- The ordinary unit `u(x) = x ⊗ 1` on the standard differential complex.
Source: Stacks, Tag 07A6, and cotangent.tex Tag 08QQ
(blueprint: lem-trf-cotangent-base-change-adjunct-formula). -/
def squareTensorUnit (C : Coherence.{u}) {f g : Arrow CommRingCat.{u}} (q : f ⟶ g) :
    differentialComplex (C.differentials (C.standard f)) ⟶
      (restrictComplex q.right).obj (squareTensorComplex C q) :=
  ((ModuleCat.extendRestrictScalarsAdj q.right.hom).mapHomologicalComplex (.up ℤ)).unit.app _

/-- The differential map `K(h)`, cancelling restriction along the identity.
Source: Stacks, Tags 08QL and 08QQ
(blueprint: lem-trf-cotangent-base-change-adjunct-formula). -/
def squareTensorDifferentialMap (C : Coherence.{u})
    {f g : Arrow CommRingCat.{u}} (q : f ⟶ g) :
    differentialComplex (C.differentials (squareTensorAugmentation q (C.standard f))) ⟶
      differentialComplex (C.differentials (C.standard g)) :=
  (C.differentialMap (squareTensorToTarget (C.standardMap q))).map ≫
    (NatTrans.mapHomologicalComplex (ModuleCat.restrictScalarsId g.right).hom (.up ℤ)).app _

/-- The resolution-level formula for the normalized scalar-extension adjunct.
Source: Stacks, cotangent.tex Tags 08QL and 08QQ, with the coefficient adjunction
of sites-cohomology.tex Tag 07A6, transported through the singleton site.
(blueprint: lem-trf-cotangent-base-change-adjunct-formula).

The pair `(L, epsilon)` is the universal total left derived scalar extension,
so `epsilon` is its canonical computation map. The equation `normalized` specifies
exactly the representative normalization of the adjunction at the complex in use,
not a freely chosen adjunction or comparison. The existential isomorphism `cK`
is required to have this very computation map as its forward morphism.

Proof:
1. The pushout descender squareTensorToTarget is the balanced map
   h(p tensor a') = t(p)a'. Its two defining restrictions imply simplicial
   compatibility, base compatibility and compatibility with the augmentations.
   Both its endpoints are polynomial resolutions by hP and the standard-resolution
   clause of lem-trf-cotangent-resolution-coherence.
2. Apply the comparison naturality of that coherence node to h over A'.
   Cancel restriction along the identity to obtain QK(h) followed by cR = cP'.
3. On differential generators, K(h) theta u sends dp tensor c to
   d(t(p)) tensor f(c), precisely the standard differential map. The Kahler
   universal property and generation by pure tensors give equality in every
   nonpositive degree. Both maps commute with faces, hence with their signed
   alternating sums. Localize and compose with the target comparison to get
   the displayed formula for cotangentMap, including the restriction factors.
4. By lem-trf-one-point-derived-ring-identification, the representative
   normalization of lem-pur-sheaf-ring-derived-coefficient-adjunction applies
   to ordinary modules with the same universal pair and computation morphism.
   K-flatness and flat terms make epsilon at K invertible, giving cK. The ordinary
   adjunct of the map in Step 3 sends x tensor b' to b' times g(x), which equals
   K(h) theta on pure tensors. Normalization and target naturality therefore give
   the first adjunct equation. Substitute Step 2 for the second equation.
   No inverse to theta, derived-multiplication hypothesis, flat ring map or
   boundedness hypothesis is used. -/
theorem cotangent_base_change_adjunct_formula (C : Coherence.{u})
    {f g : Arrow CommRingCat.{u}} (q : f ⟶ g)
    (hP : IsPolynomialResolution (squareTensorAugmentation q (C.standard f)))
    (hK : (HomologicalComplex.quasiIso (ModuleCat.{u} f.right) (.up ℤ)).kFlat
      (differentialComplex (C.differentials (C.standard f))))
    (hflat : ∀ i : ℤ, Module.Flat f.right
      ((differentialComplex (C.differentials (C.standard f))).X i))
    (L : DerivedCategory (ModuleCat.{u} f.right) ⥤
      DerivedCategory (ModuleCat.{u} g.right))
    (epsilon : DerivedCategory.Q ⋙ L ⟶
      (ModuleCat.extendScalars q.right.hom).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hL : L.IsLeftDerivedFunctor epsilon
      (HomologicalComplex.quasiIso (ModuleCat.{u} f.right) (.up ℤ)))
    (a : L ⊣ (ModuleCat.restrictScalars q.right.hom).mapDerivedCategory)
    (normalized : a.unit.app (cotangentComplex C f) ≫
      (ModuleCat.restrictScalars q.right.hom).mapDerivedCategory.map
        (epsilon.app (differentialComplex (C.differentials (C.standard f)))) ≫
      (ModuleCat.restrictScalars q.right.hom).mapDerivedCategoryFactors.hom.app
        (squareTensorComplex C q) = DerivedCategory.Q.map (squareTensorUnit C q)) :
    ∃ cK : L.obj (cotangentComplex C f) ≅ DerivedCategory.Q.obj (squareTensorComplex C q),
      cK.hom = epsilon.app (differentialComplex (C.differentials (C.standard f))) ∧
      (DerivedCategory.Q.map (squareTensorDifferentialMap C q) ≫
        (C.comparison (C.standard g) (C.standard_resolution g)).hom =
          (C.comparison (squareTensorAugmentation q (C.standard f)) hP).hom) ∧
      (cotangentMap C q = DerivedCategory.Q.map (squareTensorUnit C q) ≫
        (ModuleCat.restrictScalars q.right.hom).mapDerivedCategoryFactors.inv.app
          (squareTensorComplex C q) ≫
        (ModuleCat.restrictScalars q.right.hom).mapDerivedCategory.map
          (DerivedCategory.Q.map (squareTensorTheta C q) ≫
            DerivedCategory.Q.map (squareTensorDifferentialMap C q) ≫
            (C.comparison (C.standard g) (C.standard_resolution g)).hom)) ∧
      (((a.homEquiv _ _).symm (cotangentMap C q)) =
        cK.hom ≫ DerivedCategory.Q.map (squareTensorTheta C q) ≫
          DerivedCategory.Q.map (squareTensorDifferentialMap C q) ≫
          (C.comparison (C.standard g) (C.standard_resolution g)).hom) ∧
      (((a.homEquiv _ _).symm (cotangentMap C q)) =
        cK.hom ≫ DerivedCategory.Q.map (squareTensorTheta C q) ≫
          (C.comparison (squareTensorAugmentation q (C.standard f)) hP).hom) := by
  sorry

end Algebra.CotangentResolution
