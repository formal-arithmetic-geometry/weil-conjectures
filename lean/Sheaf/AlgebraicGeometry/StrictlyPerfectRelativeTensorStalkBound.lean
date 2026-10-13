/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Topology.Sheaves.Abelian
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.KFlatStalkCriterion
import Sheaf.Algebra.Homology.KFlatTensorQuasiIso
import Sheaf.Algebra.Homology.ModuleStalkExact
import Sheaf.Algebra.Homology.StalkTensorComplex

/-! # Relative tensor bounds from a strictly perfect local model

Source: Stacks Project, Tag 0B6G, verification of condition (3), and
Cohomology of Sheaves, Tags 08CG, 09U9, and 06YB.
(blueprint: lem-pc-strictly-perfect-relative-tensor-stalk-bound).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- A strictly perfect local model in degrees [r,s], and a Tor bound d for the
structure stalk, give relative tensor homology vanishing outside [r-d,s].
Source: Stacks Project, Tag 0B6G, `lemma-perfect-proper-perfect-direct-image`,
condition (3); Cohomology of Sheaves, Tags 08CG,
09U9, and 06YB; More on Algebra, Tag 064L.

Proof: since y belongs to V, exact restriction and the local representative
isomorphism identify the stalk of K with the stalk of L in the derived category.
Every L term is a retract of a finite free structure module. Taking stalks and
restricting scalars preserve this retraction. Tor is additive and preserves
retractions, so the assumed bound for the structure stalk gives amplitude [-d,0]
for each term. Filter L by its finitely many nonzero degrees. The quotients are
its terms placed in those degrees; after derived tensor their amplitudes are
[t-d,t]. Induction using the long exact cohomology sequence therefore gives
[r-d,s] for the scalar-restricted stalk of L. If r > s the degree hypothesis
makes every term zero and all tensor homology vanishes.
Apply the K-flat stalk criterion to the ringed space with ring sheaf f inverse
image O_Y. The given q and exactness of stalks identify its K-flat stalk complex
with the scalar-restricted stalk of K. Comparing to a common K-flat replacement
of the local model makes their derived tensors equal, by invariance under
quasi-isomorphisms between K-flat complexes. Stalks commute with total tensor
and with homology, so the underlying abelian-group stalk of the displayed tensor
homology vanishes outside [r-d,s], for every test sheaf F. This argument is
pointwise and needs no finite-type, Noetherian, or perfect-morphism hypothesis.
(blueprint: lem-pc-strictly-perfect-relative-tensor-stalk-bound). -/
theorem strictlyPerfect_relativeTensor_stalk_bound
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (V : X.Opens)
    (L : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)) ℤ)
    (hL : IsStrictlyPerfect X V L)
    (eL : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) V).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K) ≅ DerivedCategory.Q.obj L))
    (r s : ℤ) (hdegrees : ∀ t : ℤ, t < r ∨ s < t → IsZero (L.X t))
    (y : X) (hy : y ∈ V) (d : ℕ)
    (hTor : ∀ M : ModuleCat.{u} (Y.presheaf.stalk (f y)),
      ∀ j : ℕ, d < j →
        IsZero (((Tor' (ModuleCat.{u} (Y.presheaf.stalk (f y))) j).obj
          ((ModuleCat.restrictScalars (f.stalkMap y).hom).obj
            (ModuleCat.of (X.presheaf.stalk y) (X.presheaf.stalk y)))).obj M))
    (P : CochainComplex (SheafOfModules.{u} ((sheafCompose
      (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (TopCat.Sheaf.inverseImageRing f.base Y.sheaf))) ℤ)
    (hP : CochainComplex.IsKFlat (R := TopCat.Sheaf.inverseImageRing f.base Y.sheaf) P)
    (q : P ⟶ ((SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).map
          (Modules.tensorPullbackRingMap f))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) (hq : QuasiIso q) :
    ∀ F : SheafOfModules.{u} ((sheafCompose
          (Opens.grothendieckTopology X)
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (TopCat.Sheaf.inverseImageRing f.base Y.sheaf)),
        ∀ i : ℤ, i < r - (d : ℤ) ∨ s < i →
          IsZero ((TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
            TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).obj
              ((SheafOfModules.toSheaf _).obj
                ((CochainComplex.mapBifunctor P
                  ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)
                  (@MonoidalCategory.curriedTensor _ _ (SheafOfModules.monoidalCategory
                    (TopCat.Sheaf.inverseImageRing f.base Y.sheaf)))).homology i))) := by sorry

end AlgebraicGeometry.Scheme
