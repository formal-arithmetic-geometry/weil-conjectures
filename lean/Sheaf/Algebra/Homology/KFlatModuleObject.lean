/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal

import WeilConjectures.FromJoel.Algebra.Homology.Bifunctor
import Sheaf.CategoryTheory.DerivedCategory.KFlatDerivability
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution

/-!
# K-flat complexes of module objects on the pro-étale site

Source: blueprint main-20261015, `sec-smooth-purity/sk-def-sp-coefficient-towers/`
`pur713-def-kflat-module.md`, order 2484 (blueprint: pur713-def-kflat-module).

The coefficient tensor on abelian sheaves is the sheafification of tensor over `ℤ`.
The module tensor is the recorded `CategoryTheory.Mod.monoidalCategory` relative tensor.
`HomologicalComplex.tensorObj` takes its direct-sum total: degree `n` is the coproduct of
`P.X p ⊗ N.X q` over `p + q = n`, and the differential on that summand is
`d_P ⊗ 1 + (-1)^p (1 ⊗ d_N)`, into the `(p+1,q)` and `(p,q+1)` summands.
No monoidal structure on the category of complexes is needed to form this binary tensor.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The one-sided acyclic-test definition of K-flatness for module objects.
Source: blueprint main-20261015, `pur713-def-kflat-module.md`, first sentence
(blueprint: pur713-def-kflat-module). `Acyclic` means that cohomology vanishes in every
integer degree; the total tensor is the signed direct-sum total described above. -/
def IsKFlatModuleObject (X : Scheme.{u})
    (R : CommMon (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}))
    (P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R.X) ℤ) :
    Prop :=
  ∀ N : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R.X) ℤ,
    N.Acyclic → (HomologicalComplex.tensorObj P N).Acyclic

/-- A K-flat resolution is a quasi-isomorphism from a K-flat complex to the given complex.
Source: blueprint main-20261015, `pur713-def-kflat-module.md`, second sentence
(blueprint: pur713-def-kflat-module). -/
def IsKFlatModuleObjectResolution (X : Scheme.{u})
    (R : CommMon (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}))
    {P M : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R.X) ℤ}
    (q : P ⟶ M) : Prop :=
  IsKFlatModuleObject X R P ∧ QuasiIso q

/-- Functorial K-flat resolutions exist on the category of unbounded module-object complexes.
Source: blueprint main-20261015, `pur713-def-kflat-module.md`, final sentence
(blueprint: pur713-def-kflat-module).

Proof plan (the six steps of this node).
1. Abelian groups are Grothendieck abelian and have a functorial free flat cover, by
   `lem-weil-pbc-ring-modules-grothendieck-abelian`, `def-weil-pbc-free-module` and
   `lem-weil-pbc-projective-module-flat`, applied over the integers.
2. The essentially small pro-étale site of `def-weil-pbc-proetale-site` inherits the
   Grothendieck abelian closed symmetric tensor and functorial flat cover by
   `lem-weil-pbc-sheaf-tensor-closed`, `sk-def-sfb-sheaf-tensor` and
   `lem-sfb-sheaf-functorial-flat-resolution`.
3. Apply `lem-sfb-modobj-grothendieck` and `def-sfb-modobj-internal-hom`. The relative
   tensor is exactly `pur713-def-relative-tensor`, with symmetry from
   `def-sfb-modobj-symmetric-tensor`. Its two fixed-factor functors are left adjoints,
   hence preserve colimits by `lem-weil-pbc-left-adjoint-preserves-colimits`; their
   preservation of zero and biproducts also gives additivity.
4. `lem-sfb-modobj-flat-resolutions` gives a functorial flat epimorphism onto each module:
   take the free module on a functorial flat cover of its underlying abelian sheaf,
   and compose its augmentation with the module action.
5. The direct sums exist by the Grothendieck property. The displayed signed differential
   squares to zero: the pure terms vanish, and the two mixed terms have opposite signs.
   Tensoring maps degreewise commutes with this differential. This is the total tensor
   of `def-sfb-preserves-kflat-quasi-iso` and `def-weil-abstract-derived-category`.
6. `lem-sfb-kflat-derivability` supplies a functor `Q` and a natural quasi-isomorphism
   `q : Q ⟶ 𝟭 _` with two-sided K-flat values. For an acyclic `N`, its map to zero is a
   quasi-isomorphism. Tensor it on the left by `Q.obj M`; the result is again a
   quasi-isomorphism and its target is zero, since relative tensor preserves zero and
   so does the total direct sum. Thus `Q.obj M` satisfies precisely the one-sided
   acyclic test here. Naturality is on complexes, with no choice on the homotopy category. -/
theorem exists_functorial_kFlatModuleObject_resolution (X : Scheme.{u})
    (R : CommMon (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})) :
    ∃ (Q : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R.X) ℤ ⥤
        CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R.X) ℤ)
      (q : Q ⟶ 𝟭 _),
      ∀ M : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R.X) ℤ,
        IsKFlatModuleObjectResolution X R (q.app M) := by
  classical
  let B := Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R.X
  let : Zero (CochainComplex B ℤ) := HasZeroObject.zero' _
  have : Abelian.HasFunctorialFlatResolution B := inferInstance
  let Λ : Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ B) :=
    Classical.choice (inferInstance : Abelian.HasFunctorialFlatResolution B)
  obtain ⟨Q, q, hQ, hq, _⟩ := kFlat_derivability
    (Λ.F ⋙ ObjectProperty.flat.ι) Λ.π (fun M ↦ (Λ.F.obj M).property)
    (fun M ↦ Λ.epi_π_app M)
  refine ⟨Q, q, fun M ↦ ⟨?_, ?_⟩⟩
  · intro N hN
    let T := ((MonoidalCategory.curriedTensor B).map₂CochainComplex).obj (Q.obj M)
    have hz : (0 : CochainComplex B ℤ).Acyclic :=
      HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)
    have hs : QuasiIso (0 : N ⟶ 0) :=
      ⟨fun i ↦ (quasiIsoAt_iff_exactAt' _ i (hz i)).2 (hN i)⟩
    have ht : QuasiIso (HomologicalComplex.tensorHom (𝟙 (Q.obj M)) (0 : N ⟶ 0)) :=
      (hQ M).1 _ hs
    have htzero : (HomologicalComplex.tensorObj (Q.obj M) (0 : CochainComplex B ℤ)).Acyclic :=
      HomologicalComplex.acyclic_of_isZero _ (T.map_isZero (isZero_zero _))
    intro i
    exact (quasiIsoAt_iff_exactAt' _ i (htzero i)).1 (ht.quasiIsoAt i)
  · exact hq M

end AlgebraicGeometry.ProEtale
