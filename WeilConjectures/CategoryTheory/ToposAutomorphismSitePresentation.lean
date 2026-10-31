/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.InvariantFiniteLimitGenerators
import WeilConjectures.CategoryTheory.InvariantGeneratorSite
import WeilConjectures.CategoryTheory.EquivariantNervePullback
import WeilConjectures.CategoryTheory.IntegerShiftComparison
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # An invariant site presenting a topos automorphism

Source: Stacks Project, Sites, Tag 03CI, lemma-topos-good-site, with the equivariant
refinement in the DAG proof (blueprint: lem-pur-topos-automorphism-site-presentation).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The sheaf inverse image induced by a continuous endofunctor of a small site.
Source: Stacks Project, Sites, Tags 00WW and 00WX (blueprint:
lem-pur-topos-automorphism-site-presentation).
The data is the canonical Mathlib sheaf pullback for the Grothendieck topology
of the covering presieves.
-/
noncomputable def siteSheafInverseImage
    {D : Type u} [SmallCategory D] (K : Precoverage D)
    (s : D ⥤ D)
    (hs : s.IsContinuous K.toGrothendieck K.toGrothendieck) :
    Sheaf K.toGrothendieck (Type u) ⥤ Sheaf K.toGrothendieck (Type u) := by
  letI := hs
  exact Functor.sheafPullback s (Type u) K.toGrothendieck K.toGrothendieck

/-- The coherent integer-power shift of a chosen category autoequivalence.
Source: the unit and counit in the equivariant refinement of Stacks Sites Tag 03CI
(blueprint: lem-pur-topos-automorphism-site-presentation).
The inverse object is the chosen inverse functor and the two cancellation maps are
its unit and counit.
-/
@[instance_reducible] noncomputable def toposAutomorphismPowerShift
    {A : Type v} [Category.{w} A] (F : A ≌ A) : HasShift A ℤ := by
  letI := endofunctorMonoidalCategory A
  let t : MonoidalCategory.TensorInverse F.functor :=
    ⟨F.inverse, F.unitIso.symm, F.counitIso⟩
  exact ⟨t.intTensorFamily.toFunctor, t.intTensorFamily.coreMonoidal.toMonoidal⟩

/-- A small finite-limit site presenting an arbitrary automorphism of a sheaf topos.
Source: Stacks Project, Sites, Tag 03CI, lemma-topos-good-site, with the equivariant
refinement (blueprint: lem-pur-topos-automorphism-site-presentation).

Proof: close all finite words in the automorphism and its inverse applied to the
sheafified representables under terminal objects, pullbacks and isomorphisms.
Mathlib's limits closure is essentially small. Restrict the equivalence to this
closure and conjugate it to a small model. The inclusion is fully faithful and
preserves finite limits. The full-subcategory comparison gives an epimorphic
covering site and the restricted Yoneda nerve equivalence. The ambient adjunction
Hom bijections transfer joint epimorphy through both site equivalences, so both
preserve covers. Finite-limit preservation then gives continuity. Precomposition
by these two continuous functors gives inverse sheaf equivalences. Its left
adjoint, the canonical sheaf pullback, is therefore an equivalence. The nerve
Hom bijection Hom(H(sd),Y) ≃ Hom(Hd,σ.inverse(Y)) gives an isomorphism of right
adjoints; taking adjoint conjugates gives the required degree-one intertwiner.
View integer shifts as coherent tensor families in endofunctors. The existing
integer tensor-family comparison extends degree-one isomorphisms coherently.
Transport the target shift through the nerve equivalence, compare it to the
source shift on the identity functor, and compose the comparisons. Finally take
its degree-one isomorphism as b. Equivalences preserve all limits and colimits.
-/
theorem toposAutomorphismSitePresentation
    {C : Type u} [SmallCategory C] (J : Precoverage C)
    (_hJ : J.IsSiteForCoverings)
    (σ : Sheaf J.toGrothendieck (Type u) ≌ Sheaf J.toGrothendieck (Type u)) :
    ∃ (D : Type u) (_ : SmallCategory D) (K : Precoverage D)
      (_ : K.IsSiteForCoverings) (_ : HasFiniteLimits D) (s : D ≌ D)
      (e : Sheaf K.toGrothendieck (Type u) ≌ Sheaf J.toGrothendieck (Type u))
      (hs : s.functor.IsContinuous K.toGrothendieck K.toGrothendieck),
      s.inverse.IsContinuous K.toGrothendieck K.toGrothendieck ∧
      (∀ (U : D) (R : Presieve U), R ∈ K U →
        R.map s.functor ∈ K (s.functor.obj U)) ∧
      (∀ (U : D) (R : Presieve U), R ∈ K U →
        R.map s.inverse ∈ K (s.inverse.obj U)) ∧
      PreservesFiniteLimits s.functor ∧ PreservesFiniteLimits s.inverse ∧
      PreservesFiniteLimits e.functor ∧ PreservesFiniteLimits e.inverse ∧
      PreservesColimitsOfSize.{u, u} e.functor ∧
      PreservesColimitsOfSize.{u, u} e.inverse ∧
      ∃ P : Sheaf K.toGrothendieck (Type u) ≌ Sheaf K.toGrothendieck (Type u),
        P.functor = siteSheafInverseImage K s.functor hs ∧
        ∃ b : P.functor ⋙ e.functor ≅ e.functor ⋙ σ.functor,
          ∃ c : @Functor.CommShift (Sheaf K.toGrothendieck (Type u))
              (Sheaf J.toGrothendieck (Type u)) _ _ e.functor ℤ _
              (toposAutomorphismPowerShift P) (toposAutomorphismPowerShift σ),
            c.commShiftIso 1 = b := by
  obtain ⟨D, hD, hFD, H, s, hfull, hfaithful, hH, ⟨a⟩, hrep⟩ :=
    invariantFiniteLimitGenerators
      (fun U : C ↦ (presheafToSheaf J.toGrothendieck (Type u)).obj (yoneda.obj U)) σ
  obtain ⟨K, hK, n, ⟨hnerve⟩, hf, hi, hs, hsi⟩ :=
    invariantGeneratorSite J _hJ H s σ a hrep
  let := hs
  let := hsi
  obtain ⟨hP, ⟨b⟩⟩ :=
    equivariantNervePullback J.toGrothendieck K.toGrothendieck H s σ a n hnerve
  let := hP
  let P := (Functor.sheafPullback s.functor (Type u)
    K.toGrothendieck K.toGrothendieck).asEquivalence
  obtain ⟨c⟩ := integerShiftEquivalenceComparison
    (toposAutomorphismPowerShift P) (toposAutomorphismPowerShift σ) n.symm b
  exact ⟨D, hD, K, hK, hFD, s, n.symm, hs, hsi, hf, hi,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    P, rfl, c.commShiftIso 1, c, rfl⟩

end CategoryTheory
