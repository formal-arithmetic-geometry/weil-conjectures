/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.Paper.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Paper.SiteDerivedTensorRestriction
import Sheaf.CategoryTheory.SiteCoveringAxioms

/-!
# Tor bounds from bounded flat models on a finite pro-etale cover

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md, (2) Local models; Stacks Tags 06YQ, 06YY, 07A4, 06YU
(blueprint: lem-sfb-local-model-tor-bound-descent).

Module objects are identified with sectionwise module sheaves by the existing
`InternalAbelianSheafModule.sectionModuleEquivalence`. Flatness below uses exactly
`SheafOfModules.IsFlatOnSite` on that sectionwise encoding. The derived tensor and Tor
amplitude use the internal-module encoding of the recorded Tor-amplitude dependency.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A common interval of bounded flat local models bounds Tor amplitude globally.
Source: blueprint main-20261015, det-prop-scalar-six-ctf.proof.md (2) Local models
(blueprint: lem-sfb-local-model-tor-bound-descent).

Proof:
1. Identify the site over each cover object with its slice by
   lem-weil-proetale-weakly-etale-localization (1). The section formula of
   def-pur-localized-ringed-site and the Cartesian coefficient isomorphism
   lem-sfb-alpha-iso identify inverse image with restriction and transport of scalars.
2. Exact inverse image commutes with cohomology and preserves quasi-isomorphisms by
   lem-weil-pbc-exact-functor-complex-cohomology. Apply lem-pc-kflat-resolution and
   lem-weil-pbc-ringed-topoi-derived-pullback to identify it with derived inverse image.
3. Apply lem-weil-pbc-ringed-topoi-derived-tensor-pullback to Q and N in degree zero,
   then substitute the given local isomorphism from the pullback of Q to L_i.
4. Each L_i is bounded above and termwise flat, hence K-flat by
   lem-pc-bounded-above-flat-kflat-site. The identity-coefficient specialization of
   lem-trf-site-derived-tensor-restriction computes its tensor with the pullback of N
   by the ordinary total tensor complex. This gives the asserted local isomorphism.
5. By def-pc-tensor-complex-sheaves, its degree-q term is L_i^q tensor g_i^*N and is
   zero outside [r,s]. Thus its cohomology vanishes there. The exact-functor cohomology
   comparison gives zero restrictions of H^q(Q tensor-derived N) on every cover member.
6. Base change the cover to any site object using def-weil-pbc-sites-and-cohomology.
   The restriction formula of def-pur-localized-ringed-site makes every restricted
   section zero. Sheaf separatedness forces every section to be zero, also for an
   empty cover. For arbitrary N and q this is the condition in
   det-def-sfb-constructible-tor-amplitude (3). No flatness of N is used. -/
theorem localModel_torBound_descent
    (Γ : Profinite.CondensedRing.{u}) [IsCommMonObj Γ.X]
    (S : Scheme.{u})
    (Q : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Γ.X S)))
    (n : ℕ) (V : Fin n → S.ProEt)
    (hcover : Presieve.ofArrows (fun i ↦ (V i).left) (fun i ↦ (V i).hom) ∈
      Scheme.proetalePrecoverage S)
    (r s : ℤ) (hrs : r ≤ s)
    (L : ∀ i : Fin n, CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology (V i).left) Ab.{u + 1})
        (condensedRingObj Γ.X (V i).left)) ℤ)
    (hbound : ∀ (i : Fin n) (q : ℤ), q < r ∨ s < q → IsZero ((L i).X q))
    (hflat : ∀ (i : Fin n) (q : ℤ), SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology (V i).left)
      (R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology (V i).left) (condensedRingObj Γ.X (V i).left))
      ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
        (Scheme.ProEt.topology (V i).left) (condensedRingObj Γ.X (V i).left)).functor.obj
          ((L i).X q)))
    (model : ∀ i : Fin n,
      (CondensedRing.upperStar Γ.X (V i).hom).mapDerivedCategory.obj Q ≅
        DerivedCategory.Q.obj (L i)) :
    (∀ (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Γ.X S))
      (i : Fin n), Nonempty
        ((CondensedRing.upperStar Γ.X (V i).hom).mapDerivedCategory.obj
          (Q ⊗ (DerivedCategory.singleFunctor _ 0).obj N) ≅
        DerivedCategory.Q.obj (CochainComplex.mapBifunctor (L i)
          ((CochainComplex.singleFunctor _ 0).obj
            ((CondensedRing.upperStar Γ.X (V i).hom).obj N)) (curriedTensor _)))) ∧
    (∀ (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Γ.X S))
      (q : ℤ), q < r ∨ s < q → IsZero
        ((DerivedCategory.homologyFunctor _ q).obj
          (Q ⊗ (DerivedCategory.singleFunctor _ 0).obj N))) ∧
    DerivedCategory.torAmplitudeIn
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Γ.X S)) r s Q := by
  sorry

end AlgebraicGeometry.ProEtale
