/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Sheaf.FieldTheory.PurelyTranscendentalExtension

import WeilConjectures.AlgebraicGeometry.AffineEtaleClosedImmersionLift
import Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ModulePullbackFiniteType
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import Sheaf.AlgebraicGeometry.FiniteTypeSheafFinitePresentationSupport
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Sheaf.TraceFormula.EtaleFiniteSmoothLocalStructure

/-! # Elementary étale dévissage of a finite-type module

Source: Stacks Project, flat.tex, Tag 057S, lemma-elementary-devissage.
(blueprint: lem-trf-elementary-module-devissage).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Elementary étale dévissage at a point of the support of the fibre module.
The natural number `n` is identified with the local topological dimension of that support.
Residue-field isomorphisms refer to the canonical maps of the two étale neighbourhoods.
The final algebra structure is the canonical residue-field map of `h` at `π z'`.

Source: Stacks Project, flat.tex, Tag 057S, lemma-elementary-devissage.
(blueprint: lem-trf-elementary-module-devissage).

Proof (the seven steps of the DAG):
1. Restrict to affine neighbourhoods in source and base; local support dimension is
   unchanged because open neighbourhoods in the restriction are cofinal.
2. By 057Q choose a finitely presented supporting closed subscheme `Z` and a finite-type
   quasi-coherent module on it whose direct image is `F`, with the prescribed fibre support.
3. Apply 057K and its affine refinement 057L to `Z` at the corresponding point. This gives
   elementary neighbourhoods and a finite map to the smooth geometrically integral family,
   including the singleton fibre and purely transcendental residue extension.
4. Base change the closed immersion to the new base. The induced map from the étale
   neighbourhood of `Z` is étale by cancellation; all schemes in this step are affine.
5. Apply the affine étale lifting lemma 057R to embed that neighbourhood as the pullback
   of `Z` in an affine scheme étale over the base-changed ambient scheme. Finite presentation
   of the closed immersion is preserved under base change.
6. Compose with the projection to the original ambient scheme. The cartesian square gives
   the commutative diagram and the distinguished points. Residue-field maps of closed
   immersions are isomorphisms, so the new ambient neighbourhood is elementary too.
7. Pull back the module on `Z`. Pullback preserves finite type and quasi-coherence, and
   affine pushforward base change (02KG) identifies its direct image with `g* F`.
   The geometric properties and distinguished finite fibre from step 3 are unchanged. -/
theorem exists_elementary_module_devissage
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (x : X)
    (hx : ¬ Subsingleton
      (((tensorPullback (f.fiberι (f x))).obj F).presheaf.stalk (f.asFiber x))) :
    ∃ (n : ℕ),
      topologicalKrullDimAt
        (⟨f.asFiber x, hx⟩ :
          {q : f.fiber (f x) |
            ¬ Subsingleton (((tensorPullback (f.fiberι (f x))).obj F).presheaf.stalk q)}) =
        (n : WithBot ℕ∞) ∧
      ∃ (X' Z' Y' S' : Scheme.{u})
        (g : X' ⟶ X) (e : S' ⟶ S) (f' : X' ⟶ S')
        (i : Z' ⟶ X') (π : Z' ⟶ Y') (h : Y' ⟶ S')
        (x' : X') (s' : S') (z' : Z') (G : Z'.Modules),
        Etale g ∧ Etale e ∧ g x' = x ∧ e s' = f x ∧
        IsIso (g.residueFieldMap x') ∧ IsIso (e.residueFieldMap s') ∧
        g ≫ f = f' ≫ e ∧ i ≫ f' = π ≫ h ∧
        IsAffine X' ∧ IsAffine Z' ∧ IsAffine Y' ∧ IsAffine S' ∧
        IsClosedImmersion i ∧ LocallyOfFinitePresentation i ∧
        QuasiCompact i ∧ QuasiSeparated i ∧ IsFinite π ∧
        G.IsFiniteType ∧ G.IsQuasicoherent ∧
        Nonempty ((pushforward i).obj G ≅ (tensorPullback g).obj F) ∧
        SmoothOfRelativeDimension n h ∧ GeometricallyIntegral h ∧
        i z' = x' ∧ h (π z') = s' ∧
        (π ⁻¹' ({π z'} : Set Y')) = {z'} ∧
        (letI : Algebra (S'.residueField (h (π z'))) (Y'.residueField (π z')) :=
          (h.residueFieldMap (π z')).hom.toAlgebra
         Algebra.IsPurelyTranscendentalExtension
           (S'.residueField (h (π z'))) (Y'.residueField (π z'))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
