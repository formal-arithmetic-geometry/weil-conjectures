/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.TraceFormula.ElementaryModuleDevissage
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

import WeilConjectures.Mathlib.RingTheory.Finiteness.Descent

/-! # Finite presentation across elementary module dévissage

Source: Stacks Project, flat.tex, Tag 057T, lemma-devissage-finite-presentation
(blueprint: lem-trf-elementary-devissage-finite-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- In elementary étale module dévissage, finite presentation of the structural morphism
makes the finite map finitely presented. Finite presentation near the three marked points
is equivalent, as is finite presentation of the three stalks (a separate equivalence).

Source: Stacks Project, flat.tex, Tag 057T, lemma-devissage-finite-presentation
(blueprint: lem-trf-elementary-devissage-finite-presentation).

Proof:
1. The composites Z' → S and Y' → S are locally of finite presentation, by composition
   of the closed immersion, étale maps, and smooth map with f. Finite-presentation
   permanence makes π locally of finite presentation; finiteness makes it quasi-compact
   and separated, hence of finite presentation
   (lem-trf-finite-morphism-finite-presentation).
2. Introduce finite presentation of g^*F near x'. Pullback preserves finite presentation;
   conversely g is open and its restriction to any neighbourhood of x' covers its image.
   Faithfully flat descent gives equivalence with finite presentation of F near x
   (lem-trf-etale-module-finite-presentation-local).
3. The given isomorphism i_*G ≅ g^*F and finite-pushforward finite-presentation comparison
   for i give the equivalence with G near z'. Apply that comparison to π, using its
   finite presentation and singleton fibre, to compare with π_*G near π z'
   (lem-trf-finite-pushforward-module-finite-presentation).
4. On stalks, the étale local ring map is faithfully flat, so finite presentation descends
   and ascends (lem-trf-finite-presentation-module-descent-flat-local). The closed immersion
   gives a surjective finitely presented local ring map; the finite finitely presented map
   π with singleton fibre gives a finite finitely presented map of local rings.
   Finite-extension module comparison and i_*G ≅ g^*F identify the three conditions
   (lem-trf-finite-extension-module-finite-presentation and
   lem-trf-finite-pushforward-module-finite-presentation). -/
theorem elementary_devissage_finite_presentation
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) (_hF : F.IsQuasiCoherentFiniteType) (x : X)
    (hx : ¬ Subsingleton
      (((tensorPullback (f.fiberι (f x))).obj F).presheaf.stalk (f.asFiber x)))
    (n : ℕ)
    (_hn : topologicalKrullDimAt
      (⟨f.asFiber x, hx⟩ :
        {q : f.fiber (f x) |
          ¬ Subsingleton (((tensorPullback (f.fiberι (f x))).obj F).presheaf.stalk q)}) =
      (n : WithBot ℕ∞))
    (X' Z' Y' S' : Scheme.{u})
    (g : X' ⟶ X) (e : S' ⟶ S) (f' : X' ⟶ S')
    (i : Z' ⟶ X') (π : Z' ⟶ Y') (h : Y' ⟶ S')
    (x' : X') (s' : S') (z' : Z') (G : Z'.Modules)
    [Etale g] [Etale e] (_hg : g x' = x) (_he : e s' = f x)
    [IsIso (g.residueFieldMap x')] [IsIso (e.residueFieldMap s')]
    (_hfg : g ≫ f = f' ≫ e) (_hπ : i ≫ f' = π ≫ h)
    [IsAffine X'] [IsAffine Z'] [IsAffine Y'] [IsAffine S']
    [IsClosedImmersion i] [LocallyOfFinitePresentation i] [QuasiCompact i] [QuasiSeparated i]
    [IsFinite π] (_hG : G.IsQuasiCoherentFiniteType)
    (_hiso : Nonempty ((pushforward i).obj G ≅ (tensorPullback g).obj F))
    [SmoothOfRelativeDimension n h] [GeometricallyIntegral h]
    (_hi : i z' = x') (_hs : h (π z') = s')
    (_hfibre : (π ⁻¹' ({π z'} : Set Y')) = {z'})
    (_hpure : @Algebra.IsPurelyTranscendentalExtension
      (S'.residueField (h (π z'))) (Y'.residueField (π z'))
      inferInstance inferInstance (h.residueFieldMap (π z')).hom.toAlgebra)
    [LocallyOfFinitePresentation f] :
    (LocallyOfFinitePresentation π ∧ QuasiCompact π ∧ QuasiSeparated π) ∧
    ((∃ U : X.Opens, x ∈ U ∧ (F.over U).IsFinitePresentation) ↔
      (∃ U : Z'.Opens, z' ∈ U ∧ (G.over U).IsFinitePresentation)) ∧
    ((∃ U : Z'.Opens, z' ∈ U ∧ (G.over U).IsFinitePresentation) ↔
      (∃ U : Y'.Opens, π z' ∈ U ∧ ((pushforward π).obj G |>.over U).IsFinitePresentation)) ∧
    (Module.FinitePresentation (X.presheaf.stalk x)
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F) ↔
      Module.FinitePresentation (Z'.presheaf.stalk z')
        ((RingedSpace.moduleStalkFunctor Z'.toRingedSpace z').obj G)) ∧
    (Module.FinitePresentation (Z'.presheaf.stalk z')
        ((RingedSpace.moduleStalkFunctor Z'.toRingedSpace z').obj G) ↔
      Module.FinitePresentation (Y'.presheaf.stalk (π z'))
        ((RingedSpace.moduleStalkFunctor Y'.toRingedSpace (π z')).obj
          ((pushforward π).obj G))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
