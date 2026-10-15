/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf

import WeilConjectures.ConstructibleSheaf.Pullback
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear
import Sheaf.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.AlgebraicGeometry.ConstructibleColimitFactorization
import Sheaf.Paper.InverseImageStalkGerm
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.ConstructibleSheaf.KernelCokernel

/-!
# Constructibility descends through surjective pullback

Source: Stacks Project, Tag 095Q, lemma-check-constructible (3), for finite commutative rings
(blueprint: lem-weil-pbc-etale-constructible-surjective-pullback).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Constructibility of a module sheaf over a finite commutative ring can be checked after
surjective pullback between quasi-compact quasi-separated schemes.

Source: Stacks Project, Tag 095Q, lemma-check-constructible (3)
(blueprint: lem-weil-pbc-etale-constructible-surjective-pullback).

Proof:
1. For the forward direction pull back the finite locally closed stratification
   (`lemma-constructible-pullback-stratification`). Its strata remain constructible
   (`lem-pur-scheme-constructible-preimage`). Module inverse image and its composition
   isomorphism (`prop-weil-pbc-inverse-image-modules-exact`,
   `lem-weil-pbc-inverse-image-composition-module-linear`) identify the stratum restrictions.
   Finite locally constant module values remain so, by
   `lem-weil-pbc-finite-locally-constant-module-values`,
   `lemma-constructible-pullback-locally-constant`, `lemma-constructible-pullback-finite`,
   and `lemma-constructible-iso-invariance`. This direction needs no surjectivity.
2. For any sheaf H with constructible pullback, present H as a filtered colimit of
   constructible module sheaves (`lem-weil-pbc-module-sheaf-colimit-constructible`).
   Inverse image is a left adjoint (`prop-weil-pbc-inverse-image-modules-exact`) and preserves
   this colimit (`lem-weil-pbc-left-adjoint-preserves-colimits`). Apply
   `lem-weil-pbc-constructible-large-colimit-factorization` to the identity of the pullback
   of H: one pulled-back colimit leg is a split epimorphism.
3. Exactness of inverse image makes the cokernel of that leg vanish after pullback.
   Surjectivity supplies a geometric point above every point of U. The stalk comparison
   (`lem-weil-pbc-inverse-image-stalk-germ`) and detection of isomorphisms on these stalks
   (`lem-weil-pbc-sets-etale-iso-on-geometric-stalks`) make the cokernel zero already on U.
   Thus every such H is a quotient of a constructible module sheaf.
4. Apply this to F to obtain an epimorphism G to F with G constructible. Its kernel K
   has constructible pullback, by exactness and the kernel clause of
   `thm-constructible-serre`. Apply steps 2 and 3 to K to obtain an epimorphism C to K
   with C constructible.
5. The composite C to K to G has cokernel F. The cokernel clause of
   `thm-constructible-serre` therefore makes F constructible, proving the converse. -/
theorem isConstructibleEtaleModuleSheaf_iff_surjective_pullback
    {U V : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace U]
    [CompactSpace V] [QuasiSeparatedSpace V] (f : V ⟶ U) [Surjective f]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsConstructibleEtaleModuleSheaf F ↔
      IsConstructibleEtaleModuleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj F) := by
  sorry

end AlgebraicGeometry.Scheme
