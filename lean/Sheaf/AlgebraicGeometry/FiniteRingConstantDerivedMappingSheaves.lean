/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleDerivedMapPresheaves
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

import WeilConjectures.AlgebraicGeometry.ConstantEtaleSheafShortExact
import WeilConjectures.RingTheory.FiniteConeFreeModel
import Sheaf.Paper.FiniteFreeEtaleLocalActual
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk

import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Derived mapping sheaves on constant complexes -/

@[expose] public section

universe u
open CategoryTheory Limits AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Etale

/-- Sheafified derived Hom and Isom between bounded finite constant complexes are the
constant algebraic Hom and Isom sets.

Source: Stacks Project, Tags 09BE and 08FR, and the finite-source argument of
`lem-weil-pbc-finite-ring-derived-local-constancy`, steps 2--7.
(blueprint: lem-weil-pbc-finite-ring-constant-derived-mapping-sheaves)

Proof: Resolve E by a bounded-above finite free complex. Its cone finiteness hypothesis
holds because all terms of E and of finite free complexes are finite sets. Cut the
resolution strictly below the support of G. The discarded tail is orthogonal to G
and to G shifted by -1, so the triangle Hom sequence identifies maps from the finite
truncation with maps from E. Constant sheaves are exact, so the same comparison holds
on every localized etale site. Maps from this bounded finite free constant complex
are locally actual chain maps by Tag 08FR. Each of their finitely many components
locally comes from a module map; on a common refinement a geometric stalk detects
the chain equations. Likewise, Tag 08FR makes equality locally a homotopy, whose
finitely many components become algebraic after refinement. Thus the natural map
from the constant algebraic Hom presheaf to derived Hom is locally surjective and
locally injective. Local representatives for sheafification then give the Hom
isomorphism. An algebraic isomorphism stays invertible under constant sheaves;
conversely a geometric stalk detects invertibility of a constant algebraic map.
The same local representative and uniqueness argument therefore identifies Isom
with the constant subset of algebraic isomorphisms. Empty schemes and an empty
Isom set are allowed; no finite Tor bound is needed. -/
theorem finiteRing_constant_derived_mapping_sheaves
    (U : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Finite B]
    (E G : CochainComplex (ModuleCat.{u + 1} B) ℤ)
    (hE : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n))
    (hG : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    (hEfin : ∀ n : ℤ, Finite (E.X n)) (hGfin : ∀ n : ℤ, Finite (G.X n)) :
    Nonempty
      (((presheafToSheaf U.smallEtaleTopology (Type (u + 1))).obj
        (derivedHomPresheaf B
          (DerivedCategory.Q.obj
            (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E))
          (DerivedCategory.Q.obj
            (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj G)))) ≅
        (constantSheaf U.smallEtaleTopology (Type (u + 1))).obj
          (DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj G)) ∧
    Nonempty
      (((presheafToSheaf U.smallEtaleTopology (Type (u + 1))).obj
        (derivedIsoPresheaf B
          (DerivedCategory.Q.obj
            (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E))
          (DerivedCategory.Q.obj
            (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj G)))) ≅
        (constantSheaf U.smallEtaleTopology (Type (u + 1))).obj
          (DerivedCategory.Q.obj E ≅ DerivedCategory.Q.obj G)) := by sorry

end AlgebraicGeometry.Etale
