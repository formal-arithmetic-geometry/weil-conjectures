/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.ExtensionByZeroAdjunction
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Algebra.Homology.FilteredColimitsTensor
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import Sheaf.AlgebraicGeometry.ModuleStalkFilteredColimit
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import Mathlib.Topology.Sheaves.Stalks

/-! # Colimit of a strict system on increasing opens

Source: Stacks Project, Cohomology, Tag 0D6B, proof of
`lemma-glueing-increasing-union`, the termwise extension-by-zero colimit and stalk display
(blueprint: lem-trf-derived-strict-open-colimit).

Local module sheaves are represented on the localized opens site, identified with modules
on the open subscheme by `Scheme.Modules.overEquiv`. The isomorphisms `e` merely present
the extension-by-zero objects as the values of the functor `D`. Its transported arrows
are characterized degreewise by the normalized adjunction, rather than chosen freely.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.StrictOpenColimit

/-- Termwise application of the recorded normalized extension by zero.
Source: Stacks Project, Tag 0D6B, termwise colimit in the proof
(blueprint: lem-trf-derived-strict-open-colimit). -/
abbrev extension (X : Scheme.{u}) (U : X.Opens) :
    CochainComplex (SheafOfModules.{u} (X.ringCatSheaf.over U)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ :=
  letI := (Scheme.Modules.module_extensionByZero_adjunction X U).1
  (SheafOfModules.extensionByZeroPresheaf.{u} X.ringCatSheaf U ⋙
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapHomologicalComplex (.up ℤ)

/-- The unit of the recorded normalized adjunction, applied termwise.
The adjunction is chosen with the section formula in `module_extensionByZero_adjunction`,
which determines its unit; this is not a choice of an arbitrary comparison map.
Source: Stacks Project, Tags 00A7 and 0D6B, restricted coprojections in the stalk display
(blueprint: lem-trf-derived-strict-open-colimit). -/
def unit (X : Scheme.{u}) (U : X.Opens)
    (K : CochainComplex (SheafOfModules.{u} (X.ringCatSheaf.over U)) ℤ) :
    K ⟶ ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapHomologicalComplex
      (.up ℤ)).obj ((extension X U).obj K) :=
  letI := (Scheme.Modules.module_extensionByZero_adjunction X U).1
  ((Classical.choose (Scheme.Modules.module_extensionByZero_adjunction X U).2).mapHomologicalComplex
    (.up ℤ)).unit.app K

/-- A strict system of local quasi-isomorphisms has a termwise extension-by-zero colimit,
whose restricted coprojections are compatible quasi-isomorphisms and give derived
isomorphisms. A set-sized ordinal is represented by its well-ordered index type `E`.
Strict compatibility of `f` is written sectionwise in every degree, avoiding implicit
identifications between iterated restrictions. No continuity or boundedness is imposed.

Source: Stacks Project, Tag 0D6B, proof of `lemma-glueing-increasing-union`
(blueprint: lem-trf-derived-strict-open-colimit).

Proof (the seven steps of the node):
1. Transpose the restricted unit followed by each f, using
   `lem-weil-pbc-module-extension-by-zero-adjunction`. Naturality of the unit and the
   chain-map identity make the transposes chain maps. Strict composition of f and
   injectivity of the adjunction bijection give strict composition of the transposes.
   Adding identities gives D; e identifies its values with the extensions by zero.
2. `lem-weil-pbc-module-sheaves-colimits-forgetful` supplies the termwise colimits.
   Their differentials are induced by the differentials of D. The equation d² = 0 and
   the universal property for complexes follow after precomposing each coprojection
   (`def-weil-pbc-category-colimit`). This also covers an empty ordinal.
3. If an index a exists, E is filtered. Exactness from
   `lem-pc-module-filtered-colimits-tensor` and
   `src-weil-homology-preserves-exact-colimits` identifies every cohomology sheaf of
   the colimit with the corresponding colimit of cohomology sheaves, in all degrees.
4. `lem-weil-pbc-module-stalk-filtered-colimit` and
   `lem-weil-pbc-module-stalk-exact` identify these stalks with the colimit of the
   cohomologies of the stalk complexes. At x in U a, the extension-by-zero stalk
   identifications identify the tail transitions with f. They are quasi-isomorphisms.
   The same inside-stalk formula and `lem-weil-pbc-module-iso-on-stalks` show the
   normalized units are isomorphisms.
5. Restriction to the tail b ≥ a preserves the colimit: extend a tail cocone at c by
   using its leg at max(a,c) and the transition from c. Strict composition verifies
   the cocone identities; extension and restriction are inverse.
6. On this tail all cohomology transitions are invertible. Their inverses to the
   a-th term form a cocone inverse to its colimit leg. The stalk criterion
   `lem-weil-pbc-module-iso-on-stalks` now makes every s a a quasi-isomorphism
   (`def-pc-quasi-iso-modules`).
7. The cocone equation and the adjunct formula give the asserted strict equality
   for s. Exact restriction (`lem-sc-derived-open-restriction-adjunction-exact`)
   descends to the derived category. Localization inverts s; the usual comparison
   with derived restriction gives the last assertion (`def-weil-abstract-derived-category`,
   `def-pc-derived-category`). Neither negative Hom vanishing nor K-injectivity is used. -/
theorem derived_strict_open_colimit
    (X : Scheme.{u}) (E : Type u) [LinearOrder E] [WellFoundedLT E]
    (U : E → X.Opens) (hU : Monotone U) (_hcover : iSup U = ⊤)
    (I : ∀ a : E, CochainComplex (SheafOfModules.{u} (X.ringCatSheaf.over (U a))) ℤ)
    (f : ∀ (b a : E) (h : b < a), I b ⟶
      ((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (hU h.le))).mapHomologicalComplex (.up ℤ)).obj (I a))
    (_hf : ∀ (b a : E) (h : b < a), QuasiIso (f b a h))
    (_hcomp : ∀ (c b a : E) (hcb : c < b) (hba : b < a) (n : ℤ)
        (V : X.Opens) (hV : V ≤ U c),
      ((f c a (hcb.trans hba)).f n).val.app (Opposite.op (Over.mk (homOfLE hV))) =
        ((f c b hcb).f n).val.app (Opposite.op (Over.mk (homOfLE hV))) ≫
          ((f b a hba).f n).val.app
            (Opposite.op (Over.mk (homOfLE (hV.trans (hU hcb.le))))))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ a : E, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (U a).toScheme.toRingedSpace))] :
    (∀ a : E, IsIso (unit X (U a) (I a))) ∧
      ∃ (D : E ⥤ CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
        (e : ∀ a : E, D.obj a ≅ (extension X (U a)).obj (I a)),
        (∀ (b a : E) (h : b < a) (n : ℤ),
          (Classical.choose (Scheme.Modules.module_extensionByZero_adjunction X (U b)).2).homEquiv
              _ _ (((e b).inv ≫ D.map (homOfLE h.le) ≫ (e a).hom).f n) =
            (f b a h).f n ≫
              (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
                (homOfLE (hU h.le))).map ((unit X (U a) (I a)).f n) ≫
              (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace)
                (homOfLE (hU h.le))).hom.app (((extension X (U a)).obj (I a)).X n)) ∧
        ∃ c : Cocone D, Nonempty (IsColimit c) ∧
          (∀ n : ℤ, Nonempty (IsColimit
            ((HomologicalComplex.eval _ (.up ℤ) n).mapCocone c))) ∧
          ∃ s : ∀ a : E, I a ⟶
              (Functor.mapHomologicalComplex
                (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) (U a))
                (.up ℤ)).obj c.pt,
            (∀ a : E, s a = unit X (U a) (I a) ≫
              (Functor.mapHomologicalComplex
                (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) (U a))
                (.up ℤ)).map ((e a).inv ≫ c.ι.app a)) ∧
            (∀ a : E, QuasiIso (s a)) ∧
            (∀ (b a : E) (h : b < a), s b = f b a h ≫
              ((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
                (homOfLE (hU h.le))).mapHomologicalComplex (.up ℤ)).map (s a) ≫
              (Functor.mapHomologicalComplexCompIso
                (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace)
                  (homOfLE (hU h.le))) (.up ℤ)).hom.app c.pt) ∧
            (∀ a : E, IsIso
              (DerivedCategory.Q.map
                  (((Equivalence.functor
                    (C := SheafOfModules.{u} (X.ringCatSheaf.over (U a)))
                    (D := SheafOfModules.{u} (moduleRings (U a).toScheme.toRingedSpace))
                    (Scheme.Modules.overEquiv (U a))).mapHomologicalComplex (.up ℤ)).map
                      (s a)) ≫
                (schemeOpenRestriction X (U a)).mapDerivedCategoryFactors.inv.app c.pt)) := by
  sorry

end AlgebraicGeometry.StrictOpenColimit
