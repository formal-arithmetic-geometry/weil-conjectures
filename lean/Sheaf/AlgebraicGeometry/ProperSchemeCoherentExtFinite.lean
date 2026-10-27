/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.DerivedGlobalScalar
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.DerivedSectionsPushforwardComparison
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.AffineDerivedSectionsHomologyComparison
import WeilConjectures.AlgebraicGeometry.CoherentAffineSectionsFinite

/-!
# Finite global Ext on a proper scheme

Source: Stacks Project, Derived Categories of Schemes, Tag 0D0D, lemma-ext-finite
(blueprint: lem-sfb-proper-scheme-coherent-ext-finite).
-/

@[expose] public section
set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The structure morphism sends a scalar to its compatible family on all opens.
At `U` this is `A → Γ(Spec A, ⊤) → Γ(X, U)`, using `ΓSpecIso` and `f.appLE`.
Source: Stacks Project, Tag 0D0D, the structure-morphism action on Ext
(blueprint: lem-sfb-proper-scheme-coherent-ext-finite). -/
noncomputable def Scheme.Hom.extScalarSections {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) :
    A →+* RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}) where
  toFun a := ⟨fun U ↦
    (f.appLE ⊤ U.unop (by simp)).hom ((Scheme.ΓSpecIso (.of A)).inv a), by
      intro U V i
      change X.presheaf.map i
        ((f.appLE ⊤ U.unop (by simp)).hom ((Scheme.ΓSpecIso (.of A)).inv a)) = _
      exact ConcreteCategory.congr_hom (f.appLE_map (by simp) i)
        ((Scheme.ΓSpecIso (.of A)).inv a)⟩
  map_one' := Subtype.ext (funext fun U ↦ by simp)
  map_mul' a b := Subtype.ext (funext fun U ↦ by simp)
  map_zero' := Subtype.ext (funext fun U ↦ by simp)
  map_add' a b := Subtype.ext (funext fun U ↦ by simp)

/-- The canonical `A`-module on `Hom(K,E[n])`: restrict the localized sectionwise
scalar action along the structure morphism. No arbitrary action is supplied.
Source: Stacks Project, Tag 0D0D, definition of its Ext modules
(blueprint: lem-sfb-proper-scheme-coherent-ext-finite). -/
@[instance_reducible]
noncomputable def Scheme.Hom.coherentExtModule {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (K E : schemeDerivedCategory X) (n : ℤ) : Module A (K ⟶ E⟦n⟧) :=
  letI : Linear
      (RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.homLinear X.sheaf.obj (moduleRings X.toRingedSpace).property
  Module.compHom (K ⟶ E⟦n⟧) f.extScalarSections

/-- Global Ext between a bounded-above coherent complex and a bounded-below coherent
complex on a proper scheme over a Noetherian ring is finite over that ring, in every
integer degree, with scalars induced by its structure morphism.
Source: Stacks Project, Tag 0D0D (lemma-ext-finite)
(blueprint: lem-sfb-proper-scheme-coherent-ext-finite).

Proof:
1. Spec A is Noetherian (its affine ring is A, and it is quasi-compact).
   Properness implies finite type, so X is Noetherian by
   lem-weil-pbc-finite-type-over-noetherian.
2. Apply lem-sfb-scheme-coherent-derived-internal-hom to obtain bounded-below coherent
   cohomology for G = RHom(K,E), using the two given bounds and local Noetherianity.
3. Apply lem-sfb-proper-scheme-coherent-derived-image to obtain bounded-below coherent
   cohomology for T = Rf_*G on Spec A.
4. At the top open, lem-trf-open-ext-hypercohomology-comparison identifies Ext^n with
   H^n RΓ(X,G). Its naturality in E, applied to a times identity, makes it A-linear.
5. The natural derived-sections/pushforward comparison
   lem-pc-derived-sections-pushforward-comparison identifies this with H^n RΓ(Spec A,T).
   Naturality in G likewise identifies the structure-morphism scalar actions.
6. Coherence implies quasi-coherence by pqf-lem-coherent-ft-locnoeth. Apply
   lem-pc-affine-derived-sections-homology-comparison and ΓSpecIso to identify the last
   module with Γ(Spec A,H^n(T)). It is finite by
   lem-weil-pbc-coherent-affine-sections-finite. Transport finite generators through
   the composite A-linear isomorphism. This works for every integer n. -/
theorem proper_scheme_coherent_ext_finite
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (K E : schemeDerivedCategory X)
    (hK : ∀ i : ℤ, RingedSpace.IsCoherent X.toRingedSpace
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj K))
    (hE : ∀ i : ℤ, RingedSpace.IsCoherent X.toRingedSpace
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E))
    (hK_bound : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj K))
    (hE_bound : ∃ a : ℤ, ∀ i : ℤ, i < a → IsZero
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E))
    (n : ℤ) :
    @Module.Finite A (K ⟶ E⟦n⟧) _ _ (f.coherentExtModule K E n) := by
  sorry

end AlgebraicGeometry
