/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactCompositionProjection.CompositionProjectionMate
public import WeilConjectures.SixFunctors.Supporting.SixFunctorOperationDatumStages
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCompositionTowerNormalization
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.ProjectionTriangleAssembly.CartesianCandidateCompositor
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCandidateSiteSquare

/-! # Cartesian compact-support compositor on the origin category

Source: Stacks Project, Tags 0F7J and 0F7K; the compatible Cartesian tower calculation
in the blueprint composition clause (blueprint: lem-sf-cartesian-compact-support-compositor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.AmbientProperOpen
open AlgebraicGeometry.ProEtale.CompactCompositionProjection

namespace AlgebraicGeometry.ProEtale

namespace ProjectionTriangleAssembly

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  towerCandidateComparison originCompositionAmbient alpha candidateCompositor

private theorem naturality
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (a : F ⟶ G) {X Y : C} (f : X ⟶ Y) :
    F.map f ≫ a.app Y = a.app X ≫ G.map f := a.naturality f

private theorem epi_hom
    {C : Type*} [Category C] {X Y : C} (h : X ≅ Y) : Epi h.hom := by
  infer_instance

private theorem epi_map
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (hf : IsIso f) : Epi (F.map f) := by
  have : IsIso f := hf
  infer_instance

private theorem epi_map_map
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) {X Y : C} (h : X ≅ Y) :
    Epi (G.map (F.map h.hom)) := by
  infer_instance

private theorem cancel_boundary_square
    {C : Type*} [Category C] {A₀ A₁ A₂ A₃ B₀ B₁ B₂ Z : C}
    {d : A₀ ⟶ A₁} {s : A₁ ⟶ A₂} {l : A₂ ⟶ A₃}
    {e : A₀ ⟶ B₀} {b : B₀ ⟶ B₁} {t : B₁ ⟶ B₂} {v : B₂ ⟶ Z}
    {p : A₁ ⟶ B₁} {r : A₂ ⟶ B₂} {r' c : A₃ ⟶ Z}
    [hd : Epi d] [hs : Epi s] [hl : Epi l]
    (hp : e ≫ b = d ≫ p) (hr : p ≫ t = s ≫ r)
    (hn : l ≫ r' = r ≫ v) (hc : e ≫ b ≫ t ≫ v = d ≫ s ≫ l ≫ c) : r' = c := by
  apply (cancel_epi l).mp
  apply (cancel_epi s).mp
  apply (cancel_epi d).mp
  rw [hn, ← reassoc_of% hr, ← reassoc_of% hp]
  exact hc

end ProjectionTriangleAssembly

/-- The Cartesian proper/open tower computes the independently specified origin compositor
on its three factor compactifications. This normalization involves no tensor or projection
formula. No separatedness of a structure map is assumed.

Source: Stacks Project, Tag 0F7J, compatible triangle in lemma-shriek-composition;
blueprint fix-prop-projection-formula, composition clause, normalization steps 2--3
(blueprint: lem-sf-cartesian-compact-support-compositor).

Proof:
1. The Cartesian square identifies its clopen lift with the entire pullback. Hence its
   clopen projector is the identity. Transpose the resulting beta under the two proper
   adjunctions. Its further transpose under the open adjunction is the inverse restriction
   exchange followed by inverse open unit: restriction of beta is the identity, and the
   remaining proper unit and counit cancel by the triangle identities.
2. The etale-origin proper/open interchange theorem identifies exactly this open adjunct
   with the site-transported etale proper/open map. This is equality of the specified maps,
   not an inference that an arbitrary adjunct preserves invertibility.
3. Apply finite-site-tower-paste. Its etale tower map is the restriction of the unbounded
   etale compositor by unbounded-compact-support-comparisons. Its pro-etale tower map is
   the raw alpha on the left, by step 2 and the adjunction-normalized proper and open
   compositors. All objects are Noetherian because they lie in Spaces F.
4. Compact-support-site-coherence gives the identical site square for the canonical origin
   compositor. Insert the canonical candidate comparisons on the two inputs and output;
   these are defined from the same site comparisons and etale refinement comparisons.
   Cancel the invertible site boundary. This proves the equality on comparison images of
   bounded-below etale complexes. Naturality and an origin witness extend it to every K.
-/
theorem cartesianCompactSupportCompositor
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X V W Y B Z : Spaces F}
    (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion ((geometry F).map j)] [IsOpenImmersion ((geometry F).map b)]
    [IsOpenImmersion ((geometry F).map i)] [QuasiCompact ((geometry F).map b)]
    [QuasiCompact ((geometry F).map i)]
    [IsProper ((geometry F).map q)] [IsProper ((geometry F).map p)]
    [IsProper ((geometry F).map s)]
    (hb : b ≫ p = q ≫ i)
    (_sq : IsPullback b.hom.left q.hom.left p.hom.left i.hom.left)
    (K : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A)
      X.obj.left).FullSubcategory) :
    (alpha (ordinary F A) j b q p i s hb).app K.obj =
    ProjectionTriangleAssembly.candidateCompositor A
      (f := (j ≫ q).hom.left) (g := (i ≫ s).hom.left)
    (WeilConjectures.sixFunctorFactorCompactification j q
      ‹IsOpenImmersion ((geometry F).map j)› ‹IsProper ((geometry F).map q)›
      (j ≫ q) rfl)
    (WeilConjectures.sixFunctorFactorCompactification i s
      ‹IsOpenImmersion ((geometry F).map i)› ‹IsProper ((geometry F).map s)›
      (i ≫ s) rfl)
    (WeilConjectures.sixFunctorFactorCompactification (j ≫ b) (p ≫ s)
      (mappedCompositeOpen (geo := geometry F) j b)
      (mappedCompositeProper (geo := geometry F) p s) ((j ≫ q) ≫ (i ≫ s)) (by
        simp only [Category.assoc]
        rw [← Category.assoc q i s, ← hb]
        simp only [Category.assoc])) K := by
  let : IsOpenImmersion j.hom.left := ‹IsOpenImmersion ((geometry F).map j)›
  let : IsOpenImmersion b.hom.left := ‹IsOpenImmersion ((geometry F).map b)›
  let : IsOpenImmersion i.hom.left := ‹IsOpenImmersion ((geometry F).map i)›
  let : QuasiCompact b.hom.left := ‹QuasiCompact ((geometry F).map b)›
  let : QuasiCompact i.hom.left := ‹QuasiCompact ((geometry F).map i)›
  let : IsProper q.hom.left := ‹IsProper ((geometry F).map q)›
  let : IsProper p.hom.left := ‹IsProper ((geometry F).map p)›
  let : IsProper s.hom.left := ‹IsProper ((geometry F).map s)›
  let : IsOpenImmersion (j ≫ b).hom.left :=
    mappedCompositeOpen (geo := geometry F) j b
  let : IsProper (p ≫ s).hom.left := mappedCompositeProper (geo := geometry F) p s
  let cf := WeilConjectures.sixFunctorFactorCompactification j q
    ‹IsOpenImmersion ((geometry F).map j)› ‹IsProper ((geometry F).map q)›
    (j ≫ q) rfl
  let cg := WeilConjectures.sixFunctorFactorCompactification i s
    ‹IsOpenImmersion ((geometry F).map i)› ‹IsProper ((geometry F).map s)›
    (i ≫ s) rfl
  let cfg := WeilConjectures.sixFunctorFactorCompactification (j ≫ b) (p ≫ s)
    (mappedCompositeOpen (geo := geometry F) j b)
    (mappedCompositeProper (geo := geometry F) p s) ((j ≫ q) ≫ (i ≫ s)) (by
      simp only [Category.assoc]
      rw [← Category.assoc q i s, ← hb]
      simp only [Category.assoc])
  let a :
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg ⟶
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cfg :=
    alpha (ordinary F A) j b q p i s hb
  change a.app K.obj =
    ProjectionTriangleAssembly.candidateCompositor A cf cg cfg K
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X.obj.left
  let E := Φ.objPreimage K
  let e := Φ.objObjPreimageIso K
  let h : (Φ.obj E).obj ≅ K.obj :=
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X.obj.left).ι.mapIso e
  have hp := FiniteSiteTower.paste A j.hom.left b.hom.left p.hom.left s.hom.left
    i.hom.left q.hom.left _sq E
  have hc := cartesianCandidateSiteSquare F A j b q p i s hb _sq E K e
  have hr := cartesianTowerRestriction F A j b q p i s hb _sq E
  have ht := congrArg DerivedCategory.Plus.ι.map hp.2.1
  simp only [Functor.map_comp] at ht
  have hn := ProjectionTriangleAssembly.naturality a h.hom
  change
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).map
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).map e.hom.hom) ≫
      a.app K.obj = a.app (Φ.obj E).obj ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cfg).map
          e.hom.hom at hn
  have hd : Epi (DerivedCategory.Plus.ι.map
      (FiniteSiteTower.D A j.hom.left s.hom.left i.hom.left q.hom.left E)) :=
    ProjectionTriangleAssembly.epi_map _ _ hp.2.2.2.1
  have hs : Epi
      (CartesianTower.sourceInclusion A j.hom.left q.hom.left i.hom.left s.hom.left
        ((FiniteSiteTower.N A X.obj.left).obj E)).hom :=
    ProjectionTriangleAssembly.epi_hom _
  have hl : Epi
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).map
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).map e.hom.hom)) :=
    ProjectionTriangleAssembly.epi_map_map _ _ h
  set_option maxRecDepth 1024 in
  exact ProjectionTriangleAssembly.cancel_boundary_square
    (C := DerivedCategory (Sheaf (Scheme.ProEt.topology Z.obj.left) (ModuleCat.{u + 1} A)))
    (r := a.app (Φ.obj E).obj) (r' := a.app K.obj)
    (c := ProjectionTriangleAssembly.candidateCompositor A cf cg cfg K)
    (hd := hd) (hs := hs) (hl := hl) ht hr hn hc

end AlgebraicGeometry.ProEtale
