/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonNatural
import Sheaf.AlgebraicGeometry.RightAdjointTensorLocusTriangles
import Sheaf.AlgebraicGeometry.DerivedQCohDirectSumsAux
import Sheaf.AlgebraicGeometry.DerivedTensorRightCoproducts
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-! # Localizing operations on the right-adjoint tensor-comparison locus

Source: Stacks Project, Duality for Schemes, Tag 0A9U,
lemma-compare-with-pullback-flat-proper-noetherian, proof.
(blueprint: lem-sc-right-adjoint-tensor-locus-localizing).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

/-- The counit-pinned comparison locus is closed under isomorphisms, shifts, cones,
retracts and coproducts if the right adjoint preserves coproducts. No assertion that
it contains perfect objects, or that it is the whole category, is made here.
Source: Stacks Project, Tag 0A9U, proof of
lemma-compare-with-pullback-flat-proper-noetherian, first two sentences.
(blueprint: lem-sc-right-adjoint-tensor-locus-localizing).

Proof. The qcqs projection formula supplies the isomorphism pf for every K; its
inverse is pinned by the stated pullback-adjunction equation, hence is unique.
Naturality of the pullback counit, tensor comparison and right-adjoint counit shows
that its mate defines a natural comparison Lf^*(-) tensor c(O_Y) → c(-).
Both functors are exact: K-flat pullback and tensor preserve distinguished triangles,
and the right adjoint of exact derived pushforward is exact by transporting shifts
and triangles across its adjunction. The comparison respects shifts by the same
counit and monoidal coherence identities. Naturality gives closure under object
isomorphisms; shift compatibility gives closure under shifts; applying the comparison
to a distinguished triangle and using two invertible components gives the third
by the morphism-of-triangles lemma. A retract diagram induces a retract diagram of
comparison arrows, and a retract of an invertible arrow is invertible. Finally,
derived pullback preserves coproducts as a left adjoint, K-flat tensor preserves
coproducts, and c preserves them by hsums. Naturality identifies the comparison on
a coproduct with the coproduct of its components under these preservation
isomorphisms, which is invertible if every component is. The inclusion of D_QCoh
creates coproducts: ambient termwise sums have quasi-coherent cohomology. Thus the
same assertion applies to every ambient cofan appearing below and transports to B
along the specified isomorphism. This covers empty coproducts and zero triangles. -/
theorem rightAdjointTensorLocus_localizing
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    [HasCoproducts.{u} (schemeDerivedQCohCategory Y)]
    [HasCoproducts.{u} (schemeDerivedQCohCategory Z)]
    (hRf : ∀ E : schemeDerivedQCohCategory Z,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj))
    (hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)))
    (hTensor : ∀ (K : schemeDerivedQCohCategory Y) (E : schemeDerivedQCohCategory Z),
      schemeDerivedQCohProperty Z (((derivedPullback f).obj K.obj) ⊗ E.obj))
    [Functor.Monoidal (derivedPullback f)]
    (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory Z)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage f) hRf ⊣ c)
    (hsums : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) c) :
    let P : ObjectProperty (schemeDerivedQCohCategory Y) := fun K ↦
      ∃ pf : (schemeDerivedDirectImage f).obj
            (((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
          K.obj ⊗ (schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj,
          pf.inv = (a.homEquiv _ _)
            ((Functor.Monoidal.μIso (derivedPullback f) K.obj
              ((schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj)).inv ≫
              (derivedPullback f).obj K.obj ◁ a.counit.app (c.obj ⟨𝟙_ _, hO⟩).obj) ∧
          IsIso ((adj.homEquiv
            ⟨((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj,
              hTensor K (c.obj ⟨𝟙_ _, hO⟩)⟩ K)
            (ObjectProperty.homMk (pf.hom ≫
              K.obj ◁ (adj.counit.app ⟨𝟙_ _, hO⟩).hom ≫ (ρ_ K.obj).hom)))
    (∀ (A B : schemeDerivedQCohCategory Y), P A → Nonempty (A ≅ B) → P B) ∧
    (∀ (A : schemeDerivedQCohCategory Y) (n : ℤ), P A →
      ∀ (B : schemeDerivedQCohCategory Y), Nonempty (B.obj ≅ A.obj⟦n⟧) → P B) ∧
    (∀ (A B : schemeDerivedQCohCategory Y), P A → P B →
      ∀ (T : Pretriangulated.Triangle (schemeDerivedCategory Y)),
        T ∈ Pretriangulated.distinguishedTriangles →
        Nonempty (T.obj₁ ≅ A.obj) → Nonempty (T.obj₂ ≅ B.obj) →
        ∀ (C : schemeDerivedQCohCategory Y), Nonempty (T.obj₃ ≅ C.obj) → P C) ∧
    (∀ (A B : schemeDerivedQCohCategory Y), P B →
      Nonempty (Retract A.obj B.obj) → P A) ∧
    (∀ (J : Type u) (E : J → schemeDerivedQCohCategory Y),
      ∀ (S : schemeDerivedCategory Y) (ι : ∀ j, (E j).obj ⟶ S),
        IsColimit (Cofan.mk S ι) →
        ∀ (B : schemeDerivedQCohCategory Y), Nonempty (B.obj ≅ S) →
          (∀ j, P (E j)) → P B) := by
  dsimp only
  obtain ⟨τ, hτ⟩ := rightAdjointTensorComparison_natural f hRf hO hTensor a c adj
  have hcriterion (K : schemeDerivedQCohCategory Y) :
      (∃ pf : (schemeDerivedDirectImage f).obj
            (((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
          K.obj ⊗ (schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj,
          pf.inv = (a.homEquiv _ _)
            ((Functor.Monoidal.μIso (derivedPullback f) K.obj
              ((schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj)).inv ≫
              (derivedPullback f).obj K.obj ◁ a.counit.app (c.obj ⟨𝟙_ _, hO⟩).obj) ∧
          IsIso ((adj.homEquiv
            ⟨((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj,
              hTensor K (c.obj ⟨𝟙_ _, hO⟩)⟩ K)
            (ObjectProperty.homMk (pf.hom ≫
              K.obj ◁ (adj.counit.app ⟨𝟙_ _, hO⟩).hom ≫ (ρ_ K.obj).hom)))) ↔
        IsIso (τ.app K) := by
    obtain ⟨pf, hpin, heq⟩ := hτ K
    constructor
    · rintro ⟨pf', hpin', h⟩
      have hpf : pf' = pf := Iso.ext_inv (hpin'.trans hpin.symm)
      subst pf'
      rwa [heq]
    · intro h
      exact ⟨pf, hpin, heq ▸ h⟩
  have hretract (A B : schemeDerivedQCohCategory Y)
      (hB : IsIso (τ.app B)) (r : Retract A.obj B.obj) : IsIso (τ.app A) := by
    let r' : Retract A B :=
      { i := ObjectProperty.homMk r.i
        r := ObjectProperty.homMk r.r
        retract := ObjectProperty.hom_ext _ r.retract }
    exact MorphismProperty.of_retract (P := MorphismProperty.isomorphisms _)
      (τ.retractArrowApp r') hB
  obtain ⟨hshift, hcone⟩ := rightAdjointTensorLocus_triangles f hRf hO hTensor a c adj
  refine ⟨?_, hshift, hcone, ?_, ?_⟩
  · intro A B hA ⟨e⟩
    apply (hcriterion B).mpr
    exact hretract B A ((hcriterion A).mp hA)
      (((schemeDerivedQCohProperty Y).ι.mapIso e).symm.retract)
  · intro A B hB ⟨r⟩
    exact (hcriterion A).mpr (hretract A B ((hcriterion B).mp hB) r)
  · intro J E S ι hc B ⟨e⟩ hE
    let q : Cofan E := Cofan.mk B (fun j ↦ ObjectProperty.homMk (ι j ≫ e.inv))
    have hq : IsColimit q := by
      refine Cofan.IsColimit.mk q
        (fun s ↦ ObjectProperty.homMk (e.hom ≫
          hc.desc (Cofan.mk s.pt.obj (fun j ↦ (s.inj j).hom)))) ?_ ?_
      · intro s j
        apply ObjectProperty.hom_ext _
        simpa [q, Category.assoc] using hc.fac
          (Cofan.mk s.pt.obj (fun j ↦ (s.inj j).hom)) ⟨j⟩
      · intro s m hm
        apply ObjectProperty.hom_ext _
        apply (cancel_epi e.inv).mp
        change e.inv ≫ m.hom = e.inv ≫ e.hom ≫ _
        rw [Iso.inv_hom_id_assoc]
        apply hc.hom_ext
        intro ⟨j⟩
        simpa [q, Category.assoc] using (congrArg (fun φ ↦ φ.hom) (hm j)).trans
          (hc.fac (Cofan.mk s.pt.obj (fun j ↦ (s.inj j).hom)) ⟨j⟩).symm
    let F := (schemeDerivedQCohProperty Z).lift
      ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙
        tensorRight (c.obj ⟨𝟙_ _, hO⟩).obj)
      (fun K ↦ hTensor K (c.obj ⟨𝟙_ _, hO⟩))
    let : PreservesColimitsOfShape (Discrete J)
        (tensorRight (c.obj ⟨𝟙_ _, hO⟩).obj) :=
      derivedTensorRight_preservesCoproducts Z (c.obj ⟨𝟙_ _, hO⟩).obj J
    let : PreservesColimitsOfShape (Discrete J) (derivedPullback f) :=
      a.leftAdjoint_preservesColimits.preservesColimitsOfShape
    let : HasCoproducts.{u} (schemeDerivedCategory Y) := derivedAmbientHasCoproducts Y
    let : (schemeDerivedQCohProperty Y).IsClosedUnderColimitsOfShape (Discrete J) :=
      schemeDerivedQCohClosedUnderCoproducts Y J
    have : PreservesColimitsOfShape (Discrete J)
        (F ⋙ (schemeDerivedQCohProperty Z).ι) := by
      change PreservesColimitsOfShape (Discrete J)
        ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙
          tensorRight (c.obj ⟨𝟙_ _, hO⟩).obj)
      infer_instance
    let : PreservesColimitsOfShape (Discrete J) F :=
      preservesColimitsOfShape_of_reflects_of_preserves F (schemeDerivedQCohProperty Z).ι
    let : PreservesColimitsOfShape (Discrete J) c := hsums J
    have : ∀ j : J, IsIso (τ.app (E j)) := fun j ↦ (hcriterion (E j)).mp (hE j)
    have : ∀ j : Discrete J, IsIso ((Functor.whiskerLeft (Discrete.functor E) τ).app j) :=
      fun j ↦ (hcriterion (E j.as)).mp (hE j.as)
    have : IsIso (Functor.whiskerLeft (Discrete.functor E) τ) :=
      NatIso.isIso_of_isIso_app _
    exact (hcriterion B).mpr
      (isIso_app_coconePt_of_preservesColimit (Discrete.functor E) τ q hq)


end AlgebraicGeometry
