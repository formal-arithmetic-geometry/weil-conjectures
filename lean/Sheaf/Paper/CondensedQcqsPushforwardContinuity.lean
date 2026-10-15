/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.Paper.CondensedQcqsPushforwardLocalComparison
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-!
# Continuity of ordinary condensed-coefficient pushforward

Source: Hemo--Richarz--Scholbach, Constructible sheaves, Lemma 5.3(1)
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-continuity).
-/

@[expose] public section

universe u v w x y z

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj


namespace AlgebraicGeometry.ProEtale

/-- The cocone obtained from good truncation, retaining the original complexes as its
source. Source: Hemo--Richarz--Scholbach, Lemma 5.3(1)
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-continuity). -/
noncomputable def condensedContinuityCocone
    {A : Type v} [Category.{w} A] [Abelian A]
    {I : Type x} [Category.{y} I] (D : I ⥤ CochainComplex A ℤ) (a : ℤ)
    [HasColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A)] : Cocone D :=
  (Cocone.precompose (Functor.whiskerLeft D
    ((ComplexShape.embeddingUpIntGE a).πTruncGENatTrans A))).obj
      (colimit.cocone (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A))

/-- The canonical comparison induced by the maps to the termwise truncated colimit.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(1)
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-continuity). -/
noncomputable def condensedContinuityComparison
    {A : Type v} [Category.{w} A] [Abelian A]
    {B : Type u} [Category.{z} B]
    {I : Type x} [Category.{y} I] (D : I ⥤ CochainComplex A ℤ) (a : ℤ)
    (T : CochainComplex A ℤ ⥤ B)
    [HasColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A)]
    [HasColimit (D ⋙ T)] :
    colimit (D ⋙ T) ⟶ T.obj (condensedContinuityCocone D a).pt :=
  colimit.desc (D ⋙ T) (T.mapCocone (condensedContinuityCocone D a))

/-- Naturality in the strict diagram, including the specified map of truncated colimits.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(1)
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-continuity).
Proof: precompose both sides with each colimit inclusion. Functoriality of good
truncation and naturality of its projection identify the resulting maps. The colimit
universal property gives equality. -/
theorem condensedContinuityComparison_naturality
    {A : Type v} [Category.{w} A] [Abelian A]
    {B : Type u} [Category.{z} B]
    {I : Type x} [Category.{y} I] (D E : I ⥤ CochainComplex A ℤ) (α : D ⟶ E)
    (a : ℤ) (T : CochainComplex A ℤ ⥤ B)
    [HasColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A)]
    [HasColimit (E ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A)]
    [HasColimit (D ⋙ T)] [HasColimit (E ⋙ T)] :
    colimMap (Functor.whiskerRight α T) ≫ condensedContinuityComparison E a T =
      condensedContinuityComparison D a T ≫
        T.map (colimMap (Functor.whiskerRight α
          ((ComplexShape.embeddingUpIntGE a).truncGEFunctor A))) := by
  apply colimit.hom_ext
  intro i
  simp only [condensedContinuityComparison, colimit.ι_desc_assoc]
  rw [colimit.map_desc, colimit.ι_desc]
  dsimp [condensedContinuityCocone]
  rw [← T.map_comp, ← T.map_comp]
  congr 1
  rw [Category.assoc]
  have hnat := ((ComplexShape.embeddingUpIntGE a).πTruncGENatTrans A).naturality
    (α.app i)
  dsimp at hnat
  rw [← Category.assoc, hnat, Category.assoc]
  congr 1
  exact (ι_colimMap
    (Functor.whiskerRight α ((ComplexShape.embeddingUpIntGE a).truncGEFunctor A)) i).symm

/-- The canonical comparison respects natural transformations of the output functor.
Together with the shifted cocone statements below, this specifies the comparison under
the usual derived shift and cohomology identifications.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(1)
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-continuity).
Proof: precompose with every colimit inclusion and use naturality at the corresponding
map to the truncated colimit. The colimit universal property identifies the maps. -/
theorem condensedContinuityComparison_functor_naturality
    {A : Type v} [Category.{w} A] [Abelian A]
    {B : Type u} [Category.{z} B]
    {I : Type x} [Category.{y} I] (D : I ⥤ CochainComplex A ℤ) (a : ℤ)
    (T S : CochainComplex A ℤ ⥤ B) (β : T ⟶ S)
    [HasColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A)]
    [HasColimit (D ⋙ T)] [HasColimit (D ⋙ S)] :
    colimMap (Functor.whiskerLeft D β) ≫ condensedContinuityComparison D a S =
      condensedContinuityComparison D a T ≫ β.app (condensedContinuityCocone D a).pt := by
  apply colimit.hom_ext
  intro i
  simp only [condensedContinuityComparison, colimit.ι_desc_assoc]
  rw [colimit.map_desc, colimit.ι_desc]
  dsimp [condensedContinuityCocone]
  rw [← β.naturality]

/-- Evaluation of the underlying abelian sheaf at the terminal pro-etale object.
Its right derived functor is ordinary uncompleted derived global sections of modules.
Source: Hemo--Richarz--Scholbach, proof of Lemma 5.3(1)
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-continuity). -/
noncomputable abbrev condensedModuleSections
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) (condensedRingObj Λ X) ⥤
      AddCommGrpCat.{u + 1} :=
  Mod.forget (condensedRingObj Λ X) ⋙
    sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} ⋙
      (evaluation X.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj
        (Opposite.op (Scheme.ProEt.mk (𝟙 X)))

private theorem isIso_of_weaklyContractible_sections (X : Scheme.{u})
    {M N : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}} (f : M ⟶ N)
    (hf : ∀ (V : X.ProEt), IsAffine V.left →
      (∀ (F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (g : F ⟶ G),
        Epi g → Function.Surjective (g.hom.app (Opposite.op V))) →
      IsIso (f.hom.app (Opposite.op V))) : IsIso f := by
  have hinj (V : X.ProEtᵒᵖ) : Function.Injective (f.hom.app V) := by
    intro x y hxy
    obtain ⟨I, W, g, hcov, haff, hweak⟩ :=
      Scheme.ProEt.exists_affine_weaklyContractible_covering_family X V.unop
    have hcover : Sieve.ofArrows W g ∈ Scheme.ProEt.topology X V.unop :=
      Precoverage.generate_mem_toGrothendieck hcov
    apply Sheaf.isSeparated M V.unop _ hcover x y
    rintro Z h ⟨_, b, _, ⟨i⟩, rfl⟩
    have := hf (W i) (haff i) (hweak i)
    have hi : Function.Injective (f.hom.app (Opposite.op (W i))) :=
      (AddCommGrpCat.mono_iff_injective _).1 inferInstance
    have heq : M.obj.map (g i).op x = M.obj.map (g i).op y := by
      apply hi
      rw [f.hom.naturality_apply, f.hom.naturality_apply, hxy]
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, heq]
  have hsurj : Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) f.hom := by
    constructor
    intro V x
    obtain ⟨I, W, g, hcov, haff, hweak⟩ :=
      Scheme.ProEt.exists_affine_weaklyContractible_covering_family X V
    apply (Scheme.ProEt.topology X).superset_covering _
      (Precoverage.generate_mem_toGrothendieck hcov)
    rintro Z h ⟨_, b, _, ⟨i⟩, rfl⟩
    have := hf (W i) (haff i) (hweak i)
    have hs : Function.Surjective (f.hom.app (Opposite.op (W i))) :=
      (AddCommGrpCat.epi_iff_surjective _).1 inferInstance
    obtain ⟨y, hy⟩ := hs (N.obj.map (g i).op x)
    refine ⟨M.obj.map b.op y, ?_⟩
    rw [f.hom.naturality_apply, hy, op_comp, Functor.map_comp]
    rfl
  apply (Sheaf.isLocallyBijective_iff_isIso f).1
  exact ⟨(Sheaf.isLocallyInjective_iff_injective f).2 hinj, hsurj⟩


set_option synthInstance.maxHeartbeats 100000 in
-- Colimit inference for the internal module category needs a larger search budget.
set_option synthInstance.maxSize 4096 in
/-- The ordinary uncompleted derived pushforward commutes with uniformly bounded-below
filtered colimits on cohomology. There is no torsion, completeness, or constructibility
condition on the coefficient ring or its modules.

Source: Hemo--Richarz--Scholbach, Lemma 5.3(1)
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-continuity).

Proof: replace each complex by its good truncation at the common lower bound. Exactness
of filtered colimits in module sheaves identifies cohomology of their termwise colimit
with the colimit of cohomology. Cover every object of the target site by affine weakly
contractible objects V. Their inverse images W are qcqs because f is qcqs. Resolve W
by an acyclic hypercover whose terms are finite disjoint unions of weakly contractible
affines. On each component, evaluation is exact and preserves filtered colimits
(lem-weil-pbc-proetale-wcontractible-affine-evaluation-colimits). The hypercover
computes derived sections (lem-weil-pbc-proetale-hypercover-computes-bounded-complex).
In total degree r only the finitely many hypercover degrees 0 through r-a occur.
Evaluation commutes with the filtered colimit in each of these degrees; finite products
and finite sums commute with filtered colimits of modules. Thus the total complexes
are canonically identified, including both differential summands. Exact filtered
colimits then commute with cycles, boundaries and their quotient. On K-injective
resolutions, the formula (f_*J)(V)=J(W) identifies this with precisely the cohomology
comparison induced by the original cocone legs. The comparison is invertible on every
V. A sheaf map invertible on this covering basis is invertible: injectivity follows
from separation and surjectivity follows by lifting locally and gluing. -/
theorem condensed_qcqs_pushforward_continuity
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ X)) ℤ)
    (a : ℤ) (ha : ∀ (i : I) (n : ℤ), n < a → IsZero ((D.obj i).homology n))
    (q : ℤ) :
    IsIso (condensedContinuityComparison D a
      (DerivedCategory.Q ⋙ (CondensedRing.lowerStar Λ f).rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor _ q)) := by
  have : IsIso ((Mod.forget (condensedRingObj Λ Y)).map
      (condensedContinuityComparison D a
        (DerivedCategory.Q ⋙ (CondensedRing.lowerStar Λ f).rightDerivedFunctor ⋙
          DerivedCategory.homologyFunctor _ q))) := by
    apply isIso_of_weaklyContractible_sections Y
    intro V hV hweak
    exact condensed_qcqs_pushforward_local_comparison Λ f D a ha q V hV hweak
  exact isIso_of_reflects_iso _ (Mod.forget (condensedRingObj Λ Y))

set_option synthInstance.maxHeartbeats 100000 in
-- Colimit inference for the internal module category needs a larger search budget.
set_option synthInstance.maxSize 4096 in
/-- Ordinary derived global sections of a qcqs scheme satisfy the same comparison.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(1)
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-continuity).

Proof: apply the finite-diagonal hypercover calculation in the pushforward proof
directly to W=X. Exact evaluation on weakly contractible affines commutes with the
filtered colimit, and a common lower bound makes every total diagonal finite.
Filtered colimits of modules are exact, so taking cohomology gives precisely the
map induced by derived sections of each original cocone leg. Forgetting the scalar
action gives the asserted isomorphism of abelian groups. -/
theorem condensed_qcqs_globalSections_continuity
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ X)) ℤ)
    (a : ℤ) (ha : ∀ (i : I) (n : ℤ), n < a → IsZero ((D.obj i).homology n))
    (q : ℤ) :
    IsIso (condensedContinuityComparison D a
      (DerivedCategory.Q ⋙ (condensedModuleSections Λ X).rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor _ q)) := by
  sorry

private theorem condensedContinuityComparison_isIso_of_iso
    {A : Type v} [Category.{w} A] [Abelian A]
    {B : Type u} [Category.{z} B]
    {I : Type x} [Category.{y} I] [IsConnected I]
    (D : I ⥤ CochainComplex A ℤ) (a : ℤ)
    (T S : CochainComplex A ℤ ⥤ B) (e : T ≅ S)
    [HasColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A)]
    [HasColimit (D ⋙ T)] [HasColimit (D ⋙ S)]
    (h : IsIso (condensedContinuityComparison D a S)) :
    IsIso (colimMap ((T.mapCocone (condensedContinuityCocone D a)).ι)) := by
  have := h
  have hf := condensedContinuityComparison_functor_naturality D a T S e.hom
  have : IsIso (condensedContinuityComparison D a T ≫
      e.hom.app (condensedContinuityCocone D a).pt) := by
    rw [← hf]
    infer_instance
  have ht : IsIso (condensedContinuityComparison D a T) :=
    IsIso.of_isIso_comp_right _ (e.hom.app (condensedContinuityCocone D a).pt)
  have hc : IsColimit (T.mapCocone (condensedContinuityCocone D a)) :=
    IsColimit.ofPointIso (colimit.isColimit (D ⋙ T)) (i := ht)
  exact hc.isIso_colimMap_ι

private noncomputable def condensedContinuityShiftIso
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type u} [Category.{z} B] [Abelian B] [HasDerivedCategory.{z} B]
    (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ] (s q : ℤ) :
    shiftFunctor _ s ⋙ (DerivedCategory.Q ⋙ F ⋙ DerivedCategory.homologyFunctor B q) ≅
      DerivedCategory.Q ⋙ F ⋙ DerivedCategory.homologyFunctor B (s + q) :=
  Functor.isoWhiskerRight ((DerivedCategory.Q ⋙ F).commShiftIso s)
      (DerivedCategory.homologyFunctor B q) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Q ⋙ F)
      ((DerivedCategory.homologyFunctor B 0).shiftIso s q (s + q) rfl)

set_option synthInstance.maxHeartbeats 100000 in
-- Colimit inference for the internal module category needs a larger search budget.
set_option synthInstance.maxSize 4096 in
/-- Compatibility of pushforward continuity with every integral shift. The shifted
cocone has exactly the shifts of the original cocone legs; its vertex is the shift of
Q(colim τ≥a D). Under the standard shift comparisons its universal colimit map is thus
the shifted original comparison, with lower bound a-s and cohomology degree q+s.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(1)
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-continuity-shift-colimMap).
Proof: commutation of Q and the right derived functor with shifts, followed by
the homology shift isomorphism, identifies the shifted output functor with the
unshifted output functor in degree s+q. Naturality of the continuity comparison
transports invertibility from the unshifted theorem. Its mapped cocone is therefore
colimiting. Since the filtered indexing category is connected, colimMap of the
cocone legs is an isomorphism. -/
theorem condensed_qcqs_pushforward_continuity_shift_colimMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ X)) ℤ)
    (a : ℤ) (ha : ∀ (i : I) (n : ℤ), n < a → IsZero ((D.obj i).homology n))
    (s q : ℤ) :
    IsIso (colimMap (((DerivedCategory.Q ⋙ (CondensedRing.lowerStar Λ f).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor _ q).mapCocone
        ((shiftFunctor _ s).mapCocone (condensedContinuityCocone D a))).ι)) := by
  let _ : IsConnected I := IsFiltered.isConnected I
  exact condensedContinuityComparison_isIso_of_iso D a _ _
    (condensedContinuityShiftIso (CondensedRing.lowerStar Λ f).rightDerivedFunctor s q)
    (condensed_qcqs_pushforward_continuity Λ f D a ha (s + q))

set_option synthInstance.maxHeartbeats 100000 in
-- Needed for colimit inference in the internal module category.
set_option synthInstance.maxSize 4096 in
theorem condensed_qcqs_pushforward_continuity_shift
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ X)) ℤ)
    (a : ℤ) (ha : ∀ (i : I) (n : ℤ), n < a → IsZero ((D.obj i).homology n))
    (s q : ℤ) :
    Nonempty (IsColimit ((DerivedCategory.Q ⋙ (CondensedRing.lowerStar Λ f).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor _ q).mapCocone
        ((shiftFunctor _ s).mapCocone (condensedContinuityCocone D a)))) := by
  let _ : IsConnected I := IsFiltered.isConnected I
  apply (Cocone.isColimit_iff_isIso_colimMap_ι _).2
  exact condensed_qcqs_pushforward_continuity_shift_colimMap Λ f D a ha s q

set_option synthInstance.maxHeartbeats 100000 in
-- Colimit inference for the internal module category needs a larger search budget.
set_option synthInstance.maxSize 4096 in
/-- Compatibility of derived global sections continuity with every integral shift. The shifted
cocone has exactly the shifts of the original cocone legs; its vertex is the shift of
Q(colim τ≥a D). Under the standard shift comparisons its universal colimit map is thus
the shifted original comparison, with lower bound a-s and cohomology degree q+s.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(1)
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-continuity-global-shift-colimMap).
Proof: commutation of Q and the right derived functor with shifts, followed by
the homology shift isomorphism, identifies the shifted output functor with the
unshifted output functor in degree s+q. Naturality of the continuity comparison
transports invertibility from the unshifted theorem. Its mapped cocone is therefore
colimiting. Since the filtered indexing category is connected, colimMap of the
cocone legs is an isomorphism. -/
theorem condensed_qcqs_globalSections_continuity_shift_colimMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ X)) ℤ)
    (a : ℤ) (ha : ∀ (i : I) (n : ℤ), n < a → IsZero ((D.obj i).homology n))
    (s q : ℤ) :
    IsIso (colimMap (((DerivedCategory.Q ⋙ (condensedModuleSections Λ X).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor _ q).mapCocone
        ((shiftFunctor _ s).mapCocone (condensedContinuityCocone D a))).ι)) := by
  let _ : IsConnected I := IsFiltered.isConnected I
  exact condensedContinuityComparison_isIso_of_iso D a _ _
    (condensedContinuityShiftIso (condensedModuleSections Λ X).rightDerivedFunctor s q)
    (condensed_qcqs_globalSections_continuity Λ X D a ha (s + q))

set_option synthInstance.maxHeartbeats 100000 in
-- Needed for colimit inference in the internal module category.
set_option synthInstance.maxSize 4096 in
theorem condensed_qcqs_globalSections_continuity_shift
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ X)) ℤ)
    (a : ℤ) (ha : ∀ (i : I) (n : ℤ), n < a → IsZero ((D.obj i).homology n))
    (s q : ℤ) :
    Nonempty (IsColimit ((DerivedCategory.Q ⋙ (condensedModuleSections Λ X).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor _ q).mapCocone
        ((shiftFunctor _ s).mapCocone (condensedContinuityCocone D a)))) := by
  let _ : IsConnected I := IsFiltered.isConnected I
  apply (Cocone.isColimit_iff_isIso_colimMap_ι _).2
  exact condensed_qcqs_globalSections_continuity_shift_colimMap Λ X D a ha s q

/-- The representative comparison induces the canonical isomorphism on each homology object.
Source: Hemo--Richarz--Scholbach, Constructible sheaves, Lemma 5.3(1), representative
comparison step.
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-continuity-representatives-homology)

Proof: apply the homology functor to the leg equation, transport along the componentwise
isomorphism `e`, and identify the target using `ε`. Naturality and the colimit universal
property identify the resulting map with the canonical continuity comparison, which is an
isomorphism by the hypothesis `h`. Exact colimits commute with complex homology;
cancel this invertible homology-colimit comparison and the isomorphism induced by `e`
to obtain the asserted homology map. This is the homology-level statement used to prove
the representative quasi-isomorphism below.
-/
theorem condensedContinuityComparison_representatives_homology
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type u} [Category.{z} B] [Abelian B] [HasDerivedCategory.{z} B]
    {I : Type x} [Category.{y} I] [IsFiltered I]
    [HasColimitsOfShape I B] [HasExactColimitsOfShape I B]
    (D : I ⥤ CochainComplex A ℤ) (a : ℤ)
    [HasColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A)]
    (F : DerivedCategory A ⥤ DerivedCategory B)
    [∀ q : ℤ, HasColimit (D ⋙ (DerivedCategory.Q ⋙ F ⋙
      DerivedCategory.homologyFunctor B q))]
    (h : ∀ q : ℤ, IsIso (condensedContinuityComparison D a
      (DerivedCategory.Q ⋙ F ⋙ DerivedCategory.homologyFunctor B q)))
    (P : I ⥤ CochainComplex B ℤ) [HasColimit P] (L : CochainComplex B ℤ)
    (e : D ⋙ DerivedCategory.Q ⋙ F ≅ P ⋙ DerivedCategory.Q)
    (ε : F.obj (DerivedCategory.Q.obj (condensedContinuityCocone D a).pt) ≅
      DerivedCategory.Q.obj L)
    (ι : P ⟶ (Functor.const I).obj L)
    (hι : ∀ i : I, e.hom.app i ≫ DerivedCategory.Q.map (ι.app i) =
      F.map (DerivedCategory.Q.map ((condensedContinuityCocone D a).ι.app i)) ≫ ε.hom) :
    ∀ q : ℤ, IsIso (HomologicalComplex.homologyMap (colimit.desc P (Cocone.mk L ι)) q) := by
  intro q
  let H := HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) q
  let H' := DerivedCategory.homologyFunctor B q
  let e' : D ⋙ (DerivedCategory.Q ⋙ F ⋙ H') ≅ P ⋙ H :=
    Functor.isoWhiskerRight e H' ≪≫
      Functor.isoWhiskerLeft P (DerivedCategory.homologyFunctorFactors B q)
  let ε' : H'.obj (F.obj (DerivedCategory.Q.obj (condensedContinuityCocone D a).pt)) ≅
      H.obj L :=
    H'.mapIso ε ≪≫ (DerivedCategory.homologyFunctorFactors B q).app L
  let k := colimit.desc P (Cocone.mk L ι)
  have hk : colimMap e'.hom ≫ colimit.post P H ≫ H.map k =
      condensedContinuityComparison D a (DerivedCategory.Q ⋙ F ⋙ H') ≫ ε'.hom := by
    apply colimit.hom_ext
    intro i
    simp only [ι_colimMap_assoc, colimit.ι_post_assoc, ← H.map_comp,
      condensedContinuityComparison, colimit.ι_desc_assoc]
    rw [show colimit.ι P i ≫ k = ι.app i from colimit.ι_desc _ i]
    dsimp only [e', ε', Iso.trans_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      NatTrans.comp_app, Functor.mapIso_hom, H, H']
    simp only [Category.assoc]
    change H'.map (e.hom.app i) ≫
      (DerivedCategory.homologyFunctorFactors B q).hom.app (P.obj i) ≫
        HomologicalComplex.homologyMap (ι.app i) q =
      H'.map (F.map (DerivedCategory.Q.map
        ((condensedContinuityCocone D a).ι.app i))) ≫ H'.map ε.hom ≫
          (DerivedCategory.homologyFunctorFactors B q).hom.app L
    rw [← DerivedCategory.homologyFunctorFactors_hom_naturality,
      ← Category.assoc, ← Functor.map_comp, hι i, Functor.map_comp, Category.assoc]
    rfl
  have := h q
  have : IsIso (colimMap e'.hom ≫ colimit.post P H ≫ H.map k) := by
    rw [hk]
    infer_instance
  have : IsIso (colimit.post P H ≫ H.map k) :=
    IsIso.of_isIso_comp_left (colimMap e'.hom) _
  exact IsIso.of_isIso_comp_left (colimit.post P H) (H.map k)

/-- The representative form of continuity, independent of the choice of functorial
quasi-isomorphic representatives. The equation on each leg requires the specified
canonical derived map, rather than an arbitrary map of representatives.

Source: Hemo--Richarz--Scholbach, Lemma 5.3(1), hypercover proof
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-continuity).

Proof: exact filtered colimits in B commute with kernels, images, and cokernels,
so cohomology of the termwise colimit P is the colimit of its cohomology.
The natural isomorphism e identifies each term with F(QD_i), and ε identifies the
value at the truncated colimit. The leg equation identifies the cohomology map of
the displayed chain map with precisely the continuity comparison. It is an
isomorphism in every degree by h. Thus the chain map is a quasi-isomorphism.
The argument quantifies over all choices of P,L,e,ε and the normalized cocone, so
objectwise quasi-isomorphic replacements give the same derived comparison under
these identifications. Apply this with F equal to derived pushforward, or to derived
module sections, and h the corresponding continuity theorem above. -/
theorem condensedContinuityComparison_representatives
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type u} [Category.{z} B] [Abelian B] [HasDerivedCategory.{z} B]
    {I : Type x} [Category.{y} I] [IsFiltered I]
    [HasColimitsOfShape I B] [HasExactColimitsOfShape I B]
    (D : I ⥤ CochainComplex A ℤ) (a : ℤ)
    [HasColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A)]
    (F : DerivedCategory A ⥤ DerivedCategory B)
    [∀ q : ℤ, HasColimit (D ⋙ (DerivedCategory.Q ⋙ F ⋙
      DerivedCategory.homologyFunctor B q))]
    (h : ∀ q : ℤ, IsIso (condensedContinuityComparison D a
      (DerivedCategory.Q ⋙ F ⋙ DerivedCategory.homologyFunctor B q)))
    (P : I ⥤ CochainComplex B ℤ) [HasColimit P] (L : CochainComplex B ℤ)
    (e : D ⋙ DerivedCategory.Q ⋙ F ≅ P ⋙ DerivedCategory.Q)
    (ε : F.obj (DerivedCategory.Q.obj (condensedContinuityCocone D a).pt) ≅
      DerivedCategory.Q.obj L)
    (ι : P ⟶ (Functor.const I).obj L)
    (hι : ∀ i : I, e.hom.app i ≫ DerivedCategory.Q.map (ι.app i) =
      F.map (DerivedCategory.Q.map ((condensedContinuityCocone D a).ι.app i)) ≫ ε.hom) :
    QuasiIso (colimit.desc P (Cocone.mk L ι)) := by
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact condensedContinuityComparison_representatives_homology D a F h P L e ε ι hι q

end AlgebraicGeometry.ProEtale
