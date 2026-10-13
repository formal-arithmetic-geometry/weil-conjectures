/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Sheaf.AlgebraicGeometry.PerfectHomPushPullCocone
public import Sheaf.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
public import Sheaf.AlgebraicGeometry.PerfectHomLocalComparison

/-! # Recognition of a single-open Hom colimit comparison

Source: Stacks Project, perfect.tex Tag 09RE, the open-local comparison in the
Mayer--Vietoris induction; cohomology.tex Tag 08BW.
(blueprint: lem-pc-perfect-hom-open-colimit-local-comparison).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

/-- The canonical group-colimit comparison for Hom into a restricted direct image
has a pinned local Hom presentation. This concerns one compact open, independently
of a Mayer--Vietoris family, a biproduct, or continuity on that open.

Source: Stacks Project, perfect.tex Tag 09RE, the open-local Hom comparison;
cohomology.tex Tag 08BW.
(blueprint: lem-pc-perfect-hom-open-colimit-local-comparison).

Proof:
1. Apply perfect_hom_open_stage_presentation to W with shift zero. It constructs
an open immersion k : Z -> X with image W, a locally finitely presented qcqs
structural map s', and perfect objects P',Q'. It supplies equivalences e_j from
Hom(P,H(F_j)[0]) to the base-changed Hom sets on Z, an apex equivalence b, and
exact compatibility with perfectStageMap and perfectLimitMap. The construction
also handles W empty; it chooses no unpinned representing object.
2. The tail Set.Ici i is nonempty (it contains i) and directed (take an upper bound
of the underlying indices). Thus it is filtered. The forgetful functor from
abelian groups preserves its colimit: start with its standard filtered-colimit
preservation instance at size max u w and shrink the index size to u. The image
of the canonical group-colimit cocone is therefore a colimit cocone in Type.
3. Use Z,k,s',P',Q' and this underlying cocone in PerfectHomLocalComparison.
Compose each e_j and b with ULift.down to remove the row's universe lift. The
source equivalence is the identity. The stage equation is exactly the equation
from step 1. For the pinning equation at a stage element, colimit.iota_desc
identifies the comparison applied to its inclusion with the apex cocone leg;
the apex equation of step 1 then gives perfectLimitMap. These witnesses establish
the asserted presentation, without asserting that the comparison is bijective. -/
theorem perfect_hom_open_colimit_local_comparison
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (X : Scheme.{u}) (s₀ : X ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s₀] [QuasiCompact s₀] [QuasiSeparated s₀]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (W : X.Opens) (hW : IsCompact (W : Set X))
    (Y : Scheme.{u}) (t : Y ⟶ X) [IsOpenImmersion t]
    (ht : W ≤ t.opensRange)
    (s : Y ⟶ Spec (R.obj i)) (hs : s = t ≫ s₀)
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ B : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over B))]
    (P Q : schemeDerivedCategory Y) (hP : Y.IsPerfect P) (hQ : Y.IsPerfect Q)
    (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F)
    (h : PerfectHomPushPullData R c s Q F d) :
    let H := schemeMVDerivedRestriction Y (t ⁻¹ᵁ W) ⋙
      schemeDerivedDirectImage (t ⁻¹ᵁ W).ι
    let T := (preadditiveCoyoneda.obj (Opposite.op P)).shift (0 : ℤ) ⋙
      AddCommGrpCat.uliftFunctor.{u}
    PerfectHomLocalComparison R c i X s₀ W
      (colimit.desc (F ⋙ H ⋙ T) ((H ⋙ T).mapCocone d)) := by sorry

end AlgebraicGeometry
