/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectHomTransport
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.Algebra.Homology.ScalarExtensionHom
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.PerfectImpliesQCoh
import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective

/-! # Comparison of affine sheaf Hom transport with module scalar extension

Source: Stacks Project, perfect.tex, Tag 09RE, affine calculation, using Tags
08EB and 06Z0 for the models and Tag 08DW for pullback.
(blueprint: lem-pc-affine-perfect-hom-presentation).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- A perfect pair on an affine scheme admits a module-derived Hom presentation,
compatible with both finite-stage transport and transport to the limit.
This is a comparison theorem only: it asserts neither bijectivity of the colimit
comparison nor descent of morphisms or homotopies.

Source: Stacks Project, perfect.tex, Tag 09RE, affine part of the proof of
lemma-descend-homomorphisms; Tags 08EB, 06Z0 and 08DW.
(blueprint: lem-pc-affine-perfect-hom-presentation).

Proof: Set J = {j | i ≤ j} with initial stage o = i. Write Y = Spec B using
Y.isoSpec, and form the diagram F(j) = B tensor over R(i) with R(j). Tensor
extension preserves the filtered ring colimit; the colimit of F is therefore
B tensor over R(i) with c.pt. Identify these spectra with the chosen pullbacks
by their universal properties. Perfectness implies quasi-coherent cohomology.
Transport P and Q along this scheme isomorphism using its exact derived
equivalence; the localized-site equivalences preserve their perfectness and
quasi-coherence. The affine bounded-projective criterion supplies bounded
finite-projective models E and K. The initial ring B tensor over R(i) with R(i)
is canonically B, so transport the models through this ring isomorphism.
Their flat terms compute derived scalar extension without
resolutions. The affine quasi-coherent derived equivalence is fully faithful,
and its termwise tilde comparison and derived-pullback tilde comparison give
equivalences between module-derived and sheaf-derived Hom sets at every stage
and at the limit. Take H to be the module-derived Hom diagram on the tail above o,
and d its canonical scalar-extension cocone, whose vertex is the module-derived
Hom at colimit F. Thus ident and e can be the identity equivalences. Chain-map
scalar extension gives the two module compatibility equations. Conjugating by
the tilde and pullback comparisons gives stage and limit. Naturality of tilde
base change and the counit-pinned derived composition comparison identify these
conjugations with perfectStageMap and perfectLimitMap, giving the final two
equations. The identity and composition laws for scalar extension make H a
functor and d a cocone. None of this uses morphism or homotopy descent. For the
zero ring the module and sheaf categories are zero and the same construction
works. The tail is inhabited by o, even if I is otherwise only a preorder. -/
theorem exists_affinePerfectHomPresentation
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Y : Scheme.{u}) [IsAffine Y] (s : Y ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    [∀ A : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
    (P Q : schemeDerivedCategory Y) (hP : Y.IsPerfect P) (hQ : Y.IsPerfect Q) :
    ∃ (F : Set.Ici i ⥤ CommRingCat.{u})
      (E K : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ),
      ((∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n)) ∧
        ∀ n : ℤ, Module.Finite (F.obj ⟨i, le_rfl⟩) (E.X n) ∧
          Module.Projective (F.obj ⟨i, le_rfl⟩) (E.X n)) ∧
      ((∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n)) ∧
        ∀ n : ℤ, Module.Finite (F.obj ⟨i, le_rfl⟩) (K.X n) ∧
          Module.Projective (F.obj ⟨i, le_rfl⟩) (K.X n)) ∧
      ∃ (H : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i) ⥤ Type (u + 1))
        (ident : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i), H.obj j ≃
          (DerivedCategory.Q.obj
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj E) ⟶
           DerivedCategory.Q.obj
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj K)))
        (d : Cocone H)
        (e : d.pt ≃
          (DerivedCategory.Q.obj
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (colimit.ι F ⟨i, le_rfl⟩).hom) (.up ℤ)).obj E) ⟶
           DerivedCategory.Q.obj
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (colimit.ι F ⟨i, le_rfl⟩).hom) (.up ℤ)).obj K)))
        (stage : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i), H.obj j ≃
          ((derivedPullback (pullback.fst s
            (Spec.map (R.map (homOfLE j.val.property))))).obj P ⟶
           (derivedPullback (pullback.fst s
            (Spec.map (R.map (homOfLE j.val.property))))).obj Q))
        (limit : d.pt ≃
          ((derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj P ⟶
           (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj Q)),
        (∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k)
          (f : ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj E) ⟶
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj K)),
          ident k (H.map (homOfLE hjk) ((ident j).symm (DerivedCategory.Q.map f))) =
            DerivedCategory.Q.map (CochainComplex.scalarExtensionHom
              (F.map (homOfLE j.property)).hom (F.map (homOfLE hjk)).hom
              (F.map (homOfLE k.property)).hom
              (congrArg CommRingCat.Hom.hom (F.map_comp
                (homOfLE j.property) (homOfLE hjk))) E K f)) ∧
        (∀ (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i))
          (f : ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj E) ⟶
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj K)),
          e (d.ι.app j ((ident j).symm (DerivedCategory.Q.map f))) =
            DerivedCategory.Q.map (CochainComplex.scalarExtensionHom
              (F.map (homOfLE j.property)).hom (colimit.ι F j.val).hom
              (colimit.ι F ⟨i, le_rfl⟩).hom
              (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE j.property)).symm)
              E K f)) ∧
        (∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k) (f : H.obj j),
          stage k (H.map (homOfLE hjk) f) =
            perfectStageMap R s j.val.property hjk (stage j f)) ∧
        (∀ (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (f : H.obj j),
          limit (d.ι.app j f) = perfectLimitMap R c s j.val.property (stage j f)) := by
  sorry

end AlgebraicGeometry
