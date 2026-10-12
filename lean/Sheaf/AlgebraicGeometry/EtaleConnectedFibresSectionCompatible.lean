/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Sheaf.AlgebraicGeometry.EtaleGeometricFibreConstantSections
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import Sheaf.AlgebraicGeometry.EtaleSetSectionsGeometricGermExt

/-! # Compatibility of sections on connected geometric fibres

Source: Stacks Project, Etale Cohomology, Tag 0A3H, final paragraph.
(blueprint: lem-weil-pbc-etale-connected-fibres-section-compatible).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Every section of an etale inverse image along a morphism with connected
geometric fibres has equal pullbacks along the two Cech projections. The comparisons
are the unit-compatible composition comparisons, evaluated at the terminal etale
object. Flatness and quasi-compactness are not required for this assertion.

Source: Stacks Project, Etale Cohomology, Tag 0A3H, final paragraph.
(blueprint: lem-weil-pbc-etale-connected-fibres-section-compatible).

Proof:
1. For s in S, take the algebraic closure Omega of its residue field and the
   geometric point q : Spec Omega -> S. On U = T times_S Spec Omega, transport
   the section through the composition comparison, using the pullback condition.
   By etaleGeometricFibreConstantSections and connectedness of U, the transported
   section is the constant section of a unique element of the geometric stalk F_q.
2. Put D = T times_S T. On D times_S Spec Omega the two projection restrictions
   are the pullbacks of this same constant section. The naturality clause of
   etaleGeometricFibreConstantSections identifies both with the constant section
   of the same stalk element; associativity of etaleSetInverseImageCompositionUnits
   identifies the iterated pullback comparisons. This does not require the product
   fibre to be connected.
3. Any geometric point of D has image s in S and its algebraically closed field
   contains an embedding of the chosen algebraic closure of kappa(s). Thus it lifts
   to D times_S Spec Omega. Step 2 and etaleSetInverseImageStalkGerm give equal
   germs of the two displayed sections there, and hence at the original geometric
   point. Apply etaleSetSection_ext_of_geometric_germs to obtain their equality.
   Terminal-object identifications are the canonical pullback lifts and projections.
   If S is empty, T and D are empty and the empty sheaf covering gives equality. -/
theorem etaleSet_section_compatible_of_connected_geometricFibres
    {S T : Scheme.{u}} (f : T ⟶ S)
    (hconn : ∀ s : S, ConnectedSpace
      (pullback f
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
            S.fromSpecResidueField s) : Scheme.{u}))
    (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (a : ((Scheme.etaleSetPullback f).obj F).obj.obj
      (op (Scheme.Etale.mk (𝟙 T)))) :
      ((Classical.choose etaleSetInverseImageCompositionUnits.2.2
          S T (pullback f f) f (pullback.fst f f)).hom.app F).hom.app
        (op (Scheme.Etale.mk (𝟙 (pullback f f))))
        (((Scheme.etaleSetPullback (pullback.fst f f)).obj
            ((Scheme.etaleSetPullback f).obj F)).obj.map
          (MorphismProperty.Over.homMk
            (pullback.lift (pullback.fst f f) (𝟙 (pullback f f))
              ((Category.comp_id _).trans (Category.id_comp _).symm))
            (by simp) :
            Scheme.Etale.mk (𝟙 (pullback f f)) ⟶
              (MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst f f)).obj
                (Scheme.Etale.mk (𝟙 T))).op
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst f f)) _
            (T.smallGrothendieckTopology @Etale)
            ((pullback f f).smallGrothendieckTopology @Etale)).unit.app
              ((Scheme.etaleSetPullback f).obj F)).hom.app
            (op (Scheme.Etale.mk (𝟙 T))) a)) =
        Eq.mp (congrArg (fun k : pullback f f ⟶ S ↦
          ((Scheme.etaleSetPullback k).obj F).obj.obj
            (op (Scheme.Etale.mk (𝟙 (pullback f f)))))
          (pullback.condition (f := f) (g := f)).symm)
        (((Classical.choose etaleSetInverseImageCompositionUnits.2.2
            S T (pullback f f) f (pullback.snd f f)).hom.app F).hom.app
          (op (Scheme.Etale.mk (𝟙 (pullback f f))))
          (((Scheme.etaleSetPullback (pullback.snd f f)).obj
              ((Scheme.etaleSetPullback f).obj F)).obj.map
            (MorphismProperty.Over.homMk
              (pullback.lift (pullback.snd f f) (𝟙 (pullback f f))
                ((Category.comp_id _).trans (Category.id_comp _).symm))
              (by simp) :
              Scheme.Etale.mk (𝟙 (pullback f f)) ⟶
                (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd f f)).obj
                  (Scheme.Etale.mk (𝟙 T))).op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd f f)) _
              (T.smallGrothendieckTopology @Etale)
              ((pullback f f).smallGrothendieckTopology @Etale)).unit.app
                ((Scheme.etaleSetPullback f).obj F)).hom.app
              (op (Scheme.Etale.mk (𝟙 T))) a))) := by sorry

end AlgebraicGeometry
