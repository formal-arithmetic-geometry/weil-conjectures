/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Sections of etale sheaves under flat maps with connected geometric fibres

Source: Stacks Project, Etale Cohomology, Lemma 59.39.3 (Tag 0A3H)
(blueprint: lem-weil-pbc-etale-sections-flat-qc-connected-fibres).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Pullback induces a bijection on sections of every etale sheaf of sets under a flat,
quasi-compact morphism with connected geometric fibres. Sections upstairs are evaluated
at the base change of the terminal etale object of `S`, which is terminal over `T`.
The map is the unit of the same inverse-image adjunction used in
`etaleSetInverseImageCompositionUnits`.
Source: Stacks Project, Etale Cohomology, Lemma 59.39.3 (Tag 0A3H)
(blueprint: lem-weil-pbc-etale-sections-flat-qc-connected-fibres).

Proof:
1. Every geometric fibre is nonempty by def-weil-connected-scheme. Hence `f` is
   surjective by def-weil-geometric-fibre. Flatness and quasi-compactness give the
   singleton fpqc covering by def-weil-pbc-fpqc-covering: above an affine open of `S`,
   finitely many affine opens cover its quasi-compact inverse image and their images
   cover the original affine open (def-weil-flat-morphism, def-weil-finite-type-morphism).
2. Restrict a section upstairs to the geometric fibre at each point of `S`.
   The inverse-image composition comparisons of
   lem-weil-pbc-sets-etale-inverse-image-composition-units identify the restricted sheaf
   with the constant sheaf of the geometric stalk, by
   lem-weil-pbc-etale-geometric-fibre-constant-sections. Connectedness and nonemptiness
   make the section constant with a unique value. The two projections from the product
   of this fibre with itself pull back this same value, by naturality and the same
   composition comparisons, so the two pullbacks agree on every product fibre.
3. Each geometric point of `T ×_S T` factors through such a product fibre after
   embedding the chosen algebraic closure into its algebraically closed residue field
   (def-weil-geometric-point). By lem-weil-pbc-sets-etale-inverse-image-stalk-germ the
   two sections therefore have equal germs. The geometric-stalk definition and the
   separated sheaf axiom (def-weil-pbc-geometric-stalks,
   def-weil-pbc-etale-sheaf-of-sets) give equality of the sections. Apply
   lem-weil-pbc-etale-sections-fpqc-descent to the singleton covering to descend the
   section uniquely. This gives surjectivity and injectivity of the unit map. -/
theorem etaleSet_sections_bijective_of_flat_qc_connected_geometricFibres
    {S T : Scheme.{u}} (f : T ⟶ S) [Flat f] [QuasiCompact f]
    (hconn : ∀ s : S, ConnectedSpace
      (pullback f
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
            S.fromSpecResidueField s) : Scheme.{u}))
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    Function.Bijective
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
        (S.smallGrothendieckTopology @Etale)
        (T.smallGrothendieckTopology @Etale)).unit.app F).hom.app
          (op (Scheme.Etale.mk (𝟙 S)))) := by
  sorry

end AlgebraicGeometry
