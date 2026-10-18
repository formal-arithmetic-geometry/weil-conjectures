/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleFieldLimitDescent
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
public import Mathlib.Algebra.Group.Subgroup.Ker
import Sheaf.FieldTheory.AlgebraicSeparableSmooth
import Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence

/-!
# Fundamental groups and algebraic constant-field limits

Source: Stacks Project, Fundamental Groups, Tag 0BTV (lemma-limit), second assertion,
specialized to the finite intermediate fields of a separable algebraic extension
(blueprint: lem-wf-pi1-algebraic-field-limit).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- Fundamental groups of the constant-field limit are the topological inverse limit of
fundamental groups at the finite intermediate fields.

Source: Stacks Tag 0BTV (lemma-limit), second assertion
(blueprint: lem-wf-pi1-algebraic-field-limit).

The groups are arbitrary small models of the recorded fibre-functor automorphism groups,
using `IsFundamentalGroup`; `toAutContinuousMulEquiv` identifies each with that group.
The finite-field index is the subtype of all finite-dimensional intermediate fields.
The witnesses `τ` are the canonical fibre identifications: their projection equation
specifies their value on every geometric point, and hence determines them uniquely.
The infimum of equalizer subgroups is precisely the subgroup of compatible families;
its topology is the subtype topology from the product. The final equation specifies
all components of the displayed topological group isomorphism.

Proof (the explicit fibre-functor argument for Tag 0BTV):
1. The finite intermediate fields form a nonempty directed set with union L, by
   lem-kun-algebraic-separable-smooth. No normality assumption is needed.
2. By thm-galois-lc-etale the finite-etale and finite-locally-constant fibre functors
   agree. Their evaluation topologies agree: isomorphic objects conjugate evaluations
   by fixed finite-set bijections, and every object has a representative.
3. The projection fibre identifications of lem-galois-pi1-functoriality compose, since
   both composites send a point to its projection to the original cover. Thus the
   transition maps and the maps from G_L are compatible. The latter give a continuous
   homomorphism into the subgroup, since all product coordinates are continuous.
4. If all these coordinates kill g, object descent in
   lem-wf-finite-etale-field-limit-descent supplies a finite-field model of each cover.
   The action on that model is trivial; naturality transports this to the given cover.
   Faithful evaluation of def-galois-fibre-functor gives g = 1.
5. Given a compatible family, descend each cover to E and conjugate the action of its
   E-component by the fibre identification of that model with the given cover.
6. Enlarging E leaves this permutation unchanged, by compatibility and the action
   characterization of lem-galois-pi1-functoriality.
7. Compare two models at a common field. Morphism descent in
   lem-wf-finite-etale-field-limit-descent descends their comparison morphism after
   enlargement. Naturality intertwines the permutations. An isomorphism need not
   descend as an isomorphism for this argument, so the action is independent of models.
8. Descend any morphism between two covers after choosing models at a common field.
   Naturality there gives naturality of the constructed permutations. Their inverses
   are constructed from the inverse family, yielding an automorphism of the fibre functor.
9. On a cover already defined at E the construction has exactly the prescribed action
   of the E-component. This proves surjectivity and the asserted component formula;
   step 4 gives the other inverse identity.
10. For a fixed cover choose one finite-field model. Evaluation of the inverse map is
    a product projection, followed by evaluation at that model and conjugation by a
    fixed finite-set bijection. Each is continuous. The evaluation topology from step 2
    makes the inverse continuous, completing the topological group isomorphism.
-/
theorem fundamentalGroup_algebraicFieldLimit
    {K L : Type u} [Field K] [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    (X₀ : Over (Spec (.of K)))
    [IsSeparated X₀.hom] [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [ConnectedSpace (fieldExtensionBase X₀ L)]
    [∀ E : {E : IntermediateField K L // FiniteDimensional K E},
      ConnectedSpace (fieldExtensionBase X₀ E.val)]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ fieldExtensionBase X₀ L)
    (G_L : Type u) [Group G_L] [TopologicalSpace G_L] [IsTopologicalGroup G_L]
    [CompactSpace G_L] [∀ P, MulAction G_L ((fiber s).obj P)]
    [IsFundamentalGroup (fiber s) G_L]
    (G : {E : IntermediateField K L // FiniteDimensional K E} → Type u)
    [∀ E, Group (G E)] [∀ E, TopologicalSpace (G E)]
    [∀ E, IsTopologicalGroup (G E)] [∀ E, CompactSpace (G E)]
    [∀ E P, MulAction (G E) ((fiber (s ≫ fieldExtensionBaseMap X₀ E.val.val)).obj P)]
    [∀ E, IsFundamentalGroup (fiber (s ≫ fieldExtensionBaseMap X₀ E.val.val)) (G E)] :
    ∃ τ : ∀ (E E' : {E : IntermediateField K L // FiniteDimensional K E}) (h : E.val ≤ E'.val),
        pullback (fieldExtensionBaseMap X₀ (IntermediateField.inclusion h)) ⋙
            fiber (s ≫ fieldExtensionBaseMap X₀ E'.val.val) ≅
          fiber (s ≫ fieldExtensionBaseMap X₀ E.val.val),
      (∀ (E E' : {E : IntermediateField K L // FiniteDimensional K E}) (h : E.val ≤ E'.val)
        (P : (fieldExtensionBase X₀ E.val).FiniteEtale)
        (z : (fiber (s ≫ fieldExtensionBaseMap X₀ E'.val.val)).obj
          ((pullback (fieldExtensionBaseMap X₀ (IntermediateField.inclusion h))).obj P)),
        ((τ E E' h).hom.app P z).left =
          z.left ≫ Limits.pullback.fst P.obj.hom
            (fieldExtensionBaseMap X₀ (IntermediateField.inclusion h))) ∧
      ∃ e : G_L ≃ₜ* ↥(⨅ E, ⨅ E', ⨅ h : E.val ≤ E'.val,
          MonoidHom.eqLocus
            ((fundamentalGroupMap (τ E E' h) (G E') (G E)).comp
              (Pi.evalMonoidHom G E'))
            (Pi.evalMonoidHom G E)),
        ∀ (g : G_L) (E : {E : IntermediateField K L // FiniteDimensional K E}),
          (e g).val E =
            fundamentalGroupMap (pullbackFiberIso (fieldExtensionBaseMap X₀ E.val.val) s)
              G_L (G E) g :=
  sorry

end AlgebraicGeometry.Scheme.FiniteEtale
