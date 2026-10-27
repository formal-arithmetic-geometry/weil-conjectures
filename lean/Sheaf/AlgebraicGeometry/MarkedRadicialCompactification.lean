/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q108
-/
module

public import Sheaf.FieldTheory.FieldTower
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.Sober
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.Compactification.Dense
import Sheaf.Compactification.BoundaryRefinement
import Sheaf.AlgebraicGeometry.FiniteInseparableGeometricReduction
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
import WeilConjectures.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Marked compactification and radicial extension of constants

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose X, 2.3, Step 1,
printed p.150; Stacks Project, Tags 04KT and 01S4
(blueprint: lem-sfb-marked-radicial-compactification).

The final lambda is applied to the actual reduction of the constant base change and its
canonical two projections. It only names these expressions within the conclusion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- A dense proper compactification with its closed marking, followed by a finite radicial
extension of constants with geometrically reduced reduction.
Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose X, 2.3, Step 1,
printed p.150; Stacks Project, Tags 04KT and 01S4
(blueprint: lem-sfb-marked-radicial-compactification).

Proof:
1. The affine base Spec k is quasi-compact and quasi-separated
   [lem-weil-pbc-affine-scheme-qcqs]. Apply [sk-thm-nagata-compactification] and unpack
   [sk-def-nagata-sketch-data] to obtain an open immersion j into a proper compactification.
   Scheme-theoretic density implies topological density: on a nonempty open disjoint from
   the image, the structure sheaf would inject into zero, impossible at a nonzero local ring.
2. Put C = closure (j '' Z). Closure in the open image of j agrees with j '' Z, since Z is
   closed. Thus its inverse image is Z. A nonempty open contained in C would meet the dense
   image of j in a nonempty open contained in j '' Z, contradicting nowhere density.
   This also works when Z is empty.
3. A field is Noetherian, as its only ideals are zero and the unit ideal. Finite type over
   Spec k makes the compactification Noetherian [lem-weil-pbc-finite-type-over-noetherian],
   hence it has finitely many components [lem-weil-pbc-noetherian-finitely-many-components].
   Apply [lem-pur-finite-inseparable-geometric-reduction] to get one finite purely inseparable
   e/k making the reduced base change geometrically reduced. In characteristic zero the
   constants map is surjective [def-pc-field-tower], so the extension is trivial.
4. Reduction is a surjective closed immersion and a universal homeomorphism
   [lem-weil-pbc-reduction-universal-homeomorphism]. Properness survives base change and
   closed immersions [lem-weil-pbc-proper-fp-permanence], giving properness and finite type
   over e. As in step 3, this gives Noetherianness and finitely many components of T.
5. Spec e to Spec k is finite, since e is a finite k-module, and universally injective
   [lem-pc-spec-pure-insep-integral-radicial-surjective]. Its base change is finite and
   universally injective [lem-trf-finite-radicial-basechange]. Reduction is finite
   [lem-weil-pbc-closed-immersion-finite] and universally injective. Composition gives
   finiteness and radiciality of the canonical projection t [def-weil-radicial-morphism].
6. The constant base-change projection is a homeomorphism [lem-pc-homeo-pure-insep], as is
   reduction. Therefore t is a homeomorphism. It follows that T is nonempty and the inverse
   image of C is closed with empty interior.
7. A homeomorphism bijects maximal irreducible closed subsets and their unique generic
   points [lem-sc-scheme-sober]. Radiciality gives purely inseparable residue extensions.
8. These residue extensions are finite: locally a finite morphism comes from a finite
   A-algebra B. Tensor with kappa(p) and quotient by the prime corresponding to a point
   over p. The resulting finite-dimensional domain over kappa(p) is a field, since
   multiplication by a nonzero element is injective and hence surjective. Its fraction
   field is kappa(q) by localization and the residue-field definitions
   [def-weil-pbc-localization-at-prime, def-weil-residue-field]. Apply this to the component
   generic points. -/
theorem exists_marked_radicial_compactification
    (k : Type u) [Field k] (X : Scheme.{u}) [Nonempty X]
    (f : X ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Z : Set X) (hZ : IsClosed Z) (hZnd : interior Z = ∅) :
    ∃ (Xbar : Scheme.{u}) (fbar : Xbar ⟶ Spec (.of k)) (j : X ⟶ Xbar),
      IsProper fbar ∧ LocallyOfFiniteType fbar ∧ QuasiCompact fbar ∧
      IsOpenImmersion j ∧ DenseRange j ∧ j ≫ fbar = f ∧
      ∃ C : Set Xbar, IsClosed C ∧ interior C = ∅ ∧ j ⁻¹' C = Z ∧
        C = closure (j '' Z) ∧
        ∃ (e : Type u) (_ : Field e) (_ : Algebra k e),
          Module.Finite k e ∧ IsPurelyInseparable k e ∧
          (ringChar k = 0 → Function.Surjective (algebraMap k e)) ∧
          (fun (T : Scheme.{u}) (b : T ⟶ Spec (.of e)) (t : T ⟶ Xbar) ↦
            Nonempty T ∧ IsProper b ∧ LocallyOfFiniteType b ∧ QuasiCompact b ∧
            GeometricallyReduced b ∧ IsFinite t ∧ IsHomeomorph t.base ∧
            UniversallyInjective t ∧
            Set.BijOn t
              {η : T | ∃ D ∈ irreducibleComponents T, IsGenericPoint η D}
              {η : Xbar | ∃ D ∈ irreducibleComponents Xbar, IsGenericPoint η D} ∧
            (∀ (D : Set T), D ∈ irreducibleComponents T →
              ∀ η : T, IsGenericPoint η D →
                (t.residueFieldMap η).hom.Finite ∧
                (t.residueFieldMap η).hom.IsPurelyInseparable) ∧
            IsClosed (t ⁻¹' C) ∧ interior (t ⁻¹' C) = ∅ ∧
            IsNoetherian Xbar ∧ IsNoetherian T ∧
            (irreducibleComponents Xbar).Finite ∧ (irreducibleComponents T).Finite)
            (pullback fbar (Spec.map (CommRingCat.ofHom (algebraMap k e)))).nilradical.subscheme
            ((pullback fbar (Spec.map (CommRingCat.ofHom (algebraMap k e)))).nilradical.subschemeι ≫
              pullback.snd fbar (Spec.map (CommRingCat.ofHom (algebraMap k e))))
            ((pullback fbar (Spec.map (CommRingCat.ofHom (algebraMap k e)))).nilradical.subschemeι ≫
              pullback.fst fbar (Spec.map (CommRingCat.ofHom (algebraMap k e)))) := by
  sorry

end AlgebraicGeometry
