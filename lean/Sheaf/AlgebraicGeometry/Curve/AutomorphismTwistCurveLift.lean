/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q116
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

import Sheaf.AlgebraicGeometry.CurveBaseChangeRelativeDimensionOne
import WeilConjectures.Topology.PresheafModuleStalkFunctor

/-!
# Automorphism twists of curves and compatible lifts

Source: Stacks Project, Curves, Tag 0CCY, first proof paragraph; Varieties, Tag 0CCG,
the cartesian diagram and its automorphism-base-change refinement
(blueprint: lem-sfb-automorphism-twist-curve-lift).

The twist is the chosen scheme pullback. Both projection equations characterize its
inverse and the unique lift. Function-field maps are the existing generic stalk maps;
the field equivalence below is required to equal the first projection's stalk map.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Twisting a smooth proper integral dimension-one curve by a field automorphism gives
an isomorphic scheme and a smooth proper integral dimension-one curve. Every compatible
homeomorphic endomorphism has a unique morphism over the field to the twist, with the
asserted topology, nonconstancy and functorial generic-stalk pullback.

Source: Stacks Project, Curves, Tag 0CCY, first proof paragraph; Varieties, Tag 0CCG,
cartesian diagram (blueprint: lem-sfb-automorphism-twist-curve-lift).

Proof, following the six steps of the node:
1. Put s = Spec(σ). Functoriality gives its inverse Spec(σ.symm). The pullback
   universal property constructs j = (id_C, a followed by s inverse). Its first
   projection is id_C; the pullback relation shows π followed by j is also
   the identity of the twist. Thus π is an isomorphism with exactly this inverse.
2. Apply lem-sc-curve-base-change-relative-dimension-one to a, first with identity
   base change (identified with C by its projection) and then with s. This gives
   relative dimension one for a and b. Proper base change (lem-pc-proper-base-change)
   gives properness of b, hence separatedness and finite type. The isomorphism π
   identifies affine section rings and irreducible-closed-subset chains, so the twist
   is integral and has dimension one, and is a curve in the sense of def-sc-curves.
3. Compatibility u followed by a = a followed by s gives the universal lift (u,a).
   Its two projections determine it uniquely; the second makes it a morphism over k.
   The first gives v = u followed by j, hence its underlying map is a homeomorphism.
4. Integral schemes have unique generic points by lem-sc-scheme-sober. Homeomorphisms
   preserve the closure of a singleton, hence preserve these points. A factorization
   through a rational point would make the surjective image of v a singleton, which
   contradicts dimension one of the twist.
5. Pullback on generic stalks is induced by pullback of sections and passage to germs
   (def-sc-function-field and def-weil-pbc-module-stalk). Pullback respects composition,
   so v* composed with π* equals u*. The inverse j induces the inverse of π*, giving
   the displayed field equivalence β. A unital map out of a field is injective: if it
   killed nonzero x, applying it to x times its inverse would give 0 = 1.
6. When σ and u are identities, the lift is (id_C,a), the inverse of the canonical
   identity-base-change projection. Its first projection therefore identifies it with
   the identity. All field maps here are ring homomorphisms with no scalar-linearity
   assumption. -/
theorem automorphism_twist_curve_lift
    (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) (a : C ⟶ Spec (.of k))
    [IsCurve a] [Smooth a] [IsProper a] [IsIntegral C]
    (hCdim : topologicalKrullDim C = 1) (σ : k ≃+* k) :
    SmoothOfRelativeDimension 1 a ∧
    SmoothOfRelativeDimension 1 (pullback.snd a (Spec.map (CommRingCat.ofHom σ.toRingHom))) ∧
    IsProper (pullback.snd a (Spec.map (CommRingCat.ofHom σ.toRingHom))) ∧
    IsCurve (pullback.snd a (Spec.map (CommRingCat.ofHom σ.toRingHom))) ∧
    topologicalKrullDim ((pullback a (Spec.map (CommRingCat.ofHom σ.toRingHom))) : Scheme.{u}) = 1 ∧
    ∃ (_ : IsIntegral (pullback a (Spec.map (CommRingCat.ofHom σ.toRingHom)))),
      ∃ e : (pullback a (Spec.map (CommRingCat.ofHom σ.toRingHom))) ≅ C,
        e.hom = (pullback.fst a (Spec.map (CommRingCat.ofHom σ.toRingHom))) ∧
        e.inv ≫ (pullback.fst a (Spec.map (CommRingCat.ofHom σ.toRingHom))) = 𝟙 C ∧
        e.inv ≫ (pullback.snd a (Spec.map (CommRingCat.ofHom σ.toRingHom))) =
          a ≫ Spec.map (CommRingCat.ofHom σ.symm.toRingHom) ∧
        ∃ hπ : (pullback.fst a (Spec.map (CommRingCat.ofHom σ.toRingHom)))
            (genericPoint
              (pullback a (Spec.map (CommRingCat.ofHom σ.toRingHom)) : Scheme.{u})) =
                genericPoint C,
          ∃ β : C.functionField ≃+*
              (pullback a (Spec.map (CommRingCat.ofHom σ.toRingHom)) : Scheme.{u}).functionField,
            β.toRingHom =
              ((pullback.fst a
                (Spec.map (CommRingCat.ofHom σ.toRingHom))).functionFieldMap hπ).hom ∧
            ∀ (u : C ⟶ C), u ≫ a = a ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) →
              IsHomeomorph u →
              ∃ v : C ⟶ pullback a (Spec.map (CommRingCat.ofHom σ.toRingHom)),
                v ≫ pullback.fst a (Spec.map (CommRingCat.ofHom σ.toRingHom)) = u ∧
                v ≫ pullback.snd a (Spec.map (CommRingCat.ofHom σ.toRingHom)) = a ∧
                (∀ w : C ⟶ pullback a (Spec.map (CommRingCat.ofHom σ.toRingHom)),
                  w ≫ pullback.fst a (Spec.map (CommRingCat.ofHom σ.toRingHom)) = u →
                  w ≫ pullback.snd a (Spec.map (CommRingCat.ofHom σ.toRingHom)) = a → w = v) ∧
                IsHomeomorph v ∧
                (¬ ∃ t : Spec (.of k) ⟶ pullback a (Spec.map (CommRingCat.ofHom σ.toRingHom)),
                  t ≫ pullback.snd a (Spec.map (CommRingCat.ofHom σ.toRingHom)) =
                    𝟙 (Spec (.of k)) ∧ a ≫ t = v) ∧
                ∃ hv : v (genericPoint C) = genericPoint
                    (pullback a (Spec.map (CommRingCat.ofHom σ.toRingHom)) : Scheme.{u}),
                  ∃ hu : u (genericPoint C) = genericPoint C,
                    Function.Injective (v.functionFieldMap hv).hom ∧
                    (v.functionFieldMap hv).hom.comp β.toRingHom = (u.functionFieldMap hu).hom ∧
                    (σ = RingEquiv.refl k → u = 𝟙 C →
                      v ≫ pullback.fst a (Spec.map (CommRingCat.ofHom σ.toRingHom)) = 𝟙 C) := by
  sorry

end AlgebraicGeometry
