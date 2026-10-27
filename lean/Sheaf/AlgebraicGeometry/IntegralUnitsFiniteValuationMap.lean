/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q151
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Group.Units.Hom
import Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
import Sheaf.AlgebraicGeometry.NagataAffineOpensProjective
import Sheaf.TraceFormula.ReducedSchemeImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.StructureSheaf
import Sheaf.AlgebraicGeometry.ProperReducedGlobalSectionsProduct

/-!
# A finite valuation map on global units of an integral scheme

Source: Stacks Project, Varieties, Tags 04L5 and 04L4, finite boundary valuation map
and its kernel (blueprint: lem-sfb-integral-units-finite-valuation-map).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The global units of an integral scheme locally of finite type over an algebraically
closed field admit a map to a finite product of integers, additive on products, whose
kernel consists exactly of the nonzero constant functions. The scalar map is induced
by the given structure morphism. The finite index set is represented by `Fin n`,
including `Fin 0`; neither separatedness nor quasi-compactness is assumed.

Source: Stacks Project, Varieties, Tags 04L5 and 04L4, restriction to an affine open,
normalization of a projective closure, and the displayed finite valuation map.
(blueprint: lem-sfb-integral-units-finite-valuation-map)

Proof:
1. Choose a nonempty finite-type affine chart U of T. By
   lem-sc-integral-function-field-affine-fraction, sections on nonempty affine opens
   inject into the generic stalk F. The sheaf axiom then makes global sections inject
   into F, hence into sections on U. No separation or compactness of T is needed.
2. Embed U into affine space using lemma-nagata-quasi-affine-immersion-affine-space-exists,
   and take the projective closure C using det-nagata-affine-opens-projective.
   By lem-trf-reduced-scheme-image, C is reduced; density of integral U makes C integral.
3. By lem-sfb-finite-normalization-model-functoriality, normalize C in F to obtain a
   finite surjective normal integral model N. By lem-sc-normalization-exists it is
   proper. The inverse image V of U is nonempty, and global units of T and their
   inverses give rational functions regular on V, with their specified generic germs.
4. Cover C by finitely many nonempty affines using
   lem-weil-pbc-qcqs-finite-affine-open-cover. By def-weil-finite-integral-morphism and
   lem-trf-normalization-affine-stalk-closure, their inverse images cover N by affines
   Spec D_i, with D_i Noetherian integral closures in F. By
   lem-weil-pbc-integral-closure-finite-extension-normal they are normal domains with
   fraction field F.
5. Let J_i consist of height-one primes of D_i outside V. Such a prime is the generic
   point of an irreducible component of N minus V: any smaller prime of that component
   is nonzero, since the generic point of N lies in V, and height one forces equality.
   By lem-sc-noetherian-closed-subset-finite-components and lem-sc-scheme-sober these
   generic points form a finite set. Thus the disjoint union J of the J_i is finite.
6. By lem-trf-normal-domain-principal-divisor-kernel, each chart-prime pair gives a
   normalized integer valuation on F-units, additive on products. Compose with the
   injective generic-germ map on global units. Reindex the finite J by Fin n.
7. If all these valuations vanish, then every height-one valuation on each D_i
   vanishes: outside V this is the assumption, and inside V the function and its
   inverse are regular. Here lem-weil-pbc-spec-domain-stalks-function-field identifies
   stalks with localizations. The principal-divisor kernel lemma makes the function
   a unit on every Spec D_i.
8. These local units and their inverses glue, since their generic germs agree and
   the affine-fraction-field maps are injective. Integral N is reduced and connected.
   By lem-weil-pbc-proper-reduced-algclosed-global-sections-product its global sections
   are K, so the resulting global unit is a nonzero constant.
9. Injectivity of generic germs identifies the original unit on T with that constant.
   Conversely a nonzero constant and its inverse are regular everywhere on N, hence
   every boundary valuation is zero by the valuation unit criterion. This proves
   both kernel inclusions, also when J is empty. -/
theorem exists_integral_units_finite_valuation_map
    (K : Type u) [Field K] [IsAlgClosed K] (T : Scheme.{u}) [IsIntegral T]
    (f : T ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f] :
    ∃ (n : ℕ) (v : Γ(T, ⊤)ˣ → (Fin n → ℤ)),
      (∀ a b : Γ(T, ⊤)ˣ, v (a * b) = v a + v b) ∧
      ∀ a : Γ(T, ⊤)ˣ, v a = 0 ↔
        ∃ c : Kˣ,
          Units.map (((ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom.toMonoidHom) c = a := by
  sorry

end AlgebraicGeometry.Scheme
