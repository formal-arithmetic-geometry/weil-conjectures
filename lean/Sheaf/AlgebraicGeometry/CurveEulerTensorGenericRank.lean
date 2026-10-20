/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact
import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import Sheaf.AlgebraicGeometry.EulerCharZeroDimSupport
import Sheaf.AlgebraicGeometry.CoherentPropertyDevissage
import Sheaf.AlgebraicGeometry.CoherentFiniteType

/-! # Euler characteristic of an invertible twist on an integral proper curve

Source: Stacks Project, Varieties, Tag 0AYV, `lemma-degree-on-proper-curve`,
the case of an invertible first factor (rank one).
(blueprint: lem-trf-curve-euler-tensor-generic-rank).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Twisting a coherent module on a proper integral curve by an invertible module changes
its Euler characteristic by the generic rank times the degree of the invertible module.
The rank is computed over the generic local ring, which is a field and is canonically
isomorphic to the residue field at `ξ`; thus this is exactly `dim_{κ(ξ)} F_ξ`.

Source: Stacks Project, Varieties, Tag 0AYV, `lemma-degree-on-proper-curve`, with `n = 1`.
(blueprint: lem-trf-curve-euler-tensor-generic-rank).

Proof:
1. The field k is Noetherian and Spec k is quasi-compact and locally Noetherian.
Properness makes C finite type over Spec k, hence Noetherian
(lem-weil-pbc-finite-type-over-noetherian). Its structure module is coherent by
pqf-lem-coherent-ft-locnoeth. Local triviality of L shows that L tensor H is coherent
when H is. Finite generation gives finite-dimensional generic stalks. Define
D(H) = chi(L tensor H) - chi(H) - rank(H) degree(L), and P(H) to mean D(H) = 0.
The zero module has zero tensor, stalk and cohomology, so P(0) holds.
2. Tensoring a coherent short exact sequence by L preserves exactness
(lem-sc-ext-tensor-exact). Apply lem-pc-euler-additive to the original and twisted
sequences to get additivity of both Euler characteristics.
3. Stalk exactness (lem-weil-pbc-module-stalk-exact) gives a short exact sequence of
finite-dimensional generic vector spaces. Extend a basis of the first term using
lifts of a basis of the third. This proves additivity of rank and therefore of D,
so P satisfies two out of three.
4. Every integral closed subscheme Z of C is C or a reduced closed point: dimension
one excludes a chain of two strict irreducible closed inclusions. A closed subscheme
containing the generic point has zero defining ideal on every integral affine open;
an integral singleton is the spectrum of its residue field.
5. For Z = C use O_C. It is coherent, has support C, and its generic stalk is the
one-dimensional field killed by its zero maximal ideal. The tensor unit isomorphism
and def-pc-degree-line-bundle give D(O_C) = 0.
6. For a closed point z use i_* O_z. Coherence and support follow from clause (1) of
lem-weil-pbc-closed-immersion-coherent-equivalence. By
lem-weil-pbc-closed-pushforward-stalks its stalk at z is κ(z), killed by the maximal
ideal and of residue-field dimension one; its generic stalk is zero.
7. The support of this witness has dimension zero. The last clause of
lem-pc-chi-zero-dim-support gives chi(G tensor L) = chi(G). The tensor symmetry
interchanges the factors and cohomology preserves isomorphisms. Since rank(G) = 0,
this proves D(G) = 0.
8. Apply lem-pc-coherent-property-devissage using steps 1, 2-3 and 4-7 for its zero,
two-out-of-three and integral-support witness conditions. Expanding D(F) = 0 yields
the asserted identity, including generic rank zero. -/
theorem eulerChar_tensor_invertible_generic_rank
    (k : Type u) [Field k] (C : Scheme.{u}) [C.Over (Spec (.of k))]
    [IsIntegral C] [IsProper (C ↘ Spec (.of k))]
    (hdim : topologicalKrullDim C = 1)
    (L : C.Modules) [L.IsInvertible]
    (F : C.Modules) (hF : RingedSpace.IsCoherent C.toRingedSpace F)
    (ξ : C) (hξ : closure ({ξ} : Set C) = Set.univ) :
    (L ⊗ F).eulerChar k =
      (Module.finrank (C.presheaf.stalk ξ) (F.presheaf.stalk ξ) : ℤ) * L.degree k +
        F.eulerChar k := by
  sorry

end AlgebraicGeometry.Scheme.Modules
