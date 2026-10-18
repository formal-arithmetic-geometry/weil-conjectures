/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.Paper.LocalizingClosure
public import Sheaf.Paper.ConstantModelTorAmplitude
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.CategoryTheory.SheafTensor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit

import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
/-!
# Existence and thickness of the localizing closure

Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-localizing-closure,
node det-def-localizing-closure-existence, clauses (1)--(3)
(blueprint: det-def-localizing-closure-existence).

Coefficients are arbitrary condensed rings, including noncommutative rings. The
module category is Mathlib's category of internal left modules over the actual
pulled-back ring object. Index sets live in `Type (u + 1)`; the larger universe
of the type of all module objects does not enlarge the required coproduct existence.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The three assertions of the localizing-closure existence lemma.

The termwise cocone assertion specifies both degreewise coproducts and the
coprojections after localization. A sum of triangles is specified by a cocone
whose three vertex cocones are coproducts; its maps therefore are the induced
sums, including the connecting map into the shifted first vertex.

`localizingClosure` is the landed intersection construction. Its localizing
predicate asks for closure under all existing coproducts in the object universe.
Here this agrees with closure under `Type (u + 1)`-indexed coproducts, since the
Hom types live in that universe: an existing larger coproduct has only that
many nonzero summands. The generating class `S` need not be small.

Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-localizing-closure,
node det-def-localizing-closure-existence, clauses (1)--(3)
(blueprint: det-def-localizing-closure-existence).

Proof plan:
1. Identify internal left modules with sectionwise left module sheaves: evaluate
ring multiplication, unit, and actions on pure tensors. Conversely natural
bilinear actions extend uniquely through the sheaf tensor universal property
(lem-pc-sites-sheaf-tensor-bilinear-universal, sk-def-sfb-sheaf-tensor).
These constructions are inverse on objects and on action-compatible maps and
work without commutativity (sk-def-sfb-module-objects).
2. Choose the small site skeleton in the fixed coefficient universe. The
ring-sheaf Grothendieck theorem lem-weil-pbc-ring-sheaves-grothendieck makes this
module category Grothendieck abelian. Apply lem-kun-grothendieck-derived-coproducts:
the termwise coproduct complex, with its actual coprojections, is a coproduct
after localization. Every derived object has a complex representative, so this
also supplies arbitrary derived coproducts, including the empty coproduct.
3. Choose cone representatives of distinguished triangles. Degreewise,
the sum of cones is canonically the cone of the sum of the maps: rebracket
sums of L_i^r plus K_i^(r+1), with differential having blocks d_L, f, 0, -d_K.
This identifies all three arrows, including the negative projection and shift.
Thus the sum is a cone triangle, hence distinguished; transport the original
triangle isomorphisms. The empty family gives the zero cone triangle.
4. Relate the landed closure predicate to the fixed small indexing convention.
Small coproducts are included among object-universe coproducts by universe lift.
For any existing larger coproduct C, each nonzero summand gives a distinct
nonzero coordinate idempotent in End(C), by its injection and projection.
Since End(C) is small, the nonzero summands form a small index type; removing
zero summands expresses C as a small coproduct. Thus closure under small
coproducts is equivalent to closure under all existing object-universe sums.
Every closure condition is inherited pointwise by intersection: zero,
all integer shifts, isomorphisms, two-out-of-three for distinguished triangles,
and small sums. The ambient category is a candidate. Every member of S lies
in the intersection, which is contained in every candidate, proving minimality.
5. If A plus B is in the closure, so is T, the countable sum of copies of
A plus B. Reindex the A-summands by shifting their natural-number indices by
one to obtain A plus T isomorphic to T, fixing all B-summands. The split
triangle T to T plus A to A to T[1] is distinguished by
lem-sbc-biproduct-triangle-distinguished. Its first two vertices are in the
closure, so A is too. Interchange A and B. Retracts give the same direct-summand
condition, hence thickness (pur9-def-thick).
6. If S is contained in S' and S' in Loc(S), minimality gives both inclusions
between Loc(S) and Loc(S'), hence their equality. -/
theorem localizingClosure_exists
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u})
    [HasDerivedCategory.{u + 1}
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))]
    (S : ObjectProperty (DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))) :
    HasCoproducts.{u + 1} (DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) ∧
    (∀ (I : Type (u + 1))
      (K : I → CochainComplex
        (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ),
      ∃ c : Cofan K,
        (∀ n : ℤ, Nonempty (IsColimit
          ((HomologicalComplex.eval _ _ n).mapCocone c))) ∧
        Nonempty (IsColimit (DerivedCategory.Q.mapCocone c))) ∧
    (∀ (I : Type (u + 1))
      (T : I → Triangle (DerivedCategory
        (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))),
      (∀ i : I, T i ∈ distTriang _) →
      ∃ c : Cofan T,
        Nonempty (IsColimit (Triangle.π₁.mapCocone c)) ∧
        Nonempty (IsColimit (Triangle.π₂.mapCocone c)) ∧
        Nonempty (IsColimit (Triangle.π₃.mapCocone c)) ∧
        c.pt ∈ distTriang _) ∧
    IsLocalizingSubcategory (localizingClosure S) ∧
    (S ≤ localizingClosure S) ∧
    (∀ P : ObjectProperty (DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      IsLocalizingSubcategory P → S ≤ P →
        localizingClosure S ≤ P) ∧
    (localizingClosure S).IsStableUnderRetracts ∧
    (∀ S' : ObjectProperty (DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      S ≤ S' → S' ≤ localizingClosure S →
        localizingClosure S' = localizingClosure S) := by
  sorry

end AlgebraicGeometry.ProEtale
