/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import Sheaf.AlgebraicGeometry.NormalScheme
public import Sheaf.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Sheaf.AlgebraicGeometry.EtaleNormalComponents
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.AlgebraicGeometry.Gluing
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Extending a finite etale cover by normalization

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/
lem-fin-normalization-extends-cover.md (blueprint: lem-fin-normalization-extends-cover).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The normalization of `X` in the function field of a connected finite etale cover of a
nonempty normal open `V` restricts to that cover, as an isomorphism over `V`.
The existential integral structure makes `k(P)` available without assuming integrality of
`P`; the algebra structure is constrained to be the one induced by the given cover.

Source: smooth-purity blueprint, unit sk-prop-a1-kummer,
lem-fin-normalization-extends-cover (blueprint: lem-fin-normalization-extends-cover).

Proof plan:
1. The field spectrum is Noetherian. Finite type over it makes `X` Noetherian
   (lem-weil-pbc-finite-type-over-noetherian), and its open `V` is Noetherian
   (lem-weil-pbc-noetherian-open-subscheme-noetherian). The finite cover is proper
   (lem-weil-pbc-finite-proper), hence of finite type (def-weil-proper-morphism), so `P`
   is Noetherian by the same finite-type lemma.
2. Etale.exists_clopen_normal_integral_components (lem-fin-etale-normal-components)
   decomposes `P` into finitely many normal integral clopen pieces. Connectedness,
   including nonemptiness, makes exactly one piece occur, so `P` is integral and normal
   in the sense of def-sbc-normal-dominant-galois.
3. Etale morphisms are open (lem-weil-pbc-etale-morphism-open-map), so the nonempty image
   is dense in the integral `V`, and the generic point maps to the generic point.
   Nonempty affine opens Spec B in `V` have affine inverse images Spec D, finite over B
   (def-weil-finite-integral-morphism). Their fraction fields are k(X) and k(P)
   (lem-sc-integral-function-field-affine-fraction); nonempty open restriction preserves
   the generic stalk (def-weil-open-immersion). Restriction is base change
   (lem-weil-pbc-open-preimage-fibre-product), hence etale
   (lem-weil-pbc-etale-scheme-base-change). Applying
   lem-weil-pbc-etale-algebra-residue-field-separable at the zero primes gives the finite
   separable extension k(P)/k(X), with its induced structural map.
4. Over Spec B, def-fin-normalization-extension gives Spec C, where C is the integral
   closure of B in k(P). Finiteness makes D integral over B
   (lem-weil-pbc-finite-algebra-is-integral), so D is contained in C. Conversely an element
   of C is integral over every local ring of P. Those rings embed in k(P)
   (lem-sc-integral-scheme-stalks-in-function-field) and are integrally closed by step 2;
   hence the element lies in each stalk. The section-gluing theorem
   (lem-sc-function-field-sections-glue) puts it in D. Thus C = D as B-algebras in k(P).
5. The spectrum equivalence (def-weil-affine-spectrum) gives local isomorphisms over
   Spec B. On overlaps both maps induce the same inclusion of each affine target's
   coordinate ring into k(P). Injectivity of generic germs
   (lem-sc-integral-scheme-stalks-in-function-field) makes the ring maps equal.
   Scheme-morphism gluing (lem-weil-pbc-scheme-morphism-gluing) glues these isomorphisms
   and their inverses over V. Finally lem-weil-pbc-open-preimage-fibre-product identifies
   the inverse-image open with the pullback used below. -/
theorem normalizationIn_functionField_extends_cover
    {k : Type u} [Field k] (X : Scheme.{u}) [IsIntegral X]
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (V : X.Opens) [Nonempty V] (hV : IsNormalScheme V.toScheme)
    (P : Scheme.{u}) [ConnectedSpace P] (f : P ⟶ V.toScheme) [IsFinite f] [Etale f] :
    ∃ (_ : IsIntegral P) (_ : Algebra X.functionField P.functionField),
      X.fromSpecOfAlgebraFunctionField P.functionField =
        P.fromSpecFunctionField ≫ f ≫ V.ι ∧
      ∃ e : pullback (X.fromNormalizationIn P.functionField) V.ι ≅ P,
        e.hom ≫ f = pullback.snd (X.fromNormalizationIn P.functionField) V.ι := by
  sorry

end AlgebraicGeometry.Scheme
