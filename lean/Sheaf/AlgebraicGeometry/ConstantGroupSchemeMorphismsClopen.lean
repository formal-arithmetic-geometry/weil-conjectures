/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.ConstantGroupScheme
public import Sheaf.AlgebraicGeometry.CoproductCopiesMorphismsClopen
public import Mathlib.Topology.LocallyConstant.Algebra
import Sheaf.AlgebraicGeometry.ConstantGroupSchemeMultiplication

/-!
# Constant group scheme morphisms and clopen decompositions

Source: Stacks Project, Etale Cohomology, Remark 59.23.2 (Tag 03P5), and Groupoids,
Example 39.5.6 (Tag 03YW)
(blueprint: lem-weil-pbc-constant-group-scheme-morphism-clopen).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

open Classical in
/-- Source: Stacks Project, Remark 59.23.2 (Tag 03P5), Example 39.5.6 (Tag 03YW)
(blueprint: lem-weil-pbc-constant-group-scheme-morphism-clopen).

Step 1: the coproduct components are disjoint open sets covering the constant scheme,
hence closed (lem-weil-pbc-scheme-coproduct-family). The projection on each is the identity.
Step 2: inverse images of these components give a clopen decomposition of the domain.
Step 3: factor the restriction through its component
(lem-weil-pbc-morphism-factors-through-open-subscheme); the equation over the base forces
this factor to be the restricted structure morphism.
Step 4: conversely glue these component maps over any clopen decomposition
(lem-weil-pbc-scheme-morphism-gluing). Empty overlaps give agreement; uniqueness of gluing
forces the base equation and both inverse identities of the decomposition correspondence.
Step 5: assign to each point its unique component label. Open fibres are also closed because
their complements are unions of the other fibres. A quasi-compact domain has a finite
subcover of the fibres, so only finitely many fibres can be nonempty.
Step 6: the canonical point indexed by `e` lies entirely in the `e`-component, and therefore
corresponds to the constant function `e` and the decomposition with only that piece nonempty.
Step 7: on the pair component `(e,e')`, multiplication lands in component `e + e'`
(lem-weil-pbc-constant-group-scheme-multiplication). Thus the label of the sum is the sum
of the labels. Pointwise addition, zero and negation preserve locally constant functions;
transport their abelian group structure across the bijection. The canonical map is additive
because constant functions add pointwise. No step uses etaleness. -/
theorem constantGroupSchemeMorphismsClopen (T U : Scheme.{u}) (E : Type v)
    [Small.{u} E] [AddCommGroup E] (s : U ⟶ T) :
    (∃ b : ConstantGroupSchemePoint T E s ≃
        {P : E → U.Opens // IsClopenDecomposition U E P},
      (∀ f e, ((b f).1 e : Set U) =
        f.1 ⁻¹' constantGroupSchemeComponent T E e) ∧
      (∀ (P : {P : E → U.Opens // IsClopenDecomposition U E P}) (e : E), (P.1 e).ι ≫ (b.symm P).1 =
        ((P.1 e).ι ≫ s) ≫ constantGroupSchemeIncl T E e) ∧
      (∀ (P : {P : E → U.Opens // IsClopenDecomposition U E P}) (e : E), IsClopen (P.1 e : Set U)) ∧
      (∀ P : {P : E → U.Opens // IsClopenDecomposition U E P}, IsCompact (Set.univ : Set U) →
        Set.Finite {e : E | (P.1 e : Set U).Nonempty}) ∧
      (∀ e₀ e, (b (constantGroupSchemeCanonicalMap T E s e₀)).1 e =
        if e = e₀ then ⊤ else ⊥) ∧
      (∀ P : {P : E → U.Opens // IsClopenDecomposition U E P},
        ∃! f : ConstantGroupSchemePoint T E s,
        ∀ e, (P.1 e).ι ≫ f.1 = ((P.1 e).ι ≫ s) ≫ constantGroupSchemeIncl T E e)) ∧
    (∀ φ : U → E,
      (∀ e, IsOpen (φ ⁻¹' {e})) ↔ (∀ e, IsClopen (φ ⁻¹' {e}))) ∧
    (∃ a : AddCommGroup (ConstantGroupSchemePoint T E s),
      letI := a
      (∀ f g : ConstantGroupSchemePoint T E s,
        f + g = constantGroupSchemePointAdd T E s f g) ∧
      ∃ Φ : ConstantGroupSchemePoint T E s ≃+ LocallyConstant U E,
        (∀ f x e, Φ f x = e ↔ f.1 x ∈ constantGroupSchemeComponent T E e) ∧
        (∀ e, Φ (constantGroupSchemeCanonicalMap T E s e) = LocallyConstant.const U e) ∧
        (∀ f g x, Φ (constantGroupSchemePointAdd T E s f g) x = Φ f x + Φ g x) ∧
        ∃ c : E →+ ConstantGroupSchemePoint T E s,
          ∀ e, c e = constantGroupSchemeCanonicalMap T E s e) := by
  sorry

end AlgebraicGeometry
