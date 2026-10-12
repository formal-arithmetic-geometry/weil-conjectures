/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Sheaf.CategoryTheory.Galois.StacksGaloisCategory
public import Mathlib.CategoryTheory.Galois.Equivalence
import Sheaf.CategoryTheory.Galois.StacksGaloisAxioms
import Sheaf.CategoryTheory.Galois.StacksMonoComplement

/-!
# The abstract equivalence theorem for Stacks Galois categories

Source: Stacks Project, Fundamental Groups of Schemes, Proposition 0BN4;
the blueprint, `sec-curve-estimates/sk-prop-h2`
(blueprint: thm-galois-abstract-equivalence).
-/

@[expose] public section

universe w v u

open CategoryTheory

namespace CategoryTheory

/-- Stacks Project, Proposition 0BN4 (blueprint: thm-galois-abstract-equivalence).
A Stacks Galois category is equivalent, through its given functor, to finite discrete
sets with continuous action of its automorphism group. Bundling the finite values in
`FintypeCat` retains their underlying sets and all maps. The hypothesis is on the
underlying set-valued functor, using precisely the Stacks axioms, not Mathlib's
`GaloisCategory` or `FiberFunctor` classes. The topology on `Aut F` is induced from
the product of the discrete groups `Aut (F.obj X)` (Stacks, Section 0BMQ).

Proof (Stacks, Proposition 0BN4):
1. Finiteness comes from `def-galois-category`. By `lem-galois-aut-profinite` and
   `lem-galois-action-continuous` the automorphism actions are continuous; naturality
   makes every `F.map f` equivariant, and functoriality is inherited from `F`.
2. Faithfulness is `lem-galois-axioms` (1).
3. Decompose each object into connected components by `def-galois-category`.
   Exactness identifies its fibre with the disjoint union of their fibres.
   These fibres are nonempty by `lem-galois-axioms` (3) and transitive by
   `lem-galois-transitive`, so their images are exactly the automorphism orbits.
4. Every stable subset is a union of these orbits, hence the fibre of a finite
   subcoproduct. Its inclusion is monic by `lem-galois-axioms` (2).
5. For an equivariant map, its graph is stable in the fibre of the product.
   Realize it by step 4. Projection to the source is a fibre bijection, hence
   an isomorphism by conservativity. The other projection gives the required
   morphism. Together with step 2 this proves full faithfulness.
6. Split a finite continuous action into its orbits. Each is `G/H` for an open
   finite-index stabilizer `H`. Exactness reduces essential surjectivity to these.
7. The product topology supplies finitely many objects whose evaluation kernel
   lies in `H`. Decompose them into connected objects; their common kernel still
   lies in `H`. An empty family gives `H = G`, realized by a final object.
8. For a nonempty family, take a connected component of its product and a Galois
   object `Y` above it using `lem-galois-object-exists`. The maps to each factor
   are epi and fibre-surjective by `lem-galois-axioms` (4) and (2).
9. By `lem-galois-transitive` identify `F(Y)` with `G/U`, with `U` an open
   stabilizer by `lem-galois-action-continuous`. Transitivity of `Aut(Y)` and
   equivariance of its action show that `U` is normal.
10. Normality makes `U` act trivially on `F(Y)`, hence on the surjective images
    in all factors. Thus `U` lies in their common kernel and in `H`.
11. Full faithfulness identifies `Aut(Y)` with `Aut_G(G/U)`, the opposite group
    of `G/U`, acting by right translations. Let `M` correspond to `(H/U)` opposite.
12. The finite colimit `Y/M` exists by `def-galois-category`; exactness identifies
    its fibre with the orbit quotient `(G/U)/(H/U) = G/H`, equivariantly.
    Step 6 proves essential surjectivity; with steps 2 and 5 this is an equivalence.
-/
theorem stacksGalois_functorToContAction_isEquivalence {C : Type u} [Category.{v} C]
    (F : C ⥤ FintypeCat.{w}) (hG : IsStacksGaloisCategory (F ⋙ FintypeCat.incl)) :
    (PreGaloisCategory.functorToContAction F).IsEquivalence := by
  let := hG.hasFiniteLimits
  let := hG.hasFiniteColimits
  let := hG.preservesFiniteLimits
  let := hG.preservesFiniteColimits
  let := hG.reflectsIsomorphisms
  let : Limits.PreservesFiniteLimits F :=
    Limits.preservesFiniteLimits_of_reflects_of_preserves F FintypeCat.incl
  let : Limits.PreservesFiniteColimits F :=
    Limits.preservesFiniteColimits_of_reflects_of_preserves F FintypeCat.incl
  let : F.ReflectsIsomorphisms := reflectsIsomorphisms_of_comp F FintypeCat.incl
  let : PreGaloisCategory C := {
    monoInducesIsoOnDirectSummand := fun i ↦
      stacksGalois_mono_complement (F ⋙ FintypeCat.incl) hG i
    hasQuotientsByFiniteGroups := fun G _ _ ↦ by
      obtain ⟨G', hgroup, hfinite, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
      let := hgroup
      let := hfinite
      let := Fintype.ofFinite G'
      exact Limits.hasColimitsOfShape_of_equivalence e.toSingleObjEquiv.symm }
  let : F.PreservesEpimorphisms := {
    preserves := fun f _ ↦ by
      apply ConcreteCategory.epi_of_surjective
      exact ((stacksGaloisCategory_axioms.{0, 0, w, v, u} (F ⋙ FintypeCat.incl) hG).2.1 f).2.mp
        inferInstance }
  let : PreGaloisCategory.FiberFunctor F := {
    preservesQuotientsByFiniteGroups := fun G _ _ ↦ by
      obtain ⟨G', hgroup, hfinite, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
      let := hgroup
      let := hfinite
      let := Fintype.ofFinite G'
      exact Limits.preservesColimitsOfShape_of_equiv e.toSingleObjEquiv.symm F }
  let : GaloisCategory C := {
    hasFiberFunctor := ⟨F ⋙ FintypeCat.uSwitch.{w, v}, ⟨inferInstance⟩⟩ }
  infer_instance

end CategoryTheory
