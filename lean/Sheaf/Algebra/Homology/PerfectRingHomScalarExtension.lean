/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap
import Sheaf.Algebra.Homology.FiniteProjectiveRingHomExtension
import Sheaf.Algebra.Homology.BoundedRingHomExtensionDegree

/-! # Scalar extension of a Hom complex with bounded finite-projective source

Source: Stacks Project, more-algebra.tex, lemma-base-change-RHom, clause (1).
(blueprint: lem-pc-perfect-ring-hom-scalar-extension)
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The normalized scalar-extension map on Hom complexes is a chain isomorphism when
its source argument is bounded finite projective. The target argument need not be K-flat.

Source: Stacks Project, more-algebra.tex, equation-base-change-RHom and
lemma-base-change-RHom, clause (1)
(blueprint: lem-pc-perfect-ring-hom-scalar-extension).

Proof: evaluate at the unique object of the one-object site. Sheafification for the
bottom topology and restriction to the slice identify sheaf scalar extension and
internal Hom with scalar extension and Hom of ordinary modules. For a finite free
module A^r the map `B ⊗ Hom(A^r,M) → Hom(B^r,B ⊗ M)` is the finite-coordinate
isomorphism. A finite projective module is a direct summand of A^r; tensoring its
splitting and applying Hom on both sides restricts that isomorphism and its inverse
to the desired summands. In degree n, all the factors outside the bounded support of
P vanish, so the product defining `Hom(P,Q)^n` is a finite product. Tensor commutes
with this finite product, giving the degreewise isomorphism to the product of
`Hom(B ⊗ P^p,B ⊗ Q^(p+n))`. Each component sends
`b ⊗ f` to the function `c ⊗ x ↦ bc ⊗ f(x)`; hence `homMap_pure`, generation by pure
tensors, and the product projections identify it with `(d.homMap P Q).f n`.
Thus each component of the already constructed chain map is invertible, which
makes the chain map an isomorphism. The degreewise inverses commute with the
differentials by the chain-map equation, so they constitute its inverse. -/
theorem perfectRingHom_scalarExtension_isIso
    {A B : Type u} [CommRing A] [CommRing B] {φ : A →+* B}
    [HasDerivedCategory.{w} (RingSiteModules A)]
    [HasDerivedCategory.{w} (RingSiteModules B)]
    (d : RingRHomBaseChangeData φ) (P Q : CochainComplex (RingSiteModules A) ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hp : ∀ n : ℤ, Module.Projective A ((P.X n).val.obj (op ⟨PUnit.unit⟩)))
    (hf : ∀ n : ℤ, Module.Finite A ((P.X n).val.obj (op ⟨PUnit.unit⟩))) :
    IsIso (d.homMap P Q) := by
  have hcomponents : ∀ n : ℤ, IsIso ((d.homMap P Q).f n) := by
    intro n
    apply boundedRingHom_extension_degree_isIso φ d.extension d.objects d.additive P Q n hb
    · intro p
      exact finiteProjectiveRingHom_extension_exists φ d.extension d.objects
        (P.X p) (Q.X (p + n)) (hp p) (hf p)
    · exact d.homMap_pure P Q n
  exact HomologicalComplex.Hom.isIso_of_components (d.homMap P Q)

end CategoryTheory
