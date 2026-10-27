/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.AlgebraicGeometry.EtaleSpaceLocallyQuasiFinite
import Sheaf.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Étale monomorphisms of algebraic spaces are open immersions

Source: Stacks Project, spaces-morphisms.tex, Tag 05W5
(lemma-etale-universally-injective-open, monomorphism specialization)
(blueprint: lem-sfb-space-etale-monomorphism-open).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- An étale monomorphism of algebraic spaces is represented by open immersions after
scheme base change.

Source: Stacks Project, spaces-morphisms.tex, Tag 05W5
(lemma-etale-universally-injective-open, monomorphism specialization)
(blueprint: lem-sfb-space-etale-monomorphism-open).

Proof: For a scheme test `T → Y`, form the sheaf fibre product `E := X ×_Y h_T`.
The fibre-product closure theorem makes `E` an algebraic space, and chartwise étale
base-change permanence makes `E → h_T` chartwise étale. Injectivity on sections of
`X → Y` makes this projection a monomorphism; its diagonal is therefore an isomorphism
on every scheme test and hence a closed immersion in the required representable sense.
The locally quasi-finite theorem and separated locally quasi-finite representability
then identify `E` with a scheme `Z` over `T`. The scheme-source chartwise equivalence
makes `Z → T` étale. Injectivity on sections makes it a scheme monomorphism, so the
flat locally finitely presented monomorphism theorem gives an open immersion. Since
`T → Y` was arbitrary, this is precisely the asserted representable open-immersion
condition for every scheme base change.
-/
theorem etale_monomorphism_is_open_immersion
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : IsChartwiseEtale f)
    (hmono : ∀ (T : Over S),
      Function.Injective (fun x : yoneda.obj T ⟶ X.obj.obj => x ≫ f.hom.hom)) :
    ∀ (T : Over S) (y : yoneda.obj T ⟶ Y.obj.obj),
      IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left)
        (Limits.pullback.snd f.hom.hom y) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
