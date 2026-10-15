/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale

/-! # Local lifting along represented epimorphisms on the pro-etale site
Source: Stacks Project, Tags 00WN, 098I and 0990.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- An epimorphism between represented sheaves lifts each represented section locally.
Source: Stacks Project, Tag 00WN, with the small pro-etale site of Tag 098K and
bounded affine weakly contractible refinements of Tags 098I and 0990.
(blueprint: lem-weil-pbc-proetale-representable-epi-local-lifting).

Proof: use the image sieve of the section g under the represented map of mu.
Its membership at f:V→T is exactly the existence of t with t mu=f g. The
sheaf-epimorphism/local-surjectivity criterion says this image sieve is covering;
choose that sieve and read its membership witnesses to obtain the conclusion.

The criterion must be established in the value universe of these representables.
One can use the usual associated-sheaf construction in that universe: on an
arbitrary object first take a small affine open cover, and on each affine fix a
bounded affine weakly contractible pro-etale refinement. On a fixed such compact
projective object every covering is refined by a finite clopen partition: lift
its covering epimorphism to the sheaf coproduct, then use the clopen component
partition and compactness. The partitions of the fixed small scheme form a small
type. Matching families and their refinement colimits are therefore small there;
descent across the fixed covers constructs small associated sheaves on the
original objects. The associated-sheaf adjunction is left exact by the usual
finite-limit argument. Thus the epi/local-surjectivity criterion applies to the
Type-u-valued represented sheaves, without replacing their epi hypothesis by a
larger-universe one. Isomorphisms give the top sieve; empty sources and empty
targets are handled by the same image-sieve argument. -/
theorem representable_epi_local_lifting
    (X : Scheme.{u}) {A B : X.ProEt} (μ : A ⟶ B)
    (hμ : Epi ((topology X).yoneda.map μ)) (T : X.ProEt) (g : T ⟶ B) :
    ∃ S : Sieve T, S ∈ topology X T ∧
      ∀ (V : X.ProEt) (f : V ⟶ T), S f → ∃ t : V ⟶ A, t ≫ μ = f ≫ g := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
