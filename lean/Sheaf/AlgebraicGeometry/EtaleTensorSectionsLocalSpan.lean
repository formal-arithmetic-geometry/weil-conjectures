/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorOpenSectionsNaturality
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Local generation of tensor sections by sections on base opens

Source: Stacks Project, Sheaves, Tags 0095 and 0096, and Descent, Tag 070S (2).
(blueprint: lem-trf-etale-tensor-sections-local-span).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Every tensor-pullback section is locally a linear combination of pullbacks of
sections on base opens. The covering sieve may depend on the section. No target
sheaf or morphism out of the tensor-sections presheaf is involved.

Source: Stacks Project, Sheaves, Tags 0095 and 0096 (the tensor construction of
pullback), and Descent, Tag 070S (2), whose small-site proof is omitted.
(blueprint: lem-trf-etale-tensor-sections-local-span).

Proof: Fix u : V to T and s in Gamma(V,u^*M). The tensor pullback is the
sheafification of O_V tensor over u^{-1}O_T with u^{-1}M. Thus around each
point of V, s is represented by a finite sum of pure tensors. Each of the finitely
many sections of u^{-1}M is, after a further open refinement, the image of some
section m of M on an open W of T. Shrink their neighborhoods simultaneously;
each resulting open A of V maps into every relevant W. The pure tensors are
then functions on A times the pullbacks of these m. The unit equation of the
canonical open comparison identifies its inverse applied to m with the unit
section on W. The normalization of tensorSectionsComp identifies its restriction
along A to W with the unit section for A to T. Consequently s restricted to A
belongs to the displayed span. These A cover V and are etale objects over T.
Generate a sieve by their inclusions. On any further arrow, the restriction of a
generator is the generator given by composition, by the composition law for
etaleTensorSectionsRestriction. Its semilinearity takes a linear combination to
a linear combination with restricted coefficients. Thus every arrow in this
covering sieve has the asserted span membership. For an empty V the empty cover
suffices; zero sections and zero modules give membership of zero in every span. -/
theorem etaleTensorSections_locally_span_open (T : Scheme.{u}) (M : T.Modules)
    (V : T.Etale) (s : Γ((tensorPullback V.hom).obj M, ⊤)) :
    ∃ S : Sieve V, S ∈ T.smallEtaleTopology V ∧
      ∀ (U : T.Etale) (g : U ⟶ V), S g →
        etaleTensorSectionsRestriction M g s ∈
          Submodule.span Γ(U.left, ⊤)
            {t | ∃ (W : T.Opens) (m : Γ(M, W)) (f : U ⟶ Scheme.Etale.mk W.ι),
              etaleTensorSectionsRestriction M f ((tensorOpenSectionIso T M W).inv m) = t} := by
  sorry

end AlgebraicGeometry.Scheme.Modules
