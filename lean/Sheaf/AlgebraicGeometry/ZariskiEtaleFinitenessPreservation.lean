/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence

/-!
# Preservation of finite generators and relations by étale extension

Source: Stacks Project, Descent, Tag 05VG, lemma-equivalence-quasi-coherent-properties
(blueprint: lem-sfb-zariski-etale-finiteness-preservation).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Canonical tensor extension carries Zariski finite generators and finite
presentations to étale local finite generators and finite presentations.

Source: Stacks Project, Descent, Tag 05VG, lemma-equivalence-quasi-coherent-properties,
the forward implication for finite type and finite presentation
(blueprint: lem-sfb-zariski-etale-finiteness-preservation).

Proof: choose a Zariski open cover on which F admits a finite generating epimorphism,
respectively a finite free presentation. Tensor extension is a left adjoint, hence
preserves epimorphisms and cokernel presentations, and its structure-module comparison
identifies the images of finite free modules with the same finite free modules on the
étale site. On each open j:V to T, the tensor-section formula and pullback composition
identify the extension of j^*F with the restriction of the extension of F to V_et.
Étale composition and cancellation identify this site with the slice over V. Thus
the extended presentations give the required local data, because the original open
cover is also an étale cover. For finite type no assertion about the kernel is needed;
for finite presentation preservation of the cokernel suffices. The empty scheme and
finite free modules of rank zero are included. The context contains only proofs of
continuity and adjoint existence, so the construction and its properties are
independent of the chosen context. -/
theorem zariskiEtale_finiteness_preservation (T : Scheme.{u})
    (c : ZariskiEtaleModuleContext T) (F : T.Modules) [F.IsQuasicoherent] :
    (F.IsFiniteType → (c.extension.obj F).IsFiniteType) ∧
      (F.IsFinitePresentation → (c.extension.obj F).IsFinitePresentation) := by sorry

end AlgebraicGeometry.Scheme.Modules
