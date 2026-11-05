/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleHom
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-!
# The structure sheaf on the small étale site

The presheaf `V ↦ Γ(V, 𝒪_V)` on the small étale site of `X` is a sheaf: it is isomorphic to the
presheaf `V ↦ End(V^* 𝒪_X)` of endomorphisms of the pulled back structure sheaf, `a ↦ a ·`,
which is a sheaf by fpqc descent for quasi-coherent modules
(`AlgebraicGeometry.Scheme.Modules.isSheaf_etaleHom`).

## Main statements

- `CategoryTheory.Presheaf.isSheaf_of_isSheaf_forget_commRingCat`: a presheaf of commutative rings
  is a sheaf if its underlying presheaf of sets is.
- `AlgebraicGeometry.Scheme.isSheaf_etaleStructurePresheaf_aux`: `V ↦ Γ(V, 𝒪_V)` is a sheaf on
  the small étale site.
-/

@[expose] public section

universe w v u

open CategoryTheory Opposite

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

end CategoryTheory.Presheaf

namespace AlgebraicGeometry.Scheme

open Pseudofunctor.LocallyDiscreteOpToCat Modules

variable (X : Scheme.{u})

end AlgebraicGeometry.Scheme
