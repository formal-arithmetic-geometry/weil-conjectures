/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits

import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleFpDirectedApproximation
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian

/-! # Finite-type quasi-coherent submodules exhaust a module

Source: Stacks Project, Limits of Algebraic Spaces, Tag 0829,
lemma-directed-colimit-finite-type
(blueprint: lem-sfb-space-qcoh-finite-type-union).

The indexing poset contains all finite-type quasi-coherent subobjects in the
universe of subobjects. Its diagram uses the canonical inclusions. The colimit
assertion specifies these inclusions into the original module, so it identifies
the canonical colimit comparison rather than an unrelated isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The inclusion-ordered set of all finite-type quasi-coherent submodules of M.
Source: Stacks Project, Tag 0829, lemma-directed-colimit-finite-type, first paragraph
of proof (blueprint: lem-sfb-space-qcoh-finite-type-union). -/
abbrev finiteTypeQuasiCoherentSubmodules {S : Scheme.{u}} {X : AlgebraicSpace S}
    (M : X.Modules) :=
  {N : Subobject M //
    SheafOfModules.IsQuasicoherent (N : X.Modules) ∧
      SheafOfModules.IsFiniteType (N : X.Modules)}

/-- The diagram sending a finite-type quasi-coherent subobject to its module sheaf,
with the inclusion maps supplied by the subobject order.
Source: Stacks Project, Tag 0829, lemma-directed-colimit-finite-type
(blueprint: lem-sfb-space-qcoh-finite-type-union). -/
def finiteTypeQuasiCoherentSubmoduleDiagram {S : Scheme.{u}} {X : AlgebraicSpace S}
    (M : X.Modules) : (finiteTypeQuasiCoherentSubmodules M) ⥤ X.Modules :=
  Monotone.functor (f := fun N : finiteTypeQuasiCoherentSubmodules M ↦ N.val)
    (fun {_ _} h ↦ h) ⋙ Subobject.underlying

/-- The finite-type quasi-coherent submodules of a quasi-coherent module on a qcqs
algebraic space form a nonempty directed poset, and their inclusion cocone is a
colimit in all module sheaves. No Noetherian or finite-type condition on M is assumed.
Source: Stacks Project, Tag 0829, lemma-directed-colimit-finite-type
(blueprint: lem-sfb-space-qcoh-finite-type-union).

Proof:
1. The zero submodule is quasi-coherent and finite type. For two such submodules
   N and P, take the image of N ⊕ P → M. By lem-sfb-space-qcoh-kernels-colimits
   it is quasi-coherent. The images of their finite local generating families
   generate this image, so it is finite type and contains both N and P.
2. The quasi-compact atlas gives a continuous surjection on point spaces
   (def-a1-space-point-topology), so the point space of X is quasi-compact.
   Apply lem-sfb-space-module-fp-directed-approximation to obtain a small filtered
   diagram F_j of finitely presented quasi-coherent modules with colimit M.
   The images G_j of F_j → M are quasi-coherent by
   lem-sfb-space-qcoh-kernels-colimits, and finite local generators of F_j
   surject onto local generators of G_j. Thus each G_j is in the indexing poset.
3. Use the subobject universe of def-weil-size-convention. By
   lem-pur-ringed-site-grothendieck-abelian, filtered colimits of module sheaves
   are exact. Apply this to 0 → N → M → M/N → 0 over the directed poset.
   Its constant M diagram has colimit M, since any two indices have an upper
   bound. Hence the canonical map c from the colimit C of the N into M is monic.
4. Factor F_j → M through G_j. Composing with G_j → C gives a compatible
   cocone on the F_j: for each transition F_j → F_k the images satisfy G_j ≤ G_k,
   and their image factorizations commute. The colimit property gives b : M → C.
   Testing on every F_j gives b ≫ c = 𝟙 M. Monicity of c then gives
   c ≫ b = 𝟙 C. Therefore c is an isomorphism, and transporting the colimit
   cocone along it gives exactly the inclusion cocone with vertex M, as stated
   using def-weil-pbc-category-colimit. -/
theorem finiteTypeQuasiCoherentSubmodules_colimit
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hqc : ∃ (T : Over S) (a : yoneda.obj T ⟶ X.obj.obj),
      CompactSpace T.left ∧ IsEtale a ∧ IsSurjective a)
    (hqs : IsAbsolutelyQuasiSeparated X)
    (M : X.Modules) [M.IsQuasicoherent] :
    Nonempty (finiteTypeQuasiCoherentSubmodules M) ∧
      Directed (· ≤ ·) (fun N : (finiteTypeQuasiCoherentSubmodules M) ↦ N) ∧
      ∃ (c : Cocone (finiteTypeQuasiCoherentSubmoduleDiagram M)) (h : c.pt = M),
        Nonempty (IsColimit c) ∧
          ∀ N : (finiteTypeQuasiCoherentSubmodules M),
            c.ι.app N ≫ eqToHom h = N.val.arrow := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
