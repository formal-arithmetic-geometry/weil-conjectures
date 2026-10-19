/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.AlgebraicGeometry.EtaleGloballyGenerated
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Global generation detected on geometric stalks

Source: the Weil conjectures blueprint, chapter `sec-smooth-purity`, unit
`sk-prop-sf-kunneth-ordinary` (blueprint: lem-kun-global-generated-stalkwise);
Stacks Project, Tags 03DA, 010B, 010C, 03PT and 03PU.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Global generation of an étale sheaf of modules is equivalent to surjectivity
on every geometric stalk.

The evaluation morphism is the one from
`AlgebraicGeometry.Scheme.etaleGlobalSectionsEvaluation`; a geometric stalk is
the `pointSmallEtale` sheaf fibre, as in `def-weil-pbc-geometric-stalks`.
Proof: `isConservativeFamilyOfPoints_ulift_pointSmallEtale` gives joint reflection of
epimorphisms for module-valued sheaves. In the forward direction, the skyscraper
adjunction makes each sheaf fibre preserve epimorphisms, and
`ModuleCat.epi_iff_surjective` gives surjectivity. Conversely, apply joint reflection
at the algebraic-closure points. The resulting lifted fibre map is epi because it is
identified by `uliftSheafFiberIso` with the original surjective fibre map.
Source: Stacks Project, Tags 03DA, 010B, 010C, 03PT and 03PU; blueprint proof of
`lem-kun-global-generated-stalkwise` (blueprint: lem-kun-global-generated-stalkwise).
-/
theorem isGloballyGeneratedEtaleSheaf_iff_geometricStalk_surjective
    {T : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsGloballyGeneratedEtaleSheaf F ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (t : Spec (.of Ω) ⟶ T),
        Function.Surjective
          (((pointSmallEtale t).sheafFiber
            (A := ModuleCat.{u + 1} Λ)).map
            (etaleGlobalSectionsEvaluation F)) := by
  classical
  let e := etaleGlobalSectionsEvaluation F
  constructor
  · intro he Ω _ _ t
    have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
      hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
    have : Epi e := he
    have : ((pointSmallEtale t).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).PreservesEpimorphisms :=
      Functor.preservesEpimorphisms_of_adjunction
        ((pointSmallEtale t).skyscraperSheafAdjunction)
    exact (ModuleCat.epi_iff_surjective _).mp inferInstance
  · intro h
    let hpoints := isConservativeFamilyOfPoints_ulift_pointSmallEtale T
    apply (hpoints.jointlyReflectEpimorphisms (ModuleCat.{u + 1} Λ)).epi_iff e |>.mpr
    rintro ⟨-, ⟨x⟩⟩
    let t := T.algClosurePoint x
    have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
      hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
    have ht := h (AlgebraicClosure (T.residueField x)) t
    have : Epi ((pointSmallEtale t).sheafFiber.map e) :=
      (ModuleCat.epi_iff_surjective _).mpr ht
    let iso := (pointSmallEtale t).uliftSheafFiberIso.{u + 1}
      (ModuleCat.{u + 1} Λ)
    change Epi (((pointSmallEtale t).ulift.{u + 1}).sheafFiber.map e)
    rw [← epi_comp_iff_of_isIso _ (iso.hom.app F)]
    erw [iso.hom.naturality e]
    infer_instance

end AlgebraicGeometry.Scheme
