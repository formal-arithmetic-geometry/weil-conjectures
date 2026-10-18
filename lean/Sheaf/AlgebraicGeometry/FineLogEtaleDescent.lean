/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineLogEtaleDescentDatum
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

import Sheaf.CategoryTheory.SetSheafCoverDescent
import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver

/-!
# Étale descent of fine log structures and arbitrary prelog morphisms

Source: ILO, Exposé VI 1.1 and Exposé VIII 3.3.8, pp. 69, 107--108;
Stacks, Tags 04TR and 04TQ (blueprint: lem-trf-fine-log-structure-etale-descent).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Fine log structures descend effectively, uniquely with their labelled identifications,
and fs charts descend as well. Maps of arbitrary monoid sheaves over the structure sheaf
also glue uniquely; no log condition on their source or target is needed.

Source: ILO VI 1.1, VIII 3.3.8; Stacks, Tags 04TR and 04TQ
(blueprint: lem-trf-fine-log-structure-etale-descent).

Proof:
1. Use the size convention and `Scheme.Etale.overEquiv` to identify the localized sites
   and their structure sheaves, including repeated localization and the terminal slice.
2. Apply `setSheafCoverDescent` (Tag 04TR) to the underlying set sheaves, retaining the
   labelled identifications and their prescribed overlap equations.
3. Glue multiplication and identity sectionwise by the sheaf equalizer condition.
   Naturality and every monoid equation hold by local verification and separatedness.
   Glue the structural maps by Tag 04TQ and check their monoid equations locally.
4. For every unit, glue its unique local preimages. Local uniqueness proves uniqueness
   globally, so the inverse image of the unit sheaf maps isomorphically to the unit sheaf.
5. Transport the local fine charts through the identifications and compose the étale
   coverings. Their monoids remain finitely generated and integral; saturated monoids
   remain saturated. This proves fineness and the conditional fs assertion.
6. For arbitrary prelog sheaves, apply Tag 04TQ to the underlying sheaf maps. Check
   preservation of products, identity and the structural map by separatedness. Uniqueness
   already holds for maps of set sheaves, including inverse-image sheaves with their
   composite structural map; the log axiom is never used here.
7. Given a second gluing, glue the local comparison isomorphisms by step 6. Glue their
   inverses too. Both composites are identities by local uniqueness. The resulting
   isomorphism is unique subject to compatibility with all the given identifications. -/
theorem fineLogStructure_etale_descent
    {T : Scheme.{u}} [IsLocallyNoetherian T] {ι : Type v} (U : ι → T.Etale)
    (hcover : ∀ x : T, ∃ (a : ι) (y : (U a).left), (U a).hom y = x) :
    (∀ D : FineLogEtaleDescentDatum U,
      ∃ (M : EtaleLogStructure T) (_hM : M.IsFine) (e : D.Gluing M),
        ((∀ a : ι, (D.localLog a).IsFineSaturated) → M.IsFineSaturated) ∧
        ∀ (N : EtaleLogStructure T) (_hN : N.IsFine) (f : D.Gluing N),
          ∃! h : EtalePrelogStructure.Iso M.toEtalePrelogStructure N.toEtalePrelogStructure,
            ∀ (a : ι) (V : T.Etale) (g : V ⟶ U a) (s : M.monoidSheaf.obj.obj (op V)),
              f.component a V g (h.iso.hom.app (op V) s) = e.component a V g s) ∧
    (∀ (A B : EtalePrelogStructure T) (localHom : ∀ a : ι, A.LocalHom B (U a)),
      (∀ (a b : ι) (V : T.Etale) (f : V ⟶ U a) (g : V ⟶ U b),
        (localHom a).hom.app (op (Over.mk f)) = (localHom b).hom.app (op (Over.mk g))) →
      ∃! h : A.Hom B, ∀ (a : ι) (V : T.Etale) (f : V ⟶ U a),
        h.hom.app (op V) = (localHom a).hom.app (op (Over.mk f))) := by
  sorry

end AlgebraicGeometry
