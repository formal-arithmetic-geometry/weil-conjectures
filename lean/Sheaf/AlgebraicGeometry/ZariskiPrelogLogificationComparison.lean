/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.PrelogLogificationData
import Sheaf.AlgebraicGeometry.PrelogLogificationEtaleConstruction
import Sheaf.AlgebraicGeometry.PrelogEtaleInverseImageConstruction
import Sheaf.AlgebraicGeometry.ZariskiPrelogLogificationGeometry
import Sheaf.AlgebraicGeometry.PrelogLogificationEtaleGeometry

/-!
# Zariski prelog logification and its étale extension

Source: ILO VIII, opening of §3 and §3.3.2, pp.97, 106.
(blueprint: lem-trf-zariski-prelog-logification-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- Logification of an arbitrary Zariski prelog sheaf and change to the étale site.
Source: ILO VIII, opening of §3, p.97, and 3.3.2, p.106
(blueprint: lem-trf-zariski-prelog-logification-comparison).

Proof:
1. `zariski_prelog_logification_geometry` constructs the Zariski logification and
   characteristic quotient, with their universal property, stalks and restrictions.
2. `prelog_etale_inverse_image_construction` constructs the two normalized inverse
   images by monoid sheafification of the actual open-image diagrams.
3. `prelog_logification_etale_construction` applies the existing étale pushout and
   hom-extension theorems to each inverse image. Transport along the quotient-kernel
   isomorphism proves the exact presentation fields and both universal properties.
4. `prelog_logification_etale_geometry` constructs the canonical comparison and
   characteristic quotient and supplies the remaining stalk and restriction clauses.
5. Package these fixed witnesses and all thirteen properties in the stated order.
-/
theorem zariski_prelog_logification_comparison (X : Scheme.{u}) [IsLocallyNoetherian X]
    (P : ZariskiPrelogStructure X) :
    ∃ (Z : ZariskiLogStructure X)
      (z : PrelogPushoutPresentation (Opens.grothendieckTopology X.carrier)
        P.monoidSheaf.obj X.presheaf P.alpha Z.monoidSheaf Z.alpha)
      (E : PrelogEtaleInverseImage P) (L : EtaleLogStructure X)
      (l : PrelogPushoutPresentation X.smallEtaleTopology E.prelog.monoidSheaf.obj
        X.etaleStructurePresheaf E.prelog.alpha L.monoidSheaf L.alpha)
      (F : PrelogEtaleInverseImage Z.toZariskiPrelogStructure) (N : EtaleLogStructure X)
      (n : PrelogPushoutPresentation X.smallEtaleTopology F.prelog.monoidSheaf.obj
        X.etaleStructurePresheaf F.prelog.alpha N.monoidSheaf N.alpha)
      (K : TopCat.Sheaf CommMonCat.{u} X.carrier)
      (k : PrelogCharacteristicPresentation (Opens.grothendieckTopology X.carrier)
        Z.monoidSheaf K)
      (H : Sheaf X.smallEtaleTopology CommMonCat.{u})
      (h : PrelogCharacteristicPresentation X.smallEtaleTopology L.monoidSheaf H),
      z.ZariskiUniversal P Z ∧ l.EtaleUniversal E.prelog L ∧
      n.EtaleUniversal F.prelog N ∧
      PrelogLogificationComparison P Z z E F L N l n ∧
      z.ZariskiStalks P Z ∧ l.EtaleStalks P E L ∧ k.ZariskiStalks P Z K z ∧
      h.EtaleStalks P E L H l ∧ z.Restricts ∧ l.Restricts ∧ n.Restricts ∧
      k.Restricts ∧ h.Restricts := by
  obtain ⟨Z, z, K, k, hz, hzs, hks, hzr, hkr⟩ :=
    zariski_prelog_logification_geometry X P
  obtain ⟨E⟩ := prelog_etale_inverse_image_construction X P
  obtain ⟨L, l, hl⟩ := prelog_logification_etale_construction X E.prelog
  obtain ⟨F⟩ := prelog_etale_inverse_image_construction X Z.toZariskiPrelogStructure
  obtain ⟨N, n, hn⟩ := prelog_logification_etale_construction X F.prelog
  obtain ⟨H, h, hc, hls, hhs, hlr, hnr, hhr⟩ :=
    prelog_logification_etale_geometry X P Z z hz E L l hl F N n hn
  exact ⟨Z, z, E, L, l, F, N, n, K, k, H, h,
    hz, hl, hn, hc, hzs, hls, hks, hhs, hzr, hlr, hnr, hkr, hhr⟩

end AlgebraicGeometry
