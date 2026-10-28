/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Sheaf.Paper.LisseTowerEtaleDescentData
public import Sheaf.AlgebraicGeometry.DerivedIsomSheafComparisonFromHom
import Sheaf.AlgebraicGeometry.DerivedMorphismSheafComparison

/-! # Étale covers carrying representatives of pro-étale Isom sections

Source: Stacks Project, proetale.tex, Tags 09BV and 00WJ.
(blueprint: new-lem-weil-pbc-lisse-finite-level-etale-local-representative-cover).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- A pro-étale local derived Isom section is represented by actual isomorphisms on an étale
cover of its étale object.

Source: Stacks Project, proetale.tex, Tags 09BV and 00WJ.
(blueprint: new-lem-weil-pbc-lisse-finite-level-etale-local-representative-cover).

Proof: use local surjectivity of sheafification to represent the section by an inverse pair on a
common étale refinement.  The finite-limit equations for the pair remain valid after refinement,
so every member of the resulting étale cover carries an actual derived isomorphism.  This is the
local-cover part of the geometric-point representative argument; the point-lifting step is kept
separate in the importing theorem.
-/
theorem exists_etale_iso_cover_of_proetale_local_iso_section
    (X : Scheme.{u}) (V : X.Etale)
    {B : Type (u + 1)} [CommRing B]
    (A D : DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (s : (derivedLocalIsoPresheaf (ProEt.topology X) B
      ((derivedComparison X B).obj A)
      ((derivedComparison X B).obj D)).obj
        (op ((toProEt X).obj V))) :
    ∃ 𝒰 : Cover.{u} etalePrecoverage V.left,
      ∀ i : 𝒰.I₀,
        Nonempty ((localIsomorphismRestriction X B
          (Etale.mk (𝒰.f i ≫ V.hom))).obj A ≅
          (localIsomorphismRestriction X B
            (Etale.mk (𝒰.f i ≫ V.hom))).obj D) := by
  sorry

end AlgebraicGeometry.Scheme
