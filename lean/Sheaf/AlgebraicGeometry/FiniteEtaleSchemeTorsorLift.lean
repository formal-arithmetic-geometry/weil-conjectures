/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor

import Sheaf.AlgebraicGeometry.FiniteLocallyConstantSetsRepresentability
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Lifting an equivariant finite étale scheme

Source: Stacks Project Tag 0A5G, final paragraph.
(blueprint: lem-weil-pbc-finite-etale-scheme-torsor-lift)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- A finite étale base-change equivalence lifts a scheme torsor together with its action.
Source: Stacks Project Tag 0A5G, final paragraph, categorical action-lifting argument.
(blueprint: lem-weil-pbc-finite-etale-scheme-torsor-lift)

Proof: A torsor R₀ under the finite constant group is locally the finite constant set M.
Tag 03RV represents its underlying sheaf by a finite étale scheme. Yoneda lifts each
constant action map; its faithfulness gives the action equations. Simple transitivity
on sections and local existence make the representative a scheme torsor t₀, with a
sheaf torsor isomorphism to R₀. This is the argument of
EtaleTorsorDescent.exists_toSheafTorsor_equiv, applied through lower representability
interfaces rather than importing that module, which now creates an import cycle.
Essential surjectivity lifts the finite étale scheme underlying t₀ to P over Y.
Fullness lifts each action endomorphism, conjugated by the chosen base-change isomorphism.
Faithfulness gives the zero and addition equations. Finite coproducts and fibre products
of finite étale schemes are finite étale and are preserved by base change. Thus the map
from the coproduct of the copies of P, indexed by M, to P ×_Y P becomes the torsor
isomorphism for t₀. Reflection of isomorphisms makes it an isomorphism upstairs.
The image of P → Y is open because P → Y is étale and closed because it is finite.
Its open-and-closed immersion U → Y is finite étale, and its pullback is an isomorphism:
t₀ is surjective, so its base-changed image is all Y₀. Reflecting this isomorphism
shows U = Y and hence P → Y is surjective. These data define the lifted scheme torsor.
The chosen isomorphism commutes with the structure maps and every lifted action.
No geometric point is selected, so empty bases and the trivial group are included. -/
theorem finiteEtale_lifts_scheme_torsor
    [(@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange]
    {Y Y₀ : Scheme.{u}} (i : Y₀ ⟶ Y)
    (hFE : (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i).IsEquivalence)
    (M : Type (u + 1)) [AddCommGroup M] [Finite M]
    (R₀ : Sheaf.Torsor
      ((constantSheaf Y₀.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of M))) :
    ∃ (t₀ : Scheme.EtaleTorsor M Y₀) (_ : t₀.toSheafTorsor ≈ R₀)
      (t : Scheme.EtaleTorsor M Y) (e : pullback t.π i ≅ t₀.P),
      e.hom ≫ t₀.π = pullback.snd t.π i ∧
      ∀ m : M,
        pullback.map t.π i t.π i (t.vadd m) (𝟙 Y₀) (𝟙 Y)
          (by rw [Category.comp_id, t.vadd_π])
          (by rw [Category.comp_id, Category.id_comp]) ≫ e.hom =
        e.hom ≫ t₀.vadd m := by sorry

end AlgebraicGeometry.Etale
