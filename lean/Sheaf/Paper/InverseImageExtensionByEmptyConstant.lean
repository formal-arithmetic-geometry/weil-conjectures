module

public import Sheaf.Topology.SetsExtensionByEmpty
public import Mathlib.Topology.Sheaves.Functors

/-!
# Inverse image of extension by the empty set of a constant sheaf

Source: `literature/stacks-project/modules.tex`, proof of Lemma 0CAK
(blueprint: `lem-weil-pbc-sets-inverse-image-extension-by-empty-constant`).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace TopologicalSpace.Opens

namespace TopCat

/-- Inverse image identifies extension by the empty set of a constant sheaf with the
corresponding extension on the inverse image open, compatibly with constant sections.
Source: Stacks, Lemma 0CAK (blueprint: lem-weil-pbc-sets-inverse-image-extension-by-empty-constant).
Proof:
1. Extension-by-empty adjunction (lem-weil-pbc-sets-extension-by-empty-adjunction)
and constant-sheaf sections (lem-weil-pbc-constant-sheaf-open-maps-sections) identify
maps from the extension with maps from T to sections, by evaluation at the
sheafification of constant sections. This bijection beta is natural in the target.
2. The inverse-image/direct-image adjunction
(lem-weil-pbc-sets-inverse-image-colimits-finite-products) sends a morphism phi to
g_* phi composed with the unit; direct image evaluates at inverse-image opens.
3. Compose these bijections to identify Hom(g⁻¹ j_{V!} T, K) and
Hom(j_{V'!} T, K), naturally in K.
4. Apply lem-weil-pbc-coyoneda-iso-of-natural-hom-bijection: the image of the
identity is an isomorphism from j_{V'!} T to g⁻¹ j_{V!} T; take its inverse lambda.
5. Apply this Hom identification to g⁻¹ psi. Naturality of the adjunction unit
and of beta gives beta(g⁻¹ psi composed with lambda inverse) = eta composed with
beta(psi). The displayed equality evaluates this identity at each t : T.
-/
theorem inverseImageExtensionByEmptyConstant
    {Z Z' : TopCat.{u}} (g : Z' ⟶ Z) (V : Opens Z) (T : Type u) :
    ∃ e : (TopCat.Sheaf.pullback (Type u) g).obj (extensionByEmptyConstant V T) ≅
        extensionByEmptyConstant ((Opens.map g).obj V) T,
      ∀ (K : Z.Sheaf (Type u)) (ψ : extensionByEmptyConstant V T ⟶ K) (t : T),
        (e.inv ≫ (TopCat.Sheaf.pullback (Type u) g).map ψ).hom.app
            (op ((Opens.map g).obj V))
          ((toSheafify (Opens.grothendieckTopology Z')
              (extensionByEmptyPresheafObj ((Opens.map g).obj V)
                (sheafToTop (X := (toTopCat Z').obj ((Opens.map g).obj V))
                  (TopCat.discrete.obj T)))).app (op ((Opens.map g).obj V))
            ((cast (if_pos (le_refl ((Opens.map g).obj V))).symm)
              (TopCat.const (Y := TopCat.discrete.obj T) t))) =
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app K).hom.app
            (op V)
          (ψ.hom.app (op V)
            ((toSheafify (Opens.grothendieckTopology Z)
                (extensionByEmptyPresheafObj V
                  (sheafToTop (X := (toTopCat Z).obj V)
                    (TopCat.discrete.obj T)))).app (op V)
              ((cast (if_pos (le_refl V)).symm)
                (TopCat.const (Y := TopCat.discrete.obj T) t)))) := by
  sorry

end TopCat
