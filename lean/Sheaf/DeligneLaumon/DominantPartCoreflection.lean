module

public import Sheaf.AlgebraicGeometry.DominantPart
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.ReductionGenericFibre
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Reduced dominant part and its coreflection

Source: Illusie--Laszlo--Orgogozo, Exposé II, 1.2.5 and 1.2.8,
printed pp. 23--26 (blueprint: lem-per-dominant-part-coreflection).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/--
Source: Illusie--Laszlo--Orgogozo, Exposé II, 1.2.5 and 1.2.8,
printed pp. 23--26 (blueprint: lem-per-dominant-part-coreflection).

Proof (node steps 1--8).  (1) The inverse image of the generic points of `S`
is the union of the generic fibres.  Noetherian finite type gives finitely many
components, and sobriety identifies the components meeting that inverse image
with exactly those whose generic points map to generic points of `S`; hence its
closure is their finite union.  (2) The vanishing ideal construction gives the
reduced induced closed subscheme and its closed immersion; closed immersions are
proper and finite type, so the resulting scheme is finite type over `S`.  (3) A
reduced `T` whose generic points map to generic points of `S` has image in this
closure.  The reduced-source factorization theorem gives the unique lift, and
the lifts form the displayed Hom bijection.  (4) Apply this bijection to the
composite with the closed immersion to obtain each induced map; uniqueness
proves identity and composition.  (5) Base change to a generic point gives a
closed immersion with full support, and the generic-fibre reduction theorem
identifies it with the reduction of the fibre.  (6) An étale morphism is open,
so inverse images commute with the closure in (1).  Its base change to the
reduced dominant part of `Y` is reduced; the closed immersion and its support
then identify the pullback with the dominant part of `X`.  (7) For a proper
surjection, the induced map is proper by proper-to-separated, and its image is
closed.  Surjectivity after base change shows that its image contains the dense
set of generic points, hence it is all of `Y_md`.  (8) These constructions are
canonical by the uniqueness clauses, giving the stated functorial and
comparison assertions.
-/
theorem dominantPart_coreflection
    {S X : Scheme.{u}} (p : X ⟶ S) [AlgebraicGeometry.IsNoetherian S]
    [LocallyOfFiniteType p] [QuasiCompact p] :
    IsReduced (dominantPart X S p) ∧
      IsClosedImmersion (dominantPartι X S p) ∧
      ((dominantPartClosed X S p : Set X) =
        {x | ∃ ξ ∈ genericPoints X, p ξ ∈ genericPoints S ∧
          x ∈ closure ({ξ} : Set X)}) ∧
      (∀ {T : Scheme.{u}} (q : T ⟶ S) [IsReduced T]
        [LocallyOfFiniteType q] [QuasiCompact q],
        (∀ t ∈ genericPoints T, q t ∈ genericPoints S) →
          Function.Bijective
            (fun g : {g : T ⟶ dominantPart X S p //
                g ≫ (dominantPartι X S p ≫ p) = q} =>
              (⟨g.1 ≫ dominantPartι X S p,
                by simp only [Category.assoc, g.2]⟩ :
                {g : T ⟶ X // g ≫ p = q}))) ∧
      (∀ {Y : Scheme.{u}} (r : Y ⟶ S) [LocallyOfFiniteType r]
        [QuasiCompact r] (f : X ⟶ Y),
        f ≫ r = p →
          ∃! fmd : dominantPart X S p ⟶ dominantPart Y S r,
            fmd ≫ dominantPartι Y S r = dominantPartι X S p ≫ f) ∧
      (∀ {Y Z : Scheme.{u}} (r : Y ⟶ S) (s : Z ⟶ S)
        [LocallyOfFiniteType r] [QuasiCompact r]
        [LocallyOfFiniteType s] [QuasiCompact s]
        (f : X ⟶ Y) (g : Y ⟶ Z),
        f ≫ r = p → g ≫ s = r →
          ∀ (fmd : dominantPart X S p ⟶ dominantPart Y S r)
            (gmd : dominantPart Y S r ⟶ dominantPart Z S s)
            (hmd : dominantPart X S p ⟶ dominantPart Z S s),
            fmd ≫ dominantPartι Y S r = dominantPartι X S p ≫ f →
            gmd ≫ dominantPartι Z S s = dominantPartι Y S r ≫ g →
            hmd ≫ dominantPartι Z S s = dominantPartι X S p ≫ (f ≫ g) →
            hmd = fmd ≫ gmd) ∧
      (∀ (fmd : dominantPart X S p ⟶ dominantPart X S p),
        fmd ≫ dominantPartι X S p = dominantPartι X S p →
          fmd = 𝟙 _) ∧
      (∀ (s : S), s ∈ genericPoints S →
        ∃ e : (dominantPartι X S p ≫ p).fiber s ≅ (p.fiber s).nilradical.subscheme,
          e.hom ≫ (p.fiber s).nilradical.subschemeι ≫ p.fiberι s =
              (dominantPartι X S p ≫ p).fiberι s ≫ dominantPartι X S p ∧
            e.hom ≫ (p.fiber s).nilradical.subschemeι ≫
                p.fiberToSpecResidueField s =
              (dominantPartι X S p ≫ p).fiberToSpecResidueField s) ∧
      (∀ {Y : Scheme.{u}} (r : Y ⟶ S) [LocallyOfFiniteType r]
        [QuasiCompact r] (f : X ⟶ Y) [Etale f],
        f ≫ r = p →
          ∀ (fmd : dominantPart X S p ⟶ dominantPart Y S r)
            (hcomp : dominantPartι X S p ≫ f = fmd ≫ dominantPartι Y S r),
              IsIso (pullback.lift (dominantPartι X S p) fmd hcomp)) ∧
      (∀ {Y : Scheme.{u}} (r : Y ⟶ S) [LocallyOfFiniteType r]
        [QuasiCompact r] (f : X ⟶ Y),
        f ≫ r = p → IsProper f → Surjective f →
          ∀ (fmd : dominantPart X S p ⟶ dominantPart Y S r),
            fmd ≫ dominantPartι Y S r = dominantPartι X S p ≫ f →
              IsProper fmd ∧ Surjective fmd) := by
  sorry

end AlgebraicGeometry
