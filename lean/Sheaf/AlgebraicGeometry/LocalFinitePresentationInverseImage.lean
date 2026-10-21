/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import Sheaf.CategoryTheory.SheafTensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import Sheaf.AlgebraicGeometry.WeaklyEtaleStability
import Sheaf.CategoryTheory.MonoidalFiniteFreeTransport
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The specified finite presentation on a base-changed pro-étale cover

Source: blueprint main-20261015, sec-six-functors-basics,
`sk-def-sfb-dc-restricted-functors/lem-sfb-dc-upper-star-preserves.proof.md`,
from "Choose a pro-étale cover" to the end
(blueprint: lem-sfb-local-finite-presentation-inverse-image).

The witness records the canonical comparison and coordinate maps, and the
cokernel arrow equation ties the resulting presentation to the given one.
-/

@[expose] public section

set_option autoImplicit false

universe u v w₁ w₂ w₃ w₄ z₁ z₂ z₃ z₄

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The local witnesses in the specified-cover inverse-image assertion. This record
only packages its ring, module, basis and presentation isomorphisms. It uses abstract
ambient categories to keep their elaboration independent of the sheaf constructions.
The comparison e is supplied in the theorem by the existing `upperStarCompIso` of the
pullback square.

Source: blueprint main-20261015, proof of `lem-sfb-dc-upper-star-preserves`,
from "Choose a pro-étale cover" through the final sentence
(blueprint: lem-sfb-local-finite-presentation-inverse-image).
-/
structure FinitePresentationTransportWitness
    {C : Type w₁} [Category.{z₁} C] [MonoidalCategory C]
    {B : Type w₂} [Category.{z₂} B] [MonoidalCategory B]
    {D : Type w₃} [Category.{z₃} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D] [∀ A : D, PreservesFiniteColimits (tensorLeft A)]
    {E : Type w₄} [Category.{z₄} E] [MonoidalCategory E] [Abelian E]
    [MonoidalPreadditive E] [∀ A : E, PreservesFiniteColimits (tensorLeft A)]
    (F : C ⥤ B) (G : B ⥤ E) (J : C ⥤ D) (H : D ⥤ E)
    [F.LaxMonoidal] [G.LaxMonoidal] [J.LaxMonoidal] [H.LaxMonoidal]
    (e : F ⋙ G ≅ J ⋙ H) (R : C) [MonObj R] (M : Mod C R) (m n : ℕ)
    (d : Mod.finiteFree (J.obj R) m ⟶ Mod.finiteFree (J.obj R) n)
    (p : (J.mapMod R).obj M ≅ cokernel d) where
  /-- The ring isomorphism supplied by the specified composition comparison. -/
  ringIso : Mon.mk (G.obj (F.obj R)) ≅ Mon.mk (H.obj (J.obj R))
  /-- The ring map is the component of the specified comparison. -/
  ringIso_hom : ringIso.hom.hom = e.hom.app R
  /-- The comparison of actual module objects, with restriction along beta. -/
  moduleIso : (G.mapMod (F.obj R)).obj ((F.mapMod R).obj M) ≅
    (Mod.comap ringIso.hom.hom).obj ((H.mapMod (J.obj R)).obj ((J.mapMod R).obj M))
  /-- Its underlying sheaf map is the component of the same comparison. -/
  moduleIso_hom : moduleIso.hom.hom = e.hom.app M.X
  /-- The finite-free identification for every rank, including zero. -/
  freeIso : ∀ k : ℕ,
    (Mod.comap ringIso.hom.hom).obj
      ((H.mapMod (J.obj R)).obj (Mod.finiteFree (J.obj R) k)) ≅
    Mod.finiteFree (G.obj (F.obj R)) k
  /-- Its coordinates determine the canonical identification uniquely. -/
  freeIso_projection : ∀ (k : ℕ) (j : Fin k),
    (freeIso k).hom.hom ≫
      (biproduct.π (fun _ : Fin k ↦ Mod.regular (G.obj (F.obj R))) j).hom =
    H.map ((biproduct.π (fun _ : Fin k ↦ Mod.regular (J.obj R)) j).hom) ≫ ringIso.inv.hom
  /-- The presentation with the actual conjugated transported differential. -/
  presentationIso : (G.mapMod (F.obj R)).obj ((F.mapMod R).obj M) ≅
    cokernel ((freeIso m).inv ≫
      (Mod.comap ringIso.hom.hom).map ((H.mapMod (J.obj R)).map d) ≫ (freeIso n).hom)
  /-- The chosen presentation induces this cokernel arrow, fixing its normalization. -/
  presentationIso_π : (freeIso n).inv ≫
      (Mod.comap ringIso.hom.hom).map
        ((H.mapMod (J.obj R)).map (cokernel.π d ≫ p.inv)) ≫
      moduleIso.inv ≫ presentationIso.hom =
    cokernel.π ((freeIso m).inv ≫
      (Mod.comap ringIso.hom.hom).map ((H.mapMod (J.obj R)).map d) ≫ (freeIso n).hom)

/-- Pullback transports the chosen covering and all its specified finite presentations,
with unchanged ranks; in particular it preserves local finite presentation.

Source: blueprint main-20261015, proof of `lem-sfb-dc-upper-star-preserves`,
from "Choose a pro-étale cover" through the final sentence
(blueprint: lem-sfb-local-finite-presentation-inverse-image).

Proof, following the eight steps of the DAG node:
1. Abelian sheaves have the closed sheaf tensor, so tensor preserves finite colimits
and internal module categories are abelian (`lem-sfb-grothendieck-sheafification`,
`sk-def-sfb-sheaf-tensor`, `lem-sfb-modobj-abelian`). Inverse image is additive and a
left adjoint (`def-sfb-finite-upper-lower-star-adjunction`,
`lem-weil-pbc-left-adjoint-preserves-colimits`, `lem-sfb-preserving-colimits-additive`);
its braided structure preserves commutativity (`lem-sfb-finite-upper-star-braided`).
2. Base change preserves weakly etale maps and fpqc covering families, so precisely
this pullback family covers X (`sk-lem-pe-weakly-etale-stability`,
`lem-weil-pbc-fpqc-covering-axioms`).
3. The specified inverse-image compositors are monoidal: expand their mate as
counit, image of pushforward compositor, and image of composite unit. Each is monoidal
by `lem-sfb-finite-monoidal-adjunction`, `def-weil-pbc-composite-adjunction`, and
`lem-sfb-pushforward-comp-monoidal`. Apply the resulting comparison to R to get beta.
4. Apply `lem-sfb-restricted-transport-comparison-linear` with both scalar maps
identities and the ring comparison beta. The inverse underlying sheaf map is linear
too, giving the displayed module isomorphism for the actual iterated actions.
5. The monoidal adjunction induces a module adjunction
(`def-sfb-modobj-transport-adjunction`), so transport preserves cokernel coforks.
6. Use `lem-sfb-monoidal-finite-free-transport` for each k, restrict along beta, and
apply beta inverse in each coordinate. The biproduct identities give the freeIso
and its coordinate formula. For k=0 the same identities use the empty sum.
7. Restriction preserves colimits (`sk-def-sfb-change-of-scalars`). Conjugate the
transported differential by freeIso. Its transported cokernel arrow, conjugated by
the target freeIso, has the universal cokernel property: a map killing the conjugate
corresponds to a map killing the original transported differential, and hence factors
uniquely. The two universal cokernel maps are inverse. Composing with the image of p
and the module comparison gives presentationIso and its arrow equation.
8. These presentations, on exactly the cover in step 2, witness
`def-sfb-locally-finitely-presented`. Arbitrary index universes can be reduced for
this existential predicate by choosing finite affine subfamilies on each affine open;
the explicit witness retains the entire original index set. Zero ranks, the zero ring,
and the empty cover on the empty scheme are included; no flatness or Noetherian
hypothesis is used.
-/
theorem localFinitePresentation_inverseImage
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) R)
    (𝒰 : Scheme.Cover.{v} Scheme.proetalePrecoverage Y) (m n : 𝒰.I₀ → ℕ)
    (d : ∀ i, Mod.finiteFree ((upperStar Ab.{u + 1} (𝒰.f i)).obj R) (m i) ⟶
      Mod.finiteFree ((upperStar Ab.{u + 1} (𝒰.f i)).obj R) (n i))
    (p : ∀ i, ((upperStar Ab.{u + 1} (𝒰.f i)).mapMod R).obj M ≅ cokernel (d i)) :
    (𝒰.toPreZeroHypercover.pullback₁ f).presieve₀ ∈ Scheme.proetalePrecoverage X ∧
    (∀ i : 𝒰.I₀, Nonempty (FinitePresentationTransportWitness
      (upperStar Ab.{u + 1} f) (upperStar Ab.{u + 1} (pullback.fst f (𝒰.f i)))
      (upperStar Ab.{u + 1} (𝒰.f i)) (upperStar Ab.{u + 1} (pullback.snd f (𝒰.f i)))
      (upperStarCompIso Ab.{u + 1} (pullback.condition (f := f) (g := 𝒰.f i)))
      R M (m i) (n i) (d i) (p i))) ∧
    IsLocallyFinitelyPresented ((upperStar Ab.{u + 1} f).obj R)
      (((upperStar Ab.{u + 1} f).mapMod R).obj M) := by
  sorry

end AlgebraicGeometry.ProEtale
