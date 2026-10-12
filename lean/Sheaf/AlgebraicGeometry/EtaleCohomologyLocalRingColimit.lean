/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.DerivedInverseImageComposition
import Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import Sheaf.AlgebraicGeometry.OpenRestrictionPullbackUnit
import Sheaf.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import Sheaf.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Étale cohomology over a local ring as a colimit

Source: Stacks Project, Étale Cohomology, Tag 09AX, proof, and Tags 03Q6 and 09YQ;
Cohomology on Sites, Tag 03F3
(blueprint: lem-weil-pbc-etale-cohomology-local-ring-colimit).

The diagram is a presentation of the actual object-cohomology presheaf, with its arrows
specified as well as its objects. The object cohomology H^q(U, F) is Ext from the
sheafified free abelian sheaf on the representable `uliftYoneda U` (Mathlib's
`Sheaf.cohomologyPresheaf` construction, written out because the coefficients
`AddCommGrpCat.{u + 1}` lie above the site's morphism universe; the form of the landed
AbelianHigherDirectImagePresheaf). The conclusion supplies the restriction comparison,
the unique factorizations of the local-scheme morphism, and a colimit cocone whose legs
are the pullbacks followed by inverse-image composition. `Sheaf.H` is the recorded Ext
encoding of abelian-sheaf cohomology; its K-injective comparison is a stage-3 bridge.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

/-- Object cohomology on open subschemes identifies with cohomology of the restricted
sheaf, and its canonical pullbacks to the local scheme form a colimit cocone.
Source: Stacks Project, Tags 09AX (proof), 03Q6, 09YQ and 03F3
(blueprint: lem-weil-pbc-etale-cohomology-local-ring-colimit).

Proof, following the seven steps of the node:
1. Restrict an injective resolution of F to each open. Open immersions are étale
   (lem-weil-pbc-open-immersion-etale), and restriction preserves injectives by
   lem-weil-pbc-cohomology-pullback-functorial (5). The natural restriction isomorphism
   of lem-weil-pbc-etale-inverse-image-restriction identifies its section complex with
   the original resolution evaluated on that open. This gives the comparison e,
   independent of the resolution by prop-weil-pbc-cohomology-resolution-independent.
2. Naturality of that restriction isomorphism and the unit identity from
   lem-weil-pbc-open-restriction-pullback-unit identify restrictions with pullbacks
   along inclusions, followed by inverse-image composition. This is the equation on e.
3. The image of fromSpecStalk consists of generalizations of x
   (lem-weil-pbc-spec-local-ring-canonical-morphism), so it factors uniquely through
   each neighbourhood. Pullback functoriality and the associativity of inverse-image
   composition (lem-weil-pbc-derived-inverse-image-composition) give compatible legs.
4. On affine neighbourhoods the local scheme is their inverse limit
   (lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods). Apply
   lem-weil-pbc-etale-cohomology-limit-of-schemes to the restricted sheaves.
5. Inverse-image composition identifies the sheaves on the limit with the fixed
   pullback of F; coherence identifies their transitions with identities. Their
   colimit is that pullback by lem-weil-pbc-colimit-constant-connected-diagram.
6. Step 2 identifies the diagrams. Affine neighbourhoods are cofinal among all
   neighbourhoods; lem-weil-pbc-colimit-initial-full-subcategory gives the colimit
   cocone over all opens, with precisely the prescribed legs.
7. If a class maps to zero, injectivity of the induced colimit isomorphism makes its
   coprojection zero. By lem-weil-pbc-filtered-colimit-modules-elementwise it vanishes
   on a smaller neighbourhood.
-/
theorem etaleCohomology_localRing_colimit
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (x : X) (q : ℕ)
    (P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (hP : P = (Functor.flip ((uliftYoneda.{u + 1} ⋙
      (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
      presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).op ⋙
        Abelian.extFunctor q)).obj F)
    (D : (OpenNhds (X := X.toLocallyRingedSpace.toTopCat) x)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (d : ∀ U : OpenNhds (X := X.toLocallyRingedSpace.toTopCat) x,
      D.obj (op U) ≅ P.obj
        (op (Scheme.Etale.mk (Scheme.Opens.ι U.1))))
    (hD : ∀ (U V : OpenNhds (X := X.toLocallyRingedSpace.toTopCat) x) (f : V ⟶ U),
      D.map f.op = (d U).hom ≫ P.map
        (MorphismProperty.Over.homMk (P := @Etale) (Q := ⊤) (X := X)
          (A := Scheme.Etale.mk (Scheme.Opens.ι V.1))
          (B := Scheme.Etale.mk (Scheme.Opens.ι U.1)) (X.homOfLE f.le)
          (X.homOfLE_ι f.le) trivial).op ≫ (d V).inv) :
    ∃ e : ∀ U : X.Opens, P.obj
        (op (Scheme.Etale.mk U.ι)) ≅
        AddCommGrpCat.of (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj F) q),
      (∀ (U V : X.Opens) (h : V ≤ U),
        P.map
            (MorphismProperty.Over.homMk (P := @Etale) (Q := ⊤) (X := X)
              (A := Scheme.Etale.mk V.ι) (B := Scheme.Etale.mk U.ι) (X.homOfLE h)
              (X.homOfLE_ι h) trivial).op ≫
            (e V).hom =
          (e U).hom ≫ AddCommGrpCat.ofHom
            (Etale.cohomologyMap (X.homOfLE h)
              ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj F) q) ≫
            AddCommGrpCat.ofHom (Sheaf.H.map
              ((Etale.upperStarComp AddCommGrpCat.{u + 1} (X.homOfLE h) U.ι V.ι
                (X.homOfLE_ι h).symm).inv.app F) q)) ∧
      ∃ (g : ∀ U : OpenNhds (X := X.toLocallyRingedSpace.toTopCat) x,
          Spec (X.presheaf.stalk x) ⟶ (Scheme.Opens.toScheme U.1))
        (hg : ∀ U, X.fromSpecStalk x = g U ≫ (Scheme.Opens.ι U.1)),
        (∀ U (g' : Spec (X.presheaf.stalk x) ⟶ (Scheme.Opens.toScheme U.1)),
          g' ≫ (Scheme.Opens.ι U.1) = X.fromSpecStalk x → g' = g U) ∧
        ∃ (B : Cocone D)
          (b : B.pt ≅ AddCommGrpCat.of
            (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1}
              (X.fromSpecStalk x)).obj F) q)),
          (∀ U, B.ι.app (op U) ≫ b.hom =
            (d U).hom ≫ (e U.1).hom ≫ AddCommGrpCat.ofHom
              (Etale.cohomologyMap (g U)
                ((Etale.upperStar AddCommGrpCat.{u + 1} (Scheme.Opens.ι U.1)).obj F) q) ≫
              AddCommGrpCat.ofHom (Sheaf.H.map
                ((Etale.upperStarComp AddCommGrpCat.{u + 1} (g U) (Scheme.Opens.ι U.1)
                  (X.fromSpecStalk x) (hg U)).inv.app F) q)) ∧
          Nonempty (IsColimit B) ∧
          ∀ U (ξ : D.obj (op U)), (B.ι.app (op U) ≫ b.hom) ξ = 0 →
            ∃ (V : OpenNhds (X := X.toLocallyRingedSpace.toTopCat) x)
              (f : V ⟶ U), D.map f.op ξ = 0 := by
  sorry

end AlgebraicGeometry
