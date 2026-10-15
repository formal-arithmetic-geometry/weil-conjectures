module

public import Sheaf.AlgebraicGeometry.ProEtale.ClosedSiteLift
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import Sheaf.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Sheaf.Paper.SiteSheafificationSectionsLocal
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Sheaf.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Once the affine lift's counit at the identity object is invertible,
projective evaluation gives the actual inverse-image unit isomorphism on V.
No specialization assumption is made in this comparison lemma.

Source: Stacks Project, Tag 09BL, lemma-closed-immersion-affines-apply (1),(2),
and Tag 09AC, localization and unit identification
(blueprint: new-lem-weil-pbc-specialization-unit-comparison).

Proof. Localize at V and use the canonical affine presentation of its closed
base change given by the kernel I and the first isomorphism theorem. The
inverse-image/direct-image adjunction transports through these site equivalences;
its unit transports with it, since the inverse-image comparisons are mates of
the base-change comparisons. If evaluation uses a different adjunction on these
fixed functors, uniqueness of left adjoints changes its counit only by an
automorphism; invertibility therefore transfers. On the affine bases write v
for the lift, r for
base change and B for the identity object. To see that r(B) is weakly
contractible, lift a finite covering of r(B) through v, take its finite disjoint
union and identify v(r(B)) with B using the assumed invertible counit. Projectivity
of evaluation at B splits this cover. Applying r and the invertible adjunction
unit gives a section of the original disjoint-union cover. Local lifts of an
epimorphism glue on that finite union and pull back by its section. Thus
evaluation at r(B) takes epimorphisms to surjections.
Affine closed inverse-image evaluation now identifies inverse-image sections
with sheafification of F(v(-)), and its sheafification unit at r(B) is bijective.
The inverse-image unit itself is restriction along the counit B <- v(r(B))
followed by this sheafification unit: the pair (B,id) in the inverse-image
colimit corresponds under v ⊣ r to the counit. Restriction along an isomorphism
is bijective, so the actual unit is bijective. For abelian sheaves the same
colimit and sheafification calculation uses additive maps. Forgetting abelian
groups computes the filtered inverse-image colimit and sheafification, so the
bijection is an isomorphism of groups. All comparisons are natural in F; the
pointwise isomorphisms therefore assemble to the asserted natural isomorphism.
The empty finite union and empty identity object are covered by the same sheaf
and coproduct identities; no nonemptiness hypothesis is used. -/
theorem isIso_proEtaleUnit_sections_of_closedSiteCounit
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (V : X.ProEt) [IsAffine V.left]
 :
    let A := Γ(V.left, ⊤)
    let I := RingHom.ker (pullback.fst V.hom i).appTop.hom
    let B := AffineProEt.ofEtale (𝟙 (Spec A))
    (∀ (P Q : Sheaf (AffineProEt.topology (Spec A)) (Type (u + 1))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op B))) →
    ∀ adj : AffineProEt.closedSiteLift A I ⊣ AffineProEt.closedSiteBaseChange A I,
      IsIso (adj.counit.app B) →
      IsIso (Functor.whiskerRight (proEtaleSheafAdjunction i AddCommGrpCat.{u + 1}).unit
        ((sheafSections (ProEt.topology X) AddCommGrpCat.{u + 1}).obj (op V))) := by
  sorry

end AlgebraicGeometry.Scheme
