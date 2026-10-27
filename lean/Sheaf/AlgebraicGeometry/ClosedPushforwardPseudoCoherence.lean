module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.MPseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.Topology.ClosedImmersionPushforwardExact
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.Topology.ClosedPushforwardAbelianStalks
import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.PerfectComplex
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Closed pushforward detects finite-stage pseudo-coherence

Source: Stacks Project, Derived Categories of Schemes, Tag 09VA,
`lemma-closed-push-pseudo-coherent`, specialized to schemes
(blueprint: lem-sfb-closed-pushforward-pseudocoherence).
-/

@[expose] public section

set_option autoImplicit false

universe u wZ wP

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Closed pushforward preserves and reflects `m`-pseudo-coherence, provided the ordinary
pushforward of the structure module, placed in degree zero, is pseudo-coherent.
The derived object is arbitrary in the unbounded derived category.

Source: Stacks Project, Derived Categories of Schemes, Tag 09VA,
`lemma-closed-push-pseudo-coherent`
(blueprint: lem-sfb-closed-pushforward-pseudocoherence).

Proof:
1. Closed pushforward is exact on abelian sheaves by
   lem-sc-closed-immersion-pushforward-exact, hence also on module sheaves: kernels and
   sheafified cokernels have the same underlying abelian sheaves
   (def-weil-sheaf-of-modules-category). It therefore commutes with cohomology. By
   lem-sc-closed-pushforward-abelian-stalks it reflects zero and vanishes off the image.
2. For any representative E and K-injective resolution E → I, termwise pushforward
   preserves quasi-isomorphisms by lem-weil-pbc-exact-functor-derived-factorization.
   Thus Q(i_*E) ≅ Q(i_*I) ≅ Ri_*E by def-pc-derived-direct-image and
   def-pc-ringed-spaces-derived-direct-image. This works without boundedness, commutes
   with shifts and preserves triangles. Restriction to an ambient open commutes with
   pushforward, since both evaluate on W as E(i⁻¹W).
3. The approximation condition def-sfb-m-pseudo-coherent-complex is local, implies the
   corresponding condition for all larger integers, and supplies a local upper
   cohomology bound. If all cohomology in degrees ≥ m vanishes, the zero approximation
   suffices.
4. For A = O_Z^r[-p], A is a-pseudo-coherent for every a by its strictly perfect model
   (def-pc-perfect-complex). Its image is B^r[-p], where B = i_*O_Z. A local bounded-above
   finite free model of B[0] (def-pur-pseudo-coherent-complex), summed and shifted and
   brutally truncated in degrees ≥ a, gives an a-approximation to this image.
5. Induct simultaneously in both directions on the nonnegative integer p-m+1 for
   objects with H^q(E)=0 for q>p, allowing every ambient open restriction. The base
   p=m-1 follows from step 3 and exactness. Off the closed image there is nothing to do.
6. In either direction H^p(E) is locally finite type: apply
   lem-sfb-ringed-site-pseudocoherent-top-finite-type to E or i_*E at degree p. In the
   latter case the closed-pushforward stalk formula transports finite generators to
   Z, and generators over O_P remain generators over O_Z
   (def-weil-pbc-module-finite-type-presentation). Generation is locally surjective
   by lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective.
7. Lift the finitely many generators locally through ker d^p → H^p(E), using that same
   local-surjectivity criterion and intersecting their finitely many neighbourhoods.
   The lifted cycles define A → E surjective on H^p. Every neighbourhood in Z is the
   trace of an ambient open. Rank zero requires no lifts.
8. Complete this map to A → E → C → A[1] (def-weil-triangulated-category).
   The long exact sequence (lem-sf-derived-homology-long-exact) gives H^q(C)=0 for q≥p.
   Pushforward gives the corresponding triangle, and both A and i_*A are m- and
   (m+1)-pseudo-coherent by step 4.
9. In the forward direction clause (1) of lem-sfb-ringed-site-m-pseudocoherent-triangle
   makes C m-pseudo-coherent. Induction makes i_*C m-pseudo-coherent, and clause (2)
   applied to the pushed triangle makes i_*E m-pseudo-coherent.
10. In the reverse direction clause (1) on the pushed triangle makes i_*C
    m-pseudo-coherent. Induction makes C m-pseudo-coherent, and clause (2) on the
    original triangle makes E m-pseudo-coherent. Finally, either original condition
    supplies a local upper bound, exactness transfers it, and locality glues the
    induction. No global bound, quasi-coherence or Noetherian condition is needed. -/
theorem isMPseudoCoherent_closed_pushforward_iff
    {Z P : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i]
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{wP} (SheafOfModules.{u} (moduleRings P.toRingedSpace))]
    [∀ U : Z.Opens,
      HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ U : P.Opens,
      HasDerivedCategory.{wP} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ U : P.Opens,
      HasDerivedCategory.{wP} (SheafOfModules.{u} ((moduleRings P.toRingedSpace).over U))]
    (h : IsPseudoCoherent P
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings P.toRingedSpace)) 0).obj
          ((RingedSpace.moduleDirectImage i.toLRSHom.toShHom).obj
            (SheafOfModules.unit (moduleRings Z.toRingedSpace)))))
    (m : ℤ) (K : schemeDerivedCategory Z) :
    IsMPseudoCoherent Z m K ↔
      IsMPseudoCoherent P m ((schemeDerivedDirectImage i).obj K) := by
  sorry

end AlgebraicGeometry.Scheme
