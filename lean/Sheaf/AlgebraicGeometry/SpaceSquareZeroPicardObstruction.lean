module

public import Sheaf.AlgebraicGeometry.SpacePicardUnitsPresentation
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
public import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.Sites.RingedSitePicardH1Natural
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Mathlib.CategoryTheory.Sites.EpiMono

/-! # The Picard obstruction for a square-zero thickening of algebraic spaces

Source: Stacks Project, More on Morphisms of Spaces, Tag 0DNM, the middle row and
connecting map into H² (blueprint: lem-sfb-space-square-zero-picard-obstruction).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open CategoryTheory.RingedSitePicard

attribute [instance] SheafOfModules.isGrothendieckAbelian

namespace AlgebraicGeometry.AlgebraicSpace

/-- There is a canonical obstruction homomorphism whose kernel is exactly the image
of tensor restriction on Picard groups; vanishing of H² gives a line extension with
its restriction isomorphism. Picard groups are the existing quotients of actual lines,
with the tensor law fixed by Comparison. The equation for delta fixes it by the units
boundary and the canonical module-to-abelian comparison. The kernel presentation
identifies J, including its quotient module action, without any arbitrary choice of ideal.

Source: Stacks Project, More on Morphisms of Spaces, Tag 0DNM; Cohomology on Sites,
Tags 040E and 03FD (blueprint: lem-sfb-space-square-zero-picard-obstruction).

Proof:
1. By lem-sfb-space-first-order-ringed-description, identify the étale sites by
restriction and the ring quotient by regular-function pullback on lifted charts.
Use lem-trf-space-enlarged-etale-ringed-site-model and the small affine basis to
retain the same module topos and global sections. The kernel is quasi-coherent,
and its action factors through O_Z because J²=0. This gives the ring and ideal
part of the normalized presentation.
2. On this site 1+x is a unit with inverse 1-x. The formula
(1+x)(1+y)=1+x+y identifies the additive ideal with the units kernel. A unit b and
its inverse lift locally to a,c; if ac=1+x, then c(1-x) inverts a. Thus the units
map is locally surjective, hence epi by
lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective, giving short exactness.
3. Abelian sheaves have enough injectives by
lem-weil-pbc-site-sheaves-enough-injectives. Apply
lem-weil-pbc-right-derived-universal-delta-functor to this sequence: the image on
H¹ is precisely the kernel of the canonical connecting map into H².
4. Apply lem-sfb-ringed-site-picard-h1-natural to the thick and reduced ring
sheaves. Their comparisons send a line to its generator extension class and
respect tensor products. Naturality for the quotient identifies its H¹ map with
extension of scalars, hence with the specified tensor pullback j*. The site and
module equivalences identify this with the small-model expression below.
5. Module sheaves have enough injectives by
lem-pur-ringed-site-grothendieck-abelian and lem-sp-grothendieck-enough-injectives.
The normalized comparison of
lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison, applied at the final
object of the enlarged site, identifies module and abelian H². Under Ext from O,
this is exactly forgetful pushforward of extensions precomposed with Z→O,
1↦1. Thus moduleToAbelian is bijective, independently of the resolutions.
6. Define delta by the units boundary followed by the inverse of this comparison
and of x↦1+x. The displayed normalization fixes delta. Transport step 3 through
the generator comparisons to get exactness. If module H² vanishes, every line
class is in this kernel. Equality of line classes supplies a restriction
isomorphism, included explicitly in the last assertion. No Noetherianity,
properness, or nonemptiness was used. -/
theorem space_squareZero_picard_obstruction
    {S : Scheme.{u}} {Z Z' : AlgebraicSpace S} (j : Z ⟶ Z')
    (hj : IsSpaceFirstOrderThickening j) :
    ∃ (P : SpacePicardUnitsPresentation j)
      (c' : Comparison Z'.smallStructureSheaf) (c : Comparison Z.smallStructureSheaf)
      (r : @AddMonoidHom (Pic Z'.smallStructureSheaf) (Pic Z.smallStructureSheaf)
        c'.group.toAddZeroClass.toAddZero c.group.toAddZeroClass.toAddZero)
      (δ : @AddMonoidHom (Pic Z.smallStructureSheaf)
        (picardModuleCohomology Z (Z.smallModuleRestriction.obj P.ideal.obj) 2)
        c.group.toAddZeroClass.toAddZero inferInstance),
      (∀ M : Line Z'.smallStructureSheaf, ∃ N : Line Z.smallStructureSheaf,
        Nonempty (N.val ≅ (Z.smallModuleRestriction.obj
          ((moduleTensorPullback j).obj (Z'.smallModuleEquivalence.inverse.obj M.val)))) ∧
        r (lineClass M) = lineClass N) ∧
      Function.Bijective (P.moduleToAbelian 2) ∧
      (∀ L : Pic Z.smallStructureSheaf,
        P.moduleToAbelian 2 (δ L) = Sheaf.H.map P.unitsIdentification.inv 2
          (Sheaf.H.δSucc P.exact 1 (c.comparison L))) ∧
      Function.Exact r δ ∧
      (Subsingleton (picardModuleCohomology Z (Z.smallModuleRestriction.obj P.ideal.obj) 2) →
        ∀ L : Line Z.smallStructureSheaf, ∃ L' : Line Z'.smallStructureSheaf,
          Nonempty ((Z.smallModuleRestriction.obj
            ((moduleTensorPullback j).obj
              (Z'.smallModuleEquivalence.inverse.obj L'.val))) ≅ L.val)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
