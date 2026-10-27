module

public import Sheaf.AlgebraicGeometry.SpacePicardObstructionData
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Sheaf.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor
import Sheaf.CategoryTheory.SiteCohomologyPullback
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! # Functorial Picard obstructions for algebraic-space thickenings

Source: Stacks Project, More on Morphisms of Spaces, Tag 0DNM, with naturality
of the units sequence; Cohomology on Sites, Tags 040E, 01FT and 08J6
(blueprint: lem-sfb-space-picard-obstruction-natural).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open CategoryTheory.RingedSitePicard
namespace AlgebraicGeometry.AlgebraicSpace

/-- The normalized units boundary has exactly the line-lifting kernel and commutes
with every square of square-zero thickenings. Presentations use the existing small
etale affine basis, whose restriction equivalence preserves line classes and derived
sections. E and E' are not arbitrary short exact sequences: their maps are prescribed
on every chart by j to 1+j and the actual structure-sheaf quotient. Their extension
classes, and therefore the displayed obstruction homomorphisms, are canonical.

The coefficient map is the unique additive inverse-image map prescribed by pullback
on lifted charts. Its scalar extension is h-star J to K. The formula on cohomology
is exact inverse image on Ext followed by this coefficient map. No cartesianness
or flatness hypothesis occurs.

Source: Stacks Project, Tag 0DNM; Tags 040E, 01FT and 08J6
(blueprint: lem-sfb-space-picard-obstruction-natural).

Proof:
1. Identify the etale topoi of the thickening and its reduction using
lem-sfb-space-first-order-ringed-description. The normalized lifted-chart model
identifies the quotient with pullback of regular functions. Its kernel is the
quasi-coherent square-zero ideal with the quotient module action. Restrict to the
small affine basis. The enlarged-site model
lem-trf-space-enlarged-etale-ringed-site-model supplies the canonical ringed topoi.
2. The formula (1+j)(1+k)=1+j+k and inverse 1-j give the additive units inclusion.
A quotient unit and its inverse lift locally to r and s. If rs=1+t, correct the
inverse to s(1-t). This proves sheaf-local surjectivity, hence gives E.
3. Abelian sheaves have enough injectives by
lem-weil-pbc-site-sheaves-enough-injectives. Apply
lem-weil-pbc-horseshoe-delta-functor to global sections. By
lem-sfb-ringed-site-picard-h1-natural the Picard comparison is additive, tensor
normalized, and natural for the quotient. The long exact sequence identifies its
kernel with restrictions of line classes. The boundary is Yoneda composition with
E.exact.extClass, so is precisely E.obstruction, independently of resolutions.
4. For a commuting square, pull back the units sequence by exact additive inverse
image. The map on thickened functions sends the first ideal into the second. Its
restriction is linear for the quotient actions because K squared is zero. On lifted
charts its inclusion is the ordinary pullback of functions: IsPicardIdealMap.
This fixes the coefficient map uniquely by the local generation of inverse image;
existence follows by gluing the chart maps. Tensor adjunction gives h-star J to K.
5. The identity q(1+j)=1+q(j) gives a morphism of the units sequences. Apply
lem-weil-pbc-site-cohomology-pullback and naturality of the horseshoe boundary.
The integer comparison preserves 1, so the Ext pullback is the same resolution
pullback used by the Picard-H1 theorem. That theorem identifies its units map with
tensor pullback of line classes, giving the displayed naturality identity.
All inverse images used on exact sequences are abelian inverse images; tensor
pullback itself need not preserve exact sequences. -/
theorem space_picard_obstruction_natural {S : Scheme.{u}} :
    ∃ c : ∀ X : AlgebraicSpace S, Comparison.{u, u} X.smallStructureSheaf,
      (∀ (X X' : AlgebraicSpace S) (i : X ⟶ X'),
        IsSpaceFirstOrderThickening i →
        ∃ (T : ThickeningSiteModel i) (I : SquareZeroIdeal T),
          I.obj.IsQuasicoherent ∧ Nonempty (PicardUnitsSequence T I)) ∧
      (∀ (X X' : AlgebraicSpace S) (i : X ⟶ X'),
        IsSpaceFirstOrderThickening i →
        ∀ (T : ThickeningSiteModel i) (I : SquareZeroIdeal T),
          I.obj.IsQuasicoherent → Nonempty (PicardUnitsSequence T I)) ∧
      (∀ (X X' : AlgebraicSpace S) (i : X ⟶ X'),
        IsSpaceFirstOrderThickening i →
        ∀ (T : ThickeningSiteModel i) (I : SquareZeroIdeal T),
          I.obj.IsQuasicoherent → ∀ (E : PicardUnitsSequence T I)
            (M : Line X.smallStructureSheaf),
          E.obstruction (c X) (lineClass M) = 0 ↔
            ∃ N : Line X'.smallStructureSheaf,
              Nonempty ((smallModuleTensorPullback i).obj N.val ≅ M.val)) ∧
      ∀ (X X' Y Y' : AlgebraicSpace S) (i : X ⟶ X') (j : Y ⟶ Y'),
        IsSpaceFirstOrderThickening i → IsSpaceFirstOrderThickening j →
        ∀ (h : Y ⟶ X) (h' : Y' ⟶ X'), j ≫ h' = h ≫ i →
        ∀ (T : ThickeningSiteModel i) (W : ThickeningSiteModel j)
          (I : SquareZeroIdeal T) (K : SquareZeroIdeal W),
          I.obj.IsQuasicoherent → K.obj.IsQuasicoherent →
          ∀ (E : PicardUnitsSequence T I) (E' : PicardUnitsSequence W K),
            (∃! β : (moduleTensorPullback h).obj I.obj ⟶ K.obj,
              IsPicardModuleIdealMap T W I K h h' β) ∧
            ∃ (P : PicardAbInverse h) (α : P.functor.obj (picardIdeal I) ⟶ picardIdeal K),
              (∀ α' : P.functor.obj (picardIdeal I) ⟶ picardIdeal K,
                IsPicardIdealMap T W I K h h' P α' ↔ α' = α) ∧
              ∀ M : Line X.smallStructureSheaf,
                ∃ N : Line Y.smallStructureSheaf,
                  Nonempty ((smallModuleTensorPullback h).obj M.val ≅ N.val) ∧
                  E'.obstruction (c Y) (lineClass N) =
                    Sheaf.H.map α 2
                      (P.cohomology (picardIdeal I) 2 (E.obstruction (c X) (lineClass M))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
