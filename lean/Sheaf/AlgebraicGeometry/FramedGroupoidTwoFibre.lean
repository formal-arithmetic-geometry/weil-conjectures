module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Mathlib.CategoryTheory.Elements
import WeilConjectures.AlgebraicGeometry.ConstantPullbackCompositionCoherence
import WeilConjectures.AlgebraicGeometry.ConstantPullbackIdentityCoherence

/-!
# The two-fibre product of a framed groupoid

Source: Stacks Project, Categories, Tags 003R and 0040; the abstract frame calculation
motivated by Pikaart--de Jong, §2.3.3 (blueprint: lem-sfb-framed-groupoid-two-fibre).

The category of elements retains objects and arrows, including all automorphisms of
the unframed category. Its opposite gives the total category of framed objects.
A map from a representable fibred category specifies the chosen cartesian lifts.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- The cartesian module-sheaf assignment in the framing comparison. The two equations
use the specified inverse-image unit and associator, not strict pullback equalities.
Source: Stacks 003R and 0040, abstract framing calculation motivated by
Pikaart--de Jong §2.3.3 (blueprint: lem-sfb-framed-groupoid-two-fibre). -/
structure CartesianFramingAssignment {S : Scheme.{u}}
    (X : BasedCategory.{v, w} (Over S)) (A : Type (u + 1)) [CommRing A] where
  /-- The module sheaf assigned to each object. -/
  sheaf (x : X.obj) : Sheaf (X.p.obj x).left.smallEtaleTopology (ModuleCat.{u + 1} A)
  /-- The specified inverse-image comparison for every arrow. -/
  pull {x y : X.obj} (a : x ⟶ y) :
    (Etale.upperStar (ModuleCat.{u + 1} A) (X.p.map a).left).obj (sheaf y) ≅ sheaf x
  /-- Normalization at identity arrows. -/
  pull_id (x : X.obj) : pull (𝟙 x) =
    eqToIso (by rw [X.p.map_id]; rfl) ≪≫
      (Etale.upperStarId (ModuleCat.{u + 1} A) (X.p.obj x).left).app (sheaf x)
  /-- Compatibility with composition and the canonical inverse-image associator. -/
  pull_comp {x y z : X.obj} (a : x ⟶ y) (b : y ⟶ z) :
    (pull (a ≫ b)).hom =
      (Etale.upperStarComp (ModuleCat.{u + 1} A) (X.p.map a).left (X.p.map b).left
        (X.p.map (a ≫ b)).left (by simp)).hom.app (sheaf z) ≫
      (Etale.upperStar (ModuleCat.{u + 1} A) (X.p.map a).left).map (pull b).hom ≫
        (pull a).hom

namespace CartesianFramingAssignment

variable {S : Scheme.{u}} {X : BasedCategory.{v, w} (Over S)}
variable {A : Type (u + 1)} [CommRing A]

/-- The actual rank-`n` constant module sheaf at a test scheme. Rank zero and the
zero ring are included. Source: Stacks 003R, framing calculation
(blueprint: lem-sfb-framed-groupoid-two-fibre). -/
def constant (A : Type (u + 1)) [CommRing A] (n : ℕ) (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
    (ModuleCat.of A (Fin n → A))

/-- A frame is an isomorphism of module sheaves, not an isomorphism class.
Source: Stacks 003R, framing calculation
(blueprint: lem-sfb-framed-groupoid-two-fibre). -/
abbrev Frame (H : CartesianFramingAssignment X A) (n : ℕ) (x : X.obj) :=
  constant A n (X.p.obj x).left ≅ H.sheaf x

/-- Pullback of a frame uses the inverse constant comparison, inverse image of the
frame, and the assigned comparison for the arrow, in that order.
Source: Pikaart--de Jong §2.3.3, generalized framing formula; Stacks 003R
(blueprint: lem-sfb-framed-groupoid-two-fibre). -/
def restrict (H : CartesianFramingAssignment X A) (n : ℕ)
    {x y : X.obj} (a : x ⟶ y) (lam : H.Frame n y) : H.Frame n x :=
  ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A)
      (X.p.map a).left).app (ModuleCat.of A (Fin n → A))).symm ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} A) (X.p.map a).left).mapIso lam ≪≫ H.pull a

/-- The frame restriction equations, including identity and composite base changes.
Source: Stacks 003R and 0040, proof Steps 4--5 of the abstract framing comparison.

Proof: expand restriction as `k_a`, inverse image of the frame, then `H(a)`.
For identities, the given unit equation for `H` and the canonical constant-sheaf
unit equation cancel. For composites, insert the inverse-image associator; naturality
moves it across the frame. The composition equation for `H` combines the first
factors, and constant-pullback composition coherence combines the constant factors.
The resulting composite is exactly restriction along `a ≫ b`.
(blueprint: lem-sfb-framed-groupoid-two-fibre). -/
theorem restrict_laws (H : CartesianFramingAssignment X A) (n : ℕ) :
    (∀ (x : X.obj) (lam : H.Frame n x), H.restrict n (𝟙 x) lam = lam) ∧
    (∀ {x y z : X.obj} (a : x ⟶ y) (b : y ⟶ z) (lam : H.Frame n z),
      H.restrict n (a ≫ b) lam = H.restrict n a (H.restrict n b lam)) := by
  sorry

/-- The presheaf of frames on the total unframed category. Its data are the actual
isomorphisms and the specified restriction formula; only their proved equations
are supplied by `restrict_laws`.
Source: Stacks 003R and 0040 (blueprint: lem-sfb-framed-groupoid-two-fibre). -/
def frames (H : CartesianFramingAssignment X A) (n : ℕ) : X.objᵒᵖ ⥤ Type (u + 1) where
  obj x := H.Frame n x.unop
  map a := TypeCat.ofHom (H.restrict n a.unop)
  map_id x := by
    apply ConcreteCategory.hom_ext
    intro lam
    exact (H.restrict_laws n).1 x.unop lam
  map_comp a b := by
    apply ConcreteCategory.hom_ext
    intro lam
    exact (H.restrict_laws n).2 b.unop a.unop lam

/-- The framed total category projects to `X` by forgetting the frame. Morphisms
are precisely arrows whose specified restriction carries the target frame to the
source frame. Source: Stacks 003R and 0040
(blueprint: lem-sfb-framed-groupoid-two-fibre). -/
def framed (H : CartesianFramingAssignment X A) (n : ℕ) : BasedCategory (Over S) :=
  BasedCategory.ofFunctor ((CategoryOfElements.π (H.frames n)).leftOp ⋙ X.p)

/-- Forgetting frames as a functor over the scheme base.
Source: Stacks 003R (blueprint: lem-sfb-framed-groupoid-two-fibre). -/
def forget (H : CartesianFramingAssignment X A) (n : ℕ) : BasedFunctor (H.framed n) X where
  toFunctor := (CategoryOfElements.π (H.frames n)).leftOp
  w := rfl

/-- The representable fibred category `h_T`, modelled by the slice over `T`.
Its fibre over `U` is the discrete set of maps `U → T`.
Source: Stacks 003T and 0040 (blueprint: lem-sfb-framed-groupoid-two-fibre). -/
def representable (T : Over S) : BasedCategory (Over S) :=
  BasedCategory.ofFunctor (Over.forget T)

/-- The 2-fibre product over `h_T`, retaining its actual projection to `Sch/T`.
Source: Stacks 003R and 0040 (blueprint: lem-sfb-framed-groupoid-two-fibre). -/
def twoFibre (H : CartesianFramingAssignment X A) (n : ℕ) {T : Over S}
    (t : BasedFunctor (representable T) X) : BasedCategory (Over T) :=
  BasedCategory.ofFunctor (moduliTwoFiberFst t (H.forget n)).toFunctor

/-- The discrete fibred groupoid of frames of the chosen pullbacks of `x`.
It uses the same `H(a)` on every base arrow, including composite arrows.
Source: Stacks 003R and 0040 (blueprint: lem-sfb-framed-groupoid-two-fibre). -/
def discreteFrames (H : CartesianFramingAssignment X A) (n : ℕ) {T : Over S}
    (t : BasedFunctor (representable T) X) : BasedCategory (Over T) :=
  BasedCategory.ofFunctor (CategoryOfElements.π (t.toFunctor.op ⋙ H.frames n)).leftOp

/-- The 2-fibre of the forgetful map is naturally the discrete groupoid of frames.
The first clause makes explicit that every object `x` gives a map `h_T → X`;
the second applies to every such choice, so no cleavage is an additional hypothesis.
The comma convention stores `φ⁻¹ : x_U → y`, so its image is the restriction of
`lam` along that arrow, namely `H(φ)⁻¹ lam` after the identity comparisons.

Source: Stacks 003R and 0040; abstract comparison motivated by Pikaart--de Jong §2.3.3.

Proof, Step 1: at `U → T`, a triple consists of `(y, lam, φ : y ≅ x_U)`.
Send it to `H(φ)⁻¹ lam`. Step 2: the comma square and frame equation show that
arrows have equal images. If images agree the unique arrow is `ψ⁻¹ φ`, proving
full faithfulness; triple automorphisms are identities even when `Aut(y)` is not.
Step 3: the inverse sends `ν` to `(x_U, ν, id)`. The comparison `φ` gives the
unit, the counit is the identity, and the two triangle identities follow.
Step 4: for a base map `f`, the cartesian comparison is characterized by
`c φ_V = φ b`; the equation for `H` identifies the two restrictions of the image.
Step 5: `restrict_laws` gives the identity and composition compatibility, using
the constant-pullback coherence nodes. Step 6: the inverse and the unit respect
these same comparisons, hence this is an equivalence over `Sch/T`. Every `x`
admits a cartesian section over its slice by the fibred-in-groupoids lifting
property; uniqueness of cartesian comparisons makes different lift choices agree.
No trivial-automorphism assumption is used.
(blueprint: lem-sfb-framed-groupoid-two-fibre). -/
theorem twoFibre_equivalence (H : CartesianFramingAssignment X A) (n : ℕ)
    (hX : IsFibredInGroupoids X) :
    (∀ x : X.obj, ∃ t : BasedFunctor (representable (X.p.obj x)) X,
      ∃ i : t.obj (Over.mk (𝟙 (X.p.obj x))) ≅ x,
        X.p.IsHomLift (𝟙 (X.p.obj x)) i.hom) ∧
    (∀ (T : Over S) (t : BasedFunctor (representable T) X),
      ∃ e : BasedFunctor (H.twoFibre n t) (H.discreteFrames n t),
        e.toFunctor.IsEquivalence ∧
        ∀ z : (H.twoFibre n t).obj,
          e.obj z = op ⟨op z.obj.left,
            (H.frames n).map z.obj.hom.op z.obj.right.unop.snd⟩) := by
  sorry

end CartesianFramingAssignment

end AlgebraicGeometry
