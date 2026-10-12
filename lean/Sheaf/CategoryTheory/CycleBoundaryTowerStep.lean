module

public import Sheaf.CategoryTheory.ExactCouple

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory.BigradedExactCouple
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A single page presented as a quotient of subobjects of the initial page.
Source: blueprint def-sp-convergence (blueprint: lem-cycle-boundary-tower-step). -/
structure CycleBoundaryStage (X : BigradedExactCouple C 0) (r : ℕ) where
  Z : ∀ p q : ℤ, Subobject (X.E p q)
  B : ∀ p q : ℤ, Subobject (X.E p q)
  B_le_Z : ∀ p q, B p q ≤ Z p q
  projection : ∀ p q, (Z p q : C) ⟶ (X.pageCouple r).E p q
  projection_epi : ∀ p q, Epi (projection p q)
  projection_kernel : ∀ p q,
    kernelSubobject (projection p q) =
      Subobject.mk (Subobject.ofLE (B p q) (Z p q) (B_le_Z p q))

/-- One canonical successor of a quotient presentation. The subobjects and the
projection are pinned by the pullback formulas and the kernel-lift equation.
Source: blueprint def-sp-convergence (blueprint: lem-cycle-boundary-tower-step). -/
structure CycleBoundaryStep (X : BigradedExactCouple C 0) (r : ℕ)
    (T : CycleBoundaryStage X r) where
  next : CycleBoundaryStage X (r + 1)
  Z_succ : ∀ p q, next.Z p q =
    (Subobject.«exists» (T.Z p q).arrow).obj
      ((Subobject.pullback (T.projection p q)).obj
        (kernelSubobject ((X.pageCouple r).d p q)))
  B_succ : ∀ p q, next.B p q =
    (Subobject.«exists» (T.Z p q).arrow).obj
      ((Subobject.pullback (T.projection p q)).obj
        (imageSubobject ((X.pageCouple r).dInto p q)))
  Z_decreasing : ∀ p q, next.Z p q ≤ T.Z p q
  B_increasing : ∀ p q, T.B p q ≤ next.B p q
  cycleLift : ∀ p q, (next.Z p q : C) ⟶ kernel ((X.pageCouple r).d p q)
  cycleLift_comm : ∀ p q,
    cycleLift p q ≫ kernel.ι ((X.pageCouple r).d p q) =
      Subobject.ofLE _ _ (Z_decreasing p q) ≫ T.projection p q
  projection_succ : ∀ p q,
    next.projection p q = cycleLift p q ≫ (X.pageCouple r).derivedEProjection p q

/-- A single successor quotient presentation exists.
Pull back the differential kernel and incoming image along the given epimorphic
projection, and map these subobjects along the monic inclusion of Z in the initial
page. The differential squares to zero, so the incoming image is in the kernel;
this gives B' ≤ Z'. The image of the old kernel of the projection is in the
pullback of the incoming image, giving B ≤ B', and both pullbacks lie in Z.
Restrict the projection to Z'. Its composite with the differential is zero, so
kernel universality gives a unique cycle lift. This lift is epimorphic onto the
kernel: it is the pullback of the old epimorphism. Compose it with the canonical
homology quotient derivedEProjection to define the next projection. This composite
is epi. Its kernel is the pullback of the kernel of derivedEProjection, namely
the incoming differential image inside the differential kernel; therefore its
kernel is precisely B' as a subobject of Z'. These constructions give all fields.
The displayed equations determine Z', B', the lift (by monicity of kernel.ι), and
then the next projection; hence the witness contains no arbitrary quotient choice.
Source: blueprint def-sp-convergence; Stacks Sections 12.20--12.21
(blueprint: lem-cycle-boundary-tower-step). -/
theorem cycleBoundaryStep_exists (X : BigradedExactCouple C 0) (r : ℕ)
    (T : CycleBoundaryStage X r) : Nonempty (CycleBoundaryStep X r T) := by
  sorry

end CategoryTheory.BigradedExactCouple
