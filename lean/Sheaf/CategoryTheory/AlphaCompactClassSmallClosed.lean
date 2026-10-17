/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.CategoryTheory.AlphaCompactObject
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.CategoryTheory.AlphaCompactObjectProperties

/-! # Krause's maximal alpha-compact class identification -/

@[expose] public section

universe v u

open CategoryTheory.Limits

namespace CategoryTheory

/-- Krause's maximal alpha-compact class is small and extension closed when
there is a small shift-closed perfect generating class of alpha-small objects.

Source: Krause, On Neeman's Well Generated Triangulated Categories (2001),
Lemma 5, pages 124--125; Localization theory, Sections 6.2--6.3.
(blueprint: new-sfb-alpha-compact-class-small-closed)

Proof in words: pick a v-small skeleton G0 of G. Condition (G4) implies (G2):
factor a map into a coproduct through objects of G, lift each component using
surjectivity, and assemble the lifts by the coproduct universal property.
The proved isZero_of_localizing_generators API gives (G1). Its proof uses the
double orthogonal: for an object Y orthogonal to G,
the objects X with Hom(X[n],Y)=0 for every integer n form a localizing class
containing G. Generation makes this all of C. Taking X=Y and n=0 kills its
identity, so Y is zero.

Let H be the alpha-localizing closure of G0. Construct its skeleton iteratively
using shifts, cones, retracts and coproducts with fewer than alpha summands.
At each stage the proved EssentiallySmall.shiftClosure API bounds shifts, and
EssentiallySmall.extensionProduct bounds cones by
their connecting maps. Mathlib bounds retracts by idempotents. The proved
EssentiallySmall.bounded_coproducts API bounds the smaller coproducts by reindexing
their supports into a fixed set of cardinality alpha. Iterate these operations
through the initial ordinal of alpha, taking unions at limit stages. Every stage
is essentially v-small, and the set of stages is v-small, so their union is
essentially v-small. Regularity bounds the stages occupied by fewer than alpha
inputs below alpha, making this union closed under the bounded coproducts.
Finite operations stabilize as well since a regular cardinal is infinite.
This union is the smallest alpha-localizing hull H, which is essentially v-small.
The objects of H are alpha-small: support smallness is invariant under shifts
and retracts, and is preserved under extensions and bounded coproducts, as proved
in the alpha-small API. To propagate (G4) across a cone U to V to X, factor the restriction of a map
X to a coproduct of Y_i through a coproduct of V_i in the current class. Choose
fiber triangles F_i to V_i to Y_i. The composite from U to the coproduct of V_i
is killed in the coproduct of Y_i, so triangle exactness lifts it to the coproduct
of F_i. Factor that lift by (G4) through U_i in the current class. The maps U_i to
V_i now form a commuting square with U to V. Complete it to a morphism of cone
triangles, giving a map X to the coproduct of cones C_i of U_i to V_i. Each C_i
maps to Y_i. The difference from the original map vanishes on V, hence factors
through U[1]; apply (G4) to that residual map and add its factors to C_i.
These are again hull objects. Coproducts are handled by transposing iterated
coproduct factorizations; shifts, repletion and retracts transport them. This
proves (G4) by induction through the hull construction. Lemma 4 also expresses
this propagation as preservation of (G2).

To identify H with the maximal class S of alpha-small objects satisfying (G4),
consider objects Y such that every map from an object of S to Y factors through
an object of H. The same closure argument, without any small-skeleton assertion, shows that the
maximal class S is closed under cones. The factor-through-H class contains G0:
any map into a generator already factors through that generator. It is shift
closed because S and H are shift closed. For a map to a coproduct of its objects,
use (G4) to obtain S-components, factor each component through H, then restrict
the whole map to a support smaller than alpha. The resulting smaller coproduct
of H-objects is in H, which proves coproduct closure.
For a cone Y0 to Y1 to Y2 with Y0,Y1 in this class, factor the connecting map
X to Y2 to Y0[1], for X in S, through H0 in H. Its fiber X' belongs to S because
X,H0 do. Triangle completion lifts the restriction X' to Y2 through Y1, and this
lift factors through H1 in H. Form the cone H2 of the induced map H0[-1] to H1;
it belongs to H. Completing the two cone squares gives X to H2 to Y2, agreeing
with the original map on X'. Their difference factors through H0. Thus the
original map factors through H2 plus H0, in H. This proves cone closure.
Therefore this is a localizing class containing G0. Generation makes it all of C. For each
X in S its identity therefore factors through an object of H, so X is a retract
of an object of H and belongs to H. Conversely H satisfies (G3)--(G4), hence is
contained in S by the definition of IsAlphaCompact. This identifies S with H.
Essential smallness follows, and triangulated closure of H gives the displayed
middle-vertex closure. No Grothendieck category or choice of a larger cardinal
is involved in this generic lemma.

Reference: https://ftp.gwdg.de/pub/misc/EMIS/journals/DMJDMV/vol-06/07.pdf,
Lemma 5 and its proof.
-/
theorem alphaCompactObjects_small_closed
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C] [HasCoproducts.{v} C]
    (G : ObjectProperty C) [ObjectProperty.EssentiallySmall.{v} G]
    [G.IsStableUnderShift ℤ] (α : Cardinal.{v}) [Fact α.IsRegular]
    (hGsmall : ∀ X, G X → IsAlphaSmall X α)
    (hGfactor : G.IsCoproductFactorizationClass)
    (hGgen : ∀ (S : ObjectProperty C) [S.IsClosedUnderIsomorphisms] [S.IsTriangulated],
      (∀ (I : Type v) (Y : I → C), (∀ i, S (Y i)) → S (∐ Y)) →
      G ≤ S → ∀ X, S X) :
    ObjectProperty.EssentiallySmall.{v} (alphaCompactObjects C α) ∧
      (alphaCompactObjects C α).IsTriangulatedClosed₂ := by sorry

end CategoryTheory
