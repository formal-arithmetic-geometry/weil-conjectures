module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.RelativeFlatLocusBaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # The universal flatness open for a morphism between relative families

Source: Stacks Project, Tag 05XB, `spaces-more-morphisms-lemma-where-flat`,
statement and displayed construction in the proof, specialized to schemes.
(blueprint: lem-sfb-relative-universal-flat-open)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The complement of the image of the nonflat locus is an open subscheme representing
precisely the base changes for which the relative morphism is flat. The scheme `F.toScheme`
is equipped with the restricted structure sheaf, and its canonical inclusion `F.ι` is an
open immersion.

Source: Stacks Project, Tag 05XB, `spaces-more-morphisms-lemma-where-flat`, specialized
to schemes, with the relative source flat locus supplied by Tag 05VK.
(blueprint: lem-sfb-relative-universal-flat-open)

Proof:
1. By lem-sfb-relative-flat-locus-base-change, the locus U where f is flat at a point
   is open, and the flat locus of every f_T is the inverse image of U under the first
   projection X ×_S T -> X. Its assumptions are exactly flatness and local finite
   presentation of p, local finite type of q, and the equality f ≫ q = p.
2. Put C = X minus U. Closedness of p makes p(C) closed, so F = S minus p(C) is open.
   Give F the restricted structure sheaf. Around each point choose an affine chart of S
   and then a principal open lying in F, using lem-weil-pbc-spec-localization-away-basic-open.
   By lem-weil-pbc-principal-localization-open-immersion this is the spectrum of a
   localization, so F is a scheme. Its canonical inclusion is an open immersion.
3. For any T and h, the nonflat locus of f_T is the inverse image of C. By
   lem-weil-pbc-base-change-image, its image in T is h inverse-image of p(C). A set is
   empty exactly when its image under a function is empty. The stalkwise criterion
   in def-weil-flat-morphism therefore identifies flatness of f_T with h(T) contained
   in F. No closedness of the base-changed projection is used.
4. By lem-weil-pbc-morphism-factors-through-open-subscheme, the last containment is
   equivalent to a factorization of h through F.ι. Conversely every such factorization
   has image in F. This proves both implications for every scheme T, including empty
   and nonreduced schemes. -/
theorem exists_relativeUniversalFlatOpen {S X Y : Scheme.{u}}
    (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y) (hf : f ≫ q = p)
    [Flat p] [LocallyOfFinitePresentation p] (hp : IsClosedMap p)
    [LocallyOfFiniteType q] :
    ∃ F : S.Opens,
      (F : Set S) = (p '' {x : X | (f.stalkMap x).hom.Flat}ᶜ)ᶜ ∧
      ∀ (T : Scheme.{u}) (h : T ⟶ S),
        Flat (pullback.map p h q h f (𝟙 T) (𝟙 S)
          (by simpa only [Category.comp_id] using hf.symm) (by simp)) ↔
        ∃ l : T ⟶ F.toScheme, l ≫ F.ι = h := by
  sorry

end AlgebraicGeometry
