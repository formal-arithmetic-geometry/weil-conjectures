module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Sheaf.AlgebraicGeometry.UnramifiedMorphism

/-! # The universal closed-immersion locus in the base is open

Source: Stacks Project, Tag 05XA, `spaces-more-morphisms-lemma-where-closed-immersion`,
specialized to schemes. (blueprint: lem-sfb-universal-closed-immersion-open)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The base changes making the given morphism a closed immersion are represented
by an open subscheme of the base.

Source: Stacks Project, Tag 05XA, `spaces-more-morphisms-lemma-where-closed-immersion`.
(blueprint: lem-sfb-universal-closed-immersion-open)

Proof: The graph of f is the pullback of the diagonal of q. Separatedness of q
and lem-weil-pbc-closed-immersion-base-change make this graph a closed immersion.
Closed immersions are universally closed by lem-weil-pbc-closed-immersion-proper.
The projection A ×_B C → C is universally closed by
lem-weil-pbc-universally-closed-base-change applied to p. Graph factorization
and composition therefore make f universally closed. Base change and composition
also make every f_T and A ×_C A → B universally closed, hence the latter and p
are closed maps. Apply lem-sfb-universal-unramified-radicial-open (Tag 05X9)
with the local finite type hypothesis on p to obtain an open V representing
simultaneous unramifiedness and universal injectivity of f_T.

For any h : T → B, write g = f_T. If g is unramified and universally injective,
its diagonal is a surjective open immersion, hence an isomorphism. The two
projections from A_T ×_{C_T} A_T then agree, so cancellation through the fibre
product shows g is a monomorphism. Its diagonal is also a closed immersion,
so g is separated. Universal closedness implies quasi-compactness by
lem-weil-pbc-universally-closed-quasi-compact. Together with the local finite
type part of unramifiedness this makes g finite type and proper. Now
lem-pc-proper-monomorphism-closed makes g a closed immersion. Conversely, that
same proper-monomorphism criterion makes any closed immersion proper and mono.
It is locally of finite type and its diagonal is an isomorphism, hence open
and surjective. Thus g is unramified and universally injective by
def-weil-unramified-morphism and def-weil-radicial-morphism. Combining these
implications with the universal property of V proves the claimed equivalence
for every T and h. -/
theorem exists_universalClosedImmersionOpen {B A C : Scheme.{u}}
    (p : A ⟶ B) (q : C ⟶ B) (f : A ⟶ C) (hf : f ≫ q = p)
    [LocallyOfFiniteType p] [UniversallyClosed p] [IsSeparated q] :
    ∃ V : B.Opens, ∀ (T : Scheme.{u}) (h : T ⟶ B),
      IsClosedImmersion (pullback.map p h q h f (𝟙 T) (𝟙 B)
        (by simpa only [Category.comp_id] using hf.symm) (by simp)) ↔
      ∃ l : T ⟶ V.toScheme, l ≫ V.ι = h := by
  sorry

end AlgebraicGeometry
