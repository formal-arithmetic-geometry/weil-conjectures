module

public import Sheaf.Paper.LocalizedOrdinaryPullbackData
import Sheaf.Paper.LocalizedOrdinaryCoefficientCoherence
import Sheaf.Paper.LocalizedOrdinaryEdge
import Sheaf.Paper.LocalizedOrdinaryComposition
import Sheaf.Paper.LocalizedOrdinaryIdentity

/-! # Localized ordinary pullback normalization

Source: Stacks Project, Tags 03CB, 0D6D, 07A4; Bhatt--Scholze, Remark 6.8.15.
(blueprint: lem-per-localized-ordinary-pullback-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.LocalizedOrdinary

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (ϖ : PbcIntegralRing l E)
  {X Y Z : Scheme.{u}} (g : Y ⟶ X) (h : Z ⟶ Y)

/-- Finite and completed coefficient composition and normalized scalar-localization
pullback, including the two specified equations of natural transformations.
Source: Stacks Project, Tags 03CB, 0D6D, 07A4; Bhatt--Scholze, Remark 6.8.15, p. 62.
(blueprint: lem-per-localized-ordinary-pullback-normalization).

Proof:
1. Transpose the two finite maps through the composite site adjunction. Both
send every constant residue to itself. Constant sheafification determines the
maps uniquely, including quotient transitions, identity and uniformizer scalars.
2. Compose the defining projection equation for completedCoefficientMap twice.
Finite composition and naturality of the inverse-image compositor identify the
results. Joint monicity of the actual limit projections gives completed composition
and identity. The compatible family of constant residues gives scalar preservation.
No inverse-image/limit interchange is used.
3. Apply lem-weil-pbc-localization-inverse-image-coherence, preserving localization
units. The induced coefficient map sends b/varpi^r to c(b)/varpi^r; its unit square
fixes it uniquely, including composition and identity.
4. Resolve an arbitrary unbounded object by a flat-term K-flat complex using
lem-pc-kflat-resolution. Ringed pullback and scalar extension preserve this class
by lem-weil-pbc-ringed-topoi-derived-tensor-pullback. The normalized ordinary
comparisons of lem-sfb-ringed-derived-monoidal-comparisons compute their derived maps.
5. Flatten the source by e tensor (b tensor q) mapping to e iota(b) tensor q.
Flatten the target by e tensor (e0 tensor q) mapping to e d(e0) tensor q.
The inverse inserts one. Balancing follows from the coefficient-unit square;
these maps commute with restrictions and differentials and are natural in q.
The localization module comparison beta supplies the pulled fraction coordinates.
6. On e'' tensor b' tensor q, both composition routes give
 e'' iota(c_h(b')) tensor q, by the localized coefficient-unit square.
The rational compositor multiplies e'' d_h(e') and its inverse inserts one.
Both identity routes give e iota(b) tensor q. Pure tensors and sheafification
therefore give equal chain maps, including the ordinary squares.
7. Localize these equal maps on the flat-term K-flat resolving category using
lem-weil-pbc-site-derived-tensor-descent and
lem-weil-pbc-ringed-topoi-derived-pullback. Naturality extends to inverses of
quasi-isomorphisms and hence all derived morphisms. Conjugating by a resolving
isomorphism gives the equations for every K, independent of its representative.
No structural coefficient map is assumed invertible. -/
theorem localizedOrdinaryPullbackNormalization
    (_hϖ : Ideal.span ({ϖ} : Set (PbcIntegralRing l E)) = (pbcIntegralDatum l E).ideal)
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
    [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
    [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))] :
    Coefficients l E g h ∧
    ∃ (ag : Edge l E ϖ g) (ah : Edge l E ϖ h) (ac : Edge l E ϖ (h ≫ g))
      (ai : Edge l E ϖ (𝟙 X)),
      Nonempty (Composition l E ϖ g h ag ah ac) ∧ Nonempty (Identity l E ϖ X ai)  := by
  have hc := localizedOrdinaryCoefficientCoherence l E g h
  obtain ⟨ag⟩ := localizedOrdinaryEdge_exists l E ϖ g
  obtain ⟨ah⟩ := localizedOrdinaryEdge_exists l E ϖ h
  obtain ⟨ac⟩ := localizedOrdinaryEdge_exists l E ϖ (h ≫ g)
  obtain ⟨ai⟩ := localizedOrdinaryEdge_exists l E ϖ (𝟙 X)
  exact ⟨hc, ag, ah, ac, ai,
    localizedOrdinaryComposition_exists l E ϖ g h hc ag ah ac,
    localizedOrdinaryIdentity_exists l E ϖ X hc.completed_id ai⟩

end AlgebraicGeometry.Scheme.LocalizedOrdinary
