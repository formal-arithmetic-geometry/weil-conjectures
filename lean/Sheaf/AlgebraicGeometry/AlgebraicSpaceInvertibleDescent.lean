/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q76
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.SixFunctors.TraceFormula.SchemeEtaleInvertibleComparison

/-!
# Descent of invertible modules on an algebraic space

Source: Stacks Project, Spaces, Tags 04W8 and 060X; Descent, Tag 05VG;
Sites, Tags 04TR and 04TQ (blueprint: lem-trf-algebraic-space-invertible-descent).

Ordinary invertible modules are identified with restrictions of the descended module by
linear equivalences on every object of the localized étale site. The ordinary module's
value there is the global sections of its tensor pullback. This spells out the
Zariski/small-étale interpretation without choosing an inverse equivalence of categories.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.AlgebraicSpace

/-- Restriction of sections of ordinary pullbacks along a commuting scheme triangle.
The formula uses the canonical tensor-pullback unit and its unit-normalized composition
isomorphism, followed by transport along the triangle equation.
Source: Stacks, Descent, Tags 03DR and 05VG
(blueprint: lem-trf-algebraic-space-invertible-descent). -/
noncomputable def ordinaryEtaleSectionRestriction {X Y Z : Scheme.{u}}
    (L : Z.Modules) (p : Y ⟶ Z) (f : X ⟶ Y) (p' : X ⟶ Z) (h : f ≫ p = p') :
    Γ((tensorPullback p).obj L, ⊤) ⟶ Γ((tensorPullback p').obj L, ⊤) :=
  tensorSectionsUnit f ((tensorPullback p).obj L) ≫
    ((tensorSectionsComp f p).hom.app L).app ⊤ ≫
    (eqToHom (congrArg (fun a ↦ (tensorPullback a).obj L) h)).app ⊤

/-- Pull an overlap isomorphism back to a test scheme, identifying the two iterated
pullbacks by the canonical composition comparisons and the specified leg equations.
Source: Stacks, Spaces, Tag 04W8; Descent, Tag 03DR
(blueprint: lem-trf-algebraic-space-invertible-descent). -/
noncomputable def atlasTransitionOn {X Y R T : Scheme.{u}}
    (L : X.Modules) (K : Y.Modules) (p : R ⟶ X) (q : R ⟶ Y)
    (α : (tensorPullback q).obj K ≅ (tensorPullback p).obj L)
    (r : T ⟶ R) (a : T ⟶ X) (b : T ⟶ Y) (ha : r ≫ p = a) (hb : r ≫ q = b) :
    (tensorPullback b).obj K ≅ (tensorPullback a).obj L :=
  (eqToIso (congrArg (fun f ↦ (tensorPullback f).obj K) hb)).symm ≪≫
    ((tensorSectionsComp r q).app K).symm ≪≫
    (tensorPullback r).mapIso α ≪≫ (tensorSectionsComp r p).app L ≪≫
    eqToIso (congrArg (fun f ↦ (tensorPullback f).obj L) ha)

/-- The same canonical transition on schemes over the fixed base, retaining the leg
identities in the over category. Source: Stacks, Spaces, Tag 04W8
(blueprint: lem-trf-algebraic-space-invertible-descent). -/
noncomputable def atlasTransitionOver {S : Scheme.{u}} {X Y R T : Over S}
    (L : X.left.Modules) (K : Y.left.Modules) (p : R ⟶ X) (q : R ⟶ Y)
    (α : (tensorPullback q.left).obj K ≅ (tensorPullback p.left).obj L)
    (r : T ⟶ R) (a : T ⟶ X) (b : T ⟶ Y) (ha : r ≫ p = a) (hb : r ≫ q = b) :
    (tensorPullback b.left).obj K ≅ (tensorPullback a.left).obj L :=
  atlasTransitionOn L K p.left q.left α r.left a.left b.left
    (congrArg (fun f : T ⟶ X ↦ f.left) ha) (congrArg (fun f : T ⟶ Y ↦ f.left) hb)
/-- An identification of an ordinary module on the scheme `V` with the restriction of
an algebraic-space module `N` to `V`. On a test object `p : T ⟶ V` it is a linear
isomorphism `Γ(T, p*L) ≃ N(T)`, natural for every morphism in the localized étale site.
Thus it is precisely an isomorphism with the ordinary module's associated étale module,
with its scalar action included, rather than merely an isomorphism of abelian sheaves.
Source: Stacks, Descent, Tags 03DU and 05VG
(blueprint: lem-trf-algebraic-space-invertible-descent). -/
structure OrdinaryEtaleIdentification {S : Scheme.{u}} (F : AlgebraicSpace S)
    (V : F.EtaleSite) (N : F.Modules) (L : (F.etaleForget.obj V).Modules) where
  /-- The sectionwise linear isomorphisms. -/
  app : ∀ (T : F.EtaleSite) (p : T ⟶ V),
    ((tensorPullback (F.etaleForget.map p)).obj L).val.obj (op ⊤) ≃ₗ[
      Γ(F.etaleForget.obj T, ⊤)] N.val.obj (op T)
  /-- Naturality for the canonical ordinary pullback restrictions. -/
  naturality : ∀ (T U : F.EtaleSite) (p : T ⟶ V) (f : U ⟶ T)
    (s : ((tensorPullback (F.etaleForget.map p)).obj L).val.obj (op ⊤)),
    app U (f ≫ p)
      (ordinaryEtaleSectionRestriction L (F.etaleForget.map p) (F.etaleForget.map f)
        (F.etaleForget.map (f ≫ p)) (F.etaleForget.map_comp f p).symm s) =
      N.val.presheaf.map f.op (app T p s)

/-- The ordinary overlap isomorphisms, their identity along each diagonal, and their
cocycle after pullback to every test scheme of a triple overlap. The test-scheme
formulation is the Yoneda formulation of equality on the represented triple product;
it does not identify different iterated tensor pullbacks definitionally.
Source: Stacks, Spaces, Tag 04W8; Descent, descent data for quasi-coherent modules
(blueprint: lem-trf-algebraic-space-invertible-descent). -/
structure InvertibleAtlasDescentDatum {S : Scheme.{u}} {I : Type u}
    (V : I → Over S) (R : I → I → Over S)
    (p₁ : ∀ i j : I, R i j ⟶ V i) (p₂ : ∀ i j : I, R i j ⟶ V j)
    (M : ∀ i : I, (V i).left.Modules) where
  /-- The specified ordinary module isomorphisms on the represented double overlaps. -/
  transition : ∀ i j : I,
    (tensorPullback (p₂ i j).left).obj (M j) ≅ (tensorPullback (p₁ i j).left).obj (M i)
  /-- Identity only after restriction along the diagonal, including for self-overlaps. -/
  diagonal : ∀ (i : I) (d : V i ⟶ R i i)
    (h₁ : d ≫ p₁ i i = 𝟙 (V i)) (h₂ : d ≫ p₂ i i = 𝟙 (V i)),
    atlasTransitionOver (M i) (M i) (p₁ i i) (p₂ i i) (transition i i)
      d (𝟙 (V i)) (𝟙 (V i)) h₁ h₂ =
      Iso.refl ((tensorPullback (𝟙 (V i).left)).obj (M i))
  /-- The cocycle on all scheme tests of the triple fibre product. -/
  cocycle : ∀ (i j k : I) (T : Over S)
    (a : T ⟶ V i) (b : T ⟶ V j) (c : T ⟶ V k)
    (rᵢⱼ : T ⟶ R i j) (rⱼₖ : T ⟶ R j k) (rᵢₖ : T ⟶ R i k)
    (hᵢⱼ₁ : rᵢⱼ ≫ p₁ i j = a) (hᵢⱼ₂ : rᵢⱼ ≫ p₂ i j = b)
    (hⱼₖ₁ : rⱼₖ ≫ p₁ j k = b) (hⱼₖ₂ : rⱼₖ ≫ p₂ j k = c)
    (hᵢₖ₁ : rᵢₖ ≫ p₁ i k = a) (hᵢₖ₂ : rᵢₖ ≫ p₂ i k = c),
    atlasTransitionOver (M i) (M k) (p₁ i k) (p₂ i k) (transition i k)
      rᵢₖ a c hᵢₖ₁ hᵢₖ₂ =
    atlasTransitionOver (M j) (M k) (p₁ j k) (p₂ j k) (transition j k)
      rⱼₖ b c hⱼₖ₁ hⱼₖ₂ ≪≫
    atlasTransitionOver (M i) (M j) (p₁ i j) (p₂ i j) (transition i j)
      rᵢⱼ a b hᵢⱼ₁ hᵢⱼ₂

/-- Invertible modules and their morphisms descend along any jointly surjective family
of étale scheme maps to an algebraic space. The ordinary invertible modules `M i`
and the specified overlap isomorphisms are retained; the conclusion gives a line
module with natural linear identifications inducing exactly those isomorphisms.
The second conjunct is the bijection on morphisms, expressed as existence and
uniqueness of a global map with each prescribed local restriction.
Source: Stacks, Spaces, Tags 04W8 and 060X; Descent, Tag 05VG; Sites, Tags 04TR and 04TQ
(blueprint: lem-trf-algebraic-space-invertible-descent).

Proof:
1. Interpret each ordinary invertible module on the localized small étale site by
   its tensor-pullback sections, using lem-trf-scheme-etale-invertible-comparison.
   The unit-normalized composition comparisons transport the transitions and cocycle.
2. For every test scheme W over F, form W_i and W_ij by the representable diagonal.
   Sending W to the sections of the local module on W_i, or on W_ij, gives sheaves:
   their covering equalizers are those on the corresponding base-changed scheme.
3. Take the equalizer of the two maps from the product of the first family to the
   product of the second. By lem-weil-pbc-site-sheaf-sets-limits-sectionwise its values
   are exactly the tuples s_i with s_i restricted equal to α_ij(s_j restricted).
4. Define addition and scalar multiplication coordinatewise. Linearity of α_ij
   preserves the equations, and semilinearity of restriction gives a module sheaf.
5. Over V_a, evaluation of the a-coordinate along the graph defines the local
   identification; its inverse sends y to the tuple α_ia(y restricted). The cocycle
   makes this a compatible tuple and proves that these formulas are natural.
6. The diagonal identity and tuple compatibility prove that these maps are inverse.
   Pulling the tuple equation back along the two graphs proves that the resulting
   identifications induce precisely the specified transitions, also on self-overlaps.
7. Pull back Zariski trivializing covers of the M_i to the W_i. Covering composition
   then trivializes the descended module on every W, so it is a line module.
8. For any two line modules, apply compatible local maps to the local restrictions
   of a section. The sheaf axiom glues the results uniquely. Uniqueness proves
   naturality, additivity, scalar linearity and agreement with the local maps, and
   proves uniqueness of the resulting global map. -/
theorem exists_lineModule_of_etale_descent
    {S : Scheme.{u}} (F : AlgebraicSpace S) {I : Type u} (V : I → F.EtaleSite)
    (hjoint : ∀ (T : Over S) (a : yoneda.obj T ⟶ F.obj.obj) (x : T.left),
      ∃ (i : I) (U : Over S) (p : U ⟶ T)
        (r : yoneda.obj U ⟶ yoneda.obj (V i).obj.left),
        IsPullback r (yoneda.map p) (V i).obj.hom a ∧
          ∃ y : U.left, p.left.base y = x)
    (R : I → I → Over S)
    (p₁ : ∀ i j : I, R i j ⟶ (V i).obj.left)
    (p₂ : ∀ i j : I, R i j ⟶ (V j).obj.left)
    (hR : ∀ i j : I, IsPullback (yoneda.map (p₁ i j)) (yoneda.map (p₂ i j))
      (V i).obj.hom (V j).obj.hom)
    (M : ∀ i : I, (F.etaleForget.obj (V i)).Modules)
    (hM : ∀ i : I, Scheme.Modules.IsInvertible (M i))
    (D : InvertibleAtlasDescentDatum (fun i ↦ (V i).obj.left) R p₁ p₂ M) :
    (∃ (N : F.Modules), F.IsLineModule N ∧
      ∃ (e : ∀ i : I, OrdinaryEtaleIdentification F (V i) N (M i)),
        ∀ (i j : I) (T : F.EtaleSite) (a : T ⟶ V i) (b : T ⟶ V j)
          (r : T.obj.left ⟶ R i j)
          (h₁ : r ≫ p₁ i j = a.hom.left) (h₂ : r ≫ p₂ i j = b.hom.left)
          (s : ((tensorPullback (F.etaleForget.map b)).obj (M j)).val.obj (op ⊤)),
          (e i).app T a
            (((atlasTransitionOver (M i) (M j) (p₁ i j) (p₂ i j) (D.transition i j)
              r a.hom.left b.hom.left h₁ h₂).hom.app ⊤) s) = (e j).app T b s) ∧
    (∀ (P Q : F.Modules), F.IsLineModule P → F.IsLineModule Q →
      ∀ (g : ∀ i : I, (F.etalePullback (V i)).obj P ⟶ (F.etalePullback (V i)).obj Q),
        (∀ (i j : I) (T : F.EtaleSite) (a : T ⟶ V i) (b : T ⟶ V j),
          (g i).val.app (op (Over.mk a)) = (g j).val.app (op (Over.mk b))) →
        ∃! f : P ⟶ Q, ∀ i : I, (F.etalePullback (V i)).map f = g i) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
