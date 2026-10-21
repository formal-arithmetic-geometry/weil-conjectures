/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.Paper.CompletedBaseChangeMap
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.CategoryTheory.Triangulated.DerivedLimitLevelwiseIsomorphism
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.ProjectionFormulaBaseChangeNaturality
import Sheaf.Paper.CompletedPullback
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.CompletedRlimFunctor
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Paper.CompletedPullbackAdjunction
import Sheaf.Paper.OrderedExchangeCoefficientComparison
import Sheaf.Paper.ProEtaleConstantReductionTower
import Sheaf.Paper.StrictTowerExchangeMateNormalization

/-!
# Naturality, units, and pasting of completed exchange

Source: blueprint proper base change, completed exchange coherence, order 1348
(blueprint: lemma-weil-pbc-completed-exchange-coherence).
The comparison maps below retain ordinary tensor-unit normalization. They do not
replace canonical completed pullback compositions by arbitrary natural isomorphisms.

## Main statements

- `AdicCoefficientDatum.completedExchange_naturality`: naturality for arbitrary maps.
- `AdicCoefficientDatum.completedExchange_identity_horizontal`: horizontal identities.
- `AdicCoefficientDatum.completedExchange_identity_vertical`: vertical identities.
- `AdicCoefficientDatum.completedExchange_horizontal`: horizontal pasting.
- `AdicCoefficientDatum.completedExchange_vertical`: vertical pasting.

## Main definitions

- `AdicCoefficientDatum.completedPullComp`: the unit-normalized composition comparison.
- `AdicCoefficientDatum.completedPullId`: the unit-normalized identity comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The completed coefficient identification for a composite is the specified composite.
Source: blueprint coherence, proof step 3; Stacks Tag 098T
(blueprint: lemma-weil-pbc-completed-exchange-coherence).
Proof: the canonical profinite inverse-image comparison respects composition. Its
projections are the constant-section comparisons. The composite coefficient map has
these same projections, so limit uniqueness identifies the maps, and hence the isos. -/
theorem AdicCoefficientDatum.integralRingIso_comp {U V W : Scheme.{t}}
    (h : U ⟶ V) (g : V ⟶ W) :
    d.integralRingIso (h ≫ g) = proEtaleRingCompositeCoefficients h g
      (d.completedRing W) (d.completedRing V) (d.completedRing U)
      (d.integralRingIso g) (d.integralRingIso h) := by
  sorry

/-- Ordinary derived pullback composition with the specified coefficient transport.
Source: blueprint coherence, proof step 3; Stacks Tag 0D6D
(blueprint: lemma-weil-pbc-completed-exchange-coherence). -/
def AdicCoefficientDatum.pullComp {U V W : Scheme.{t}} (h : U ⟶ V) (g : V ⟶ W) :
    d.pull (h ≫ g) ≅ d.pull g ⋙ d.pull h :=
  eqToIso (congrArg
    (proEtaleRingDerivedPullback (h ≫ g) (d.completedRing W) (d.completedRing U))
      (d.integralRingIso_comp h g)) ≪≫
    proEtaleCanonicalDerivedPullbackComparison h g (d.completedRing W) (d.completedRing V)
      (d.completedRing U) (d.integralRingIso g) (d.integralRingIso h)

/-- Direct image composition is exactly the conjugate of pullback composition.
Source: blueprint coherence, proof step 3; mate-pasting clause (3)
(blueprint: lemma-weil-pbc-completed-exchange-coherence). -/
def AdicCoefficientDatum.pushComp {U V W : Scheme.{t}} (h : U ⟶ V) (g : V ⟶ W) :
    d.push h ⋙ d.push g ≅ d.push (h ≫ g) :=
  conjugateIsoEquiv
    ((proEtaleRingDerivedAdjunction g (d.completedRing W) (d.completedRing V)
      (d.integralRingIso g)).comp
      (proEtaleRingDerivedAdjunction h (d.completedRing V) (d.completedRing U)
        (d.integralRingIso h)))
    (proEtaleRingDerivedAdjunction (h ≫ g) (d.completedRing W) (d.completedRing U)
      (d.integralRingIso (h ≫ g))) (d.pullComp h g)

/-- Identity direct image is uniquely fixed by inverse-image restriction on each section.
Source: blueprint coherence, unit normalization in proof step 5; Stacks Tag 03D8
(blueprint: lemma-weil-pbc-completed-exchange-coherence).
Proof: the base-change identity identifies U times_T T with U. Restriction along its
inverse gives the displayed map. Naturality and the canonical coefficient identity make
it linear; the opposite restriction is inverse. Sectionwise faithfulness gives uniqueness. -/
theorem AdicCoefficientDatum.modulePushId_existsUnique (T : Scheme.{t}) :
    ∃! α : proEtaleRingModuleDirectImage (𝟙 T) (d.completedRing T) (d.completedRing T)
        (d.integralRingIso (𝟙 T)) ≅ 𝟭 _,
      ∀ (N : reductionModules T (d.completedRing T)) (U : T.ProEt)
        (m : ((proEtaleRingModuleDirectImage (𝟙 T) (d.completedRing T)
          (d.completedRing T) (d.integralRingIso (𝟙 T))).obj N).val.obj (op U)),
        (α.hom.app N).val.app (op U) m =
          N.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).inv.app U).op m := by
  sorry

/-- The normalized module identity isomorphism, with its section formula retained.
Source: blueprint coherence, proof step 5
(blueprint: lemma-weil-pbc-completed-exchange-coherence). -/
def AdicCoefficientDatum.modulePushId (T : Scheme.{t}) :=
  (d.modulePushId_existsUnique T).choose

/-- Ordinary pullback identity, derived from its section-normalized ordinary adjunction.
Source: blueprint coherence, proof step 5; Stacks Tag 03D8
(blueprint: lemma-weil-pbc-completed-exchange-coherence). -/
def AdicCoefficientDatum.pullId (T : Scheme.{t}) : d.pull (𝟙 T) ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso
    ((proEtaleRingModuleAdjunction (𝟙 T) (d.completedRing T) (d.completedRing T)
      (d.integralRingIso (𝟙 T))).leftAdjointIdIso (d.modulePushId T)) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- Derived direct-image identity is conjugate to that same pullback identity.
Source: blueprint coherence, proof steps 3 and 5
(blueprint: lemma-weil-pbc-completed-exchange-coherence). -/
def AdicCoefficientDatum.pushId (T : Scheme.{t}) : d.push (𝟙 T) ≅ 𝟭 _ :=
  (conjugateIsoEquiv Adjunction.id
    (proEtaleRingDerivedAdjunction (𝟙 T) (d.completedRing T) (d.completedRing T)
      (d.integralRingIso (𝟙 T))) (d.pullId T)).symm

/-- Completed composition is uniquely fixed by its ordinary completion-unit equation.
Source: blueprint coherence, canonical associativity and proof step 5; Stacks Tag 099N (5)
(blueprint: lemma-weil-pbc-completed-exchange-coherence).
Proof: under constant-to-completed restriction, completed pullback is ordinary pullback
followed by the derived completion reflector. Pullback of quotient reductions is the
strict tensor balancing map. The two successive completion units therefore factor
uniquely through the completion of the composite pullback. On strict K-flat quotient
models the inverse comparison is tensor reassociation, sending (x tensor b) tensor a
to x tensor q(b)a. The quotient cocycle and unit identities make both composites
identities. The reflector universal property proves uniqueness of the displayed natural
iso, so no choice of arbitrary comparison is permitted. -/
theorem AdicCoefficientDatum.completedPullComp_existsUnique {U V W : Scheme.{t}}
    (h : U ⟶ V) (g : V ⟶ W) :
    ∃! α : d.completedPull (h ≫ g) ≅ d.completedPull g ⋙ d.completedPull h,
      ∀ K : d.derived W,
        d.ordinaryToCompleted (h ≫ g) K ≫ α.hom.app K =
          (d.pullComp h g).hom.app K ≫
            (d.pull h).map (d.ordinaryToCompleted g K) ≫
              d.ordinaryToCompleted h ((d.completedPull g).obj K) := by
  sorry

/-- The canonical completed pullback composition, fixed by its completion units.
Source: blueprint coherence, canonical associativity
(blueprint: lemma-weil-pbc-completed-exchange-coherence). -/
def AdicCoefficientDatum.completedPullComp {U V W : Scheme.{t}}
    (h : U ⟶ V) (g : V ⟶ W) :
    d.completedPull (h ≫ g) ≅ d.completedPull g ⋙ d.completedPull h :=
  (d.completedPullComp_existsUnique h g).choose

/-- On complete inputs the identity completed pullback has its unique unit-normalized
identity comparison. Source: blueprint coherence, proof steps 5 and 6
(blueprint: lemma-weil-pbc-completed-exchange-coherence).
Proof: constant tower identity and its derived mate identify the displayed comparison
with the canonical completion unit. Completeness makes it invertible. Compose its
inverse with ordinary pullback identity; invertibility forces the asserted uniqueness. -/
theorem AdicCoefficientDatum.completedPullId_existsUnique (T : Scheme.{t})
    (K : d.derived T) (hK : d.TowerComplete T K) :
    ∃! α : (d.completedPull (𝟙 T)).obj K ≅ K,
      d.ordinaryToCompleted (𝟙 T) K ≫ α.hom = (d.pullId T).hom.app K := by
  sorry

/-- The completed identity comparison on a complete object, retaining its unit.
Source: blueprint coherence, identity-square clause
(blueprint: lemma-weil-pbc-completed-exchange-coherence). -/
def AdicCoefficientDatum.completedPullId (T : Scheme.{t})
    (K : d.derived T) (hK : d.TowerComplete T K) :
    (d.completedPull (𝟙 T)).obj K ≅ K :=
  (d.completedPullId_existsUnique T K hK).choose

/-- Completed exchange is natural for arbitrary morphisms of complete inputs; the
finite-level etale witnesses are retained independently on both inputs.
Source: blueprint coherence, proof step 7
(blueprint: lemma-weil-pbc-completed-exchange-coherence).
Proof: the strict tower mate is natural. The reconstruction, projection, and
pushforward/limit comparisons are natural. For k:K to H substitute these equations
in c inverse Rlim(v') s. Functoriality of Rlim and cancellation of the intermediate
comparison give the displayed naturality square. Restriction to constant coefficients
reflects this equality without identifying the ambient coefficient categories. -/
theorem AdicCoefficientDatum.completedExchange_naturality
    {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g) [IsProper f]
    (K H : d.derived X) (hK : d.TowerComplete X K) (hH : d.TowerComplete X H)
    (WK : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K))
    (WH : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj H)) (k : K ⟶ H) :
    (d.completedPull g).map ((d.push f).map k) ≫ d.completedBaseChangeMap sq H hH WH =
      d.completedBaseChangeMap sq K hK WK ≫
        (d.push f').map ((d.completedPull g').map k) := by
  sorry

/-- Identity squares with horizontal identity arrows give the identity of Rf_* after
its canonical completed unit comparisons.
Source: blueprint coherence, identity-square clause and proof steps 5--6
(blueprint: lemma-weil-pbc-completed-exchange-coherence).
Proof: the strict tower comparison for an identity square is the identity mate.
The source and target reconstruction comparisons agree by their ordinary tensor-unit
normalizations. Applying Rlim preserves the identity; cancellation gives the displayed
identity with the completed pullback unit comparisons retained. -/
theorem AdicCoefficientDatum.completedExchange_identity_horizontal
    {X Y : Scheme.{t}} (f : X ⟶ Y) [IsProper f]
    (sq : ChosenCartesianSquare (𝟙 X) f f (𝟙 Y))
    (K : d.derived X) (hK : d.TowerComplete X K)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) :
    d.completedBaseChangeMap sq K hK W =
      (d.completedPullId Y ((d.push f).obj K) (d.push_complete f K hK)).hom ≫
        (d.push f).map (d.completedPullId X K hK).inv := by
  sorry

/-- Identity vertical arrows give the identity of completed pullback after the canonical
right-adjoint identity comparisons.
Source: blueprint coherence, identity-square clause and proof steps 5--6
(blueprint: lemma-weil-pbc-completed-exchange-coherence).
Proof: the square comparison is the identity under its pullback unit comparisons.
The mate identity law, followed by Rlim and the same unit-normalized reconstruction
comparisons, gives the displayed right-adjoint identity conjugation. -/
theorem AdicCoefficientDatum.completedExchange_identity_vertical
    {U V : Scheme.{t}} (g : U ⟶ V)
    (sq : ChosenCartesianSquare g (𝟙 U) (𝟙 V) g)
    (K : d.derived V) (hK : d.TowerComplete V K)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness V (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction V n).obj K)) :
    d.completedBaseChangeMap sq K hK W =
      (d.completedPull g).map ((d.pushId V).hom.app K) ≫
        (d.pushId U).inv.app ((d.completedPull g).obj K) := by
  sorry

/-- Horizontal pasting retains the canonical completed pullback associativity maps.
The ambient formula is used for the intermediate complete pullback, so its finite
etale witnesses need not be chosen compatibly with those of K.
Source: blueprint coherence, horizontal-pasting clause and proof steps 1--6
(blueprint: lemma-weil-pbc-completed-exchange-coherence).
Proof: restrict to constant coefficients on complete objects, retaining the specified
reconstruction comparisons. Strict tower exchange is its canonical mate, as given by
strict-tower mate normalization; equality holds in the derived tower category itself.
Termwise pullback compositions are tensor balancing maps, so the two pasted pullback
squares equal the outer square before localization. Mate-pasting (1) gives the tower
horizontal equation. Apply the functor Rlim, preserving composition. The intermediate
projection and direct-image/limit comparisons agree by tensor balancing, projection
formula base-change naturality, and the universal limit projection equations on
K-injective towers. Writing each completed arrow as a_next inverse Rlim(E) a_previous,
the intermediate comparisons cancel. Their remaining outer comparisons are precisely
the unit-normalized completedPullComp maps displayed here. -/
theorem AdicCoefficientDatum.completedExchange_horizontal
    {X X' X'' Y Y' Y'' : Scheme.{t}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} {h : Y'' ⟶ Y'} {h' : X'' ⟶ X'}
    [IsProper f]
    (sq₁ : ChosenCartesianSquare g' f' f g)
    (sq₂ : ChosenCartesianSquare h' f'' f' h)
    (outer : ChosenCartesianSquare (h' ≫ g') f'' f (h ≫ g))
    (K : d.derived X) (_hK : d.TowerComplete X K)
    (_W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) :
    d.completedExchange outer K =
      (d.completedPullComp h g).hom.app ((d.push f).obj K) ≫
        (d.completedPull h).map (d.completedExchange sq₁ K) ≫
          d.completedExchange sq₂ ((d.completedPull g').obj K) ≫
            (d.push f'').map ((d.completedPullComp h' g').inv.app K) := by
  sorry

/-- Vertical pasting retains the canonical direct-image composition comparisons, which
are the conjugates of the specified pullback compositions.
Source: blueprint coherence, vertical-pasting clause and proof steps 1--6
(blueprint: lemma-weil-pbc-completed-exchange-coherence).
Proof: use the same restriction and strict-tower normalization as in horizontal pasting.
Mate-pasting (2) gives the equation for composite adjunctions; clause (3) changes to the
specified composite direct image via its conjugate pullback composition. The projection
formula maps compose because their transposes are the tensor comparison followed by the
composite counit. Direct-image/limit maps compose by their identical limit projections
on K-injective towers; exact inverse image ensures these models compute derived direct
images. Apply Rlim to the strict tower equation and cancel the same intermediate
reconstruction comparisons. This yields precisely the two pushComp maps displayed. -/
theorem AdicCoefficientDatum.completedExchange_vertical
    {X X' Y Y' Z Z' : Scheme.{t}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {e : Y ⟶ Z} {e' : Y' ⟶ Z'}
    {g' : X' ⟶ X} {g : Y' ⟶ Y} {k : Z' ⟶ Z}
    [IsProper f] [IsProper e]
    (sq₁ : ChosenCartesianSquare g' f' f g)
    (sq₂ : ChosenCartesianSquare g e' e k)
    (outer : ChosenCartesianSquare g' (f' ≫ e') (f ≫ e) k)
    (K : d.derived X) (_hK : d.TowerComplete X K)
    (_W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) :
    d.completedExchange outer K =
      (d.completedPull k).map ((d.pushComp f e).inv.app K) ≫
        d.completedExchange sq₂ ((d.push f).obj K) ≫
          (d.push e').map (d.completedExchange sq₁ K) ≫
            (d.pushComp f' e').hom.app ((d.completedPull g').obj K) := by
  sorry

end AlgebraicGeometry.Scheme
