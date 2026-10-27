module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import WeilConjectures.RingTheory.AdicCompletionNoetherian

/-! # Completed stalks and marked Artinian points

Source: Stacks Project, Artin's Axioms, Tag 0CXK, proof of lemma-versality-matches;
Schemes, Tag 01J6 (blueprint: lem-sfb-scheme-completion-artinian-points).

The residue marking is a surjection to the fixed residue field whose kernel consists
of the nonunits. This is precisely a specified identification of residue fields.
The kernel of the first-coordinate map is used for the maximal ideal of the completion,
so the statements do not need a chosen local-ring instance on that completion.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

noncomputable section

/-- The canonical map from the spectrum of the completed stalk to the scheme.
Source: Stacks, Tags 01J6 and 0CXK
(blueprint: lem-sfb-scheme-completion-artinian-points). -/
def completedStalkToScheme (Y : Scheme.{u}) (y : Y) :
    Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
      (Y.presheaf.stalk y))) ⟶ Y :=
  Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y)
    (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
      (Y.presheaf.stalk y)))) ≫ Y.fromSpecStalk y

/-- The canonical residue map of the completed stalk, its first coordinate.
Source: Stacks, Tag 0CXK; Algebra, Tag 05GI
(blueprint: lem-sfb-scheme-completion-artinian-points). -/
def completedStalkResidueMap (Y : Scheme.{u}) (y : Y) :
    AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
      (Y.presheaf.stalk y) →+* Y.residueField y :=
  (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))).toRingHom

/-- The base-ring map into a stalk over an affine base, obtained by taking germs.
Source: Stacks, Tag 01J6, the affine local-spectrum correspondence
(blueprint: lem-sfb-scheme-completion-artinian-points). -/
def stalkBaseRingMap {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of R)) (y : Y) : R →+* Y.presheaf.stalk y :=
  ((ΓSpecIso (.of R)).inv ≫ f.appTop ≫ Y.presheaf.germ ⊤ y trivial).hom

/-- Composition with the canonical spectrum-of-completion map.
Source: Stacks, Tag 0CXK, displayed identification of Artinian points
(blueprint: lem-sfb-scheme-completion-artinian-points). -/
def completedStalkPointMap (Y : Scheme.{u}) (y : Y) {A : Type u} [CommRing A]
    (v : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
      (Y.presheaf.stalk y) →+* A) : Spec (.of A) ⟶ Y :=
  Spec.map (CommRingCat.ofHom v) ≫ Y.completedStalkToScheme y

/-- The left-hand set of marked local maps in the Artinian-point identification.
Source: Stacks, Tag 0CXK, displayed identification
(blueprint: lem-sfb-scheme-completion-artinian-points). -/
def markedCompletedStalkMaps {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of R)) (y : Y) {A : Type u} [CommRing A] [Algebra R A]
    (q : A →+* Y.residueField y) :
    Set (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
      (Y.presheaf.stalk y) →+* A) :=
  {v | IsLocalHom v ∧
    v.comp ((algebraMap (Y.presheaf.stalk y) _).comp (stalkBaseRingMap f y)) =
      algebraMap R A ∧ q.comp v = Y.completedStalkResidueMap y}

/-- The completion is Noetherian local, complete for its maximal ideal, and has
canonically the original residue field. Source: Stacks, Tag 0CXK, first sentence
of the proof (blueprint: lem-sfb-scheme-completion-artinian-points).

Proof: choose an affine neighbourhood of y. Finite type over the Noetherian base
makes its coordinate ring Noetherian (finite-type-algebra-noetherian); localization
identifies the stalk and makes it Noetherian (affine-open-stalk-localization and
localization-noetherian). Local-completion-local-ring identifies the maximal ideal
with the kernel of the first coordinate and identifies the residue fields.
Adic-completion-noetherian gives Noetherianity. Module-completion-complete applied
to the stalk as its own module gives completeness; powers of the extended maximal
ideal agree with extensions of its powers. These are steps 1 and 2 of the DAG proof. -/
theorem completedStalk_properties {R : Type u} [CommRing R] [IsNoetherianRing R]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of R)) [LocallyOfFiniteType f] (y : Y)
    (hfinite : @Module.Finite R (Y.residueField y) _ _
      (((Y.residue y).hom.comp (stalkBaseRingMap f y)).toAlgebra.toModule)) :
    IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
      (Y.presheaf.stalk y)) ∧
    IsLocalRing (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
      (Y.presheaf.stalk y)) ∧
    IsAdicComplete (RingHom.ker (Y.completedStalkResidueMap y))
      (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
        (Y.presheaf.stalk y)) ∧
    Function.Surjective (Y.completedStalkResidueMap y) ∧
    (∀ x, Y.completedStalkResidueMap y x = 0 ↔ ¬ IsUnit x) := by
  sorry

/-- Marked Artinian points are exactly the local residue-preserving base-algebra
maps out of the completed stalk, and each such map kills a positive power of its
maximal ideal. Source: Stacks, Tag 0CXK, displayed identification
(blueprint: lem-sfb-scheme-completion-artinian-points).

Proof: by the local-spectrum correspondence (morphism-from-spec-local-ring), a map
from Spec A with fixed residue point corresponds to a local map from the stalk,
commuting with R and with the residue maps (DAG step 4). The maximal ideal of A is
nilpotent (artinian-local-noetherian-nilpotent); choose N positive with m_A^N = 0.
The stalk map kills m_y^N and hence factors through its quotient. Compose this
factor with the N-th completion coordinate. Module-completion-complete identifies
the coordinate kernel with the N-th power of the completed maximal ideal, and
shows the extension is local and residue-preserving. Every local completion map
kills that power as well, so values are determined by stalk representatives modulo
it. This proves existence, uniqueness and nilpotence (step 5). Functoriality of Spec
identifies the resulting bijection with the displayed composition (step 6). -/
theorem completedStalk_markedArtinianPoints {R : Type u} [CommRing R]
    [IsNoetherianRing R] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of R))
    [LocallyOfFiniteType f] (y : Y)
    (hfinite : @Module.Finite R (Y.residueField y) _ _
      (((Y.residue y).hom.comp (stalkBaseRingMap f y)).toAlgebra.toModule))
    (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra R A]
    (q : A →+* Y.residueField y) (hq : Function.Surjective q)
    (hkernel : ∀ a, q a = 0 ↔ ¬ IsUnit a)
    (hbase : q.comp (algebraMap R A) = (Y.residue y).hom.comp (stalkBaseRingMap f y)) :
    Set.BijOn (Y.completedStalkPointMap y) (markedCompletedStalkMaps f y q)
      {a | a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) ∧
        Spec.map (CommRingCat.ofHom q) ≫ a = Y.fromSpecResidueField y} ∧
    (∀ v ∈ markedCompletedStalkMaps f y q, ∃ n : ℕ, 0 < n ∧
      RingHom.ker (Y.completedStalkResidueMap y) ^ n ≤ RingHom.ker v) := by
  sorry

/-- Naturality of the marked Artinian-point identification for every local
residue-preserving R-map, including nonsurjective maps. Source: Stacks, Tag 0CXK
(blueprint: lem-sfb-scheme-completion-artinian-points).

Proof: step 6 of the DAG proof. For h : A → A', restriction of h v along the
completion map is h times the restriction of v. The base and residue equalities
are preserved by composition, as is locality. Contravariant functoriality of Spec
identifies the corresponding map with Spec(h) followed by the point for v. -/
theorem completedStalk_markedArtinianPoints_naturality {R : Type u} [CommRing R]
    [IsNoetherianRing R] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of R))
    [LocallyOfFiniteType f] (y : Y)
    (hfinite : @Module.Finite R (Y.residueField y) _ _
      (((Y.residue y).hom.comp (stalkBaseRingMap f y)).toAlgebra.toModule))
    (A A' : Type u) [CommRing A] [CommRing A'] [IsLocalRing A] [IsLocalRing A']
    [IsArtinianRing A] [IsArtinianRing A'] [Algebra R A] [Algebra R A']
    (q : A →+* Y.residueField y) (q' : A' →+* Y.residueField y)
    (hq : Function.Surjective q) (hq' : Function.Surjective q')
    (hkernel : ∀ a, q a = 0 ↔ ¬ IsUnit a)
    (hkernel' : ∀ a, q' a = 0 ↔ ¬ IsUnit a)
    (hbase : q.comp (algebraMap R A) = (Y.residue y).hom.comp (stalkBaseRingMap f y))
    (hbase' : q'.comp (algebraMap R A') = (Y.residue y).hom.comp (stalkBaseRingMap f y))
    (h : A →ₐ[R] A') (hlocal : IsLocalHom h.toRingHom)
    (hresidue : q'.comp h.toRingHom = q)
    (v : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
      (Y.presheaf.stalk y) →+* A) (hv : v ∈ markedCompletedStalkMaps f y q) :
    h.toRingHom.comp v ∈ markedCompletedStalkMaps f y q' ∧
    Y.completedStalkPointMap y (h.toRingHom.comp v) =
      Spec.map (CommRingCat.ofHom h.toRingHom) ≫ Y.completedStalkPointMap y v := by
  sorry

/-- The positive infinitesimal quotients are Artinian local with residue field k;
the coordinate isomorphism identifies their points with the canonical infinitesimal
neighbourhoods in Y. Source: Stacks, Tag 0CXK
(blueprint: lem-sfb-scheme-completion-artinian-points).

Proof: step 3 of the DAG proof. Module-completion-complete says that the n-th
coordinate is surjective with kernel the n-th power of the completed maximal
ideal, giving the canonical quotient isomorphism and its formula on stalk elements.
The noetherian-local-quotient-artinian-local lemma gives the Artinian and local
properties. Reducing further to the first coordinate gives the specified residue
field, with kernel the nonunits. Step 7 identifies the point: under the coordinate
isomorphism the quotient map composed with the stalk inclusion is the stalk's
quotient map, so the local-spectrum correspondence gives precisely the canonical
infinitesimal-neighbourhood morphism. -/
theorem completedStalk_artinianQuotients {R : Type u} [CommRing R] [IsNoetherianRing R]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of R)) [LocallyOfFiniteType f] (y : Y)
    (hfinite : @Module.Finite R (Y.residueField y) _ _
      (((Y.residue y).hom.comp (stalkBaseRingMap f y)).toAlgebra.toModule))
    (n : ℕ) (hn : 0 < n) :
    IsArtinianRing ((AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
          (Y.presheaf.stalk y)) ⧸ RingHom.ker (Y.completedStalkResidueMap y) ^ n) ∧
    IsLocalRing ((AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
          (Y.presheaf.stalk y)) ⧸ RingHom.ker (Y.completedStalkResidueMap y) ^ n) ∧
    (∃ qn : ((AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
          (Y.presheaf.stalk y)) ⧸ RingHom.ker (Y.completedStalkResidueMap y) ^ n) →+*
        Y.residueField y,
      Function.Surjective qn ∧
      qn.comp (Ideal.Quotient.mk _) = Y.completedStalkResidueMap y ∧
      (∀ a, qn a = 0 ↔ ¬ IsUnit a)) ∧
    (∃ e : ((AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
          (Y.presheaf.stalk y)) ⧸ RingHom.ker (Y.completedStalkResidueMap y) ^ n) ≃+*
      (Y.presheaf.stalk y) ⧸ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ n,
      e.toRingHom.comp ((Ideal.Quotient.mk _).comp (algebraMap (Y.presheaf.stalk y)
        (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
          (Y.presheaf.stalk y)))) = Ideal.Quotient.mk _ ∧
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Y.completedStalkPointMap y (Ideal.Quotient.mk _) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ n))) ≫ Y.fromSpecStalk y) := by
  sorry

/-- Compatibility of the canonical infinitesimal points with all quotient
transitions, including identity transitions. Source: Stacks, Tag 0CXK
(blueprint: lem-sfb-scheme-completion-artinian-points).

Proof: step 7 of the DAG proof. For r ≥ n ≥ 1 the quotient transition composed
with the r-th quotient is the n-th quotient. Contravariant functoriality of Spec,
or the naturality in step 6, gives the displayed equality. This also applies to
r = n. -/
theorem completedStalk_artinianQuotients_transition {R : Type u} [CommRing R]
    [IsNoetherianRing R] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of R))
    [LocallyOfFiniteType f] (y : Y)
    (hfinite : @Module.Finite R (Y.residueField y) _ _
      (((Y.residue y).hom.comp (stalkBaseRingMap f y)).toAlgebra.toModule))
    (n r : ℕ) (hn : 0 < n) (hnr : n ≤ r) :
    Y.completedStalkPointMap y
      (Ideal.Quotient.mk (RingHom.ker (Y.completedStalkResidueMap y) ^ n)) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (I := RingHom.ker (Y.completedStalkResidueMap y)) hnr))) ≫
      Y.completedStalkPointMap y
        (Ideal.Quotient.mk (RingHom.ker (Y.completedStalkResidueMap y) ^ r)) := by
  sorry

end

end AlgebraicGeometry.Scheme
