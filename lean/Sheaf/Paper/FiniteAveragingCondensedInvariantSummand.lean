module

public import Sheaf.Paper.ContinuousRepresentationCondensation
public import Sheaf.CategoryTheory.CondensedActionModule
public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Sheaf.CategoryTheory.SheafActionGrothendieckInflation
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.RingTheory.Flat.TorsionFree

/-! # Finite averaging and invariant summands in condensed modules

Source: blueprint latest, six-functors basics, direct-image stability proof, paragraph (3),
prime-to-ell factor removal. The auxiliary finite-average argument is agent-formulated;
an exact external ordinary-condensed reference is WANTED.
(blueprint: lem-sfb-finite-averaging-condensed-invariant-summand).

The existing product-invariants datum fixes the second factor. Swapping the factors
therefore gives precisely Q-invariants of Q times L, retaining the L-action. All tensor
products, topologies, invariant subspaces and realization maps are the recorded ones.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace Profinite.CondensedAction.PrimeToEll.FiniteAveraging
open ContinuousRepresentation AlgebraicGeometry.ProEtale

section Internal
variable (F : Type u) [NormedField F]
  (Q : Type u) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Fintype Q]
  (L : ProfiniteGrp.{u})

/-- The recorded invariants functor, with the factors exchanged to fix Q.
Source: paragraph (3) (blueprint: lem-sfb-finite-averaging-condensed-invariant-summand). -/
def invariants (d : ProductInvariants (normContinuousRing F) L Q) :
    ActionModule (normContinuousRing F) (Q × L) ⥤ ActionModule (normContinuousRing F) L :=
  inflate (R := normContinuousRing F) (ContinuousMonoidHom.swap L Q) ⋙ d.functor

/-- The actual underlying inclusion of Q-fixed sections.
Source: paragraph (3) (blueprint: lem-sfb-finite-averaging-condensed-invariant-summand). -/
def inclusion (d : ProductInvariants (normContinuousRing F) L Q) :
    invariants F Q L d ⋙ forgetAction ⟶ forgetAction where
  app M := d.inclusion.app
    ((inflate (R := normContinuousRing F) (ContinuousMonoidHom.swap L Q)).obj M)
  naturality _ _ f := d.inclusion.naturality
    ((inflate (R := normContinuousRing F) (ContinuousMonoidHom.swap L Q)).map f)

/-- The precise finite-average assertion for a normalized invariant functor. Splitting
identifies the internal image, while the section formula uses the constant 1/card Q.
Exactness is preservation of finite limits and colimits; the last clause additionally
records preservation of epimorphisms of the underlying internal module sheaves.
Source: paragraph (3) (blueprint: lem-sfb-finite-averaging-condensed-invariant-summand). -/
def InternalAssertion (d : ProductInvariants (normContinuousRing F) L Q) : Prop :=
  (invariants F Q L d).Additive ∧
  PreservesFiniteLimits (invariants F Q L d) ∧
  PreservesFiniteColimits (invariants F Q L d) ∧
  (∀ M : ActionModule (normContinuousRing F) (Q × L),
    ∃ p : M.module ⟶ ((invariants F Q L d).obj M).module,
      (inclusion F Q L d).app M ≫ p = 𝟙 _ ∧
      (∀ (S : Profinite.{u}) (x : sectionModule (normContinuousRing F) M.module S),
        (((p ≫ (inclusion F Q L d).app M).hom.hom.app (op S)).hom x) =
          (fun r : (InternalAbelianSheafModule.sectionRings
              (coherentTopology Profinite.{u}) (normContinuousRing F).X).obj (op S) ↦
            r • (∑ q : Q, M.act S (ContinuousMap.const S (q, 1)) x))
              (ULift.up (ContinuousMap.const S ((Fintype.card Q : F)⁻¹)))) ∧
      (p ≫ (inclusion F Q L d).app M) ≫ (p ≫ (inclusion F Q L d).app M) =
        p ≫ (inclusion F Q L d).app M ∧
      (∀ (S : Profinite.{u}) (g : C(S, L))
          (x : sectionModule (normContinuousRing F) M.module S),
        ((p.hom.hom.app (op S)).hom
          (M.act S ((ContinuousMonoidHom.inr Q L).toContinuousMap.comp g) x)) =
        ((invariants F Q L d).obj M).act S g ((p.hom.hom.app (op S)).hom x)) ∧
      (∀ (S : Profinite.{u}) (x : sectionModule (normContinuousRing F) M.module S),
        (∃ y : sectionModule (normContinuousRing F) ((invariants F Q L d).obj M).module S,
          (((inclusion F Q L d).app M).hom.hom.app (op S)).hom y = x) ↔
          Fixed M (ContinuousMonoidHom.snd Q L) S x)) ∧
  (∀ (M N : ActionModule (normContinuousRing F) (Q × L)) (f : M ⟶ N),
    Epi f → Epi ((invariants F Q L d).map f)) ∧
  (∀ (M N : ActionModule (normContinuousRing F) (Q × L)) (f : M ⟶ N),
    Epi f.val → Epi (((invariants F Q L d).map f).val))

end Internal

section Vectors
variable {E : Type u} [Field E]
  (Q : Type u) [Group Q] [Fintype Q] (L : ProfiniteGrp.{u})
  {V : Type (u + 1)} [AddCommGroup V] [Module E V]

/-- Mathlib's ordinary representation average, with its canonical invertibility instance.
Source: paragraph (3) (blueprint: lem-sfb-finite-averaging-condensed-invariant-summand). -/
def average (ρ : Representation E (Q × L) V) : Module.End E V :=
  @dite (Module.End E V) ((Fintype.card Q : E) = 0) (Classical.propDecidable _)
    (fun _ ↦ 0) (fun h ↦
      letI : Invertible (Fintype.card Q : E) := invertibleOfNonzero h
      Representation.averageMap (ρ.comp (MonoidHom.inl Q L)))

end Vectors

section Comparison
variable (E F : Type u) [NormedField E] [NormedField F] [Algebra E F]
  (Q : Type u) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Fintype Q]
  (L : ProfiniteGrp.{u})
  (V : Type (u + 1)) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  (ρ : Representation E (Q × L) V)

/-- An invariant comparison is specified by the actual scalar-extended inclusion on
all sections, rather than by the existence of an abstract isomorphism.
Source: paragraph (3) (blueprint: lem-sfb-finite-averaging-condensed-invariant-summand). -/
def RepresentsComparison (d : ProductInvariants (normContinuousRing F) L Q)
    (M : Realization F (Q × L) (Extended E F V)
      (extendedRepresentation E F V (Q × L) ρ))
    (W : Realization F L (Extended E F (fixedSpace Q L ρ))
      (extendedRepresentation E F (fixedSpace Q L ρ) L (fixedRepresentation Q L ρ)))
    (e : W.object ≅ (invariants F Q L d).obj M.object) : Prop :=
  ∀ (S : Profinite.{u}) (x : sectionModule (normContinuousRing F) W.object.module S) (s : S),
    (M.sections S (((e.hom.val ≫ (inclusion F Q L d).app M.object).hom.hom.app
      (op S)).hom x)).down s = fixedInclusion F Q L ρ ((W.sections S x).down s)

/-- The complete scalar-extension and condensation assertion over one coefficient field.
The topological equivalence is normalized by the actual invariant inclusion and retains
its residual action. The condensed comparison is unique with its section formula.
Source: paragraph (3) (blueprint: lem-sfb-finite-averaging-condensed-invariant-summand). -/
def RepresentationAssertion (d : ProductInvariants (normContinuousRing F) L Q) : Prop :=
  (∃ e : Extended E F (fixedSpace Q L ρ) ≃L[F]
      fixedSpace Q L (extendedRepresentation E F V (Q × L) ρ),
    (∀ v : Extended E F (fixedSpace Q L ρ),
      (e v : Extended E F V) = fixedInclusion F Q L ρ v) ∧
    (∀ (l : L) (v : Extended E F (fixedSpace Q L ρ)),
      e (extendedRepresentation E F (fixedSpace Q L ρ) L
        (fixedRepresentation Q L ρ) l v) =
      fixedRepresentation Q L (extendedRepresentation E F V (Q × L) ρ) l (e v))) ∧
  Nonempty (Realization F (Q × L) (Extended E F V)
    (extendedRepresentation E F V (Q × L) ρ)) ∧
  Nonempty (Realization F L (Extended E F (fixedSpace Q L ρ))
    (extendedRepresentation E F (fixedSpace Q L ρ) L (fixedRepresentation Q L ρ))) ∧
  (∀ (M : Realization F (Q × L) (Extended E F V)
      (extendedRepresentation E F V (Q × L) ρ))
    (W : Realization F L (Extended E F (fixedSpace Q L ρ))
      (extendedRepresentation E F (fixedSpace Q L ρ) L (fixedRepresentation Q L ρ))),
    ∃! e : W.object ≅ (invariants F Q L d).obj M.object,
      RepresentsComparison E F Q L V ρ d M W e)

/-- Naturality of the normalized condensed comparison for the actual tensor extensions of
continuous equivariant maps and their restrictions to the fixed subspaces.
Source: paragraph (3) (blueprint: lem-sfb-finite-averaging-condensed-invariant-summand). -/
def NaturalityAssertion (d : ProductInvariants (normContinuousRing F) L Q) : Prop :=
  ∀ (V' : Type (u + 1)) [AddCommGroup V'] [Module E V'] [FiniteDimensional E V']
    [TopologicalSpace V] [TopologicalSpace V']
    (ρ' : Representation E (Q × L) V') (f : V →ₗ[E] V') (_hf : Continuous f)
    (heq : ∀ (p : Q × L) (v : V), f (ρ p v) = ρ' p (f v))
    (M : Realization F (Q × L) (Extended E F V)
      (extendedRepresentation E F V (Q × L) ρ))
    (W : Realization F L (Extended E F (fixedSpace Q L ρ))
      (extendedRepresentation E F (fixedSpace Q L ρ) L (fixedRepresentation Q L ρ)))
    (M' : Realization F (Q × L) (Extended E F V')
      (extendedRepresentation E F V' (Q × L) ρ'))
    (W' : Realization F L (Extended E F (fixedSpace Q L ρ'))
      (extendedRepresentation E F (fixedSpace Q L ρ') L (fixedRepresentation Q L ρ')))
    (e : W.object ≅ (invariants F Q L d).obj M.object)
    (e' : W'.object ≅ (invariants F Q L d).obj M'.object),
    RepresentsComparison E F Q L V ρ d M W e →
    RepresentsComparison E F Q L V' ρ' d M' W' e' →
    ∃ (a : M.object ⟶ M'.object) (b : W.object ⟶ W'.object),
      RepresentsMap M M' (f.baseChange F) a ∧
      RepresentsMap W W' ((fixedMap Q L ρ ρ' f heq).baseChange F) b ∧
      e.hom ≫ (invariants F Q L d).map a = b ≫ e'.hom

end Comparison

section Coefficients
variable (E F : Type u) [NormedField E] [NormedField F] [Algebra E F]
  (hφ : Continuous (algebraMap E F))
  (Q : Type u) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Fintype Q]
  (L : ProfiniteGrp.{u})
  (V : Type (u + 1)) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  (ρ : Representation E (Q × L) V)

/-- Coefficient compatibility of theta, expressed over the recorded postcomposition ring
morphism. The unique invariant coefficient map is normalized by the inclusion square;
the second square is the claimed compatibility of the two theta isomorphisms.
Source: paragraph (3) (blueprint: lem-sfb-finite-averaging-condensed-invariant-summand). -/
def CoefficientAssertion
    (dE : ProductInvariants (normContinuousRing E) L Q)
    (dF : ProductInvariants (normContinuousRing F) L Q) : Prop :=
  ∀ (sQ : CategoryTheory.CondensedBar.ScalarAction
        (coefficientRingMap E (algebraMap E F) hφ) (Q × L))
    (sL : CategoryTheory.CondensedBar.ScalarAction
        (coefficientRingMap E (algebraMap E F) hφ) L)
    (ME : Realization E (Q × L) (Extended E E V)
      (extendedRepresentation E E V (Q × L) ρ))
    (WE : Realization E L (Extended E E (fixedSpace Q L ρ))
      (extendedRepresentation E E (fixedSpace Q L ρ) L (fixedRepresentation Q L ρ)))
    (MF : Realization F (Q × L) (Extended E F V)
      (extendedRepresentation E F V (Q × L) ρ))
    (WF : Realization F L (Extended E F (fixedSpace Q L ρ))
      (extendedRepresentation E F (fixedSpace Q L ρ) L (fixedRepresentation Q L ρ)))
    (eE : WE.object ≅ (invariants E Q L dE).obj ME.object)
    (eF : WF.object ≅ (invariants F Q L dF).obj MF.object),
    RepresentsComparison E E Q L V ρ dE ME WE eE →
    RepresentsComparison E F Q L V ρ dF MF WF eF →
    ∃ (a : ME.object ⟶ sQ.functor.obj MF.object)
      (b : WE.object ⟶ sL.functor.obj WF.object),
      RepresentsScalarMap (algebraMap E F) hφ ME MF sQ
        (scalarInsertion F V).toAddMonoidHom a ∧
      RepresentsScalarMap (algebraMap E F) hφ WE WF sL
        (scalarInsertion F (fixedSpace Q L ρ)).toAddMonoidHom b ∧
      ∃! c : (invariants E Q L dE).obj ME.object ⟶
          sL.functor.obj ((invariants F Q L dF).obj MF.object),
        (c.val ≫ sL.underlying.hom.app ((invariants F Q L dF).obj MF.object) ≫
          (Mod.comap (coefficientRingMap E (algebraMap E F) hφ).hom.hom).map
            ((inclusion F Q L dF).app MF.object) =
          (inclusion E Q L dE).app ME.object ≫ a.val ≫
            sQ.underlying.hom.app MF.object) ∧
        eE.hom ≫ c = b ≫ sL.functor.map eF.hom

end Coefficients

section Main
variable (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [NormedField Ω]
  [NormedAlgebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]
  (E : IntermediateField ℚ_[ℓ] Ω) [FiniteDimensional ℚ_[ℓ] E]
  (Q : Type u) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Fintype Q]
  (L : ProfiniteGrp.{u})
  (V : Type (u + 1)) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul E V] [T2Space V]
  (ρ : Representation E (Q × L) V)

/-- Finite averaging splits off the fully fixed internal summand, makes its functor exact,
and identifies the scalar-extended topological and condensed invariant representations
for both E and its normed algebraic closure. Completeness of Omega is never assumed.
Source: blueprint latest, direct-image stability proof, paragraph (3), finite-factor
removal (blueprint: lem-sfb-finite-averaging-condensed-invariant-summand).

Proof:
1. The internal action definition supplies section modules and restriction-natural actions.
Apply lem-sfb-sheaf-action-grothendieck-inflation to obtain abelian action categories,
sectionwise kernels, and forgetful functors detecting exactness.
2. Characteristic zero makes m=card Q invertible. Reindex the finite sum by left and
right multiplication to show every constant q fixes its average, and that averaging
fixes every fixed section. The commuting L-action commutes with this finite sum.
3. A generalized Q-element is constant on the finite clopen partition by its fibres.
Sheaf separatedness on that cover identifies constant-fixed and fully fixed sections.
Glue their submodules. Corestrict averaging to p; the invariant inclusion i satisfies
p i=1 and i p=e, so e is idempotent with exactly that image and identity restriction.
4. Restrict equivariant morphisms to these fixed sections. The finite formula commutes
with every such map. Kernels and the zero object are preserved sectionwise.
5. For an epimorphism f and maps a,b from its invariant target, the equalities
(a p)f=(b p)f imply a p=b p by epic cancellation; compose with i to get a=b.
This works for action maps and for arbitrary underlying internal-module maps. It
never assumes sectionwise surjectivity of an epimorphism.
6. For an exact pair, its map onto the kernel is epic by
lem-weil-pbc-abelian-exact-iff-epi-kernel-lift. Steps 4 and 5 preserve this criterion,
so invariants are exact and preserve finite limits and colimits.
7. On V the same average is a finite sum of continuous linear maps. Its image is the
ordinary Q-fixed subspace, with continuous corestriction p and inclusion i; they are
L-equivariant and split each other.
8. The finite extension E is complete by lem-weil-l-adic-extension-complete.
Use lem-weil-pbc-finite-dimensional-linear-homeomorphism over E to identify V and
its invariant subspace with finite powers. Tensor extensions are continuous finite
matrix formulas over F=E or Omega; their actions are jointly continuous. No use of
completeness of Omega is made.
9. Tensor p and i: P I=1 and I P=e_F on pure tensors and hence everywhere. The average
has exactly the Q-fixed vectors as image. Corestrict I to that subspace and restrict
P to obtain mutually inverse continuous L-equivariant maps with the stated formula.
10. A continuous section is fully fixed exactly when its values are ordinary fixed
vectors, after every profinite base change. Postcomposition by I and P therefore
gives the unique normalized internal isomorphism for every realization.
11. Equivariant maps commute termwise with the average and with the inclusion. Tensor
functoriality gives naturality; coefficient insertion gives e_Omega(1 tensor v)=
1 tensor e_E(v), and commutes with I and P. The coefficient ring map is the recorded
postcomposition C_E to C_Omega.
12. Trivial factors, zero spaces and empty test sets satisfy the same finite identities.
No completion, infinite sum or locally constant replacement is used. -/
theorem finite_averaging_condensed_invariant_summand
    (_horder : Nat.Coprime (Fintype.card Q) ℓ)
    (_hρ : Continuous (fun x : (Q × L) × V ↦ ρ x.1 x.2)) :
    (∃ (dE : ProductInvariants (normContinuousRing E) L Q)
      (dΩ : ProductInvariants (normContinuousRing Ω) L Q)
      (hφ : Continuous (algebraMap E Ω)),
      InternalAssertion E Q L dE ∧ InternalAssertion Ω Q L dΩ ∧
      RepresentationAssertion E E Q L V ρ dE ∧
      RepresentationAssertion E Ω Q L V ρ dΩ ∧
      NaturalityAssertion E E Q L V ρ dE ∧ NaturalityAssertion E Ω Q L V ρ dΩ ∧
      CoefficientAssertion E Ω hφ Q L V ρ dE dΩ) ∧
    (∃ p : V →L[E] fixedSpace Q L ρ,
      (∀ v : V, (p v : V) = average Q L ρ v) ∧
      (∀ v : fixedSpace Q L ρ, p v = v) ∧
      (∀ (l : L) (v : V), p (ρ (1, l) v) = fixedRepresentation Q L ρ l (p v))) ∧
    (∀ v : V, average Q L ρ v =
      (Fintype.card Q : E)⁻¹ • ∑ q : Q, ρ (q, 1) v) ∧
    (scalarInsertion Ω V).comp (fixedInclusion E Q L ρ) =
      ((fixedInclusion Ω Q L ρ).restrictScalars E).comp
        (scalarInsertion Ω (fixedSpace Q L ρ)) ∧
    (∀ v : V,
      average Q L (extendedRepresentation E Ω V (Q × L) ρ) ((1 : Ω) ⊗ₜ[E] v) =
        (1 : Ω) ⊗ₜ[E] average Q L ρ v) := by
  sorry

end Main

end Profinite.CondensedAction.PrimeToEll.FiniteAveraging
