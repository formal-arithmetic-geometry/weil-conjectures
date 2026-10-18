import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Augmented injective cycle test

Blueprint: `lem-coef-augmented-injective-cycle-test`.
Source: the agent-formulated injective-tail test in the historical blueprint
`literature/blueprint/master/blueprint/sec-six-functors/`
`sk-prop-sf-biduality-general/prop-coef-integral-exceptional-adjoint.md`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open CategoryTheory.Preadditive
open CochainComplex

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasZeroObject C]

/-- The terms of the augmented injective tail: `T` in degree zero, the
resolution terms in positive degrees, and zero in negative degrees.

Source: the agent-formulated injective-tail test in the historical blueprint,
`literature/blueprint/master/blueprint/sec-six-functors/`
`sk-prop-sf-biduality-general/prop-coef-integral-exceptional-adjoint.md`
(blueprint: lem-coef-augmented-injective-cycle-test). -/
def augmentedTerm (T : C) (I : InjectiveResolution T) (n : ℤ) : C :=
  if _hn : n < 0 then (0 : C) else if _hz : n = 0 then T
  else I.cocomplex.X (Int.toNat (n - 1))

/-- The differential of the augmented injective tail.

Source: the agent-formulated injective-tail test in the historical blueprint,
`literature/blueprint/master/blueprint/sec-six-functors/`
`sk-prop-sf-biduality-general/prop-coef-integral-exceptional-adjoint.md`
(blueprint: lem-coef-augmented-injective-cycle-test). -/
def augmentedDiff (T : C) (I : InjectiveResolution T) (n : ℤ) :
    augmentedTerm T I n ⟶ augmentedTerm T I (n + 1) := by
  classical
  by_cases hzero : n = 0
  · subst n
    simpa [augmentedTerm] using I.ι.f 0
  · by_cases hpos : 0 < n
    · let k : ℕ := Int.toNat (n - 1)
      have hk : Int.toNat n = k + 1 := by
        dsimp [k]
        omega
      have hnterm : augmentedTerm T I n = I.cocomplex.X k := by
        unfold augmentedTerm
        rw [dif_neg (not_lt.mpr (le_of_lt hpos)), dif_neg hzero]
      have hnterm' : augmentedTerm T I (n + 1) = I.cocomplex.X (k + 1) := by
        unfold augmentedTerm
        have hnp : ¬ n + 1 < 0 := by omega
        have hnz : ¬ n + 1 = 0 := by omega
        rw [dif_neg hnp, dif_neg hnz]
        congr 1
        omega
      exact eqToHom hnterm ≫ I.cocomplex.d k (k + 1) ≫ eqToHom hnterm'.symm
    · exact 0

/-- The square-zero identities for the displayed augmented differential.

Source: the resolution exactness calculation in the agent-formulated
injective-tail test, at the blueprint place cited below
(blueprint: lem-coef-augmented-injective-cycle-test).  The proof splits into
negative, zero, and positive degrees; the zero case is the augmentation
identity and the positive case is the consecutive-differential identity of
the injective resolution. -/
theorem augmentedDiff_sq (T : C) (I : InjectiveResolution T) (n : ℤ) :
    augmentedDiff T I n ≫ augmentedDiff T I (n + 1) = 0 := by
  sorry

/-- The integer cochain complex obtained by adjoining `T` to the front of an
injective resolution.

Source: the agent-formulated injective-tail test in the historical blueprint,
`literature/blueprint/master/blueprint/sec-six-functors/`
`sk-prop-sf-biduality-general/prop-coef-integral-exceptional-adjoint.md`
(blueprint: lem-coef-augmented-injective-cycle-test). -/
def augmentedComplex (T : C) (I : InjectiveResolution T) : CochainComplex C ℤ :=
  CochainComplex.of (augmentedTerm T I) (augmentedDiff T I) (augmentedDiff_sq T I)

/-- A short extension with fixed ends.  Its quotient by isomorphisms is the
Yoneda set of one extensions, used below for the Ext-one notation.

Source: Stacks Project, Homology, Tag 010I (section-extensions), as expanded
in the agent-formulated injective-tail test
(blueprint: lem-coef-augmented-injective-cycle-test). -/
structure ShortExtension (T Z : C) where
  middle : C
  f : T ⟶ middle
  g : middle ⟶ Z
  zero : f ≫ g = 0
  exact : (ShortComplex.mk f g zero).ShortExact

/-- Isomorphisms of short extensions inducing the identity on both ends.

Source: Stacks Project, Homology, Tag 010I (section-extensions)
(blueprint: lem-coef-augmented-injective-cycle-test). -/
structure ShortExtensionIso {T Z : C} (E F : ShortExtension T Z) where
  hom : E.middle ≅ F.middle
  hom_f : E.f ≫ hom.hom = F.f
  hom_g : hom.hom ≫ F.g = E.g

namespace ShortExtension

variable {T Z : C}

/-- The relation used to form the Yoneda quotient.

Source: Stacks Project, Homology, Tag 010I
(blueprint: lem-coef-augmented-injective-cycle-test). -/
def Rel (E F : ShortExtension T Z) : Prop := Nonempty (ShortExtensionIso E F)

/-- Reflexivity of endpoint-preserving extension isomorphism.

Source: Stacks Project, Homology, Tag 010I
(blueprint: lem-coef-augmented-injective-cycle-test).  The identity middle
isomorphism satisfies both endpoint equations. -/
theorem rel_refl (E : ShortExtension T Z) : Rel E E := by
  sorry

/-- Symmetry of endpoint-preserving extension isomorphism.

Source: Stacks Project, Homology, Tag 010I
(blueprint: lem-coef-augmented-injective-cycle-test).  Invert the middle
isomorphism and use its two endpoint equations. -/
theorem rel_symm {E F : ShortExtension T Z} : Rel E F → Rel F E := by
  sorry

/-- Transitivity of endpoint-preserving extension isomorphism.

Source: Stacks Project, Homology, Tag 010I
(blueprint: lem-coef-augmented-injective-cycle-test).  Compose the middle
isomorphisms and reassociate the endpoint equations. -/
theorem rel_trans {E F G : ShortExtension T Z} : Rel E F → Rel F G → Rel E G := by
  sorry

/-- The equivalence relation quotienting endpoint-preserving extension
isomorphisms.

Source: Stacks Project, Homology, Tag 010I
(blueprint: lem-coef-augmented-injective-cycle-test). -/
def setoid (T Z : C) : Setoid (ShortExtension T Z) where
  r := Rel
  iseqv := ⟨rel_refl, rel_symm, rel_trans⟩

end ShortExtension

/-- Isomorphism classes of short exact extensions of `Z` by `T`.

Source: Stacks Project, Homology, Tag 010I (section-extensions)
(blueprint: lem-coef-augmented-injective-cycle-test). -/
def ExtensionClass (T Z : C) : Type (max u v) := _root_.Quotient (ShortExtension.setoid T Z)

/-- The augmented injective cycle test.

Source: the agent-formulated injective-tail test in the historical blueprint,
`literature/blueprint/master/blueprint/sec-six-functors/`
`sk-prop-sf-biduality-general/prop-coef-integral-exceptional-adjoint.md`
(blueprint: lem-coef-augmented-injective-cycle-test).

The proof proceeds as follows.  First, exactness of `X` gives the short exact
cycle rows `0 → ZⁿX → Xⁿ → Zⁿ⁺¹X → 0`, using the abelian epi/cokernel
criterion.  The augmentation and the resolution exactness make the displayed
integer tail a complex.  Degree-zero cocycles are cochain maps, while degree
minus-one coboundaries are the stated signed homotopies.  Restricting a map's
degree-zero component to `Z¹X` identifies cocycles modulo homotopy with
`Hom(Z¹X,T)` modulo maps extending across `X¹`; injectivity of the resolution
constructs all higher components and proves both surjectivity and the converse
homotopy assertion.  Push out the first cycle row along such a map to obtain a
short extension of `Z²X`.  The pushout universal property and the five lemma
show that its class is split exactly when the map extends across `X¹`, and
that equal classes are precisely related by such an extension.  Pulling an
arbitrary extension back along `X¹ → Z²X` and using the assumed split
`Ext¹(X¹,T)` makes this assignment surjective.  The same pushout construction
identifies addition with Baer addition.  Finally, the universal properties
give naturality for cochain maps of acyclic sources and for maps of augmented
injective resolutions (under the stated split hypotheses); the chosen
comparison maps are unique up to the same homotopies. -/
theorem augmentedInjectiveCycleTest
    (T : C) (I : InjectiveResolution T)
    (X : CochainComplex C ℤ)
    (hX : ∀ n : ℤ, X.ExactAt n)
    (hExt : Subsingleton (ExtensionClass T (X.X 1))) :
    Nonempty (CochainComplex.HomComplex.CohomologyClass X
      (augmentedComplex T I) 0 ≃ ExtensionClass T (X.cycles 2)) := by
  sorry

end CategoryTheory
