/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U9
-/
module

public import Sheaf.Paper.EtaleMonodromyRealizationData
import Sheaf.SixFunctors.IntegralLisseReductionEquivalence
import Sheaf.AlgebraicGeometry.ProEtaleFiniteLocalSystemsTwist
import Sheaf.NumberTheory.Padics.AdicLimitFiniteModules
import Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuitySections
import Sheaf.RepresentationTheory.ProfiniteStableLattice
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-! # Normalized rational monodromy before exactness

Source: Bhatt--Scholze, Proposition 6.8.4(1),(4) and Corollary 6.8.5.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Integral monodromy followed by rationalization gives a fully faithful linear
functor, with simultaneous functorial normalization on every invariant lattice.
Source: Bhatt--Scholze, Proposition 6.8.4(1),(4), Corollary 6.8.5, pp. 59--60.
(blueprint: lem-sfb-normalized-monodromy-functor)

Proof: apply integral reduction equivalence and finite local-system comparison to identify
integral lisse modules with normalized towers of finite continuous representations. Taking
fibres and inverse limits gives finite free integral representations: recursively lift a basis
modulo the uniformizer, whose lifts remain bases by the unit determinant criterion. The limit
action is continuous because each finite projection is continuous. Equivariant maps are
exactly compatible maps of these towers. Conversely, reduce any invariant lattice and use
finite monodromy followed by inverse limit. The coefficient limit gives the continuous
integral scalar action and the scalar compatibility of its projections. On integral lisse
modules internal Hom is locally a matrix sheaf. Its localization is rational internal Hom;
bounded continuity of sections on the qcqs base identifies global Hom after localization
with localization of integral Hom. Every continuous rational representation has a stable
finite free lattice. Clear denominators in lattice bases to define the rational functor on
maps. Two fraction presentations agree after a common multiplication by a power of l, proving
functoriality, additivity and linearity. Any two invariant lattices are commensurable; the
identity on the rational representation gives their canonical comparison, with cocycle and
naturality identities by the Hom correspondence. This supplies all normalizations at once,
including rank zero, with the prescribed finite fibre actions and transition maps. -/
theorem exists_sf_normalized_monodromy_functor (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) (p : SfMonodromyPoint T)
    (c : GaloisLisseFiniteCorrespondence p.point p.group) :
    ∃ J : SfContinuousRepresentations l E p ⥤ SfRationalModules l E T,
      Nonempty J.FullyFaithful ∧ J.Additive ∧
      (∀ (V W : SfContinuousRepresentations l E p) (f : V ⟶ W) (a : E)
        (U : T.ProEtᵒᵖ) (x : (J.obj V).val.obj U),
        (J.map (a • f)).val.app U x =
          ProEtale.lisseFieldConstantSized l E T U a • (J.map f).val.app U x) ∧
      (∀ V, (J.obj V).IsFiniteLocallyFree) ∧
      ∃ N : ∀ (V : SfContinuousRepresentations l E p) (B : SfInvariantLattice l E V),
        SfLatticeNormalization l E p c J V B,
        ∀ (V W : SfContinuousRepresentations l E p) (f : V ⟶ W)
          (B : SfInvariantLattice l E V) (C : SfInvariantLattice l E W)
          (h : ∀ b : B.submodule, f.hom.hom b.val ∈ C.submodule),
          Nonempty (SfNormalizationMap l E f B C h (N V B) (N W C)) := by sorry

end AlgebraicGeometry.Scheme
