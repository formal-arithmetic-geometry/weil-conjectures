/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U9
-/
module

public import Sheaf.Paper.EtaleMonodromyRealizationData
import Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal
import Sheaf.SixFunctors.IntegralLisseReductionEquivalence
import Sheaf.AlgebraicGeometry.ProEtaleFiniteLocalSystemsTwist
import Sheaf.NumberTheory.Padics.AdicLimitFiniteModules
import Sheaf.AlgebraicGeometry.LisseLatticeCoefficientsSized
import Sheaf.Paper.GaloisLisseRepresentations

/-! # Etale-local monodromy models for a single lisse module

Source: Bhatt--Scholze, Proposition 6.8.4(1),(4),(6), Corollary 6.8.5, pp. 59--60.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- A single lisse module has an etale cover on which any pointed etale refinement
has a monodromy model. Source: Bhatt--Scholze, Proposition 6.8.4(1),(4),(6), and
Corollary 6.8.5, pp. 59--60.
(blueprint: lem-sfb-monodromy-single-object-cover)

Proof: choose an etale-local integral lattice using Proposition 6.8.4(6). Its restriction
along any etale arrow is finite locally free and rationalizes to the restricted module,
since the slice coefficients are the same continuous functions. On a connected pointed
qcqs Noetherian refinement its reductions form a normalized tower. Finite monodromy sends
this to compatible finite free representations over the positive coefficient quotients.
Lift a basis successively to identify the limit with a finite free module over the complete
valuation ring; the limit action is continuous because its finite projections are. Tensor
this representation with E. The original limit lattice is invariant and spans. The finite
monodromy comparison identifies its finite levels and transition maps with the original
lattice reductions. By the inverse-limit universal properties and compatibility with
constant integral scalars, every normalized realization of this representation is the
rationalization of that lattice. Compose with the chosen rationalization isomorphism.
The same construction with lifted coefficient values handles the larger coefficient universe.
Rank zero uses the zero representation. This only constructs a cover for one object; no
simultaneous refinement for a family or any lifting of arrows is included. -/
theorem exists_sf_monodromy_single_object_cover (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (S : Scheme.{u})
    (L : SfRationalModules l E S) (hL : L.IsFiniteLocallyFree) :
    ∃ (I : Type (u + 1)) (Y : I → S.Etale), S.smallEtaleTopology.CoversTop Y ∧
      ∀ (i : I) (T : Scheme.{u}) (g : T ⟶ (Y i).left) [Etale g]
        (p : SfMonodromyPoint T) (R : SfMonodromyRealization l E p),
        ∃ V : SfContinuousRepresentations l E p,
          Nonempty ((R.functor.obj V).val ≅
            (PresheafOfModules.pushforward
              (ProEtale.lisseEtaleCoefficientIdentificationSized l E (g ≫ (Y i).hom))).obj
                L.val) := by sorry

end AlgebraicGeometry.Scheme
