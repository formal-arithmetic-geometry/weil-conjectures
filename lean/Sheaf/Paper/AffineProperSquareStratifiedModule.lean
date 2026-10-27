module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.Topology.Defs.Filter
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
import Sheaf.AlgebraicGeometry.LocalFinitePresentationInverseImage
public import Sheaf.Paper.CartesianCoefficients
import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

/-!
# Affine proper squares and global stratified module refinement

Source: Stacks Project, Tags 01T3, 01T4, 01T6, 01W3, 01W4, 01OY and 03S0;
Bhatt--Scholze, Definitions 6.8.3, 6.8.6 and 6.8.8
(blueprint: lem-sf-affine-proper-square-stratified-module).

All coefficient pullbacks below use the canonical cartesian coefficient identification.
The local partitions carry no constructibility assumption. The global refinement factors
through the actual fibre products of local stratum immersions with the affine charts.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale

/-- The base change of `p : P → T` after restriction of `P ×_T T'` to an open `U` of `T`.
The source is literally `(P ×_T T') ×_T U`, and the target is `T' ×_T U`.
Source: Stacks Project, Tag 01W4, canonical fibre-product projections
(blueprint: lem-sf-affine-proper-square-stratified-module). -/
def affineProperSquareBaseChangeMap
    {P T T' : Scheme.{u}} (p : P ⟶ T) (h : T' ⟶ T) (U : T.Opens) :
    pullback (pullback.snd p h ≫ h) U.ι ⟶ pullback h U.ι :=
  pullback.lift
    (pullback.fst (pullback.snd p h ≫ h) U.ι ≫ pullback.snd p h)
    (pullback.snd (pullback.snd p h ≫ h) U.ι)
    ((Category.assoc _ _ _).trans (pullback.condition (f := pullback.snd p h ≫ h) (g := U.ι)))

/-- Affine localization supplies separated finite-type corners, and local finite-free
stratifications of an internal coefficient module admit finite global immersed refinements.

Source: Stacks Project, Tags 01T3, 01T4, 01T6, 01W3, 01W4, 01OY and 03S0;
Bhatt--Scholze, Definitions 6.8.3, 6.8.6 and 6.8.8
(blueprint: lem-sf-affine-proper-square-stratified-module).

Proof:
1. The open immersion `U.ι` is locally of finite type (immersion-base-change-lft).
Compose with the finite-type structure map of `T` (proper-fp-permanence). The affine
source makes its structure map quasi-compact and separated (affine-source-morphism-separated).
2. The quasi-compact immersion `h` is finite type. Base change preserves this and
immersions (finite-type-composition-base-change, immersion-base-change-lft). Immersions
are separated (separated-cancellation). Properness of both vertical arrows follows from
proper-fp-permanence. Composing their separated finite-type structure maps gives all corners.
3. A field is Noetherian and its spectrum is quasi-compact. Finite-type-over-noetherian
gives local Noetherianity and compactness of `P_U`; locally-noetherian-quasi-separated
gives quasi-separatedness.
4. For each affine chart `W`, restrict its chosen local partition by actual fibre
products. A free module has a zero-relation finite presentation. Apply
local-finite-presentation-inverse-image to those presentations. Cartesian-coefficients
identifies the rings, and finite-upper-star-comp identifies iterated restrictions. Thus
local finite freeness persists on the restricted strata. Noetherianity makes their
locally closed images constructible (def-weil-constructible-subset, Tag 005L).
5. Apply etale-stratification-local-gluing-core to these restricted partitions. Its
factorizations are actual morphisms to the local representatives. Pull back the same
zero-relation presentations along these morphisms, using finite-upper-star-comp and
cartesian-coefficients again. This gives the required local finite-free trivializations.
6. The identity of a finite free module is the cokernel of the zero-source arrow, so
def-sfb-finitely-presented-module and def-sfb-locally-finitely-presented give local finite
presentation on each stratum. The global partition witnesses constructibility. The
single complex has degree-zero cohomology the restricted module and all other cohomology
zero. Zero is constructible by rank zero; bounds `[0,0]` give bounded-constructible
membership. Empty schemes and empty strata require no nonempty indices or positive ranks.
-/
theorem affineProperSquare_stratifiedModule
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {P T T' : Scheme.{u}} (t : T ⟶ Spec (.of k))
    [LocallyOfFiniteType t] [QuasiCompact t]
    (p : P ⟶ T) [IsProper p] (h : T' ⟶ T) [QuasiCompact h] [IsImmersion h]
    (N : Mod (Sheaf (Scheme.ProEt.topology P) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) P))
    (I : Type v) (V : I → P.Opens)
    (hV : (⋃ i : I, (V i : Set P)) = Set.univ)
    (L : ∀ i : I, Scheme.FiniteLocallyClosedStratification (V i))
    (hN : ∀ (i : I) (c : Fin (L i).n),
      ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage ((L i).domain c),
        ∀ z : C.I₀,
          Mod.IsFree (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (C.X z))
            ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
              (C.f z ≫ (L i).immersion c ≫ (V i).ι)).obj N))
    (U : T.Opens) (hU : IsAffineOpen U) :
    (IsSeparated (U.ι ≫ t) ∧
      LocallyOfFiniteType (U.ι ≫ t) ∧ QuasiCompact (U.ι ≫ t)) ∧
    (IsSeparated (pullback.snd h U.ι ≫ U.ι ≫ t) ∧
      LocallyOfFiniteType (pullback.snd h U.ι ≫ U.ι ≫ t) ∧
      QuasiCompact (pullback.snd h U.ι ≫ U.ι ≫ t)) ∧
    (IsSeparated (pullback.snd p U.ι ≫ U.ι ≫ t) ∧
      LocallyOfFiniteType (pullback.snd p U.ι ≫ U.ι ≫ t) ∧
      QuasiCompact (pullback.snd p U.ι ≫ U.ι ≫ t)) ∧
    (IsSeparated (pullback.snd (pullback.snd p h ≫ h) U.ι ≫ U.ι ≫ t) ∧
      LocallyOfFiniteType (pullback.snd (pullback.snd p h ≫ h) U.ι ≫ U.ι ≫ t) ∧
      QuasiCompact (pullback.snd (pullback.snd p h ≫ h) U.ι ≫ U.ι ≫ t)) ∧
    IsProper (pullback.snd p U.ι) ∧ IsProper (affineProperSquareBaseChangeMap p h U) ∧
    IsLocallyNoetherian (pullback p U.ι) ∧ CompactSpace (pullback p U.ι : Scheme.{u}) ∧
    QuasiSeparatedSpace (pullback p U.ι : Scheme.{u}) ∧
    (∀ (n : ℕ) (W : Fin n → (pullback p U.ι).Opens)
      (_hW : ∀ a, IsAffineOpen (W a))
      (_hcover : (⋃ a : Fin n, (W a : Set (pullback p U.ι : Scheme.{u}))) = Set.univ)
      (a : Fin n → I) (q : ∀ j : Fin n, (W j).toScheme ⟶ (V (a j)).toScheme)
      (_hq : ∀ j, q j ≫ (V (a j)).ι = (W j).ι ≫ pullback.fst p U.ι),
      ∃ S : Scheme.FiniteLocallyClosedStratification (pullback p U.ι),
        (∀ b, Topology.IsConstructible (S.stratum b)) ∧
        (∀ b, ∃ (j : Fin n) (c : Fin (L (a j)).n)
          (r : S.domain b ⟶ pullback ((L (a j)).immersion c) (q j)),
          r ≫ pullback.snd ((L (a j)).immersion c) (q j) ≫ (W j).ι = S.immersion b) ∧
        (∀ b, ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain b),
          ∀ z : C.I₀,
            Mod.IsFree (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (C.X z))
              ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
                (C.f z ≫ S.immersion b ≫ pullback.fst p U.ι)).obj N)) ∧
        (∀ b, IsLocallyFinitelyPresented
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (S.domain b))
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
            (S.immersion b ≫ pullback.fst p U.ι)).obj N))) ∧
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (pullback p U.ι))
      ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
          (pullback.fst p U.ι)).obj N)) := by
  sorry

end AlgebraicGeometry.ProEtale
