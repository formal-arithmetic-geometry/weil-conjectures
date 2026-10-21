/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.Paper.FormalClosedSupport
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import Sheaf.AlgebraicGeometry.ClosedSupportStratumHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.CompletedCondensedCoefficients
import Sheaf.SixFunctors.CompletedCoefficientFreeResolution
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.Paper.CartesianCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleOpenExtensionProducts
import Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit
public import Sheaf.Paper.FormalClosedSupportII
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.CategoryTheory.Sites.RGammaDerivedLimit

/-!
# Supported integral lattice Hom as a reduction tower

Source: blueprint main-20261015, sec-six-functors-basics,
sk-lem-uniform-constructible-ext.proof.md, Lattices and Integral targets;
Stacks Tag 0D6K (blueprint: lem-sfb-lattice-supported-hom-reduction-tower).

The positive level n+1 is indexed by n : ℕ. Quotients are ordinary extension of
scalars, with their canonical units and quotient transitions. All derived
categories are ordinary unbounded categories of internal module sheaves.

The unchanged `stratumGlobalRHom`, `stratumRGamma`, and `stratumDual` definitions
are recorded by `def-sfb-stratum-hom-sections-dual`. In particular `stratumRGamma`
is the right derived functor of Hom from the regular module. Under the canonical
section-action equivalence this regular module is the unit sheaf, so composing
with zeroth homology is the ringed-site zeroth-hypercohomology convention. The
stratum-Hom comparison theorem is needed only for the proof.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.SupportedLatticeHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Ordinary reduction of a lattice at positive level n+1.
Source: blueprint, Lattices, M₀/πⁿ (blueprint: lem-sfb-lattice-supported-hom-reduction-tower). -/
abbrev finiteQuotient (T : Scheme.{u}) (M : AdicCompletion.Modules l E T) (n : ℕ) :=
  (Mod.extendScalars (AdicCompletion.quotient l E T n)).obj M

/-- The actual composition identification of ordinary coefficient restrictions.
Source: blueprint, quotient transitions
(blueprint: lem-sfb-lattice-supported-hom-reduction-tower). -/
def ordinaryRestrictComp (T : Scheme.{u}) (n : ℕ) :
    Mod.comap (AdicCompletion.transition l E T n) ⋙
        Mod.comap (AdicCompletion.quotient l E T (n + 1)) ≅
      (Mod.comap (AdicCompletion.quotient l E T n) :
        Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (AdicCompletion.finiteRing l E T n) ⥤ AdicCompletion.Modules l E T) :=
  (Mod.comapComp (AdicCompletion.quotient l E T (n + 1))
      (AdicCompletion.transition l E T n)).symm ≪≫
    Mod.comapCongr (AdicCompletion.quotient_transition l E T n)

/-- The quotient-induced transition, characterized by its composite with M's quotient unit.
Source: blueprint, Lattices, quotient tower
(blueprint: lem-sfb-lattice-supported-hom-reduction-tower). -/
def finiteQuotientStep (T : Scheme.{u}) (M : AdicCompletion.Modules l E T) (n : ℕ) :
    finiteQuotient l E T M (n + 1) ⟶
      (Mod.comap (AdicCompletion.transition l E T n)).obj (finiteQuotient l E T M n) :=
  ((Mod.extendRestrictAdjunction (AdicCompletion.quotient l E T (n + 1))).homEquiv _ _).symm
    ((Mod.extendRestrictAdjunction (AdicCompletion.quotient l E T n)).unit.app M ≫
      (ordinaryRestrictComp l E T n).inv.app (finiteQuotient l E T M n))

/-- The quotient as an integral module, retaining its canonical scalar restriction.
Source: blueprint, Nₙ before extension by zero
(blueprint: lem-sfb-lattice-supported-hom-reduction-tower). -/
abbrev quotient (T : Scheme.{u}) (M : AdicCompletion.Modules l E T) (n : ℕ) :=
  (Mod.comap (AdicCompletion.quotient l E T n)).obj (finiteQuotient l E T M n)

/-- Integral-module transition of the actual quotient tower.
Source: blueprint, Nₙ quotient transitions
(blueprint: lem-sfb-lattice-supported-hom-reduction-tower). -/
def quotientStep (T : Scheme.{u}) (M : AdicCompletion.Modules l E T) (n : ℕ) :
    quotient l E T M (n + 1) ⟶ quotient l E T M n :=
  (Mod.comap (AdicCompletion.quotient l E T (n + 1))).map
      (finiteQuotientStep l E T M n) ≫
    (ordinaryRestrictComp l E T n).hom.app (finiteQuotient l E T M n)

variable {T B X : Scheme.{u}} (h : B ⟶ X) (v : T ⟶ B) [IsOpenImmersion v]

/-- Supported integral lattice h_*v_!M, as an ordinary module.
Source: blueprint, Lattices, N=b_!M₀
(blueprint: lem-sfb-lattice-supported-hom-reduction-tower). -/
abbrev extension (M : AdicCompletion.Modules l E T) : AdicCompletion.Modules l E X :=
  (CondensedRing.lowerStar (DerivedNakayama.integerRing l E) h).obj
    ((CondensedRing.openImmersionLowerShriek (DerivedNakayama.integerRing l E) v).obj M)

/-- The supported ordinary quotient, before forgetting its finite coefficient action.
Source: blueprint, N-barₙ=b_!(M₀/πⁿ)
(blueprint: lem-sfb-lattice-supported-hom-reduction-tower). -/
abbrev finiteExtension (M : AdicCompletion.Modules l E T) (n : ℕ) :=
  (CondensedRing.lowerStar (DerivedNakayama.quotientRing l E (n + 1)) h).obj
    ((CondensedRing.openImmersionLowerShriek (DerivedNakayama.quotientRing l E (n + 1)) v).obj
      (finiteQuotient l E T M n))

/-- Canonical coefficient restriction commutes with h_*v_!, including quotient actions.
Source: blueprint, Lattices, Nₙ=Resₙ N-barₙ
(blueprint: lem-sfb-lattice-supported-hom-reduction-tower). -/
def restrictionIso (M : AdicCompletion.Modules l E T) (n : ℕ) :
    (Mod.comap (AdicCompletion.quotient l E X n)).obj
        (finiteExtension l E h v M n) ≅ extension l E h v (quotient l E T M n) :=
  (CondensedRing.comapLowerStarIso (DerivedNakayama.reductionRing l E (n + 1)) h).app _ ≪≫
    (CondensedRing.lowerStar (DerivedNakayama.integerRing l E) h).mapIso
      ((CondensedRing.comapOpenImmersionLowerShriekIso
        (DerivedNakayama.reductionRing l E (n + 1)) v).app _)

/-- N in degree zero in the ordinary unbounded integral category.
Source: blueprint, Integral targets (blueprint: lem-sfb-lattice-supported-hom-reduction-tower). -/
abbrev target (M : AdicCompletion.Modules l E T) :=
  (DerivedCategory.singleFunctor (AdicCompletion.Modules l E X) 0).obj
    (extension l E h v M)

/-- Nₙ, with scalar restriction moved past h_*v_! by restrictionIso.
Source: blueprint, Integral targets (blueprint: lem-sfb-lattice-supported-hom-reduction-tower). -/
abbrev level (M : AdicCompletion.Modules l E T) (n : ℕ) :=
  target l E h v (quotient l E T M n)

/-- The finite-coefficient supported quotient in degree zero.
Source: blueprint, definition of N-barₙ
(blueprint: lem-sfb-lattice-supported-hom-reduction-tower). -/
abbrev finiteDerivedExtension (M : AdicCompletion.Modules l E T) (n : ℕ) :
    AdicCompletion.FiniteDerived l E X n :=
  (DerivedCategory.singleFunctor
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (AdicCompletion.finiteRing l E X n)) 0).obj (finiteExtension l E h v M n)

/-- The canonical identification Nₙ=Resₙ N-barₙ in the unbounded derived category.
Source: blueprint, defining the supported reduction tower
(blueprint: lem-sfb-lattice-supported-hom-reduction-tower). -/
def levelRestrictionIso (M : AdicCompletion.Modules l E T) (n : ℕ) :
    (AdicCompletion.restrict l E X n).obj (finiteDerivedExtension l E h v M n) ≅
      level l E h v M n :=
  ((Mod.comap (AdicCompletion.quotient l E X n)).mapDerivedCategorySingleFunctor 0).app
      (finiteExtension l E h v M n) ≪≫
    (DerivedCategory.singleFunctor (AdicCompletion.Modules l E X) 0).mapIso
      (restrictionIso l E h v M n)

/-- The quotient transition after supported extension and degree-zero inclusion.
Source: blueprint, Integral targets (blueprint: lem-sfb-lattice-supported-hom-reduction-tower). -/
def step (M : AdicCompletion.Modules l E T) (n : ℕ) :
    level l E h v M (n + 1) ⟶ level l E h v M n :=
  (DerivedCategory.singleFunctor (AdicCompletion.Modules l E X) 0).map
    ((CondensedRing.lowerStar (DerivedNakayama.integerRing l E) h).map
      ((CondensedRing.openImmersionLowerShriek (DerivedNakayama.integerRing l E) v).map
        (quotientStep l E T M n)))

/-- The actual quotient map N to Nₙ.
Source: blueprint, reduction projections
(blueprint: lem-sfb-lattice-supported-hom-reduction-tower). -/
def projection (M : AdicCompletion.Modules l E T) (n : ℕ) :
    target l E h v M ⟶ level l E h v M n :=
  (DerivedCategory.singleFunctor (AdicCompletion.Modules l E X) 0).map
    ((CondensedRing.lowerStar (DerivedNakayama.integerRing l E) h).map
      ((CondensedRing.openImmersionLowerShriek (DerivedNakayama.integerRing l E) v).map
        ((Mod.extendRestrictAdjunction (AdicCompletion.quotient l E T n)).unit.app M)))

/-- T_R: dual tensor open restriction of derived closed support, with actual derived tensor.
Source: blueprint, Integral targets, definition of F
(blueprint: lem-sfb-lattice-supported-hom-reduction-tower). -/
abbrev supportFunctor {S Z V : Scheme.{u}} (i : Z ⟶ X) (j : V ⟶ X) (uS : S ⟶ Z)
    [IsOpenImmersion j] (L : AdicCompletion.Modules l E S) :=
  (CondensedRing.formalClosedSupport (DerivedNakayama.integerRing l E) i j).rightDerivedFunctor ⋙
    (CondensedRing.upperStar (DerivedNakayama.integerRing l E) uS).mapDerivedCategory ⋙
    (CondensedRing.derivedTensor (DerivedNakayama.integerRing l E) S).obj
      ((DerivedCategory.singleFunctor (AdicCompletion.Modules l E S) 0).obj
        (CondensedRing.stratumDual (DerivedNakayama.integerRing l E) S L))

variable {S Z V : Scheme.{u}} (i : Z ⟶ X) (j : V ⟶ X) (uS : S ⟶ Z)
  [IsOpenImmersion j] [IsOpenImmersion uS] (L : AdicCompletion.Modules l E S)

/-- F=T_R(N), using the specified support and tensor functors.
Source: blueprint, Integral targets (blueprint: lem-sfb-lattice-supported-hom-reduction-tower). -/
abbrev transformedTarget (M : AdicCompletion.Modules l E T) :=
  (supportFunctor l E i j uS L).obj (target l E h v M)

/-- Fₙ=T_R(Nₙ), at positive exponent n+1.
Source: blueprint, Integral targets (blueprint: lem-sfb-lattice-supported-hom-reduction-tower). -/
abbrev transformedLevel (M : AdicCompletion.Modules l E T) (n : ℕ) :=
  (supportFunctor l E i j uS L).obj (level l E h v M n)

/-- The quotient-induced transition on the supported tensor complexes.
Source: blueprint, Integral targets (blueprint: lem-sfb-lattice-supported-hom-reduction-tower). -/
abbrev transformedStep (M : AdicCompletion.Modules l E T) (n : ℕ) :=
  (supportFunctor l E i j uS L).map (step l E h v M n)

/-- Bₙ=RΓ(S,Fₙ), forgetting the scalar action, as a derived abelian-group object.
Source: blueprint, Integral targets (blueprint: lem-sfb-lattice-supported-hom-reduction-tower). -/
abbrev sectionsLevel (M : AdicCompletion.Modules l E T) (n : ℕ) :=
  (CondensedRing.stratumRGamma (DerivedNakayama.integerRing l E) S).obj
    (transformedLevel l E h v i j uS L M n)

/-- The transition on Bₙ, obtained by applying the actual derived sections functor.
Source: blueprint, Integral targets (blueprint: lem-sfb-lattice-supported-hom-reduction-tower). -/
abbrev sectionsStep (M : AdicCompletion.Modules l E T) (n : ℕ) :=
  (CondensedRing.stratumRGamma (DerivedNakayama.integerRing l E) S).map
    (transformedStep l E h v i j uS L M n)

/-- The canonical shift comparison on the global-sections derived functor.
Source: blueprint, applying RΓ to the Roos triangle
(blueprint: lem-sfb-lattice-supported-hom-reduction-tower). -/
instance sectionsCommShift :
    (CondensedRing.stratumRGamma (DerivedNakayama.integerRing l E) S).CommShift ℤ :=
  inferInstanceAs ((preadditiveCoyoneda.obj
    (op (Mod.regular (AdicCompletion.ring l E S)))).rightDerivedFunctor.CommShift ℤ)

/-- All reduction, Roos-triangle and global-Hom clauses for the specified lattices.
The comparison with the derived reductions commutes both with transitions and with
quotient units. Product comparisons are normalized by their actual projections.
The last two triangles are literally the images of the first, transported by those
product comparisons and the canonical shift comparisons.
Source: blueprint, Lattices and Integral targets; Stacks 0D6K
(blueprint: lem-sfb-lattice-supported-hom-reduction-tower). -/
def Assertions (M : AdicCompletion.Modules l E T) : Prop :=
  IsLisseCoefficientModule (DerivedNakayama.integerRing l E)
      (CondensedRing.stratumDual (DerivedNakayama.integerRing l E) S L) ∧
  IsDerivedComplete l E X (target l E h v M) ∧
  (∃ e : ∀ n : ℕ, level l E h v M n ≅
      AdicCompletion.integralLevel l E X (target l E h v M) n,
    (∀ n : ℕ, step l E h v M n ≫ (e n).hom =
      (e (n + 1)).hom ≫ AdicCompletion.integralStep l E X (target l E h v M) n) ∧
    ∀ n : ℕ, projection l E h v M n ≫ (e n).hom =
      (Mod.derivedExtendMapDerivedCategoryAdjunction
        (AdicCompletion.quotient l E X n)).unit.app (target l E h v M)) ∧
  (∃ (_hN : HasProduct (level l E h v M))
      (_hF : HasProduct (transformedLevel l E h v i j uS L M))
      (_hB : HasProduct (sectionsLevel l E h v i j uS L M)),
    ∃ (pN : target l E h v M ⟶ ∏ᶜ (level l E h v M))
      (δN : ∏ᶜ (level l E h v M) ⟶ (target l E h v M)⟦(1 : ℤ)⟧)
      (eF : (supportFunctor l E i j uS L).obj (∏ᶜ (level l E h v M)) ≅
        ∏ᶜ (transformedLevel l E h v i j uS L M))
      (eB : (CondensedRing.stratumRGamma (DerivedNakayama.integerRing l E) S).obj
          (∏ᶜ (transformedLevel l E h v i j uS L M)) ≅
        ∏ᶜ (sectionsLevel l E h v i j uS L M)),
    IsDerivedLimitTriangle (step l E h v M) (target l E h v M) pN δN ∧
    (∀ n : ℕ, pN ≫ Pi.π _ n = projection l E h v M n) ∧
    (∀ n : ℕ, eF.hom ≫ Pi.π _ n =
      (supportFunctor l E i j uS L).map (Pi.π (level l E h v M) n)) ∧
    (∀ n : ℕ, eB.hom ≫ Pi.π _ n =
      (CondensedRing.stratumRGamma (DerivedNakayama.integerRing l E) S).map
        (Pi.π (transformedLevel l E h v i j uS L M) n)) ∧
    IsDerivedLimitTriangle (transformedStep l E h v i j uS L M)
      (transformedTarget l E h v i j uS L M)
      ((supportFunctor l E i j uS L).map pN ≫ eF.hom)
      (eF.inv ≫ (supportFunctor l E i j uS L).map δN ≫
        ((supportFunctor l E i j uS L).commShiftIso (1 : ℤ)).hom.app (target l E h v M)) ∧
    IsDerivedLimitTriangle (sectionsStep l E h v i j uS L M)
      ((CondensedRing.stratumRGamma (DerivedNakayama.integerRing l E) S).obj
        (transformedTarget l E h v i j uS L M))
      ((CondensedRing.stratumRGamma (DerivedNakayama.integerRing l E) S).map
        ((supportFunctor l E i j uS L).map pN ≫ eF.hom) ≫ eB.hom)
      (eB.inv ≫ (CondensedRing.stratumRGamma (DerivedNakayama.integerRing l E) S).map
        (eF.inv ≫ (supportFunctor l E i j uS L).map δN ≫
          ((supportFunctor l E i j uS L).commShiftIso (1 : ℤ)).hom.app
            (target l E h v M)) ≫
        ((CondensedRing.stratumRGamma (DerivedNakayama.integerRing l E) S).commShiftIso
          (1 : ℤ)).hom.app (transformedTarget l E h v i j uS L M)) ∧
    Nonempty ((CondensedRing.stratumGlobalRHom (DerivedNakayama.integerRing l E) X
        (extension l E i uS L)).obj (target l E h v M) ≅
      (CondensedRing.stratumRGamma (DerivedNakayama.integerRing l E) S).obj
        (transformedTarget l E h v i j uS L M)) ∧
    (∀ n : ℕ, Nonempty
      ((CondensedRing.stratumGlobalRHom (DerivedNakayama.integerRing l E) X
        (extension l E i uS L)).obj (level l E h v M n) ≅
        sectionsLevel l E h v i j uS L M n)) ∧
    (∀ (D : DerivedCategory Ab.{u + 1}),
      IsDerivedLimit (K := sectionsLevel l E h v i j uS L M)
        (sectionsStep l E h v i j uS L M) D →
      Nonempty ((CondensedRing.stratumGlobalRHom (DerivedNakayama.integerRing l E) X
        (extension l E i uS L)).obj (target l E h v M) ≅ D) ∧
      ∀ q : ℤ, Nonempty
        ((preadditiveCoyoneda.obj
          (op (target l E i uS L))).obj ((target l E h v M)⟦q⟧) ≅
          (DerivedCategory.homologyFunctor Ab.{u + 1} q).obj D)) ∧
    ∀ (n : ℕ) (q : ℤ), Nonempty
      ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
        (sectionsLevel l E h v i j uS L M n) ≅
        (preadditiveCoyoneda.obj (op (target l E i uS L))).obj
          ((level l E h v M n)⟦q⟧)))

/-- Supported integral lattice Hom is computed by its actual reduction tower.
Source: blueprint main-20261015, uniform constructible Ext proof, Lattices and
Integral targets; Stacks Tag 0D6K
(blueprint: lem-sfb-lattice-supported-hom-reduction-tower).

Proof plan:
1. Finite type over k makes X Noetherian: finite affine covers are Noetherian by
   lem-wf-affine-noetherian-components. Every subset is quasi-compact by
   lem-sfb-noetherian-space-compact-subsets. Thus every open complement and stratum
   inclusion in this statement satisfies the required quasi-compactness hypotheses.
2. On a cover trivializing L, its internal dual is the dual finite free module,
   including rank zero. The dual bases glue since evaluation is intrinsic.
3. The completed coefficient comparison sk-prop-sfb-qlbar-colimit-x and
   lem-sf-completed-coefficient-free-resolution give [R --π^(n+1)--> R].
   Tensor with locally free M identifies derived reduction with its ordinary
   quotient. These augmentations commute with the quotient transitions.
4. On each trivializing slice M is the inverse limit of these quotients, using the
   coefficient limit and finite sums commuting with limits. Descent gives the
   global isomorphism; quotient transitions are epimorphic. No interchange of
   stalks and infinite products is made (def-pur-localized-ringed-site).
5. Exact v_! and h_* from lem-weil-pbc-proetale-ringed-open-closed preserve the
   quotient exact sequences; sk-prop-sfb-cartesian-coefficients identifies actions.
   Their scalar-restriction comparisons give exactly restrictionIso. Applying
   the same coefficient resolution on X gives the reduction comparisons and
   their compatibility with all transitions and quotient units.
6. By det-sf-open-closed-extension-zero-limits v_! preserves products and kernels,
   hence sequential limits. The upper-star/lower-star adjunction and
   lem-weil-pbc-right-adjoint-preserves-limits give the same property for h_*.
   Thus N is the sheaf limit of its epimorphic quotient tower.
7. Apply lem-weil-proetale-surjective-tower-derived-limit: the degree-zero Nₙ
   have their Roos triangle with first arrow the actual quotient projections.
   The reduction comparison identifies its augmentation with completion, proving
   IsDerivedComplete by sk-def-pe-derived-completion.
8. Apply sk-lem-formal-closed-support-ii first to open restriction of support and
   then to dual tensor. Their projection-normalized product comparisons carry
   1-shift to 1-shift, so the image is the asserted Roos triangle for Fₙ.
9. Apply lem-kun-site-rgamma-derived-limit (Stacks 0D6K) on S. Its product
   comparison is normalized by projections; it transports this triangle to the
   Roos triangle for Bₙ. This proves RΓ(S,F) is a derived limit of Bₙ.
10. Apply det-lem-formal-closed-support-stratum-hom to L, first at N then Nₙ,
    and its finite-projective ordinary/derived tensor comparison. Compose with
    step 9. Any derived limit of Bₙ is isomorphic to that one. Its shifted-Hom
    formula and homology of these derived isomorphisms give both degree-q
    conclusions for every integer q, including negative degrees. -/
theorem supported_lattice_hom_reduction_tower
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hp : p ≠ l)
    {X Z V S B T : Scheme.{u}}
    [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : V ⟶ X) (uS : S ⟶ Z) (h : B ⟶ X) (v : T ⟶ B)
    [IsClosedImmersion i] [IsOpenImmersion j] [IsOpenImmersion uS]
    [IsClosedImmersion h] [IsOpenImmersion v]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (L : AdicCompletion.Modules l E S) (M : AdicCompletion.Modules l E T)
    (hL : IsLisseCoefficientModule (DerivedNakayama.integerRing l E) L)
    (hM : IsLisseCoefficientModule (DerivedNakayama.integerRing l E) M) :
    Assertions l E h v i j uS L M := by
  sorry

end AlgebraicGeometry.ProEtale.SupportedLatticeHom
