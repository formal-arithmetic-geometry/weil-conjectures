/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.ContinuousCoefficientModuleEncoding
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Paper.LatticeSheafBasic
import Sheaf.Paper.LatticeSheafLocallyConstant
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.Paper.ContinuousCoefficientRealizations
import Sheaf.Paper.PadicIntegersInvertEll
import Sheaf.AlgebraicGeometry.WeaklyEtaleStability
import Sheaf.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import Sheaf.AlgebraicGeometry.IndQuasiAffineFpqcDescent
import WeilConjectures.AlgebraicGeometry.FpqcDescentEtale
import WeilConjectures.AlgebraicGeometry.IsSeparatedOfFlatSurjectiveBaseChange
import Sheaf.AlgebraicGeometry.EtaleComparison
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Sites.Precoverage

/-! # The scheme representing embedded integral lattices

Source: blueprint main-20261015, sk-lem-stratified-lattice-scheme, (1)--(3).
(blueprint: det-lem-stratified-lattice-scheme).

## Main definitions and statement

* `latticeCondensedField`, `latticeCondensedIntegers`: the actual condensed coefficients.
* `latticeCondensedRingInclusion`, `latticeCondensedInclusion`: their actual inclusion.
* `stratifiedLatticeModule`, `stratifiedLatticeScalarMap`, `stratifiedLatticeSectionRing`:
  the recorded sectionwise encoding of those same internal modules and scalar map.
* `exists_stratifiedLatticeScheme`: the three clauses of the lattice-scheme lemma.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The rational condensed coefficient ring, with the canonical extension topology.
Source: blueprint sk-lem-stratified-lattice-scheme, coefficient convention.
(blueprint: det-lem-stratified-lattice-scheme). -/
abbrev latticeCondensedField (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
  Profinite.continuousCoefficientRingObj (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))

/-- The integral condensed coefficient ring uses the induced valuation-ring topology.
Source: blueprint sk-lem-stratified-lattice-scheme, coefficient convention.
(blueprint: det-lem-stratified-lattice-scheme). -/
abbrev latticeCondensedIntegers (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
  Profinite.continuousCoefficientRingObj (latticeCoefficientIntegers l E)

/-- Inclusion of integral continuous functions into rational continuous functions.
Source: blueprint sk-lem-stratified-lattice-scheme, coefficient convention.
(blueprint: det-lem-stratified-lattice-scheme). -/
def latticeCondensedRingInclusion (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Profinite.continuousCoefficientRingSheaf (latticeCoefficientIntegers l E) ⟶
      Profinite.continuousCoefficientRingSheaf
        (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) :=
  ⟨{ app := fun S ↦ RingCat.ofHom
      (ULift.ringEquiv.symm.toRingHom.comp
        (((latticeCoefficientIntegers l E).subtype.compLeftContinuous S.unop
          continuous_subtype_val).comp ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The actual condensed coefficient inclusion as a bundled morphism of ring objects.
Source: blueprint sk-lem-stratified-lattice-scheme, coefficient convention.
(blueprint: det-lem-stratified-lattice-scheme). -/
def latticeCondensedInclusion (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Mon.mk (latticeCondensedIntegers l E) ⟶ Mon.mk (latticeCondensedField l E) :=
  Mon.ofHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (latticeCondensedRingInclusion l E))

/-- The sectionwise presentation of the given internal rational module, using the
recorded equivalence, whose underlying abelian sheaf and restrictions are unchanged.
Source: blueprint sk-lem-stratified-lattice-scheme, module-object convention.
(blueprint: det-lem-stratified-lattice-scheme). -/
abbrev stratifiedLatticeModule (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (latticeCondensedField l E) X)) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
    (condensedRingObj (latticeCondensedField l E) X)).functor.obj L

/-- The integral-to-rational scalar map in the recorded section-ring reconstruction.
Source: blueprint sk-lem-stratified-lattice-scheme, module-object convention.
(blueprint: det-lem-stratified-lattice-scheme). -/
abbrev stratifiedLatticeScalarMap (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :=
  sectionRingMap X (coefficientMap (latticeCondensedInclusion l E).hom X)

/-- The rational section ring of the same internal coefficient object.
Source: blueprint sk-lem-stratified-lattice-scheme, module-object convention.
(blueprint: det-lem-stratified-lattice-scheme). -/
abbrev stratifiedLatticeSectionRing (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :=
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
      (condensedRingObj (latticeCondensedField l E) X))

/-- The lattice functor is a sheaf, is locally the constant lattice-coset sheaf,
and is represented by a separated surjective etale scheme carrying its universal lattice.
Source: blueprint main-20261015, sk-lem-stratified-lattice-scheme, (1)--(3).
(blueprint: det-lem-stratified-lattice-scheme).

Proof: identify pulled-back condensed coefficients with continuous coefficient sheaves,
compatibly with their inclusion (lem-weil-pbc-continuous-coefficient-realizations), and
identify inversion of l with rational scalar extension
(det-prop-sfb-qlbar-colimit-x-invert-ell). A lattice pair embeds by m -> alpha(1 tensor m);
free charts show injectivity. Its image determines the pair up to a unique intertwining
isomorphism. The local lattice-classification theorem
(lem-weil-pbc-lattice-sheaf-locally-constant) therefore gives the sheaf and (1).
Choose a finite affine trivializing pro-etale cover of qcqs X. Finite disjoint unions
of affines are affine (lem-weil-pbc-affine-morphism-permanence), weak etaleness is stable
(sk-lem-pe-weakly-etale-stability), and quasi-separatedness makes the flat surjection
quasi-compact (lem-weil-pbc-affine-scheme-qcqs, lem-weil-pbc-qcqs-morphism-permanence).
Over it form the coproduct of copies indexed by lattice cosets
(lem-weil-pbc-scheme-coproduct-family). Maps into this coproduct are precisely clopen decompositions
(lem-galois-coproduct-copies-morphisms-clopen); hence it represents the constant sheaf.
The sheaf's transition isomorphisms give scheme maps component by component and satisfy
the descent cocycle. Every quasi-compact open meets finitely many components, and is
quasi-affine over each affine base open. Apply ind-quasi-affine fpqc effective descent
(lem-a1-ind-quasi-affine-fpqc-effective-descent, Stacks 0APK). Etaleness and separatedness
descend by lem-galois-fpqc-descend-etale and lem-weil-pbc-fpqc-descend-separated.
The standard lattice supplies surjectivity. On an arbitrary test object, pull back the
cover (lem-galois-fpqc-covering-base-change), then glue its classifying map by
lem-weil-pbc-fpqc-representable-descent; this identifies the
descended scheme with the original sheaf, naturally in that object.
Etale implies weakly etale (det-pe-morphisms-etale-comparison), so the representing
scheme is a site object. Evaluate its
representing isomorphism on the identity to obtain the embedded universal lattice;
naturality gives its pullback universal property. Rank zero yields the zero lattice
and representing scheme X; for empty X use the empty cover and the empty representing
scheme. No Noetherian, nonempty-base or positive-rank condition is needed. -/
theorem exists_stratifiedLatticeScheme (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (r : ℕ)
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (latticeCondensedField l E) X))
    (_hL : ∃ (I : Type (u + 1)) (U : I → X.ProEt),
      (Scheme.ProEt.topology X).CoversTop U ∧ ∀ i : I,
      Nonempty ((stratifiedLatticeModule l E X L).over (U i) ≅
        SheafOfModules.free (R := (stratifiedLatticeSectionRing l E X).over (U i))
          (ULift.{u + 1} (Fin r)))) :
    ∃ (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 2)))
      (c : ∀ U : X.ProEt,
        IntegralLatticePair (stratifiedLatticeScalarMap l E X)
          (stratifiedLatticeModule l E X L) U → F.obj.obj (op U)),
      IsLatticeClassPresentation (stratifiedLatticeScalarMap l E X)
        (stratifiedLatticeModule l E X L) F c ∧
      (∀ (V : X.ProEt)
        (_t : (stratifiedLatticeModule l E X L).over V ≅
          SheafOfModules.free (R := (stratifiedLatticeSectionRing l E X).over V)
            (ULift.{u + 1} (Fin r))),
        Nonempty (F.over V ≅
          (constantSheaf ((Scheme.ProEt.topology X).over V) (Type (u + 2))).obj
            (ULift.{u + 2} (integralMatrixCosets (latticeCoefficientIntegers l E) r)))) ∧
      ∃ Q : X.ProEt, IsSeparated Q.hom ∧ Etale Q.hom ∧ Surjective Q.hom ∧
        ∃ ρ : F.obj ≅
          ((Scheme.ProEt.forget X).op ⋙ yoneda.obj (Over.mk Q.hom)) ⋙ uliftFunctor.{u + 2},
          ∃ M : IntegralLatticePair (stratifiedLatticeScalarMap l E X)
              (stratifiedLatticeModule l E X L) Q,
            (ρ.hom.app (op Q) (c Q M)).down = 𝟙 (Over.mk Q.hom) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
