/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.NativeVerdierExchangeData
public import WeilConjectures.AlgebraicGeometry.CondensedFiniteTorConstructible
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import WeilConjectures.PoincareDuality.Verdier
import WeilConjectures.AlgebraicGeometry.CondensedSixOperationPreservation
public import WeilConjectures.AlgebraicGeometry.AdmissibleVerdierExchange
import Mathlib.CategoryTheory.Yoneda
public import WeilConjectures.SixFunctors.ModCondensedCachedInstances

/-! # Evaluation-normalized closed-adjunction exchange

Source: latest blueprint, sec-poincare-duality/sk-thm-frobenius/
prop-weil-operations.proof.md, fifth sentence; fix-lem-tensor-adjunction.proof.md, Step 1.
(blueprint: lem-pod-normalized-closed-adjunction-exchange).

All maps below use the specified closed structures. In particular the exchange is
constructed from projection inverse and evaluation, rather than chosen from its endpoints.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u₁ v₁ u₂ v₂ u
open CategoryTheory MonoidalCategory MonoidalClosed Opposite

namespace CategoryTheory.NormalizedClosedExchange

variable {X : Type u₁} [Category.{v₁} X] [MonoidalCategory X]
  [sX : SymmetricCategory X] [MonoidalClosed X]
  {Y : Type u₂} [Category.{v₂} Y] [MonoidalCategory Y]
  [sY : SymmetricCategory Y] [MonoidalClosed Y]

/-- The specified projection isomorphism, with naturality in both variables.
Source: latest blueprint fix-lem-tensor-adjunction.proof.md, Step 1.
(blueprint: lem-pod-normalized-closed-adjunction-exchange). -/
abbrev Projection (U : Y ⥤ X) (F : X ⥤ Y) :=
  curriedTensorInsertFunctor₁ F ≅
    curriedTensorPost F ⋙ (Functor.whiskeringLeft Y X Y).obj U

/-- Regard a componentwise invertible natural projection as a natural isomorphism.
This uses the given morphisms and their unique inverses, without changing any component.
Source: latest blueprint fix-lem-tensor-adjunction.proof.md, Step 1.
(blueprint: lem-pod-normalized-closed-adjunction-exchange). -/
def projectionOfNatTrans {U : Y ⥤ X} {F : X ⥤ Y}
    (p : curriedTensorInsertFunctor₁ F ⟶
      curriedTensorPost F ⋙ (Functor.whiskeringLeft Y X Y).obj U)
    [∀ (M : X) (L : Y), IsIso ((p.app M).app L)] : Projection U F :=
  letI (M : X) : IsIso (p.app M) := NatIso.isIso_of_isIso_app _
  letI : IsIso p := NatIso.isIso_of_isIso_app _
  asIso p

/-- The five-bijection chain on an arbitrary test morphism. Its first arrow is
inverse closed transposition and its second is precomposition by projection inverse.
Source: latest blueprint fix-lem-tensor-adjunction.proof.md, Step 1.
(blueprint: lem-pod-normalized-closed-adjunction-exchange). -/
def homChain {U : Y ⥤ X} {V : X ⥤ Y} {F : X ⥤ Y} {R : Y ⥤ X}
    (adjU : U ⊣ V) (adjF : F ⊣ R) (π : Projection U F)
    (M : X) (N L : Y) (h : L ⟶ (ihom (F.obj M)).obj N) :
    L ⟶ V.obj ((ihom M).obj (R.obj N)) :=
  adjU.homEquiv _ _ (curry (adjF.homEquiv _ _
    (((π.app M).app L).inv ≫ uncurry h)))

/-- The actual exchange component: apply the five-bijection chain to the identity.
Equivalently this is unit of U, followed by V of the curry of the F-adjoint of
projection inverse followed by evaluation.
Source: latest blueprint fix-lem-tensor-adjunction.proof.md, Step 1.
(blueprint: lem-pod-normalized-closed-adjunction-exchange). -/
def map {U : Y ⥤ X} {V : X ⥤ Y} {F : X ⥤ Y} {R : Y ⥤ X}
    (adjU : U ⊣ V) (adjF : F ⊣ R) (π : Projection U F) (M : X) (N : Y) :
    (ihom (F.obj M)).obj N ⟶ V.obj ((ihom M).obj (R.obj N)) :=
  adjU.unit.app _ ≫ V.map (curry (adjF.homEquiv _ _
    (((π.app M).app ((ihom (F.obj M)).obj N)).inv ≫ (ihom.ev (F.obj M)).app N)))

/-- A natural isomorphism with exactly the stated action on every test Hom set.
Naturality is contravariant in M and covariant in N.
Source: latest blueprint fix-lem-tensor-adjunction.proof.md, Step 1.
(blueprint: lem-pod-normalized-closed-adjunction-exchange). -/
def IsExchange {U : Y ⥤ X} {V : X ⥤ Y} {F : X ⥤ Y} {R : Y ⥤ X}
    (adjU : U ⊣ V) (adjF : F ⊣ R) (π : Projection U F)
    (φ : ∀ (M : X) (N : Y),
      (ihom (F.obj M)).obj N ≅ V.obj ((ihom M).obj (R.obj N))) : Prop :=
  (∀ (M : X) (N L : Y) (h : L ⟶ (ihom (F.obj M)).obj N),
    h ≫ (φ M N).hom = homChain adjU adjF π M N L h) ∧
  (∀ {M M' : X} (a : M' ⟶ M) (N : Y),
    (pre (F.map a)).app N ≫ (φ M' N).hom =
      (φ M N).hom ≫ V.map ((pre a).app (R.obj N))) ∧
  (∀ (M : X) {N N' : Y} (b : N ⟶ N'),
    (ihom (F.obj M)).map b ≫ (φ M N').hom =
      (φ M N).hom ≫ V.map ((ihom M).map (R.map b))) ∧
  (∀ M N, (φ M N).hom = map adjU adjF π M N)

include sX sY in
/-- The unique natural isomorphism specified by the five-bijection Hom chain.
Source: latest blueprint fix-lem-tensor-adjunction.proof.md, Step 1;
prop-weil-operations.proof.md, fifth sentence.
(blueprint: lem-pod-normalized-closed-adjunction-exchange).

Proof (node steps 1--3): each of inverse closed transposition, projection inverse,
F-adjunction, closed transposition and U-adjunction is a bijection. Their composite
is natural in the test object L. Yoneda fully faithfulness sends the composite and
its inverse to mutually inverse arrows. At the representing object its value on
identity is projection inverse followed by evaluation and the three transposes,
which is `map`. Naturality of the five arrows in M and N gives the two displayed
squares. Any other family with the Hom-chain property has the same components by
setting h to identity; iso extensionality proves uniqueness. -/
theorem existsUnique_exchange {U : Y ⥤ X} {V : X ⥤ Y} {F : X ⥤ Y} {R : Y ⥤ X}
    (adjU : U ⊣ V) (adjF : F ⊣ R) (π : Projection U F) :
    ∃! φ : ∀ (M : X) (N : Y),
      (ihom (F.obj M)).obj N ≅ V.obj ((ihom M).obj (R.obj N)),
      IsExchange adjU adjF π φ := by
  sorry

/-- Transport of a fixed-pair isomorphism through a commuting functor.
Source: latest blueprint lem-fix-weil-operations.proof.md, functor transport.
(blueprint: lem-pod-normalized-closed-adjunction-exchange). -/
def transport {P : X ⥤ X} {Q : Y ⥤ Y} (J : X ⥤ Y)
    (e : J ⋙ Q ≅ P ⋙ J) {M : X} (θ : P.obj M ≅ M) :
    Q.obj (J.obj M) ≅ J.obj M :=
  e.app M ≪≫ J.mapIso θ

/-- The contragredient fixed-pair structure on internal Hom. The inverse of θA
is used in its contravariant argument; the comparison is the evaluation transpose.
Source: latest blueprint lem-fix-weil-operations.proof.md, internal-Hom paragraph.
(blueprint: lem-pod-normalized-closed-adjunction-exchange). -/
def homStructure (P : X ⥤ X) [P.Monoidal] [P.IsEquivalence]
    {A B : X} (θA : P.obj A ≅ A) (θB : P.obj B ≅ B) :
    P.obj ((ihom A).obj B) ≅ (ihom A).obj B :=
  Functor.Monoidal.ihomObjIso P A B ≪≫
    (Functor.mapIso MonoidalClosed.internalHom θA.symm.op).app (P.obj B) ≪≫
    (ihom A).mapIso θB

/-- Explicit unit and counit preservation for a pair of commuting functors.
Source: latest blueprint lem-fix-weil-operations.proof.md, adjunction paragraph.
(blueprint: lem-pod-normalized-closed-adjunction-exchange). -/
structure PreservesAdjunction (P : X ⥤ X) (Q : Y ⥤ Y)
    {J : X ⥤ Y} {K : Y ⥤ X} (adj : J ⊣ K)
    (eJ : J ⋙ Q ≅ P ⋙ J) (eK : K ⋙ P ≅ Q ⋙ K) : Prop where
  unit (A : X) :
    P.map (adj.unit.app A) ≫ (eK.hom.app (J.obj A)) ≫ K.map (eJ.hom.app A) =
      adj.unit.app (P.obj A)
  counit (B : Y) :
    (eJ.hom.app (K.obj B)) ≫ J.map (eK.hom.app B) ≫ adj.counit.app (Q.obj B) =
      Q.map (adj.counit.app B)

/-- The four commuting functor isomorphisms, with actual unit, counit and projection
compatibility equations. Strong symmetric monoidal structures on P and Q are
parameters of the equivariance theorem, not arbitrary proposition fields.
Source: latest blueprint lem-fix-weil-operations.proof.md, adjunction and projection
paragraphs. (blueprint: lem-pod-normalized-closed-adjunction-exchange). -/
structure Compatible (P : X ⥤ X) (Q : Y ⥤ Y) [P.Monoidal] [Q.Monoidal]
    {U : Y ⥤ X} {V : X ⥤ Y} {F : X ⥤ Y} {R : Y ⥤ X}
    (adjU : U ⊣ V) (adjF : F ⊣ R) (π : Projection U F) where
  eU : U ⋙ P ≅ Q ⋙ U
  eV : V ⋙ Q ≅ P ⋙ V
  eF : F ⋙ Q ≅ P ⋙ F
  eR : R ⋙ P ≅ Q ⋙ R
  adjunctionU : PreservesAdjunction Q P adjU eU eV
  adjunctionF : PreservesAdjunction P Q adjF eF eR
  projection (M : X) (L : Y) :
    Q.map ((π.app M).app L).hom ≫ (eF.hom.app (M ⊗ U.obj L)) ≫
        F.map (Functor.OplaxMonoidal.δ P M (U.obj L)) ≫
        F.map (𝟙 (P.obj M) ⊗ₘ eU.hom.app L) =
      Functor.OplaxMonoidal.δ Q (F.obj M) L ≫
        (eF.hom.app M ⊗ₘ 𝟙 (Q.obj L)) ≫ ((π.app (P.obj M)).app (Q.obj L)).hom

include sX sY in
/-- Equivariance of Φ and Φ inverse, also after any equivariant dualizing
identification. Inputs are individual fixed pairs, not fixed structures on all objects.
Source: latest blueprint lem-fix-weil-operations.proof.md, evaluation and adjunction
paragraphs. (blueprint: lem-pod-normalized-closed-adjunction-exchange).

Proof (node steps 4--6): the evaluation-transpose comparison c_P satisfies its
evaluation equation. Thus the structure on Hom is H(θM inverse,θN)c_P, and evaluation
is equivariant. Uncurrying an equivariant pairing shows that its curry is equivariant:
the θM inverse cancels θM in the pairing equation. For each ordinary adjunction,
the transpose is K(b) followed after the unit; the unit compatibility in `Compatible`
therefore preserves equivariance. Apply these facts to evaluation after projection
inverse, then the F transpose, curry, and U transpose. This is exactly `map` by
steps 1--3. Cancel its two-sided inverse to obtain the inverse equation. If w is
equivariant, Hom(1,w) and V of it are equivariant by naturality of the Hom comparison
and eV; compose with Φ and repeat the inverse calculation. -/
theorem equivariant {U : Y ⥤ X} {V : X ⥤ Y} {F : X ⥤ Y} {R : Y ⥤ X}
    (adjU : U ⊣ V) (adjF : F ⊣ R) (π : Projection U F)
    (φ : ∀ (M : X) (N : Y),
      (ihom (F.obj M)).obj N ≅ V.obj ((ihom M).obj (R.obj N)))
    (hφ : IsExchange adjU adjF π φ)
    (P : X ⥤ X) (Q : Y ⥤ Y) [P.Braided] [Q.Braided]
    [P.IsEquivalence] [Q.IsEquivalence] (c : Compatible P Q adjU adjF π)
    (M : Endofunctor.IsoAlgebra P) (N : Endofunctor.IsoAlgebra Q) :
    (homStructure Q (transport F c.eF M.str) N.str).hom ≫
        (φ M.carrier N.carrier).hom =
      Q.map (φ M.carrier N.carrier).hom ≫
        (transport V c.eV
          (homStructure P M.str (transport R c.eR N.str))).hom ∧
    (transport V c.eV (homStructure P M.str (transport R c.eR N.str))).hom ≫
        (φ M.carrier N.carrier).inv =
      Q.map (φ M.carrier N.carrier).inv ≫
        (homStructure Q (transport F c.eF M.str) N.str).hom ∧
    (∀ (W : Endofunctor.IsoAlgebra P) (w : R.obj N.carrier ≅ W.carrier),
      (transport R c.eR N.str).hom ≫ w.hom = P.map w.hom ≫ W.str.hom →
      (homStructure Q (transport F c.eF M.str) N.str).hom ≫
          ((φ M.carrier N.carrier).hom ≫ V.map ((ihom M.carrier).map w.hom)) =
        Q.map ((φ M.carrier N.carrier).hom ≫ V.map ((ihom M.carrier).map w.hom)) ≫
          (transport V c.eV (homStructure P M.str W.str)).hom ∧
      (transport V c.eV (homStructure P M.str W.str)).hom ≫
          (V.map ((ihom M.carrier).map w.inv) ≫ (φ M.carrier N.carrier).inv) =
        Q.map (V.map ((ihom M.carrier).map w.inv) ≫ (φ M.carrier N.carrier).inv) ≫
          (homStructure Q (transport F c.eF M.str) N.str).hom) := by
  sorry

end CategoryTheory.NormalizedClosedExchange

open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.CondensedRing.NormalizedClosedExchange
open CategoryTheory.NormalizedClosedExchange

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The two field-coefficient domains are the ordinary bounded constructible,
finite-Tor domains, with the existing finiteTorAmplitude predicate.
Source: latest blueprint fix-cor-verdier-exchange.proof.md, Step 2, and
prop-weil-operations.proof.md, fifth sentence.
(blueprint: lem-pod-normalized-closed-adjunction-exchange).

Proof (node step 7, domains): use the field-coefficient category identification in
lem-pod-condensed-six-operation-preservation: bounded constructibility is bounded
constant-model constructibility with finite Tor amplitude. For finite E each lisse
piece is a finite-dimensional E-space and hence has Tor amplitude zero; a bounded
complex has the finite union of its degree intervals. For the algebraic closure,
finite-stage descent puts its finite constructible presentation over one finite E;
extension of scalars is exact and preserves those intervals. The reverse inclusion
is the bounded-constructible clause in the constant-model predicate. No completed
or common-stage derived category is substituted for the ordinary module category. -/
theorem condensed_field_domains (T : Over (Spec (.of k)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom] :
    (boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) T.left) =
      condensedConstructibleFiniteTor (Profinite.continuousMapRingObj E) T.left) ∧
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T.left) =
      condensedConstructibleFiniteTor (Profinite.padicAlgClRingObj ℓ) T.left) := by
  sorry

/-- Specialization to the actual condensed six operations at E and at Qbar_ell.
Postcomposing the evaluation-normalized map with V Hom(1,w) is the canonical
fix-cor-verdier-exchange map. Both sides are actual specified arrows; the right side
is the inverse evaluation/counit exchange followed by the compact-support mate.
Source: latest blueprint prop-weil-operations.proof.md, fifth sentence;
fix-cor-verdier-exchange.proof.md, Steps 1--2.
(blueprint: lem-pod-normalized-closed-adjunction-exchange).

Proof (node step 7, normalization): identify the domains by condensed_field_domains
and restrict the original tensor-Hom and pullback adjunctions, with their original
Hom equivalences as in lem-pod-condensed-six-operation-preservation. The projection
is the canonical proper-factor mate, inverse open projection and pullback compositor;
thm-sf-pf-field gives its invertibility. The five Hom bijections of steps 1--3 are
inverse to the Hom action of Verdier.exchange: expand its curry into projection,
pullback counit, evaluation and exceptional counit, then cancel units and counits
using the two triangle identities. Thus `map` is its unique inverse. For finite E,
finiteDualizingComparison is the existing upper-shriek compositor at the unit;
for Qbar use upperShriekDualizingComplexIso, the same mate. The source Step 2 and
the recorded def-sf-verdier-exchange-data construct the canonical map by inverse
exchange and V Hom(1,w). These are the inverses of the existing `Verdier.absoluteExchange` and
`absoluteVerdierExchange`, respectively, yielding each displayed equality. Its inverse
and naturality are those of the unique exchange above and of this composition mate.
The argument applies also to identity maps and empty schemes, without a choice of
lattice or an additional finite presentation of the input object. -/
theorem condensed_field_normalization (f : X ⟶ Y) :
    (∀ M : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧,
      CategoryTheory.NormalizedClosedExchange.map
          (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E f)
          (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
          (projectionOfNatTrans
            (ContinuousMapRingObj.boundedConstructibleExceptionalProjection ℓ E f))
          M (finiteDualizingComplex ℓ E Y) ≫
        (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E f).map
          ((ihom M).map (finiteDualizingComparison ℓ E f).hom) =
      @CategoryTheory.inv _ _ _ _ (Verdier.absoluteExchange
          (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E f)
          (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
          (ContinuousMapRingObj.boundedConstructibleExceptionalProjection ℓ E f)
          (finiteDualizingComplex ℓ E X) (finiteDualizingComplex ℓ E Y)
          (finiteDualizingComparison ℓ E f) M)
        (IsIso.comp_isIso' inferInstance
          (Verdier.isIso_exchange_of_isIso
            (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E f)
            (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
            (ContinuousMapRingObj.boundedConstructibleExceptionalProjection ℓ E f)
            M (finiteDualizingComplex ℓ E Y)))) ∧
    (∀ M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      CategoryTheory.NormalizedClosedExchange.map
          (boundedConstructibleUpperStarLowerStarAdjunction ℓ f)
          (boundedConstructibleUpperShriekAdjunction ℓ f)
          (projectionOfNatTrans (boundedConstructibleExceptionalProjection ℓ f))
          M (dualizingComplex ℓ Y) ≫
        (boundedConstructibleLowerStar ℓ f).map
          ((ihom M).map (upperShriekDualizingComplexIso ℓ f).hom) =
      @CategoryTheory.inv _ _ _ _ (absoluteVerdierExchange ℓ f M)
        (IsIso.comp_isIso' inferInstance
          (Verdier.isIso_exchange_of_isIso
            (boundedConstructibleUpperStarLowerStarAdjunction ℓ f)
            (boundedConstructibleUpperShriekAdjunction ℓ f)
            (boundedConstructibleExceptionalProjection ℓ f)
            M (dualizingComplex ℓ Y)))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.NormalizedClosedExchange
