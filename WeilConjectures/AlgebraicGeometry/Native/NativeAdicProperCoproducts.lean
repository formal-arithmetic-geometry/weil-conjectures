/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.Adic.Truncation
public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.NativeEncoding.NativeAdicEncodingConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic

/-! # Native proper direct image on the constructible localizing hull

Source: blueprint `sk-prop-int-brown-construction`, proper-image bullet;
steps 1 and 6--10 of `lem-sf-locally-finite-adic-compact-support-sums`.
(blueprint: lem-sf-native-adic-proper-coproducts)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

namespace AlgebraicGeometry.ProEtale

/-- The ordinary total right derived native proper direct image preserves coproducts
of objects of the bounded constructible localizing hull. Its target is the ambient
ordinary derived category; this does not assert preservation of a target hull or of
coproducts of arbitrary ambient objects.

Source: blueprint `sk-prop-int-brown-construction`, proper-image bullet, specialized
as steps 1 and 6--10 of `lem-sf-locally-finite-adic-compact-support-sums`.
(blueprint: lem-sf-native-adic-proper-coproducts)

Proof: Properness over Noetherian Y makes Z Noetherian. Use the specified exact
encoding and its derived direct-image square from
`lem-sf-native-adic-encoding-ordinary-operations`. By
`lem-sf-native-adic-encoding-bounded-constructible`, it takes native bounded
constructible generators into the condensed bounded constructible class.
Since a derived exact equivalence is triangulated and preserves coproducts,
minimality sends the native hull into the condensed hull. Lift the encoding to
these full subcategories. Their inclusions preserve and reflect coproducts,
so this lift preserves coproducts as well.

Apply `lem-sfb-proper-serre-heart-qbar` to aY and p. Its heart hypotheses imply the
proved source theorem `ProperLowerStarHeartHypotheses.preservesColimitsOfShape`:
bounded heart devissage and the uniform unbounded truncation window establish
coproduct continuity on the condensed hull. Compose with the lifted encoding.
Whisker the specified derived direct-image square by the source-hull inclusion.
It identifies this composite with the native restricted proper image followed
by the target derived encoding. The latter is an equivalence and reflects
colimits, so the original native functor preserves the coproduct. The argument
includes the empty family and imposes no absolute separatedness. -/
theorem nativeAdicProper_preservesCoproducts
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] (hl : ringChar k ≠ l)
    {Z Y : Scheme.{u}} (aY : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY] [IsNoetherian Y]
    (p : Z ⟶ Y) [IsProper p] (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I)
      ((DerivedCategory.boundedAdicConstructible l Z).localizingClosure.ι ⋙
        (adicLowerStar l p).rightDerivedFunctor) := by
  let : Fact (ringChar k ≠ l) := ⟨hl⟩
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian Z := ⟨⟩
  let P := DerivedCategory.boundedAdicConstructible l Z
  let Q := boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) Z)
  let E := NativeEncoding.derivedEncoding l Z
  have hE : ∀ K, P.localizingClosure K → Q.localizingClosure (E.obj K) :=
    ObjectProperty.localizingClosure_le_inverseImage P Q fun K hK ↦
      Q.le_localizingClosure _ (NativeEncoding.encoding_boundedConstructible l Z K hK)
  let EL := P.localizingClosure.liftFullSubcategory Q.localizingClosure E hE
  have : PreservesColimitsOfShape (Discrete I) EL := by
    have : PreservesColimitsOfShape (Discrete I) (EL ⋙ Q.localizingClosure.ι) :=
      preservesColimitsOfShape_of_natIso
        (P.localizingClosure.liftFullSubcategoryCompιIso Q.localizingClosure E hE).symm
    exact preservesColimitsOfShape_of_reflects_of_preserves EL Q.localizingClosure.ι
  have : PreservesColimitsOfShape (Discrete I)
      (Q.localizingClosure.ι ⋙ CondensedRing.moduleObjectDerivedPushforward
        (Profinite.padicAlgClRingObj l) p) :=
    CondensedRing.ProperLowerStarHeartHypotheses.preservesColimitsOfShape
      (CondensedRing.properLowerStarHeartHypotheses_padicAlgClRingObj l aY p) I
  have : PreservesColimitsOfShape (Discrete I)
      (P.localizingClosure.ι ⋙ E ⋙ CondensedRing.moduleObjectDerivedPushforward
        (Profinite.padicAlgClRingObj l) p) :=
    inferInstanceAs (PreservesColimitsOfShape (Discrete I)
      (EL ⋙ Q.localizingClosure.ι ⋙ CondensedRing.moduleObjectDerivedPushforward
        (Profinite.padicAlgClRingObj l) p))
  have : PreservesColimitsOfShape (Discrete I)
      ((P.localizingClosure.ι ⋙ (adicLowerStar l p).rightDerivedFunctor) ⋙
        NativeEncoding.derivedEncoding l Y) :=
    preservesColimitsOfShape_of_natIso
      (Functor.isoWhiskerLeft P.localizingClosure.ι
        (NativeEncoding.derivedPushComparison l p)).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves _
    (NativeEncoding.derivedEncoding l Y)

end AlgebraicGeometry.ProEtale
