/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import Sheaf.Paper.BoundedConstructibleHomFiniteness
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!
# Derived internal Hom restricted under its preservation hypothesis

Source: Weil conjectures blueprint, main-20261015, `sec-six-functors-basics`,
`sk-def-sfb-dc-restricted-functors/def-sfb-dc-hom.md`
(blueprint: def-sfb-dc-hom).

The coefficient ring is arbitrary; preservation is an explicit hypothesis. The existing
`boundedConstructibleHom` only accepts the specific ell-adic finiteness coefficients.
The ambient derived internal Hom and bounded constructibility are reused unchanged.
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Restrict the ambient derived internal Hom in both variables, assuming that its values on
bounded constructible objects are bounded constructible. The object over `(K,L)` is the ambient
`derivedHom` value equipped with the supplied proof, and every morphism is the ambient map.

Source: blueprint `sk-def-sfb-dc-restricted-functors/def-sfb-dc-hom.md`, restriction sentence
(blueprint: def-sfb-dc-hom).

Construction: (1) the hypothesis supplies the bounded constructibility of each value;
`lem-sfb-dc-hom-preserves` supplies it in the three ell-adic coefficient cases. (2) Uncurry the
ambient bifunctor after both full-subcategory inclusions, lift its values by `ObjectProperty.lift`,
and curry. Identities and composition are inherited from the ambient bifunctor. No new
internal Hom or constructibility predicate is introduced. -/
noncomputable def boundedConstructibleHomOfPreserves
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom]
    (h : ∀ K L : BoundedConstructible (condensedRingObj Λ X.left),
      boundedConstructible (condensedRingObj Λ X.left)
        (((derivedHom Λ X.left).obj (op K.obj)).obj L.obj)) :
    (BoundedConstructible (condensedRingObj Λ X.left))ᵒᵖ ⥤
      BoundedConstructible (condensedRingObj Λ X.left) ⥤
        BoundedConstructible (condensedRingObj Λ X.left) :=
  Functor.curry.obj ((boundedConstructible _).lift
    (((boundedConstructible _).ι.op.prod (boundedConstructible _).ι) ⋙
      Functor.uncurry.obj (derivedHom Λ X.left))
    (fun KL ↦ h KL.1.unop KL.2))

/-- For fixed `K`, the restricted Hom commutes with the full-subcategory inclusions. Both
components of this comparison are ambient identity maps.

Source: blueprint `sk-def-sfb-dc-restricted-functors/def-sfb-dc-hom.md`, final sentence
(blueprint: def-sfb-dc-hom).

Construction: (3) composing `ObjectProperty.lift` with inclusion recovers the ambient
bifunctor definitionally. The canonical currying comparison and the inverse currying unit
identify its fixed-first-variable functor with the ambient Hom after inclusion. These
canonical comparisons have identity components, so does their composite. Their naturality
is precisely composition with identities on the ambient map `H(1_K,v)`. -/
noncomputable def boundedConstructibleHomOfPreservesObjCompatibility
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom]
    (h : ∀ K L : BoundedConstructible (condensedRingObj Λ X.left),
      boundedConstructible (condensedRingObj Λ X.left)
        (((derivedHom Λ X.left).obj (op K.obj)).obj L.obj))
    (K : BoundedConstructible (condensedRingObj Λ X.left)) :
    (boundedConstructibleHomOfPreserves Λ ℓ X h).obj (op K) ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (derivedHom Λ X.left).obj (op K.obj) :=
  (Functor.curryObjProdComp (boundedConstructible _).ι.op (boundedConstructible _).ι
    (Functor.uncurry.obj (derivedHom Λ X.left))).app (op K) ≪≫
    Functor.isoWhiskerLeft (boundedConstructible _).ι
      (((Functor.currying.unitIso.app (derivedHom Λ X.left)).symm).app (op K.obj))

end AlgebraicGeometry.ProEtale.CondensedRing
