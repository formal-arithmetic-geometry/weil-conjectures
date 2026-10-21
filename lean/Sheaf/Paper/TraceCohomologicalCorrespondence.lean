/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.Paper.TraceExceptionalAdmissibility
public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Finite-coefficient cohomological correspondences

Source: Weil conjectures blueprint, main-20261015,
sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/def-trf-correspondence.md
(blueprint: def-trf-correspondence).

We use the canonical fixed-scalar realization of the recorded intrinsic finite-Tor
category, exactly as in exceptional admissibility. The index `n` denotes the positive
coefficient stage `A_{E,n+1}`. The scheme `X` is any separated finite-type `k`-scheme;
no descent of `X` to the finite field is required.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (F : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)

/-- The canonical compactification instance for a leg between separated finite-type
`k`-schemes. The leg's properties follow from its source's structure map, using its
commutation over `k`; compactifiability is the recorded theorem, not additional data.
Source: blueprint def-trf-correspondence, the two legs
(blueprint: def-trf-correspondence). -/
abbrev trfCorrespondenceCompactifiable (C X : Over (Spec (.of F.k)))
    [IsSeparated C.hom] [LocallyOfFiniteType C.hom] [QuasiCompact C.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : C ⟶ X) : HasCompactification f.left := by
  let : IsSeparated (f.left ≫ X.hom) := f.w.symm ▸ inferInstance
  let : LocallyOfFiniteType (f.left ≫ X.hom) := f.w.symm ▸ inferInstance
  let : QuasiCompact (f.left ≫ X.hom) := f.w.symm ▸ inferInstance
  let : IsSeparated f.left := IsSeparated.of_comp f.left X.hom
  let : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left X.hom
  let : QuasiCompact f.left := QuasiCompact.of_comp f.left X.hom
  exact @hasCompactification_of_finiteType_over_field F.k inferInstance C.left X.left
    ⟨C.hom⟩ ⟨X.hom⟩ (inferInstance : LocallyOfFiniteType C.hom)
    (inferInstance : QuasiCompact C.hom) (inferInstance : LocallyOfFiniteType X.hom)
    (inferInstance : QuasiCompact X.hom)
    f.left inferInstance inferInstance inferInstance

/-- The specified constructible exceptional inverse image of a correspondence leg,
using the very same fixed-scalar functor as `TrfExceptionalStage`.
Source: blueprint def-trf-correspondence, `Rc₁^!`
(blueprint: def-trf-correspondence). -/
def trfCorrespondenceExceptional (C X : Over (Spec (.of F.k)))
    [IsSeparated C.hom] [LocallyOfFiniteType C.hom] [QuasiCompact C.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : C ⟶ X) :=
  letI := trfCorrespondenceCompactifiable F C X f
  trfExceptional l E n f.left

/-- Exceptional admissibility of a leg, with its separated finite-type properties
inferred from the stated geometry rather than supplied as extra hypotheses.
Source: blueprint def-trf-correspondence, admissibility sentence
(blueprint: def-trf-correspondence). -/
def trfCorrespondenceLegAdmissible (hl : l ≠ F.p) (C X : Over (Spec (.of F.k)))
    [IsSeparated C.hom] [LocallyOfFiniteType C.hom] [QuasiCompact C.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : C ⟶ X) : Prop := by
  letI : IsSeparated (f.left ≫ X.hom) := f.w.symm ▸ inferInstance
  letI : LocallyOfFiniteType (f.left ≫ X.hom) := f.w.symm ▸ inferInstance
  letI : QuasiCompact (f.left ≫ X.hom) := f.w.symm ▸ inferInstance
  letI : IsSeparated f.left := IsSeparated.of_comp f.left X.hom
  letI : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left X.hom
  letI : QuasiCompact f.left := QuasiCompact.of_comp f.left X.hom
  exact IsExceptionallyAdmissibleAt l E n F hl C X f

/-- A cohomological endocorrespondence of `K` on a separated finite-type `k`-scheme.
Its two `k`-morphisms are equivalent to a map `C → X ×_k X`. The coefficient map
has ordinary pullback on leg 2 and the specified exceptional inverse image on leg 1.
The full subcategory uses the dependency's intrinsic finite-Tor predicate through
its canonical coefficient realization. No admissibility or invertibility is assumed.
Source: blueprint main-20261015, def-trf-correspondence, first two paragraphs
(blueprint: def-trf-correspondence). -/
structure TrfCohomologicalCorrespondence (hl : l ≠ F.p)
    (X : Over (Spec (.of F.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (K : (trfFiniteTorFixed l E n X.left).FullSubcategory) where
  C : Over (Spec (.of F.k))
  [separated : IsSeparated C.hom]
  [finiteType : LocallyOfFiniteType C.hom]
  [quasiCompact : QuasiCompact C.hom]
  c₁ : C ⟶ X
  c₂ : C ⟶ X
  u : ((ProEtale.upperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
      c₂.left).leftDerivedFunctor).obj K.obj ⟶
    (trfCorrespondenceExceptional F l E n C X c₁).obj K.obj

attribute [instance] TrfCohomologicalCorrespondence.separated
  TrfCohomologicalCorrespondence.finiteType TrfCohomologicalCorrespondence.quasiCompact

namespace TrfCohomologicalCorrespondence

variable {F l E n} {hl : l ≠ F.p} {X : Over (Spec (.of F.k))}
  [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  {K : (trfFiniteTorFixed l E n X.left).FullSubcategory}

/-- The map to the fibre product with ordered projections `(c₁,c₂)`.
Source: blueprint def-trf-correspondence, the displayed map `c`
(blueprint: def-trf-correspondence). -/
def toProduct (c : TrfCohomologicalCorrespondence F l E n hl X K) :
    c.C.left ⟶ pullback X.hom X.hom :=
  pullback.lift c.c₁.left c.c₂.left (c.c₁.w.trans c.c₂.w.symm)

/-- Admissibility at the fixed coefficient stage: the exceptional leg and its
base changes in the separated finite-type `k`-scheme setting are exceptionally
admissible. An arbitrary Cartesian presentation is accepted, so no particular
choice of a fibre product or of its identification is built into the predicate.
Source: blueprint def-trf-correspondence, final sentence
(blueprint: def-trf-correspondence). -/
def IsAdmissible (c : TrfCohomologicalCorrespondence F l E n hl X K) : Prop :=
  trfCorrespondenceLegAdmissible F l E n hl c.C X c.c₁ ∧
    ∀ (C' X' : Over (Spec (.of F.k)))
      [IsSeparated C'.hom] [LocallyOfFiniteType C'.hom] [QuasiCompact C'.hom]
      [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
      (g' : C' ⟶ c.C) (f' : C' ⟶ X') (g : X' ⟶ X),
      IsPullback g'.left f'.left c.c₁.left g.left →
        trfCorrespondenceLegAdmissible F l E n hl C' X' f'

end TrfCohomologicalCorrespondence
end WeilConjectures
