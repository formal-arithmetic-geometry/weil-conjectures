/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.Algebra.Category.Ring.Sheaf.PrincipalPowerQuotients
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Successive quotient sequences on flat-term complexes

Source: blueprint main-20261015, integral criterion reductions, second paragraph;
Stacks Project, Modules on Sites, Tags 03DA, 03CY, 03EI, 03EK and 03ER.
(blueprint: lem-pe-successive-quotient-flat-complex-sequence)

The witness structures package the precise coefficient maps, the actual sheafified
scalar-extension objects and differentials, and both degreewise short exactness assertions.
They introduce no derived functor, points, or sectionwise flatness assumption.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v r
open CategoryTheory
open scoped ChangeOfRings

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

/-- A presentation of the termwise tensor complex by its actual scalar-extension objects
and the maps `1 ⊗ d`. Both equalities concern the existing change-of-rings construction.
Source: Stacks 03EK, blueprint integral criterion reductions, second paragraph
(blueprint: lem-pe-successive-quotient-flat-complex-sequence). -/
structure PrincipalQuotientTensorComplex {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S)
    (P : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) ℤ) where
  /-- The unbounded scalar-extension cochain complex. -/
  complex : CochainComplex (ringedSiteModules.{r}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) ℤ
  /-- Its degree-i object is the sheafification of S(U) tensor P^i(U). -/
  obj_eq : ∀ i : ℤ, complex.X i = changeOfRings φ (P.X i)
  /-- The differential is scalar extension of the original differential. -/
  differential : ∀ i j : ℤ,
    complex.d i j ≫ eqToHom (obj_eq j) =
      eqToHom (obj_eq i) ≫ changeOfRingsHom φ (P.X i) (P.d i j)

/-- The image of a local pure tensor in the specified term of a tensor complex.
This is the actual sheafification unit, transported only by the specified object equality.
Source: Stacks 03EK (blueprint: lem-pe-successive-quotient-flat-complex-sequence). -/
def principalQuotientTensorSection {B S : Sheaf J CommRingCat.{r}} {φ : B ⟶ S}
    {P : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) ℤ}
    (K : PrincipalQuotientTensorComplex φ P) (i : ℤ) (U : Cᵒᵖ)
    (s : S.obj.obj U) (p : (P.X i).val.obj U) : (K.complex.X i).val.obj U :=
  (eqToHom (K.obj_eq i).symm).val.app U
    ((toSheafify J (changeOfRingsPresheaf φ (P.X i)).presheaf).app U
      (s ⊗ₜ[B.obj.obj U, (φ.hom.app U).hom] p))

/-- Termwise scalar restriction, with unchanged underlying differential.
Source: Stacks 03DA, 03EK
(blueprint: lem-pe-successive-quotient-flat-complex-sequence). -/
def principalQuotientRestrictComplex {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S)
    (K : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) ℤ) :
    CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ :=
  ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map q)).mapHomologicalComplex
    (.up ℤ)).obj K

/-- All conclusions about tensoring the given coefficient maps with a fixed complex.
The formulas on arbitrary local pure tensors identify the maps with `a ⊗ 1` and `b ⊗ 1`.
Source: Stacks 03DA, 03EK, 03ER, blueprint integral criterion reductions, second paragraph
(blueprint: lem-pe-successive-quotient-flat-complex-sequence). -/
structure SuccessiveQuotientFlatTensorSequence
    {B SPrev SN SOne : Sheaf J CommRingCat.{r}}
    (πPrev : B ⟶ SPrev) (πN : B ⟶ SN) (πOne : B ⟶ SOne)
    (qPrev : SN ⟶ SPrev) (qOne : SN ⟶ SOne)
    (a : (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map qPrev)).obj
      (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj SPrev)) ⟶
        unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj SN))
    (b : unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj SN) ⟶
      (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map qOne)).obj
        (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj SOne)))
    (P : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) ℤ) where
  /-- The preceding quotient tensor complex. -/
  prev : PrincipalQuotientTensorComplex πPrev P
  /-- The middle quotient tensor complex. -/
  middle : PrincipalQuotientTensorComplex πN P
  /-- The first quotient tensor complex. -/
  one : PrincipalQuotientTensorComplex πOne P
  /-- Multiplication on the coefficient factor, linear over SN. -/
  α : principalQuotientRestrictComplex qPrev prev.complex ⟶ middle.complex
  /-- Quotient on the coefficient factor, linear over SN. -/
  β : middle.complex ⟶ principalQuotientRestrictComplex qOne one.complex
  /-- The composite vanishes in every degree. -/
  zero : ∀ i : ℤ, α.f i ≫ β.f i = 0
  /-- Short exactness in every degree over SN. -/
  shortExact : ∀ i : ℤ, (ShortComplex.mk (α.f i) (β.f i) (zero i)).ShortExact
  /-- Short exactness in every degree after scalar restriction to B. -/
  restrictedShortExact : ∀ i : ℤ,
    ((ShortComplex.mk (α.f i) (β.f i) (zero i)).map
      (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map πN))).ShortExact
  /-- The tensor of a with the identity, normalized on all local pure tensors. -/
  alpha_formula : ∀ (i : ℤ) (U : Cᵒᵖ) (s : SPrev.obj.obj U) (p : (P.X i).val.obj U),
    (α.f i).val.app U (principalQuotientTensorSection prev i U s p) =
      principalQuotientTensorSection middle i U (a.val.app U s) p
  /-- The tensor of b with the identity, normalized on all local pure tensors. -/
  beta_formula : ∀ (i : ℤ) (U : Cᵒᵖ) (s : SN.obj.obj U) (p : (P.X i).val.obj U),
    (β.f i).val.app U (principalQuotientTensorSection middle i U s p) =
      principalQuotientTensorSection one i U (b.val.app U s) p

/-- The quotient maps, the short exact coefficient sequence, and its flat-term tensor
sequences. All the maps are fixed by local formulas, rather than arbitrary choices.
Source: Stacks 03DA, 03EK, 03ER, blueprint integral criterion reductions, second paragraph
(blueprint: lem-pe-successive-quotient-flat-complex-sequence). -/
structure SuccessiveQuotientFlatComplexSequence
    {B SPrev SN SOne : Sheaf J CommRingCat.{r}}
    (t : (B.obj ⋙ CategoryTheory.forget CommRingCat.{r}).sections)
    (πPrev : B ⟶ SPrev) (πN : B ⟶ SN) (πOne : B ⟶ SOne) where
  /-- The quotient ring map to the preceding power. -/
  qPrev : SN ⟶ SPrev
  /-- The quotient ring map to the first power. -/
  qOne : SN ⟶ SOne
  /-- Normalization of the preceding quotient. -/
  qPrev_projection : πN ≫ qPrev = πPrev
  /-- Normalization of the first quotient. -/
  qOne_projection : πN ≫ qOne = πOne
  /-- The coefficient multiplication map. -/
  a : (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map qPrev)).obj
      (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj SPrev)) ⟶
        unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj SN)
  /-- The coefficient quotient map. -/
  b : unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj SN) ⟶
      (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map qOne)).obj
        (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj SOne))
  /-- The formula [c] maps to [tc]. -/
  a_formula : ∀ (U : Cᵒᵖ) (c : B.obj.obj U),
    a.val.app U (πPrev.hom.app U c) =
      πN.hom.app U ((@id (B.obj.obj U) (t.val U)) * c)
  /-- The formula [c] maps to [c]. -/
  b_formula : ∀ (U : Cᵒᵖ) (c : B.obj.obj U),
    b.val.app U (πN.hom.app U c) = πOne.hom.app U c
  /-- The coefficient composite vanishes. -/
  zero : a ≫ b = 0
  /-- Short exactness over the middle quotient ring. -/
  shortExact : (ShortComplex.mk a b zero).ShortExact
  /-- Short exactness after restriction along B to the middle quotient ring. -/
  restrictedShortExact : ((ShortComplex.mk a b zero).map
    (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map πN))).ShortExact
  /-- Tensoring with any flat-term unbounded complex gives the specified sequence. -/
  tensors : ∀ (P : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) ℤ),
    (∀ i : ℤ, IsFlatOnSite (P.X i)) →
      Nonempty (SuccessiveQuotientFlatTensorSequence πPrev πN πOne qPrev qOne a b P)

variable [HasSheafify J CommRingCat.{r}]

/-- The successive coefficient sequence remains degreewise short exact on every
unbounded flat-term complex. No sectionwise flatness or K-flatness is assumed.

Source: blueprint main-20261015, integral criterion reductions, second paragraph;
Stacks 03CY, 03EI, 03DA, 03EK, 03ER and Sites 00YR.
(blueprint: lem-pe-successive-quotient-flat-complex-sequence).

Proof:
1. The ideal inclusions (t^n) ⊆ (t^(n-1)) and (t^n) ⊆ (t) give quotient
presheaf ring maps. Sheafify to obtain qPrev and qOne. Their projection equations
hold before sheafification, hence also afterwards (def-pe-principal-power-ring-quotients,
def-weil-pbc-sheafification).
2. On sections define a([c]) = [tc] and b([c]) = [c]. The first is well-defined
because t times (t^(n-1)) lies in (t^n). Both are additive, linear over the middle
quotient ring, and commute with restrictions (def-pc-sheaf-restrict-scalars,
def-weil-presheaf-modules-sheafification).
3. Injectivity of multiplication by t gives cancellation: tc = t^n d implies
c = t^(n-1)d. Thus a is injective. The second map is surjective, with kernel
precisely the multiples of t, which are the image of a. This proves the sectionwise
presheaf short exact sequence (def-weil-sheaf-of-modules-category).
4. Module sheafification extends these maps and actions. The underlying set
sheafification comparison identifies the outer terms with the scalar restrictions
of the quotient ring sheaves, preserving both local formulas
(lem-pc-sites-module-sheafification-interface, lem-pc-sites-sheafification-underlying-sets).
5. Exactness of module sheafification gives short exactness over B
(lem-weil-pbc-ringed-site-module-sheafification-exact).
6. Restriction changes only the scalar action. Kernels and sheafified cokernels
have unchanged underlying abelian sheaves. It therefore preserves and reflects
short exactness, proving short exactness over R_n as well
(def-pc-sheaf-restrict-scalars, def-weil-sheaf-of-modules-category,
def-weil-presheaf-modules-sheafification).
7. Sheafify the balanced maps a tensor 1 and b tensor 1, with the first-factor
quotient actions. Their SN-linearity follows on pure tensors. They obey precisely
the displayed local formulas (def-pur-sheaf-tensor-product,
lem-pc-sites-module-sheafification-interface, def-pc-sheaf-restrict-scalars).
8. Put d = 1 tensor d_P. Its square vanishes, and the pure-tensor calculations
show that both tensor maps commute with d. Sheafification preserves those equations
(def-weil-abstract-derived-category, def-pur-sheaf-tensor-product,
def-weil-presheaf-modules-sheafification).
9. In each degree, apply the exact tensor functor defining IsFlatOnSite to the
short exact B-module sequence. Step 6 reflects its short exactness to R_n.
This is degreewise and uses no bounds, points, or sectionwise flatness
(def-pc-flat-sheaf-modules). -/
theorem nonempty_successiveQuotientFlatComplexSequence [EssentiallySmall.{r} C]
    (B : Sheaf J CommRingCat.{r})
    (t : (B.obj ⋙ CategoryTheory.forget CommRingCat.{r}).sections)
    (hregular : ∀ U : Cᵒᵖ,
      Function.Injective (fun c : B.obj.obj U ↦ (@id (B.obj.obj U) (t.val U)) * c))
    (n : ℕ) (hn : 1 < n) :
    Nonempty (SuccessiveQuotientFlatComplexSequence t
      (principalPowerRingProjection B t (n - 1))
      (principalPowerRingProjection B t n) (principalPowerRingProjection B t 1)) := sorry

end SheafOfModules
