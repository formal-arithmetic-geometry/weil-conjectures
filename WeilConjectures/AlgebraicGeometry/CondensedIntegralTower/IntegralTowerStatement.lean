/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.CondensedNormalizedTowers
/-! # Reduction, completion unit, and the normalized equivalence
Source: sk-lem-sp-tower, both paragraphs (blueprint: sk-lem-sp-tower).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedIntegralTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- Reduction restricted to the full constructible subcategory, once closure is proved.
Source: sk-lem-sp-tower, equivalence clause (blueprint: sk-lem-sp-tower). -/
def boundedReduction (D : Model l E T)
    (h : ∀ K : Dbc l E T, Normalized l E T D (D.red.obj K.obj)) :
    Dbc l E T ⥤ NormalizedTowers l E T D :=
  ObjectProperty.lift _ ((constantModelBoundedConstructible
    (DerivedNakayama.integerRing l E) T).ι ⋙ D.red) h

/-- Total inverse limit restricted to normalized constructible towers, once closure is proved.
Source: sk-lem-sp-tower, equivalence clause (blueprint: sk-lem-sp-tower). -/
def boundedLimit (D : Model l E T)
    (h : ∀ C : NormalizedTowers l E T D,
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) T
        (D.rlim.obj C.obj)) : NormalizedTowers l E T D ⥤ Dbc l E T :=
  ObjectProperty.lift _ ((Normalized l E T D).ι ⋙ D.rlim) h

set_option maxHeartbeats 1600000 in
-- Checking these dependent construction coordinates needs the larger kernel budget.
/-- The same reduction/limit adjunction restricts to the equivalence; both maps are
literally the ambient unit and counit. Source: sk-lem-sp-tower, second paragraph
(blueprint: sk-lem-sp-tower). -/
structure BoundedEquivalence (D : Model l E T) (adj : D.red ⊣ D.rlim) where
  redClosed : ∀ K : Dbc l E T, Normalized l E T D (D.red.obj K.obj)
  limitClosed : ∀ C : NormalizedTowers l E T D,
    constantModelBoundedConstructible (DerivedNakayama.integerRing l E) T (D.rlim.obj C.obj)
  adjunction : boundedReduction l E T D redClosed ⊣ boundedLimit l E T D limitClosed
  unit : ∀ K : Dbc l E T, (adjunction.unit.app K).hom = adj.unit.app K.obj
  counit : ∀ C : NormalizedTowers l E T D,
    (adjunction.counit.app C).hom = adj.counit.app C.obj
  unitIso : IsIso adjunction.unit
  counitIso : IsIso adjunction.counit

/-- The unit is the actual derived-completion map, in the Roos coordinates of every
K-flat representative. Using the cofinal ell-power tower gives the same canonical map.
Source: sk-lem-sp-tower, first paragraph (blueprint: sk-lem-sp-tower). -/
def CompletionUnit (D : Model l E T) (adj : D.red ⊣ D.rlim) : Prop :=
  ∀ (K : Integral l E T) (P : CochainComplex (AdicCompletion.Modules l E T) ℤ)
    (e : DerivedCategory.Q.obj P ≅ K),
    (HomologicalComplex.quasiIso (AdicCompletion.Modules l E T) (.up ℤ)).kFlat P →
      ∃ c : D.rlim.obj (D.red.obj K) ≅
      DerivedCategory.Q.obj (AdicCompletion.roos l E T P),
      adj.unit.app K ≫ c.hom = AdicCompletion.completionMap l E T K P e

/-- Canonical reduction is left adjoint to total derived inverse limit, with its unit
identified with derived completion, and over a Noetherian scheme this same adjunction
restricts to the normalized constructible equivalence.

Source: latest blueprint, sk-lem-sp-tower, both paragraphs (blueprint: sk-lem-sp-tower).
Proof: the change of rings h from towers to constant inverse systems and the topos
morphism p with p_* = inverse limit give Lh^* p^{-1} ⊣ Rp_* h_* (Stacks 06YV, 07A6).
In strict-system coordinates this is the specified ordinary tensor/limit adjunction,
derived using K-flat and K-injective representatives. Its unit is the augmented Roos
completion map; cofinal ell- and uniformizer-power ideals identify their completion maps.
By sk-prop-sp-integral-towers(1), red sends Dbc into normalized constructible towers.
The integral criterion gives derived completeness, so the restricted unit is invertible.
Conversely for a normalized tower C, reduction of Rlim C modulo ell^m differs from C_m
by Rlim of (C_m[1])_n with transition multiplication by ell. This limit vanishes since
ell^m kills C_m. Thus the limit is derived complete and its first reduction constructible.
Repleteness (sk-prop-pe-replete, Stacks 0940) supplies boundedness, and
sk-prop-sp-integral-towers(2) gives Dbc. The counit is at level m this same reduction
isomorphism; evaluations detect isomorphisms, so the whole counit is invertible.
The full inclusions retain these exact unit and counit maps. -/
theorem sp_tower_statement :
    ∃ D : Model l E T, ∃ adj : D.red ⊣ D.rlim,
      CompletionUnit l E T D adj ∧
      (IsNoetherian T → Nonempty (BoundedEquivalence l E T D adj)) := by
  sorry

/-- Canonical reduction/total-limit coordinates, determined up to the canonical derived
isomorphisms by the ordinary tensor/limit construction and universal derived functors.
Source: sk-lem-sp-tower (blueprint: sk-lem-sp-tower). -/
def model : Model l E T := (sp_tower_statement l E T).choose

/-- The adjunction supplied by sk-lem-sp-tower in the chosen canonical coordinates.
Source: sk-lem-sp-tower (blueprint: sk-lem-sp-tower). -/
def adjunction : (model l E T).red ⊣ (model l E T).rlim :=
  (sp_tower_statement l E T).choose_spec.choose

end AlgebraicGeometry.ProEtale.CondensedIntegralTower
