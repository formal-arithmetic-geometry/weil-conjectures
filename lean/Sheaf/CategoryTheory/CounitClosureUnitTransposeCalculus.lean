/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q125
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Counit-normalized transpose and closure comparison unit

Source: blueprint main-20261015, lem-weil-finite-duality-site-comparison.proof.md,
second paragraph; categorical calculation using Stacks Project, Tags 0037 and 0B65
(blueprint: lem-sf-counit-closure-unit-transpose-calculus).

The data structures below only bundle the hypotheses of the node. They impose no
adjunction on the comparison functor and no full faithfulness on ambient objects.
The three statements give the calculus and its naturality in both variables.
-/

@[expose] public section

set_option autoImplicit false

universe uA uB uP uQ vA vB vP vQ

namespace CategoryTheory

/-- The functors, full subcategories and natural transformations in the categorical
calculation of the second paragraph of the blueprint site-comparison proof, using
Stacks Tags 0037 and 0B65. This record bundles exactly the hypotheses independent of M.
(blueprint: lem-sf-counit-closure-unit-transpose-calculus) -/
structure CounitClosureTransposeData
    (A : Type uA) (B : Type uB) (P : Type uP) (Q : Type uQ)
    [Category.{vA} A] [Category.{vB} B] [Category.{vP} P] [Category.{vQ} Q] where
  Fe : A ⥤ B
  Je : B ⥤ A
  Fp : P ⥤ Q
  Jp : Q ⥤ P
  CS : A ⥤ P
  CT : B ⥤ Q
  adjE : Fe ⊣ Je
  adjP : Fp ⊣ Jp
  A₀ : ObjectProperty A
  B₀ : ObjectProperty B
  Q₀ : ObjectProperty Q
  hCT : ∀ X : B₀.FullSubcategory, Q₀ (CT.obj X.obj)
  hFe : ∀ L : A₀.FullSubcategory, B₀ (Fe.obj L.obj)
  hom_bijective : ∀ X Y : B₀.FullSubcategory,
    Function.Bijective (CT.map : (X.obj ⟶ Y.obj) → (CT.obj X.obj ⟶ CT.obj Y.obj))
  U : Q₀.FullSubcategory ⥤ B
  eta : B₀.ι ⟶ Q₀.lift (B₀.ι ⋙ CT) hCT ⋙ U
  delta : A₀.ι ⋙ Fe ⋙ CT ≅ A₀.ι ⋙ CS ⋙ Fp
  Ee : A ⥤ B
  Ep : P ⥤ Q
  hEe : ∀ L : A₀.FullSubcategory, B₀ (Ee.obj L.obj)
  qe : Fe ≅ Ee
  qp : Fp ≅ Ep
  closure : A₀.ι ⋙ Ee ⋙ CT ≅ A₀.ι ⋙ CS ⋙ Ep
  compatibility : ∀ L : A₀.FullSubcategory,
    delta.hom.app L ≫ qp.hom.app (CS.obj L.obj) =
      CT.map (qe.hom.app L.obj) ≫ closure.hom.app L

namespace CounitClosureTransposeData

variable {A : Type uA} {B : Type uB} {P : Type uP} {Q : Type uQ}
  [Category.{vA} A] [Category.{vB} B] [Category.{vP} P] [Category.{vQ} Q]
  (D : CounitClosureTransposeData A B P Q)

/-- Restriction of C_T to the specified full subcategories, using the given membership proof.
Source: blueprint site-comparison proof, second paragraph; Stacks Tag 0037 calculation.
(blueprint: lem-sf-counit-closure-unit-transpose-calculus) -/
abbrev comparison : D.B₀.FullSubcategory ⥤ D.Q₀.FullSubcategory :=
  D.Q₀.lift (D.B₀.ι ⋙ D.CT) D.hCT

/-- Regard a morphism between comparison objects as a morphism of the full subcategory Q_0.
Source: blueprint site-comparison proof, second paragraph; fullness in the Tag 0037 calculation.
(blueprint: lem-sf-counit-closure-unit-transpose-calculus) -/
def comparisonHom (X Y : D.B₀.FullSubcategory) (f : D.CT.obj X.obj ⟶ D.CT.obj Y.obj) :
    D.comparison.obj X ⟶ D.comparison.obj Y :=
  ObjectProperty.homMk f

/-- The arrow U(z B_L) eta_(E_e L), with U applied only to morphisms of Q_0.
Source: blueprint site-comparison proof, second paragraph; comparison-unit calculation.
(blueprint: lem-sf-counit-closure-unit-transpose-calculus) -/
def closureInput (L : D.A₀.FullSubcategory) (M : D.B₀.FullSubcategory)
    (z : D.Ep.obj (D.CS.obj L.obj) ⟶ D.CT.obj M.obj) :
    D.Ee.obj L.obj ⟶ D.U.obj (D.comparison.obj M) :=
  D.eta.app ⟨D.Ee.obj L.obj, D.hEe L⟩ ≫
    D.U.map (D.comparisonHom ⟨D.Ee.obj L.obj, D.hEe L⟩ M (D.closure.hom.app L ≫ z))

/-- The specified closure transpose Phi, using the adjunction transported along q_e.
Source: blueprint site-comparison proof, second paragraph; Stacks Tags 0037 and 0B65.
(blueprint: lem-sf-counit-closure-unit-transpose-calculus) -/
def phi (L : D.A₀.FullSubcategory) (M : D.B₀.FullSubcategory)
    (z : D.Ep.obj (D.CS.obj L.obj) ⟶ D.CT.obj M.obj) :
    D.CS.obj L.obj ⟶ D.CS.obj (D.Je.obj (D.U.obj (D.comparison.obj M))) :=
  D.CS.map ((D.adjE.ofNatIsoLeft D.qe).homEquiv L.obj _ (D.closureInput L M z))

/-- The comparison-unit arrow rho = C_S J_e(eta_M).
Source: blueprint site-comparison proof, second paragraph; comparison-unit calculation.
(blueprint: lem-sf-counit-closure-unit-transpose-calculus) -/
def rho (M : D.B₀.FullSubcategory) :
    D.CS.obj (D.Je.obj M.obj) ⟶ D.CS.obj (D.Je.obj (D.U.obj (D.comparison.obj M))) :=
  D.CS.map (D.Je.map (D.eta.app M))

/-- An allowed choice of M, H, invertible unit and counit-normalized gamma.
Source: blueprint site-comparison proof, second paragraph; ambient Tag 0037 counit calculation.
There is no condition that U C_T M belong to B_0.
(blueprint: lem-sf-counit-closure-unit-transpose-calculus) -/
structure Target where
  M : D.B₀.FullSubcategory
  hH : D.A₀ (D.Je.obj M.obj)
  unitIso : IsIso (D.eta.app M)
  gamma : D.CS.obj (D.Je.obj M.obj) ≅ D.Jp.obj (D.CT.obj M.obj)
  counit : D.delta.hom.app ⟨D.Je.obj M.obj, hH⟩ ≫
    D.Fp.map gamma.hom ≫ D.adjP.counit.app (D.CT.obj M.obj) =
      D.CT.map (D.adjE.counit.app M.obj)

private theorem closureInput_left (L' L : D.A₀.FullSubcategory) (l : L' ⟶ L)
    (M : D.B₀.FullSubcategory) (z : D.Ep.obj (D.CS.obj L.obj) ⟶ D.CT.obj M.obj) :
    D.closureInput L' M (D.Ep.map (D.CS.map l.hom) ≫ z) =
      D.Ee.map l.hom ≫ D.closureInput L M z := by
  have hn := D.closure.hom.naturality l
  dsimp at hn
  have hc : D.comparisonHom ⟨_, D.hEe L'⟩ M
      (D.closure.hom.app L' ≫ (D.Ep.map (D.CS.map l.hom) ≫ z)) =
      D.comparison.map (ObjectProperty.homMk (D.Ee.map l.hom) :
        (⟨_, D.hEe L'⟩ : D.B₀.FullSubcategory) ⟶ ⟨_, D.hEe L⟩) ≫
        D.comparisonHom ⟨_, D.hEe L⟩ M (D.closure.hom.app L ≫ z) := by
    apply ObjectProperty.hom_ext
    dsimp [comparisonHom]
    rw [← Category.assoc, ← hn, Category.assoc]
  dsimp only [closureInput]
  rw [hc, D.U.map_comp, ← Category.assoc]
  have he := D.eta.naturality
    (ObjectProperty.homMk (D.Ee.map l.hom) :
      (⟨_, D.hEe L'⟩ : D.B₀.FullSubcategory) ⟶ ⟨_, D.hEe L⟩)
  change D.Ee.map l.hom ≫ D.eta.app ⟨_, D.hEe L⟩ =
    D.eta.app ⟨_, D.hEe L'⟩ ≫ D.U.map (D.comparison.map
      (ObjectProperty.homMk (D.Ee.map l.hom))) at he
  rw [← he, Category.assoc]

private theorem closureInput_right (L : D.A₀.FullSubcategory)
    (M M' : D.B₀.FullSubcategory) (m : M.obj ⟶ M'.obj)
    (z : D.Ep.obj (D.CS.obj L.obj) ⟶ D.CT.obj M.obj) :
    D.closureInput L M' (z ≫ D.CT.map m) = D.closureInput L M z ≫
      D.U.map (D.comparisonHom M M' (D.CT.map m)) := by
  have hc : D.comparisonHom ⟨_, D.hEe L⟩ M'
      (D.closure.hom.app L ≫ (z ≫ D.CT.map m)) =
      D.comparisonHom ⟨_, D.hEe L⟩ M (D.closure.hom.app L ≫ z) ≫
        D.comparisonHom M M' (D.CT.map m) := by
    apply ObjectProperty.hom_ext
    exact (Category.assoc _ _ _).symm
  dsimp only [closureInput]
  rw [hc, D.U.map_comp, Category.assoc]

/-- Unique lifting, the three intermediate identities, both transposes and invertibility of rho.
Source: blueprint site-comparison proof, second paragraph; Stacks Tags 0037 and 0B65.
(blueprint: lem-sf-counit-closure-unit-transpose-calculus)

Proof, following Steps 1--7 of the node:
1. Both F_e L and M are in B_0. The assumed Hom bijection has a unique preimage h_0
of Delta_L followed by h; only these two objects are used for full faithfulness.
2. Put g_0 = adj_e(h_0). The inverse Hom transpose writes h_0 as F_e(g_0) followed
by epsilon^e_M (lem-weil-pbc-adjunction-of-natural-bijection). Fullness of A_0
makes g_0 a morphism in the domain of Delta, since L and H both belong to A_0.
3. Apply naturality of Delta to g_0 and then the assumed counit equation. They show
that the inverse p-transpose of C_S(g_0) followed by gamma, precomposed with Delta_L,
is C_T(h_0). Cancel Delta_L and use injectivity of the inverse Hom transpose.
4. Cancel q_p and C_T(q_e) in the compatibility square to obtain B_L followed by
q_p inverse equals C_T(q_e inverse) followed by Delta_L. Compose with h and use
the lift equation. This gives B_L followed by z = C_T(a).
5. The transported Hom equivalence sends a to adj_e(q_e followed by a) = g_0
(def-weil-pbc-adjunction-conjugate). Naturality of eta at a, whose endpoints are
in B_0, gives eta_(E_e L) followed by U(z B_L) = a followed by eta_M.
6. Right-variable naturality of the transported adjunction sends a followed by
eta_M to g_0 followed by J_e(eta_M). Apply C_S to obtain Phi(z) = C_S(g_0) rho.
7. The image under C_S J_e of the inverse of eta_M is a two-sided inverse to rho,
by functoriality and the identity and composition laws (def-nagata-category).
-/
theorem calculus (T : D.Target) :
    IsIso (D.rho T.M) ∧
    (∀ (L : D.A₀.FullSubcategory)
      (h : D.Fp.obj (D.CS.obj L.obj) ⟶ D.CT.obj T.M.obj),
      ∃! h₀ : D.Fe.obj L.obj ⟶ T.M.obj, D.delta.hom.app L ≫ h = D.CT.map h₀) ∧
    (∀ (L : D.A₀.FullSubcategory)
      (h : D.Fp.obj (D.CS.obj L.obj) ⟶ D.CT.obj T.M.obj)
      (h₀ : D.Fe.obj L.obj ⟶ T.M.obj), D.delta.hom.app L ≫ h = D.CT.map h₀ →
      D.closure.hom.app L ≫ (D.qp.inv.app (D.CS.obj L.obj) ≫ h) =
          D.CT.map (D.qe.inv.app L.obj ≫ h₀) ∧
        (D.adjE.ofNatIsoLeft D.qe).homEquiv L.obj T.M.obj
            (D.qe.inv.app L.obj ≫ h₀) = D.adjE.homEquiv L.obj T.M.obj h₀ ∧
        D.closureInput L T.M (D.qp.inv.app (D.CS.obj L.obj) ≫ h) =
          (D.qe.inv.app L.obj ≫ h₀) ≫ D.eta.app T.M ∧
        D.adjP.homEquiv (D.CS.obj L.obj) (D.CT.obj T.M.obj) h =
          D.CS.map (D.adjE.homEquiv L.obj T.M.obj h₀) ≫ T.gamma.hom ∧
        D.phi L T.M (D.qp.inv.app (D.CS.obj L.obj) ≫ h) =
          D.CS.map (D.adjE.homEquiv L.obj T.M.obj h₀) ≫ D.rho T.M) := by
  have : IsIso (D.eta.app T.M) := T.unitIso
  refine ⟨by dsimp [rho]; infer_instance, ?_, ?_⟩
  · intro L h
    obtain ⟨h₀, hh₀⟩ := (D.hom_bijective ⟨_, D.hFe L⟩ T.M).2
      (D.delta.hom.app L ≫ h)
    exact ⟨h₀, hh₀.symm, fun k hk ↦
      (D.hom_bijective ⟨_, D.hFe L⟩ T.M).1 (hk.symm.trans hh₀.symm)⟩
  · intro L h h₀ hlift
    have hsquare : D.closure.hom.app L ≫ D.qp.inv.app (D.CS.obj L.obj) =
        D.CT.map (D.qe.inv.app L.obj) ≫ D.delta.hom.app L := by
      apply (cancel_mono (D.qp.hom.app (D.CS.obj L.obj))).1
      simp only [Category.assoc, Iso.inv_hom_id_app]
      rw [D.compatibility L, ← Category.assoc, ← D.CT.map_comp]
      simp
    have hz : D.closure.hom.app L ≫ (D.qp.inv.app (D.CS.obj L.obj) ≫ h) =
        D.CT.map (D.qe.inv.app L.obj ≫ h₀) := by
      rw [← Category.assoc, hsquare, Category.assoc, hlift, D.CT.map_comp]
    have ha : (D.adjE.ofNatIsoLeft D.qe).homEquiv L.obj T.M.obj
        (D.qe.inv.app L.obj ≫ h₀) = D.adjE.homEquiv L.obj T.M.obj h₀ := by
      rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
      simp
    have hi : D.closureInput L T.M (D.qp.inv.app (D.CS.obj L.obj) ≫ h) =
        (D.qe.inv.app L.obj ≫ h₀) ≫ D.eta.app T.M := by
      dsimp [closureInput]
      rw [hz]
      exact (D.eta.naturality
        (ObjectProperty.homMk (D.qe.inv.app L.obj ≫ h₀) :
          (⟨_, D.hEe L⟩ : D.B₀.FullSubcategory) ⟶ T.M)).symm
    have hp : D.adjP.homEquiv (D.CS.obj L.obj) (D.CT.obj T.M.obj) h =
        D.CS.map (D.adjE.homEquiv L.obj T.M.obj h₀) ≫ T.gamma.hom := by
      apply (D.adjP.homEquiv _ _).symm.injective
      simp only [Equiv.symm_apply_apply, Adjunction.homEquiv_counit,
        Functor.map_comp, Category.assoc]
      apply (cancel_epi (D.delta.hom.app L)).1
      rw [hlift]
      have hn := D.delta.hom.naturality
        (ObjectProperty.homMk (D.adjE.homEquiv L.obj T.M.obj h₀) :
          L ⟶ ⟨D.Je.obj T.M.obj, T.hH⟩)
      dsimp at hn
      rw [← Category.assoc, ← Category.assoc, ← hn, Category.assoc,
        Category.assoc, T.counit, ← D.CT.map_comp]
      congr 1
      exact ((D.adjE.homEquiv _ _).symm_apply_apply h₀).symm
    refine ⟨hz, ha, hi, hp, ?_⟩
    dsimp [phi]
    rw [hi, Adjunction.homEquiv_naturality_right, ha, D.CS.map_comp]
    rfl

/-- Naturality in L, including the unique lift, g_0, z, a, the unit input and both transposes.
Source: blueprint site-comparison proof, second paragraph; Stacks Tag 0037, node Step 8.
(blueprint: lem-sf-counit-closure-unit-transpose-calculus)

Proof: naturality of Delta makes F_e(l) followed by h_0 a lift of
F_p C_S(l) followed by h. Uniqueness in Step 1 identifies it with any lift at L'.
Left naturality of the e-adjunction (lem-weil-pbc-adjunction-of-natural-bijection)
gives g'_0 = l followed by g_0. Naturality of q_p and q_e gives the stated z and a
formulas. Naturality of the closure comparison and eta gives the input formula;
left naturality of the transported e-adjunction followed by C_S gives the Phi formula.
Left naturality of the p-adjunction gives the ambient transpose formula. Substituting
these relations in Steps 3--6 precomposes their identities by the indicated maps.
-/
theorem naturality_left (T : D.Target) (L' L : D.A₀.FullSubcategory) (l : L' ⟶ L)
    (h : D.Fp.obj (D.CS.obj L.obj) ⟶ D.CT.obj T.M.obj)
    (h₀ : D.Fe.obj L.obj ⟶ T.M.obj)
    (h₀' : D.Fe.obj L'.obj ⟶ T.M.obj)
    (hlift : D.delta.hom.app L ≫ h = D.CT.map h₀)
    (hlift' : D.delta.hom.app L' ≫ (D.Fp.map (D.CS.map l.hom) ≫ h) = D.CT.map h₀') :
    h₀' = D.Fe.map l.hom ≫ h₀ ∧
    D.adjE.homEquiv L'.obj T.M.obj h₀' = l.hom ≫ D.adjE.homEquiv L.obj T.M.obj h₀ ∧
    D.qp.inv.app (D.CS.obj L'.obj) ≫ (D.Fp.map (D.CS.map l.hom) ≫ h) =
      D.Ep.map (D.CS.map l.hom) ≫ (D.qp.inv.app (D.CS.obj L.obj) ≫ h) ∧
    D.qe.inv.app L'.obj ≫ h₀' = D.Ee.map l.hom ≫ (D.qe.inv.app L.obj ≫ h₀) ∧
    (∀ z : D.Ep.obj (D.CS.obj L.obj) ⟶ D.CT.obj T.M.obj,
      D.closureInput L' T.M (D.Ep.map (D.CS.map l.hom) ≫ z) =
        D.Ee.map l.hom ≫ D.closureInput L T.M z) ∧
    D.adjP.homEquiv (D.CS.obj L'.obj) (D.CT.obj T.M.obj)
        (D.Fp.map (D.CS.map l.hom) ≫ h) =
      D.CS.map l.hom ≫ D.adjP.homEquiv (D.CS.obj L.obj) (D.CT.obj T.M.obj) h ∧
    (∀ z : D.Ep.obj (D.CS.obj L.obj) ⟶ D.CT.obj T.M.obj,
      D.phi L' T.M (D.Ep.map (D.CS.map l.hom) ≫ z) =
        D.CS.map l.hom ≫ D.phi L T.M z) := by
  have hh : h₀' = D.Fe.map l.hom ≫ h₀ := by
    apply (D.hom_bijective ⟨_, D.hFe L'⟩ T.M).1
    have hn := D.delta.hom.naturality l
    dsimp at hn
    rw [← hlift', D.CT.map_comp, ← hlift, ← Category.assoc, ← hn,
      Category.assoc]
  refine ⟨hh, ?_, ?_, ?_, D.closureInput_left L' L l T.M, ?_, ?_⟩
  · rw [hh, D.adjE.homEquiv_naturality_left]
  · simpa only [Category.assoc] using
      (D.qp.inv.naturality_assoc (D.CS.map l.hom) h).symm
  · rw [hh, ← Category.assoc]
    simpa only [Category.assoc] using (D.qe.inv.naturality_assoc l.hom h₀).symm
  · exact D.adjP.homEquiv_naturality_left (D.CS.map l.hom) h
  · intro z
    dsimp only [phi]
    rw [D.closureInput_left, Adjunction.homEquiv_naturality_left, D.CS.map_comp]

/-- Naturality for every morphism between allowed M's when gamma is natural at that morphism.
Source: blueprint site-comparison proof, second paragraph; Stacks Tag 0037, node Step 9.
The unrestricted morphism m expresses fullness of any chosen subcategory of allowed M's.
(blueprint: lem-sf-counit-closure-unit-transpose-calculus)

Proof: C_T(m) followed after h has lift h_0 followed by m, by functoriality of C_T;
Step 1 identifies every lift at M' with this one. Right-variable adjunction naturality
(lem-weil-pbc-adjunction-of-natural-bijection) gives g'_0 = g_0 followed by J_e(m).
The definitions give z' = z followed by C_T(m) and a' = a followed by m.
Naturality of eta at m, mapped by C_S J_e, gives naturality of rho. Applying that
same naturality after the closure input gives the input equation. Right naturality of
the transported e-adjunction and functoriality of C_S give the Phi equation. Naturality
of the p-adjunction gives the ambient transpose equation. Finally substitute the
assumed gamma naturality and the rho equation into Steps 3--6 to transport all formulas.
-/
theorem naturality_right (T T' : D.Target) (m : T.M.obj ⟶ T'.M.obj)
    (hgamma : D.CS.map (D.Je.map m) ≫ T'.gamma.hom =
      T.gamma.hom ≫ D.Jp.map (D.CT.map m))
    (L : D.A₀.FullSubcategory)
    (h : D.Fp.obj (D.CS.obj L.obj) ⟶ D.CT.obj T.M.obj)
    (h₀ : D.Fe.obj L.obj ⟶ T.M.obj) (h₀' : D.Fe.obj L.obj ⟶ T'.M.obj)
    (hlift : D.delta.hom.app L ≫ h = D.CT.map h₀)
    (hlift' : D.delta.hom.app L ≫ (h ≫ D.CT.map m) = D.CT.map h₀') :
    h₀' = h₀ ≫ m ∧
    D.adjE.homEquiv L.obj T'.M.obj h₀' =
      D.adjE.homEquiv L.obj T.M.obj h₀ ≫ D.Je.map m ∧
    D.qp.inv.app (D.CS.obj L.obj) ≫ (h ≫ D.CT.map m) =
      (D.qp.inv.app (D.CS.obj L.obj) ≫ h) ≫ D.CT.map m ∧
    D.qe.inv.app L.obj ≫ h₀' = (D.qe.inv.app L.obj ≫ h₀) ≫ m ∧
    D.CS.map (D.Je.map m) ≫ D.rho T'.M =
      D.rho T.M ≫ D.CS.map (D.Je.map (D.U.map (D.comparisonHom T.M T'.M (D.CT.map m)))) ∧
    (∀ z : D.Ep.obj (D.CS.obj L.obj) ⟶ D.CT.obj T.M.obj,
      D.closureInput L T'.M (z ≫ D.CT.map m) = D.closureInput L T.M z ≫
        D.U.map (D.comparisonHom T.M T'.M (D.CT.map m))) ∧
    D.adjP.homEquiv (D.CS.obj L.obj) (D.CT.obj T'.M.obj) (h ≫ D.CT.map m) =
      D.adjP.homEquiv (D.CS.obj L.obj) (D.CT.obj T.M.obj) h ≫ D.Jp.map (D.CT.map m) ∧
    (∀ z : D.Ep.obj (D.CS.obj L.obj) ⟶ D.CT.obj T.M.obj,
      D.phi L T'.M (z ≫ D.CT.map m) = D.phi L T.M z ≫
        D.CS.map (D.Je.map (D.U.map (D.comparisonHom T.M T'.M (D.CT.map m))))) ∧
    D.CS.map (D.adjE.homEquiv L.obj T.M.obj h₀) ≫ D.CS.map (D.Je.map m) ≫
        T'.gamma.hom =
      (D.CS.map (D.adjE.homEquiv L.obj T.M.obj h₀) ≫ T.gamma.hom) ≫
        D.Jp.map (D.CT.map m) := by
  have hh : h₀' = h₀ ≫ m := by
    apply (D.hom_bijective ⟨_, D.hFe L⟩ T'.M).1
    rw [← hlift', D.CT.map_comp, ← hlift, Category.assoc]
  refine ⟨hh, ?_, (Category.assoc _ _ _).symm, ?_, ?_,
    D.closureInput_right L T.M T'.M m, ?_, ?_, ?_⟩
  · rw [hh, D.adjE.homEquiv_naturality_right]
  · rw [hh, Category.assoc]
  · have he := D.eta.naturality (ObjectProperty.homMk m : T.M ⟶ T'.M)
    dsimp at he
    dsimp only [rho]
    rw [← D.CS.map_comp, ← D.Je.map_comp, he, D.Je.map_comp, D.CS.map_comp]
    rfl
  · exact D.adjP.homEquiv_naturality_right h (D.CT.map m)
  · intro z
    dsimp only [phi]
    rw [D.closureInput_right, Adjunction.homEquiv_naturality_right, D.CS.map_comp]
  · rw [hgamma, Category.assoc]

end CounitClosureTransposeData

end CategoryTheory
