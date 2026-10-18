/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.RationalFunctionRing
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Rational functions and generic stalks

Source: Stacks Project, Morphisms, Lemma 01RV, first and third assertions
(blueprint: lem-sc-rational-functions-generic-stalks).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem generic_component_opens (X : Scheme.{u}) (n : ℕ)
    (components : Fin n ≃ {Z : Set X // Z ∈ irreducibleComponents X})
    (η : Fin n → X) (hη : ∀ i, IsGenericPoint (η i) (components i).val) :
    ∃ V : Fin n → X.Opens,
      (∀ i, η i ∈ V i) ∧
      (∀ i, (V i : Set X) ⊆ (components i).val) ∧
      Pairwise (fun i j ↦ Disjoint (V i) (V j)) := by
  classical
  have hfinite : (irreducibleComponents X).Finite := by
    have heq : irreducibleComponents X = Set.range (fun i ↦ (components i).val) := by
      ext Z
      exact ⟨fun h ↦ by
        obtain ⟨i, hi⟩ := components.surjective ⟨Z, h⟩
        exact ⟨i, congrArg Subtype.val hi⟩,
        fun ⟨i, hi⟩ ↦ hi ▸ (components i).property⟩
    rw [heq]
    exact Set.finite_range _
  let V : Fin n → X.Opens := fun i ↦
    ⟨(⋃₀ (irreducibleComponents X \ {(components i).val}))ᶜ, by
      rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
      exact hfinite.sdiff.isClosed_biUnion
        (fun Z hZ ↦ isClosed_of_mem_irreducibleComponents Z hZ.1)⟩
  have hcl (i) : closure (V i : Set X) = (components i).val :=
    closure_sUnion_irreducibleComponents_sdiff_singleton hfinite _ (components i).property
  have hsub (i) : (V i : Set X) ⊆ (components i).val := by
    rw [← hcl i]
    exact subset_closure
  have hmem (i) : η i ∈ V i := by
    apply ((hη i).mem_open_set_iff (V i).isOpen).mpr
    have hne : (V i : Set X).Nonempty := by
      by_contra! h
      have hc : (components i).val = ∅ := by rw [← hcl i, h, closure_empty]
      exact (components i).property.1.nonempty.ne_empty hc
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, hsub i hx, hx⟩
  refine ⟨V, hmem, hsub, ?_⟩
  intro i j hij
  apply disjoint_iff.mpr
  apply le_antisymm _ bot_le
  intro x ⟨hxi, hxj⟩
  exact hxi (Set.mem_sUnion_of_mem (hsub j hxj)
    ⟨(components j).property, by
      simpa only [Set.mem_singleton_iff] using
        (show (components j).val ≠ (components i).val from
          fun h ↦ hij (components.injective (Subtype.ext h)).symm)⟩)

private theorem dense_of_generic_mem (X : Scheme.{u}) (n : ℕ)
    (components : Fin n ≃ {Z : Set X // Z ∈ irreducibleComponents X})
    (η : Fin n → X) (hη : ∀ i, IsGenericPoint (η i) (components i).val)
    (U : X.Opens) (hU : ∀ i, η i ∈ U) : Dense (U : Set X) := by
  intro x
  obtain ⟨i, hi⟩ := components.surjective
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  have hx : x ∈ (components i).val := by
    rw [hi]
    exact mem_irreducibleComponent
  have hcl : (components i).val ⊆ closure (U : Set X) := by
    rw [← (hη i).def]
    exact closure_mono (Set.singleton_subset_iff.mpr (hU i))
  exact hcl hx

/-- For a scheme with finitely many irreducible components, every dense open contains their
 generic points, and taking germs identifies rational functions with the product of the generic
 stalks. For an integral scheme there is one component, the whole space, and both the rational
 function ring and the generic stalk are fields. Source: Stacks Project, Lemma 01RV, first and
 third assertions (blueprint: lem-sc-rational-functions-generic-stalks).

Proof (the six steps of the node):
1. By `lem-sc-irreducible-components-cover` the components cover `X`. Remove all components
   other than the i-th to obtain a nonempty open `V_i` containing its generic point. Maximality
   of components makes these opens pairwise disjoint. An open meets a component exactly when
   it contains its generic point (`def-sc-generic-point`, `lem-sc-scheme-sober`).
2. A dense open meets each `V_i`, hence contains every generic point. Conversely an open
   containing all generic points is dense, because their closures cover `X`.
3. Germ maps respect restriction, addition and multiplication. They therefore induce a
   well-defined ring map on the colimit `def-sc-rational-functions`, with the displayed values
   on its coprojections (`def-weil-pbc-module-stalk`).
4. A section with all generic germs zero vanishes on smaller neighborhoods inside the `V_i`.
   Their disjoint union is dense, and sheaf locality makes the section zero there, proving
   injectivity (`def-pc-scheme`, `def-weil-pbc-module-stalk`, `def-sc-rational-functions`).
5. Represent each prescribed germ on a neighborhood inside `V_i`. Sheaf gluing on their
   disjoint dense union supplies a rational function with those germs, proving surjectivity
   (the same three nodes).
6. For an integral scheme, irreducibility makes `X` its only component. The generic stalk
   is a field by `lem-sc-integral-function-field-affine-fraction`, using a nonempty affine open
   and Algebra Lemma 00EU. The germ isomorphism transports this property to rational functions
   (`def-pc-integral-scheme`, `def-weil-irreducible-components`, `def-pc-scheme`). -/
theorem rationalFunctions_generic_stalks (X : Scheme.{u}) (n : ℕ)
    (components : Fin n ≃ {Z : Set X // Z ∈ irreducibleComponents X})
    (η : Fin n → X) (hη : ∀ i : Fin n, IsGenericPoint (η i) (components i).val) :
    ∃ hDense : ∀ (U : DenseOpens X) (i : Fin n), η i ∈ U.val,
      ∃ e : (X.rationalFunctionRing : Type u) ≃+* ((i : Fin n) → X.presheaf.stalk (η i)),
        (∀ (U : DenseOpens X) (f : Γ(X, U.val)) (i : Fin n),
          e ((colimit.ι (denseOpenSections X) (op U)) f) i =
            X.presheaf.germ U.val (η i) (hDense U i) f) ∧
        (IsIntegral X → n = 1 ∧ (∀ i : Fin n, (components i).val = Set.univ) ∧
          IsField (X.rationalFunctionRing : Type u) ∧
          ∀ i : Fin n, IsField (X.presheaf.stalk (η i)) ∧
            ∃ ei : (X.rationalFunctionRing : Type u) ≃+* X.presheaf.stalk (η i),
              ∀ r : X.rationalFunctionRing, ei r = e r i) := by
  classical
  obtain ⟨V, hVmem, hVsub, hVdisj⟩ := generic_component_opens X n components η hη
  have hDense (U : DenseOpens X) (i : Fin n) : η i ∈ U.val := by
    obtain ⟨x, hxV, hxU⟩ := U.property.inter_open_nonempty (V i) (V i).isOpen
      ⟨η i, hVmem i⟩
    exact ((hη i).mem_open_set_iff U.val.isOpen).mpr ⟨x, hVsub i hxV, hxU⟩
  refine ⟨hDense, ?_⟩
  let c : Cocone (denseOpenSections X) :=
    { pt := CommRingCat.of ((i : Fin n) → X.presheaf.stalk (η i))
      ι :=
        { app := fun U ↦ CommRingCat.ofHom
            (RingHom.pi fun i ↦ (X.presheaf.germ U.unop.val (η i) (hDense U.unop i)).hom)
          naturality := by
            intro U W f
            ext s
            funext i
            exact X.presheaf.germ_res_apply f.unop (η i) (hDense W.unop i) s } }
  let φ : X.rationalFunctionRing →+* ((i : Fin n) → X.presheaf.stalk (η i)) :=
    (colimit.desc (denseOpenSections X) c).hom
  have hφ (U : DenseOpens X) (s : Γ(X, U.val)) (i : Fin n) :
      φ ((colimit.ι (denseOpenSections X) (op U)) s) i =
        X.presheaf.germ U.val (η i) (hDense U i) s := by
    exact congrArg (fun f : Γ(X, U.val) ⟶ c.pt ↦ f s i)
      (colimit.ι_desc c (op U))
  let : IsCofiltered (DenseOpens X) :=
    { nonempty := ⟨⟨⊤, by change Dense (Set.univ : Set X); exact dense_univ⟩⟩
      cone_objs := fun U W ↦ ⟨U.inter W,
        homOfLE (by change U.val ⊓ W.val ≤ U.val; exact inf_le_left),
        homOfLE (by change U.val ⊓ W.val ≤ W.val; exact inf_le_right), trivial⟩
      cone_maps := fun _ _ f g ↦ ⟨_, 𝟙 _, Subsingleton.elim _ _⟩ }
  have hinj : Function.Injective φ := by
    intro r t hrt
    obtain ⟨U, s, rfl⟩ := Concrete.colimit_exists_rep (denseOpenSections X) r
    obtain ⟨T, t, rfl⟩ := Concrete.colimit_exists_rep (denseOpenSections X) t
    have hg (i : Fin n) :
        X.presheaf.germ U.unop.val (η i) (hDense U.unop i) s =
          X.presheaf.germ T.unop.val (η i) (hDense T.unop i) t := by
      simpa only [hφ] using congrFun hrt i
    choose W hW iU iT heq using fun i ↦
      X.presheaf.germ_eq (η i) (hDense U.unop i) (hDense T.unop i) s t (hg i)
    let D : DenseOpens X := ⟨⨆ i, W i,
      dense_of_generic_mem X n components η hη _ (fun i ↦ le_iSup W i (hW i))⟩
    have hDU : D.val ≤ U.unop.val := iSup_le fun i ↦ (iU i).le
    have hDT : D.val ≤ T.unop.val := iSup_le fun i ↦ (iT i).le
    apply Concrete.colimit_rep_eq_of_exists (denseOpenSections X) s t
    refine ⟨op D, (homOfLE hDU).op, (homOfLE hDT).op, ?_⟩
    change X.presheaf.map (homOfLE hDU).op s =
      X.presheaf.map (homOfLE hDT).op t
    apply X.sheaf.eq_of_locally_eq W
    intro i
    change X.presheaf.map (TopologicalSpace.Opens.leSupr W i).op
        (X.presheaf.map (homOfLE hDU).op s) =
      X.presheaf.map (TopologicalSpace.Opens.leSupr W i).op
        (X.presheaf.map (homOfLE hDT).op t)
    have hres (A : X.Opens) (hDA : D.val ≤ A) (a : Γ(X, A)) :
        X.presheaf.map (TopologicalSpace.Opens.leSupr W i).op
            (X.presheaf.map (homOfLE hDA).op a) =
          X.presheaf.map ((TopologicalSpace.Opens.leSupr W i) ≫ homOfLE hDA).op a := by
      rw [op_comp, X.presheaf.map_comp]
      rfl
    rw [hres, hres]
    exact heq i
  have hsurj : Function.Surjective φ := by
    intro t
    choose W hWV hW s hs using fun i ↦
      X.presheaf.exists_le_germ_eq (t i) (hVmem i)
    have hcompat : TopCat.Presheaf.IsCompatible X.presheaf W s := by
      intro i j
      by_cases hij : i = j
      · subst j
        rfl
      · have hdisj : W i ⊓ W j = ⊥ :=
          disjoint_iff.mp ((hVdisj hij).mono (hWV i) (hWV j))
        exact @Subsingleton.elim _
          (CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hdisj)) _ _
    obtain ⟨g, hg, -⟩ := X.sheaf.existsUnique_gluing W s hcompat
    change ∀ i, X.presheaf.map (TopologicalSpace.Opens.leSupr W i).op g = s i at hg
    let D : DenseOpens X := ⟨⨆ i, W i,
      dense_of_generic_mem X n components η hη _ (fun i ↦ le_iSup W i (hW i))⟩
    refine ⟨(colimit.ι (denseOpenSections X) (op D)) g, ?_⟩
    funext i
    rw [hφ]
    rw [← X.presheaf.germ_res_apply (TopologicalSpace.Opens.leSupr W i) (η i) (hW i),
      hg i, hs i]
  let e := RingEquiv.ofBijective φ ⟨hinj, hsurj⟩
  refine ⟨e, hφ, ?_⟩
  intro hX
  let : IsIntegral X := hX
  have hcomp (i : Fin n) : (components i).val = Set.univ := by
    simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using
      (components i).property
  have hsub : Subsingleton (Fin n) := ⟨fun i j ↦
    components.injective (Subtype.ext ((hcomp i).trans (hcomp j).symm))⟩
  let i₀ : Fin n := components.symm
    ⟨Set.univ, by simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff]⟩
  let : Unique (Fin n) := ⟨⟨i₀⟩, fun i ↦ hsub.elim i i₀⟩
  have hn : n = 1 := by simpa only [Fintype.card_fin] using Fintype.card_unique (α := Fin n)
  have hfield (i : Fin n) : IsField (X.presheaf.stalk (η i)) :=
    isField_stalk_of_closure_mem_irreducibleComponents X (η i)
      ((hη i).def.symm ▸ (components i).property)
  have hei (i : Fin n) :
      ∃ ei : (X.rationalFunctionRing : Type u) ≃+* X.presheaf.stalk (η i),
        ∀ r, ei r = e r i := by
    let : Unique (Fin n) := ⟨⟨i⟩, fun j ↦ hsub.elim j i⟩
    exact ⟨e.trans (RingEquiv.piUnique _), fun _ ↦ rfl⟩
  obtain ⟨ei, -⟩ := hei i₀
  refine ⟨hn, hcomp, ei.isField (hfield i₀), fun i ↦ ⟨hfield i, hei i⟩⟩

end AlgebraicGeometry.Scheme
