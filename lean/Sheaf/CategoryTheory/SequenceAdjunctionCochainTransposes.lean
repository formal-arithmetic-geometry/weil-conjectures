/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.CategoryTheory.SequenceProjectionDerivedAdjunction
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Mathlib.CategoryTheory.Limits.Final

/-! # Cochain transposes of the sequence coefficient adjunction

Source: Stacks Project, Cohomology on Sites, Tags 07A6 and 0FPI;
Modules on Sites, Tag 03D7; Derived Categories, Tags 0FND and 09T5.
(blueprint: lem-coef-sequence-adjunction-cochain-transposes).

The ordinary tensor and inverse-limit presentations, and the derived comparisons,
are exactly those of `SequenceProjection.derivedAdjunction`. The two equations below
state the unit and counit after the canonical resolution identifications. Since these
identifications are invertible on the specified resolutions, these are equations of
derived morphisms, independent of all choices. Level `n` denotes the paper's `n+1`.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w d

open CategoryTheory CategoryTheory.Limits Opposite

-- A full, essentially surjective functor is initial: every comma object maps
-- to a fixed lift of the target, giving a zigzag between any two objects.
private theorem initial_of_full_essSurj
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B) [F.Full] [F.EssSurj] :
    F.Initial := by
  classical
  constructor
  intro Y
  let e := F.objObjPreimageIso Y
  let Z : CostructuredArrow F Y := CostructuredArrow.mk e.hom
  have lift (X : CostructuredArrow F Y) : Nonempty (X ⟶ Z) := by
    refine ⟨CostructuredArrow.homMk (F.preimage (X.hom ≫ e.inv)) ?_⟩
    simp [Z, e]
  let : Nonempty (CostructuredArrow F Y) := ⟨Z⟩
  apply zigzag_isConnected
  intro X X'
  exact (Zigzag.of_hom (lift X).some).trans (Zigzag.of_inv (lift X').some)

-- The induced functor on structured arrows is also full and essentially
-- surjective, so restricting the defining limit cone preserves its limit.
private noncomputable def pointwise_precomp_full
    {A C D H : Type*} [Category A] [Category C] [Category D] [Category H]
    (P : A ⥤ C) [P.Full] [P.EssSurj] (Q : C ⥤ D) (F : C ⥤ H) (L : D ⥤ H)
    (α : Q ⋙ L ⟶ F)
    (h : (Functor.RightExtension.mk L α).IsPointwiseRightKanExtension) :
    (Functor.RightExtension.mk L
      ((Functor.associator P Q L).hom ≫ Functor.whiskerLeft P α)).IsPointwiseRightKanExtension := by
  intro Y
  let p := StructuredArrow.pre Y P Q
  let : p.Initial := initial_of_full_essSurj p
  apply Limits.IsLimit.ofIsoLimit ((Functor.Initial.isLimitWhiskerEquiv p _).symm (h Y))
  refine Limits.Cone.ext (Iso.refl _) ?_
  intro X
  dsimp [Functor.RightExtension.coneAt, Functor.RightExtension.mk, p]
  simp

-- Transport the defining limit cone through an equivalence of structured
-- arrow categories and the prescribed isomorphism of diagram functors.
private noncomputable def pointwise_change_iso
    {C D H : Type*} [Category C] [Category D] [Category H]
    {Q Q' : C ⥤ D} {F F' : C ⥤ H} (L : D ⥤ H)
    (i : Q ≅ Q') (j : F ≅ F') (α : Q ⋙ L ⟶ F)
    (h : (Functor.RightExtension.mk L α).IsPointwiseRightKanExtension) :
    (Functor.RightExtension.mk L
      (Functor.whiskerRight i.inv L ≫ α ≫ j.hom)).IsPointwiseRightKanExtension := by
  intro Y
  let Φ : StructuredArrow Y Q' ≌ StructuredArrow Y Q := Comma.mapRightIso _ i.symm
  let k : Φ.functor ⋙ StructuredArrow.proj Y Q ⋙ F ≅
      StructuredArrow.proj Y Q' ⋙ F' :=
    NatIso.ofComponents (fun X ↦ j.app X.right) (by
      intro X X' f
      exact j.hom.naturality f.right)
  apply Limits.IsLimit.ofIsoLimit
    ((Limits.IsLimit.postcomposeHomEquiv k _).symm ((h Y).whiskerEquivalence Φ))
  refine Limits.Cone.ext (Iso.refl _) ?_
  intro X
  dsimp [Functor.RightExtension.coneAt, Functor.RightExtension.mk, Φ, k]
  simp [Category.assoc]
  rfl

namespace SheafOfModules.SequenceProjection

private theorem tensorSection_one
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
    {A S : Sheaf J CommRingCat.{w}} (φ : A ⟶ S)
    (M : Modules A) (U : Cᵒᵖ) (x : M.val.obj U) :
    tensorSection φ M U 1 x =
      (toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
        ((ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).unit.app
          (M.val.obj U) x) := by
  exact @one_smul (S.obj.obj U) ((changeOfRings φ M).val.obj U) _ _ _

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

/-- The normalized sequence adjunction has the stated cochain unit and counit.
All the ordinary and derived presentation clauses are retained from the dependency;
no new scalar-extension, limit, or derived-category construction is chosen.
The unit equation uses the isomorphism `R(ε_Q ≫ [a])` followed by the K-injective
comparison `η_I`. The counit equation uses the isomorphism `L([q] ≫ η_I)` and `ε_Q`.
The section equations specify the actual chain maps, not just their cohomology.

Source: Stacks Project, Tags 07A6 and 0FPI
(blueprint: lem-coef-sequence-adjunction-cochain-transposes).

Proof:
1. Use lem-pur-sheaf-ring-derived-coefficient-adjunction and its ordinary adjunction
for each structural map A to B_n. The scalar transpose evaluates at 1 tensor x,
for arbitrary target complexes, as recorded separately below.
2. Use lem-coef-sequence-projection-derived-adjunction. A strict map v has transpose
h_v whose nth projection is v_n(1 tensor x). Strictness gives its cone condition;
linearity and the cochain identities give a chain map. Conversely h gives the strict
map v_h(b tensor x) = b pi_n(h(x)). Both assignments are inverse: test on pure tensors
and on all limit projections. Their compatibility with differentials is degreewise.
3. The dependency's normalized derived Hom equivalence sends ε_Q followed by [v]
to [h_v] followed by η_I. By the K-injective direct-image convention of
lem-weil-pbc-ringed-topoi-derived-pushforward-composition, η_I is invertible for
K-injective systems I. No K-injectivity of a restriction or individual level is used.
4. For a resolution a of GQ, apply this identity to a. Naturality in the target
identifies its adjunct with R(ε_Q followed by [a]) composed with the derived unit.
The ordinary transpose gives exactly the displayed formula for h.
5. For a flat-term K-flat resolution q of FI, take v to be its ordinary inverse
transpose. Its component is b times pi_n(q(x)). The normalized identity says its
adjunct is [q] followed by η_I. Naturality in the source identifies the counit after
L([q] followed by η_I) with ε_Q followed by [v], as in Stacks 0FPI.
6. These equalities identify all choices with the unit and counit of the same
adjunction. Their naturality as natural transformations gives naturality in the
derived argument; the invertible comparisons give independence of resolutions. -/
theorem adjunctionCochainTransposes
    (A : Sheaf J CommRingCat.{w}) (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B)
    [HasDerivedCategory.{d} (Modules A)] [HasDerivedCategory.{d} (StrictRingSystem B)] :
    ∃ (G : Modules A ⥤ StrictRingSystem B) (F : StrictRingSystem B ⥤ Modules A)
      (_ : G.Additive) (_ : F.Additive)
      (e : ∀ (M : Modules A) (n : ℕ),
        (G.obj M).level n ≅ changeOfRings (α.app (op n)) M)
      (π : ∀ (N : StrictRingSystem B) (n : ℕ),
        F.obj N ⟶ (restriction A B α n).obj (N.level n))
      (adj : G ⊣ F),
      (∀ {M M' : Modules A} (f : M ⟶ M') (n : ℕ),
        (G.map f).app n ≫ (e M' n).hom =
          (e M n).hom ≫ changeOfRingsHom (α.app (op n)) M f) ∧
      (∀ (M : Modules A) {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ)
        (b : (B.obj (op n)).obj.obj U) (x : M.val.obj U),
        ((G.obj M).transition h).val.app U
            ((e M n).inv.val.app U (tensorSection (α.app (op n)) M U b x)) =
          (e M m).inv.val.app U (tensorSection (α.app (op m)) M U
            ((B.map (homOfLE h).op).hom.app U b) x)) ∧
      (∀ {N N' : StrictRingSystem B} (f : N ⟶ N') (n : ℕ),
        F.map f ≫ π N' n = π N n ≫ (restriction A B α n).map (f.app n)) ∧
      (∀ (N : StrictRingSystem B) {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ)
        (x : (F.obj N).val.obj U),
        (π N m).val.app U x =
          (N.transition h).val.app U ((π N n).val.app U x)) ∧
      (∀ (M : Modules A) (N : StrictRingSystem B)
        (f : ∀ n : ℕ, M ⟶ (restriction A B α n).obj (N.level n)),
        (∀ {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ) (x : M.val.obj U),
          (f m).val.app U x = (N.transition h).val.app U ((f n).val.app U x)) →
        ∃! h : M ⟶ F.obj N, ∀ n : ℕ, h ≫ π N n = f n) ∧
      (∀ (M : Modules A) (N : StrictRingSystem B) (h : M ⟶ F.obj N)
        (n : ℕ) (U : Cᵒᵖ) (b : (B.obj (op n)).obj.obj U) (x : M.val.obj U),
        (((adj.homEquiv M N).symm h).app n).val.app U
            ((e M n).inv.val.app U (tensorSection (α.app (op n)) M U b x)) =
          @SMul.smul ((B.obj (op n)).obj.obj U) ((N.level n).val.obj U) inferInstance b
            ((π N n).val.app U (h.val.app U x))) ∧
      ∃ (L : DerivedCategory.{d} (Modules A) ⥤ DerivedCategory.{d} (StrictRingSystem B))
        (R : DerivedCategory.{d} (StrictRingSystem B) ⥤ DerivedCategory.{d} (Modules A))
        (ε : DerivedCategory.Q ⋙ L ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
        (η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
        (derivedAdj : L ⊣ R),
        L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso (Modules A) (.up ℤ)) ∧
        R.IsRightDerivedFunctor η
          (HomologicalComplex.quasiIso (StrictRingSystem B) (.up ℤ)) ∧
        (∀ (Q : CochainComplex (Modules A) ℤ), Q.IsKFlatIndependentCoefficients →
          (∀ i : ℤ, (Q.X i).IsFlatOnSite) → IsIso (ε.app Q)) ∧
        (∀ (I : CochainComplex (StrictRingSystem B) ℤ), I.IsKInjective →
          IsIso (η.app I)) ∧
        (∀ (P Q : CochainComplex (Modules A) ℤ) (q : Q ⟶ P),
          Q.IsKFlatIndependentCoefficients → (∀ i : ℤ, (Q.X i).IsFlatOnSite) →
          QuasiIso q →
          ∃ c : L.obj (DerivedCategory.Q.obj P) ≅
            DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj Q),
            L.map (DerivedCategory.Q.map q) ≫ c.hom = ε.app Q) ∧
        (∀ (Q : CochainComplex (Modules A) ℤ)
          (I : CochainComplex (StrictRingSystem B) ℤ)
          (f : (G.mapHomologicalComplex (.up ℤ)).obj Q ⟶ I),
          derivedAdj.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
              (ε.app Q ≫ DerivedCategory.Q.map f) =
            DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv Q I f) ≫
              η.app I) ∧
        (∀ (Q : CochainComplex (Modules A) ℤ), Q.IsKFlatIndependentCoefficients →
          (∀ i : ℤ, (Q.X i).IsFlatOnSite) →
          ∀ (I : CochainComplex (StrictRingSystem B) ℤ) [I.IsKInjective]
            (a : (G.mapHomologicalComplex (.up ℤ)).obj Q ⟶ I) [QuasiIso a],
          ∃ h : Q ⟶ (F.mapHomologicalComplex (.up ℤ)).obj I,
            derivedAdj.unit.app (DerivedCategory.Q.obj Q) ≫
                R.map (ε.app Q ≫ DerivedCategory.Q.map a) =
              DerivedCategory.Q.map h ≫ η.app I ∧
            ∀ (i : ℤ) (n : ℕ) (U : Cᵒᵖ) (x : (Q.X i).val.obj U),
              (π (I.X i) n).val.app U ((h.f i).val.app U x) =
                ((a.f i).app n).val.app U
                  ((e (Q.X i) n).inv.val.app U
                    (tensorSection (α.app (op n)) (Q.X i) U 1 x))) ∧
        (∀ (I : CochainComplex (StrictRingSystem B) ℤ) [I.IsKInjective]
          (Q : CochainComplex (Modules A) ℤ), Q.IsKFlatIndependentCoefficients →
          (∀ i : ℤ, (Q.X i).IsFlatOnSite) →
          ∀ (q : Q ⟶ (F.mapHomologicalComplex (.up ℤ)).obj I) [QuasiIso q],
          ∃ v : (G.mapHomologicalComplex (.up ℤ)).obj Q ⟶ I,
            L.map (DerivedCategory.Q.map q ≫ η.app I) ≫
                derivedAdj.counit.app (DerivedCategory.Q.obj I) =
              ε.app Q ≫ DerivedCategory.Q.map v ∧
            ∀ (i : ℤ) (n : ℕ) (U : Cᵒᵖ) (b : (B.obj (op n)).obj.obj U)
              (x : (Q.X i).val.obj U),
              ((v.f i).app n).val.app U
                  ((e (Q.X i) n).inv.val.app U
                    (tensorSection (α.app (op n)) (Q.X i) U b x)) =
                @SMul.smul ((B.obj (op n)).obj.obj U) (((I.X i).level n).val.obj U)
                  inferInstance b ((π (I.X i) n).val.app U ((q.f i).val.app U x))) := by
  classical
  obtain ⟨G, F, hG, hF, e, π, adj, hmap, htrans, hπ, hcone, hlim, hsection,
    L, R, ε, η, dAdj, hL, hR, hε, hη, hres, hnorm⟩ := derivedAdjunction A B α
  refine ⟨G, F, hG, hF, e, π, adj, hmap, htrans, hπ, hcone, hlim, hsection,
    L, R, ε, η, dAdj, hL, hR, hε, hη, hres, hnorm, ?_, ?_⟩
  · intro Q _ _ I _ a _
    let h := (adj.mapHomologicalComplex (.up ℤ)).homEquiv Q I a
    refine ⟨h, hnorm Q I a, ?_⟩
    intro i n U x
    have hs := hsection (Q.X i) (I.X i) (h.f i) n U 1 x
    have he : (adj.homEquiv (Q.X i) (I.X i)).symm (h.f i) = a.f i := by
      exact (adj.homEquiv (Q.X i) (I.X i)).symm_apply_apply (a.f i)
    have hone (y : ((I.X i).level n).val.obj U) :
        @SMul.smul ((B.obj (op n)).obj.obj U) (((I.X i).level n).val.obj U)
          inferInstance 1 y = y := one_smul _ y
    rw [he, hone] at hs
    exact hs.symm
  · intro I _ Q _ _ q _
    let v := ((adj.mapHomologicalComplex (.up ℤ)).homEquiv Q I).symm q
    refine ⟨v, ?_, ?_⟩
    · have hn := hnorm Q I v
      rw [Equiv.apply_symm_apply] at hn
      exact ((dAdj.homEquiv _ _).symm_apply_eq).2 hn.symm
    · intro i n U b x
      exact hsection (Q.X i) (I.X i) (q.f i) n U b x


/-- At every level, exact restriction is right adjoint to the existing derived scalar
extension. The comparison sends the adjunct of a chain map f to the chain map
x ↦ f(1 tensor x). The target complex K is arbitrary.

Source: Stacks Project, Tags 07A6, 03D7, 0FND and 09T5
(blueprint: lem-coef-sequence-adjunction-cochain-transposes).

Proof: Apply lem-pur-sheaf-ring-coefficient-ordinary-adjunction to the ordinary
functor of the cochain model: its object and map equations specify exactly the
sheafified scalar extension. Its Hom correspondence is evaluation at 1 tensor x,
so termwise application supplies the displayed chain-map section formula.
Apply lem-pur-sheaf-ring-derived-coefficient-adjunction, using the universal derived
pair of lem-pur-derived-change-of-rings. The canonical K-flat comparison carries
the derived unit to the class of x ↦ 1 tensor x. Composing with restriction of [f]
therefore gives the class of its ordinary transpose. Equivalently the inverse
adjunct sends x tensor b to b f(1 tensor x) = f(b tensor x); invert the Hom
bijection to get the displayed equality. Exactness of restriction supplies its
termwise derived factorization. No K-injectivity or boundedness of K is needed. -/
theorem scalarCochainTranspose
    (A : Sheaf J CommRingCat.{w}) (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B) (n : ℕ)
    [HasDerivedCategory.{d} (Modules A)] [HasDerivedCategory.{d} (systemLevel B n)]
    (s : DerivedChangeOfRingsCochainModel.{u, v, w, d, d}
      (O := A) (S := B.obj (op n)) (α.app (op n))) :
    ∃ (_ : PreservesFiniteLimits (restriction A B α n))
      (_ : PreservesFiniteColimits (restriction A B α n))
      (a : s.E ⊣ restriction A B α n)
      (dAdj : s.T ⊣ (restriction A B α n).mapDerivedCategory),
      (∀ (M : Modules A) (N : systemLevel B n) (f : s.E.obj M ⟶ N)
        (U : Cᵒᵖ) (x : M.val.obj U),
        (a.homEquiv M N f).val.app U x =
          f.val.app U ((eqToHom (s.obj_eq M).symm :
            changeOfRings (α.app (op n)) M ⟶ s.E.obj M).val.app U
              (tensorSection (α.app (op n)) M U 1 x))) ∧
      ∀ (Q : CochainComplex (Modules A) ℤ), Q.IsKFlatIndependentCoefficients →
        (∀ i : ℤ, (Q.X i).IsFlatOnSite) →
        IsIso (s.ε.app Q) ∧
        ∀ (K : CochainComplex (systemLevel B n) ℤ)
          (f : (s.E.mapHomologicalComplex (.up ℤ)).obj Q ⟶ K),
          dAdj.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj K)
              (s.ε.app Q ≫ DerivedCategory.Q.map f) =
            DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv Q K f) ≫
              (restriction A B α n).mapDerivedCategoryFactors.inv.app K ∧
          ∀ (i : ℤ) (U : Cᵒᵖ) (x : (Q.X i).val.obj U),
            ((((a.mapHomologicalComplex (.up ℤ)).homEquiv Q K f).f i).val.app U x) =
              (f.f i).val.app U
                ((eqToHom (s.obj_eq (Q.X i)).symm :
                  changeOfRings (α.app (op n)) (Q.X i) ⟶ s.E.obj (Q.X i)).val.app U
                  (tensorSection (α.app (op n)) (Q.X i) U 1 x)) := by
  classical
  let φ : A ⟶ B.obj (op n) := α.app (op n)
  let : HasDerivedCategory.{d}
      (SheafOfModules.{w} (derivedChangeRingIndependentCoefficients J (B.obj (op n)))) :=
    inferInstanceAs (HasDerivedCategory.{d} (systemLevel B n))
  let : HasDerivedCategory.{d}
      (SheafOfModules.{w} (derivedChangeRingIndependentCoefficients J A)) :=
    inferInstanceAs (HasDerivedCategory.{d} (Modules A))
  obtain ⟨hl, hc, ho⟩ := sheafRingDerivedCoefficientAdjunction.{d, w, u, v} φ
  let : PreservesFiniteLimits (restriction A B α n) := hl
  let : PreservesFiniteColimits (restriction A B α n) := hc
  obtain ⟨a, ha, hd⟩ := ho s.E s.obj_eq s.map_eq
  obtain ⟨E₀, h₀, hm₀, hadd₀, _, hpw, LF, εh, huniv, _, _⟩ :=
    derivedChangeOfRingsIndependentCoefficients.{d} φ
  have he : E₀ = s.E := by
    refine CategoryTheory.Functor.ext (fun M ↦ (h₀ M).trans (s.obj_eq M).symm) ?_
    intro M N f
    rw [hm₀, s.map_eq]
    simp [φ]
  subst E₀
  let : LF.IsLeftDerivedFunctor εh (HomotopyCategory.quasiIso (Modules A) (.up ℤ)) :=
    huniv
  let : (s.E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Modules A) (.up ℤ)) := hpw
  obtain ⟨dh, hdh⟩ := hd LF εh huniv
  let q := HomotopyCategory.quotient (Modules A) (.up ℤ)
  let αh := (Functor.associator q DerivedCategory.Qh LF).hom ≫
    Functor.whiskerLeft q εh
  have hαh := pointwise_precomp_full q DerivedCategory.Qh
    (s.E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) LF εh
    (Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor LF εh
      (HomotopyCategory.quasiIso (Modules A) (.up ℤ)))
  let j : q ⋙ (s.E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ≅
      s.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (s.E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso (systemLevel B n))
  let β : DerivedCategory.Q ⋙ LF ⟶
      s.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso (Modules A)).inv LF ≫ αh ≫ j.hom
  have hβ := pointwise_change_iso LF (DerivedCategory.quotientCompQhIso (Modules A)) j
    αh hαh
  let : LF.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso (Modules A) (.up ℤ)) :=
    ⟨hβ.isRightKanExtension⟩
  let : s.T.IsLeftDerivedFunctor s.ε (HomologicalComplex.quasiIso (Modules A) (.up ℤ)) :=
    s.universal
  let c : LF ≅ s.T := Functor.leftDerivedUnique s.T LF β s.ε
    (HomologicalComplex.quasiIso (Modules A) (.up ℤ))
  refine ⟨hl, hc, a, dh.ofNatIsoLeft c, ?_, ?_⟩
  · intro M N f U x
    have h := ha M N (eqToHom (s.obj_eq M).symm ≫ f) U x
    have hf : eqToHom (s.obj_eq M) ≫ (eqToHom (s.obj_eq M).symm ≫ f) = f := by
      simp
    rw [hf] at h
    rw [tensorSection_one]
    exact h
  · intro Q hQ hflat
    refine ⟨s.computes Q hQ, ?_⟩
    intro K f
    refine ⟨?_, ?_⟩
    · rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
      have hcε : c.hom.app (DerivedCategory.Q.obj Q) ≫ s.ε.app Q = β.app Q := by
        simp [c]
      rw [← Category.assoc, hcε]
      obtain ⟨_, hu, _⟩ := hdh Q hQ hflat
      clear ho hd hdh
      change dh.unit.app (DerivedCategory.Q.obj Q) ≫
        (restriction A B α n).mapDerivedCategory.map (εh.app (q.obj Q)) ≫
        (restriction A B α n).mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient _ _).obj
            ((s.E.mapHomologicalComplex (.up ℤ)).obj Q)) = _ at hu
      rw [Functor.mapDerivedCategoryFactorsh_hom_app,
        Adjunction.mapHomotopyCategory_unit_app_quotient] at hu
      have hb : β.app Q = εh.app (q.obj Q) := by
        dsimp [β, αh, j]
        change LF.map (𝟙 _) ≫ (𝟙 _ ≫ εh.app (q.obj Q)) ≫
          𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ = _
        simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
        exact Category.comp_id (εh.app (q.obj Q))
      have hu' : dh.unit.app (DerivedCategory.Q.obj Q) ≫
          (restriction A B α n).mapDerivedCategory.map (β.app Q) ≫
          (restriction A B α n).mapDerivedCategoryFactors.hom.app
            ((s.E.mapHomologicalComplex (.up ℤ)).obj Q) =
          DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app Q) := by
        rw [hb]
        change _ ≫ _ ≫
          ((restriction A B α n).mapDerivedCategory.map (𝟙 _) ≫ _ ≫ 𝟙 _ ≫
            DerivedCategory.Qh.map (𝟙 _)) = _ at hu
        rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
          Category.id_comp, Category.comp_id, Category.comp_id] at hu
        exact hu
      apply (cancel_mono
        ((restriction A B α n).mapDerivedCategoryFactors.hom.app K)).1
      change (dh.unit.app _ ≫ (restriction A B α n).mapDerivedCategory.map
        (β.app Q ≫ DerivedCategory.Q.map f)) ≫ _ = _
      simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app]
      rw [(restriction A B α n).mapDerivedCategoryFactors_hom_naturality]
      rw [← Category.assoc, ← Category.assoc, Category.assoc (dh.unit.app _), hu']
      rw [← DerivedCategory.Q.map_comp]
      exact (Category.comp_id
        (DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv Q K f))).symm
    · intro i U x
      change (a.homEquiv (Q.X i) (K.X i) (f.f i)).val.app U x = _
      have h := ha (Q.X i) (K.X i)
        (eqToHom (s.obj_eq (Q.X i)).symm ≫ f.f i) U x
      have hf : eqToHom (s.obj_eq (Q.X i)) ≫
          (eqToHom (s.obj_eq (Q.X i)).symm ≫ f.f i) = f.f i := by simp
      rw [hf] at h
      rw [tensorSection_one]
      exact h

end SheafOfModules.SequenceProjection
