/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import Sheaf.CategoryTheory.PresheafBarResolutionData
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem

/-! # Scalar restriction and composition of normalized bar maps

Source: Stacks Project, Tags 08PG (`example-left-derived-colimits`) and 08PH
(`example-morphism-categories`), coefficientwise refinement
(blueprint: lem-trf-bar-scalar-restriction-coherence).

The bar objects are the already specified `PresheafBar.Resolution`. All new records
specify maps by their values on its actual direct-sum generators. No construction is
selected from a bare existence assertion. Derived comparisons retain the normalization
by the augmentation, the derived counit, and the coefficientwise colimit isomorphism.
-/

@[expose] public section

universe u v r s t wR wS wT wA wAR wAS

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.PresheafBar

/-- The scalar comparison, natural in the coefficient presheaf, including its augmentation.
Source: Stacks 08PG--08PH, coefficientwise refinement
(blueprint: lem-trf-bar-scalar-restriction-coherence). -/
structure ScalarComparison {E : Type u} [SmallCategory E]
    {R : Type r} {S : Type s} [CommRing R] [CommRing S]
    (A : Resolution.{u, v} E R) (B : Resolution.{u, v} E S) (ρ : R →+* S) where
  /-- The augmented presheaf-complex isomorphism. -/
  beta :
    (Functor.whiskeringRight Eᵒᵖ (ModuleCat.{max u v} S) (ModuleCat.{max u v} R)).obj
        (ModuleCat.restrictScalars ρ) ⋙ A.B ≅
      B.B ⋙ ((Functor.whiskeringRight Eᵒᵖ (ModuleCat.{max u v} S)
        (ModuleCat.{max u v} R)).obj
          (ModuleCat.restrictScalars ρ)).mapHomologicalComplex (.up ℤ)
  /-- The isomorphism of category bar complexes. -/
  kappa :
    (Functor.whiskeringRight Eᵒᵖ (ModuleCat.{max u v} S) (ModuleCat.{max u v} R)).obj
        (ModuleCat.restrictScalars ρ) ⋙ A.K ≅
      B.K ⋙ (ModuleCat.restrictScalars ρ).mapHomologicalComplex (.up ℤ)
  /-- Beta retains every chain, incoming arrow and coefficient. -/
  beta_generator : ∀ (H : Presheaves.{u, v} E S) (n : ℕ) (V : E)
      (c : ComposableArrows E n) (a : V ⟶ c.left) (x : H.obj (op c.right)),
    (((beta.hom.app H).f (-(n : ℤ))).app (op V))
        ((A.termIso (H ⋙ ModuleCat.restrictScalars ρ) n V).hom
          (ι (H ⋙ ModuleCat.restrictScalars ρ) n V c a x)) =
      (B.termIso H n V).hom (ι H n V c a x)
  /-- Kappa retains every chain and coefficient. -/
  kappa_generator : ∀ (H : Presheaves.{u, v} E S) (n : ℕ)
      (c : ComposableArrows E n) (x : H.obj (op c.right)),
    ((kappa.hom.app H).f (-(n : ℤ)))
        ((A.colimitTermIso (H ⋙ ModuleCat.restrictScalars ρ) n).hom
          (colimitι (H ⋙ ModuleCat.restrictScalars ρ) n c x)) =
      (B.colimitTermIso H n).hom (colimitι H n c x)
  /-- The isomorphism respects the augmentation to the restricted presheaf in degree zero. -/
  augmented : ∀ H : Presheaves.{u, v} E S,
    beta.hom.app H ≫
        (((Functor.whiskeringRight Eᵒᵖ (ModuleCat.{max u v} S)
          (ModuleCat.{max u v} R)).obj
            (ModuleCat.restrictScalars ρ)).mapHomologicalComplex (.up ℤ)).map (B.a.app H) ≫
        (HomologicalComplex.singleMapHomologicalComplex
          ((Functor.whiskeringRight Eᵒᵖ (ModuleCat.{max u v} S)
            (ModuleCat.{max u v} R)).obj (ModuleCat.restrictScalars ρ)) (.up ℤ) 0).hom.app H =
      A.a.app (H ⋙ ModuleCat.restrictScalars ρ)

/-- The scalar comparison exists for independently sized coefficient rings.
Source: Stacks 08PG--08PH (blueprint: lem-trf-bar-scalar-restriction-coherence).

Proof (node steps 1 and 2): Use the finite-support direct-sum identification on each
term of the two complexes; it is identity on every coefficient. Its inverse has
the same formula. Both commute with every face, restriction and augmentation,
and with coefficient maps, giving the two natural isomorphisms. -/
theorem exists_scalarComparison {E : Type u} [SmallCategory E]
    {R : Type r} {S : Type s} [CommRing R] [CommRing S]
    (A : Resolution.{u, v} E R) (B : Resolution.{u, v} E S) (ρ : R →+* S) :
    Nonempty (ScalarComparison A B ρ) := by
  sorry

/-- A semilinear bar map specified by the exact chain/coefficient formula.
Source: Stacks 08PH (blueprint: lem-trf-bar-scalar-restriction-coherence). -/
structure SemilinearMap {E D : Type u} [SmallCategory E] [SmallCategory D]
    {R : Type r} {S : Type s} [CommRing R] [CommRing S]
    (A : Resolution.{u, v} E R) (B : Resolution.{u, v} D S) (u : E ⥤ D) (ρ : R →+* S)
    {F : Presheaves.{u, v} E R} {G : Presheaves.{u, v} D S}
    (t : F ⟶ u.op ⋙ G ⋙ ModuleCat.restrictScalars ρ) where
  /-- The map is a morphism of cochain complexes, not just a graded map. -/
  map : A.K.obj F ⟶ ((ModuleCat.restrictScalars ρ).mapHomologicalComplex (.up ℤ)).obj
    (B.K.obj G)
  /-- Every chain is reindexed by u and its coefficient is mapped by t. -/
  formula : ∀ (n : ℕ) (c : ComposableArrows E n) (x : F.obj (op c.right)),
    ((map.f (-(n : ℤ)))) ((A.colimitTermIso F n).hom (colimitι F n c x)) =
      (B.colimitTermIso G n).hom (colimitι G n (c ⋙ u) (t.app (op c.right) x))

/-- Semilinear maps factor through same-ring reindexing and the scalar isomorphism.
Source: Stacks 08PG--08PH, node step 4
(blueprint: lem-trf-bar-scalar-restriction-coherence).

Proof: Extend (c,x) ↦ (u(c),t(x)) linearly over the finite-support direct sum.
If chains merge, add their coefficients. Internal faces commute by functoriality;
the terminal face commutes by naturality of t. Thus it is a chain map. The scalar
comparison fixes coefficients, so its composite with the same-ring map has exactly
the prescribed formula. Positive degrees are zero in both complexes. -/
theorem exists_semilinearMap_factorization
    {E D : Type u} [SmallCategory E] [SmallCategory D]
    {R : Type r} {S : Type s} [CommRing R] [CommRing S]
    (A : Resolution.{u, v} E R) (B : Resolution.{u, v} D S)
    (C : Resolution.{u, v} D R) (u : E ⥤ D) (ρ : R →+* S)
    {F : Presheaves.{u, v} E R} {G : Presheaves.{u, v} D S}
    (t : F ⟶ u.op ⋙ G ⋙ ModuleCat.restrictScalars ρ) (k : ScalarComparison C B ρ) :
    ∃ f : SemilinearMap A B u ρ t,
      ∃ g : SemilinearMap A C u (RingHom.id R) t,
        f.map = g.map ≫ k.kappa.hom.app G := by
  sorry

/-- Composition agrees exactly with the single map for the composite data.
Source: Stacks 08PH, node step 5
(blueprint: lem-trf-bar-scalar-restriction-coherence).

Proof: On a generator both sides send (c,x) to (v(u(c)),s(t(x))). Semilinearity
is σ(ρ(a)) on both sides. The iterated restriction identification fixes the
underlying group. Finite-support additivity proves equality in negative degrees,
and the zero positive terms prove the other degrees. Nonfaithful reindexings
cause sums over identical target chains, which are the same finite sums. -/
theorem semilinearMap_composition
    {E D J : Type u} [SmallCategory E] [SmallCategory D] [SmallCategory J]
    {R : Type r} {S : Type s} {T : Type t} [CommRing R] [CommRing S] [CommRing T]
    (A : Resolution.{u, v} E R) (B : Resolution.{u, v} D S)
    (C : Resolution.{u, v} J T) (u : E ⥤ D) (v : D ⥤ J)
    (ρ : R →+* S) (σ : S →+* T)
    {F : Presheaves.{u, v} E R} {G : Presheaves.{u, v} D S} {H : Presheaves.{u, v} J T}
    (t : F ⟶ u.op ⋙ G ⋙ ModuleCat.restrictScalars ρ)
    (s : G ⟶ v.op ⋙ H ⋙ ModuleCat.restrictScalars σ)
    (a : F ⟶ (u ⋙ v).op ⋙ H ⋙ ModuleCat.restrictScalars (σ.comp ρ))
    (f : SemilinearMap A B u ρ t) (g : SemilinearMap B C v σ s)
    (h : SemilinearMap A C (u ⋙ v) (σ.comp ρ) a)
    (ha : ∀ (U : Eᵒᵖ) (x : F.obj U), a.app U x = s.app (u.op.obj U) (t.app U x)) :
    ∀ (i : ℤ) (x : (A.K.obj F).X i),
      (h.map.f i) x = (g.map.f i) ((f.map.f i) x) := by
  sorry

/-- Identity data give the identity map, including all positive degrees.
Source: Stacks 08PH, node step 5
(blueprint: lem-trf-bar-scalar-restriction-coherence).

Proof: The generator formula fixes each chain and its coefficient. Extend by
additivity to the whole direct sum. Positive-degree terms are zero. -/
theorem semilinearMap_identity
    {E : Type u} [SmallCategory E] {R : Type r} [CommRing R]
    (A : Resolution.{u, v} E R) (F : Presheaves.{u, v} E R)
    (f : SemilinearMap A A (𝟭 E) (RingHom.id R) (𝟙 F)) :
    ∀ (i : ℤ) (x : (A.K.obj F).X i), (f.map.f i) x = x := by
  sorry

/-- Both scalar isomorphisms compose by the usual iterated restriction identification.
Source: Stacks 08PG--08PH, node step 5
(blueprint: lem-trf-bar-scalar-restriction-coherence).

Proof: The beta and kappa formulas fix every chain, arrow and coefficient. Hence
the two composites agree on every summand. Their actions are both σ(ρ(a)), and
positive-degree terms are zero. This proves both equalities in every degree. -/
theorem scalarComparison_composition
    {E : Type u} [SmallCategory E]
    {R : Type r} {S : Type s} {T : Type t} [CommRing R] [CommRing S] [CommRing T]
    (A : Resolution.{u, v} E R) (B : Resolution.{u, v} E S)
    (C : Resolution.{u, v} E T) (ρ : R →+* S) (σ : S →+* T)
    (k : ScalarComparison A B ρ) (l : ScalarComparison B C σ)
    (m : ScalarComparison A C (σ.comp ρ)) :
    (∀ (H : Presheaves.{u, v} E T) (i : ℤ) (V : E)
      (x : ((A.B.obj (H ⋙ ModuleCat.restrictScalars (σ.comp ρ))).X i).obj (op V)),
      (((m.beta.hom.app H).f i).app (op V)) x =
        (((l.beta.hom.app H).f i).app (op V))
          ((((k.beta.hom.app (H ⋙ ModuleCat.restrictScalars σ)).f i).app (op V)) x)) ∧
    (∀ (H : Presheaves.{u, v} E T) (i : ℤ)
      (x : (A.K.obj (H ⋙ ModuleCat.restrictScalars (σ.comp ρ))).X i),
      ((m.kappa.hom.app H).f i) x =
        ((l.kappa.hom.app H).f i)
          (((k.kappa.hom.app (H ⋙ ModuleCat.restrictScalars σ)).f i) x)) := by
  sorry

attribute [instance] Resolution.quasiIso

/-- A total derived colimit with its assumed, augmentation-normalized bar comparison.
The pointwise condition retains the everywhere-defined total derived functor.
Source: Stacks 08PG, normalized comparison hypothesis
(blueprint: lem-trf-bar-scalar-restriction-coherence). -/
structure NormalizedModel {E : Type u} [SmallCategory E]
    {R : Type r} [CommRing R] (B : Resolution.{u, v} E R)
    [HasDerivedCategory.{wA} (Presheaves.{u, v} E R)]
    [HasDerivedCategory.{wR} (ModuleCat.{max u v} R)] where
  /-- Additivity of the ordinary colimit functor. -/
  [colimitAdditive : (C (E := E) (R := R)).Additive]
  /-- Total left-derived colimit. -/
  LC : DerivedCategory (Presheaves.{u, v} E R) ⥤ DerivedCategory (ModuleCat.{max u v} R)
  /-- Its canonical counit on cochain complexes. -/
  epsilon : DerivedCategory.Q ⋙ LC ⟶
    (C (E := E) (R := R)).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  /-- The left-derived universal property. -/
  universal : LC.IsLeftDerivedFunctor epsilon
    (HomologicalComplex.quasiIso (Presheaves.{u, v} E R) (.up ℤ))
  /-- The Stacks denominator pro-diagram is essentially constant at every object. -/
  defined : ∀ X : HomotopyCategory (Presheaves.{u, v} E R) (.up ℤ),
    IsEssentiallyConstantProDiagram
      (MorphismProperty.Over.forget
        (HomotopyCategory.quasiIso (Presheaves.{u, v} E R) (.up ℤ)) ⊤ X ⋙
        Over.forget X ⋙ (C (E := E) (R := R)).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh) (LC.obj (DerivedCategory.Qh.obj X))
  /-- Termwise left acyclicity is invertibility of the canonical single-object comparison. -/
  acyclic : ∀ (F : Presheaves.{u, v} E R) (i : ℤ),
    IsIso (epsilon.app ((CochainComplex.singleFunctor _ 0).obj ((B.B.obj F).X i)))
  /-- The assumed normalized natural bar comparison. -/
  m : CochainComplex.singleFunctor (Presheaves.{u, v} E R) 0 ⋙ DerivedCategory.Q ⋙ LC ≅
    B.K ⋙ DerivedCategory.Q
  /-- In diagrammatic order: LC(Qa) inverse, then epsilon, then Q(b). -/
  normalization : ∀ F : Presheaves.{u, v} E R,
    m.hom.app F = inv (LC.map (DerivedCategory.Q.map (B.a.app F))) ≫
      epsilon.app (B.B.obj F) ≫ DerivedCategory.Q.map (B.b.hom.app F)

/-- The uniquely normalized derived scalar comparison, natural in H.
Source: Stacks 08PG--08PH, normalized scalar refinement
(blueprint: lem-trf-bar-scalar-restriction-coherence).

Proof (node step 3): Exact restriction induces `mapDerivedCategory`, with its
localization identification `mapDerivedCategoryFactors`. Set alpha to m_R followed
by Q(kappa), the inverse localization identification, and Dr(m_S inverse).
All factors are invertible. This gives the displayed normalization, and cancellation
of Dr(m_S) and the localization identification proves uniqueness. Naturality follows
from the naturality of m_R, m_S and kappa; the normalization of m is the assumed
Q(b) epsilon LC(Qa) inverse formula. No projective preservation is used. -/
theorem exists_unique_derivedScalarComparison
    {E : Type u} [SmallCategory E] {R : Type r} {S : Type s}
    [CommRing R] [CommRing S]
    [HasDerivedCategory.{wAR} (Presheaves.{u, v} E R)]
    [HasDerivedCategory.{wAS} (Presheaves.{u, v} E S)]
    [HasDerivedCategory.{wR} (ModuleCat.{max u v} R)]
    [HasDerivedCategory.{wS} (ModuleCat.{max u v} S)]
    (A : Resolution.{u, v} E R) (B : Resolution.{u, v} E S)
    (M : NormalizedModel A) (N : NormalizedModel B) (ρ : R →+* S)
    (k : ScalarComparison A B ρ) :
    ∃! alpha :
      (Functor.whiskeringRight Eᵒᵖ (ModuleCat.{max u v} S) (ModuleCat.{max u v} R)).obj
          (ModuleCat.restrictScalars ρ) ⋙ CochainComplex.singleFunctor _ 0 ⋙
            DerivedCategory.Q ⋙ M.LC ≅
        CochainComplex.singleFunctor _ 0 ⋙ DerivedCategory.Q ⋙ N.LC ⋙
          (ModuleCat.restrictScalars.{max u v} ρ).mapDerivedCategory,
      ∀ H : Presheaves.{u, v} E S,
        alpha.hom.app H ≫
            (ModuleCat.restrictScalars.{max u v} ρ).mapDerivedCategory.map (N.m.hom.app H) ≫
            (ModuleCat.restrictScalars.{max u v} ρ).mapDerivedCategoryFactors.hom.app (B.K.obj H) =
          M.m.hom.app (H ⋙ ModuleCat.restrictScalars ρ) ≫
            DerivedCategory.Q.map (k.kappa.hom.app H) := by
  sorry

/-- Conjugate a chain map by its two specified derived comparison isomorphisms.
Source: Stacks 08PG--08PH, the normalized map formula
(blueprint: lem-trf-bar-scalar-restriction-coherence). -/
noncomputable def normalizedMap
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {K L : CochainComplex A ℤ} {X Y : DerivedCategory A}
    (m : X ≅ DerivedCategory.Q.obj K) (n : Y ≅ DerivedCategory.Q.obj L) (f : K ⟶ L) :
    X ⟶ Y := m.hom ≫ DerivedCategory.Q.map f ≫ n.inv

/-- Normalized maps preserve composition and identity; this applies in particular to
semilinear bar maps after the usual iterated scalar-restriction identification.
Source: Stacks 08PG--08PH, node step 6
(blueprint: lem-trf-bar-scalar-restriction-coherence).

Proof: Expand the three normalized maps. Functoriality of Q and associativity
reduce the composite to cancellation of n inverse followed by n. For the identity,
Q sends the identity to the identity and m followed by m inverse cancels.
Apply this to the chain identities from `semilinearMap_composition`. -/
theorem normalizedMap_coherence
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {K L P : CochainComplex A ℤ} {X Y Z : DerivedCategory A}
    (m : X ≅ DerivedCategory.Q.obj K) (n : Y ≅ DerivedCategory.Q.obj L)
    (p : Z ≅ DerivedCategory.Q.obj P) (f : K ⟶ L) (g : L ⟶ P) :
    normalizedMap m n f ≫ normalizedMap n p g = normalizedMap m p (f ≫ g) ∧
      normalizedMap m m (𝟙 K) = 𝟙 X := by
  sorry

/-- Exact scalar restriction respects normalized derived maps, using the canonical
localization identification. Together with normalized composition this gives the
iterated-scalar formula for alpha and every semilinear map, without any flatness.
Source: Stacks 08PG--08PH, node steps 3 and 6
(blueprint: lem-trf-bar-scalar-restriction-coherence).

Proof: Expand normalizedMap, use functoriality and naturality of
mapDerivedCategoryFactors, and cancel its inverse with its hom. Apply the preceding
composition identity to the restricted second map and first map. Their chain
composite is the coefficient formula s(t(x)) in `semilinearMap_composition`.
For kappa this gives Dr_rho(alpha_sigma) alpha_rho = alpha_(sigma rho);
for identity data it gives m inverse Q(1) m = 1. -/
theorem normalizedMap_restrictScalars
    {R : Type r} {S : Type s} [CommRing R] [CommRing S]
    [HasDerivedCategory.{wR} (ModuleCat.{v} R)]
    [HasDerivedCategory.{wS} (ModuleCat.{v} S)]
    (ρ : R →+* S) {K L : CochainComplex (ModuleCat.{v} S) ℤ}
    {X Y : DerivedCategory (ModuleCat.{v} S)}
    (m : X ≅ DerivedCategory.Q.obj K) (n : Y ≅ DerivedCategory.Q.obj L) (f : K ⟶ L) :
    (ModuleCat.restrictScalars.{v} ρ).mapDerivedCategory.map (normalizedMap m n f) =
      normalizedMap
        ((ModuleCat.restrictScalars.{v} ρ).mapDerivedCategory.mapIso m ≪≫
          (ModuleCat.restrictScalars.{v} ρ).mapDerivedCategoryFactors.app K)
        ((ModuleCat.restrictScalars.{v} ρ).mapDerivedCategory.mapIso n ≪≫
          (ModuleCat.restrictScalars.{v} ρ).mapDerivedCategoryFactors.app L)
        (((ModuleCat.restrictScalars ρ).mapHomologicalComplex (.up ℤ)).map f) := by
  sorry

/-- The semilinear normalized derived map, with the localization identification
written out. Source: Stacks 08PG--08PH, normalized comparison formula
(blueprint: lem-trf-bar-scalar-restriction-coherence). -/
noncomputable def scalarNormalizedMap
    {R : Type r} {S : Type s} [CommRing R] [CommRing S]
    [HasDerivedCategory.{wR} (ModuleCat.{v} R)]
    [HasDerivedCategory.{wS} (ModuleCat.{v} S)] (ρ : R →+* S)
    {K : CochainComplex (ModuleCat.{v} R) ℤ} {L : CochainComplex (ModuleCat.{v} S) ℤ}
    {X : DerivedCategory (ModuleCat.{v} R)} {Y : DerivedCategory (ModuleCat.{v} S)}
    (m : X ≅ DerivedCategory.Q.obj K) (n : Y ≅ DerivedCategory.Q.obj L)
    (f : K ⟶ ((ModuleCat.restrictScalars.{v} ρ).mapHomologicalComplex (.up ℤ)).obj L) :
    X ⟶ (ModuleCat.restrictScalars.{v} ρ).mapDerivedCategory.obj Y :=
  m.hom ≫ DerivedCategory.Q.map f ≫
    (ModuleCat.restrictScalars.{v} ρ).mapDerivedCategoryFactors.inv.app L ≫
    (ModuleCat.restrictScalars.{v} ρ).mapDerivedCategory.map n.inv

/-- The explicit derived composition identity in the iterated-restriction identification.
It applies to the semilinear maps and, in particular, to the scalar isomorphisms above.
Source: Stacks 08PG--08PH, node step 6
(blueprint: lem-trf-bar-scalar-restriction-coherence).

Proof: Substitute scalarNormalizedMap twice. Naturality of the localization
identification moves Q of the restricted second map through it. The middle factors
Dr_rho(n inverse) and Dr_rho(n) cancel, leaving exactly the right-hand composite.
`semilinearMap_composition` identifies its chain map with the single map for the
composite ring homomorphism and functor. The theorem scalarComparison_composition
gives scalar coherence;
normalizedMap_coherence gives the identity case. -/
theorem scalarNormalizedMap_composition
    {R : Type r} {S : Type s} {T : Type t} [CommRing R] [CommRing S] [CommRing T]
    [HasDerivedCategory.{wR} (ModuleCat.{v} R)]
    [HasDerivedCategory.{wS} (ModuleCat.{v} S)]
    [HasDerivedCategory.{wT} (ModuleCat.{v} T)] (ρ : R →+* S) (σ : S →+* T)
    {K : CochainComplex (ModuleCat.{v} R) ℤ} {L : CochainComplex (ModuleCat.{v} S) ℤ}
    {P : CochainComplex (ModuleCat.{v} T) ℤ}
    {X : DerivedCategory (ModuleCat.{v} R)} {Y : DerivedCategory (ModuleCat.{v} S)}
    {Z : DerivedCategory (ModuleCat.{v} T)}
    (m : X ≅ DerivedCategory.Q.obj K) (n : Y ≅ DerivedCategory.Q.obj L)
    (p : Z ≅ DerivedCategory.Q.obj P)
    (f : K ⟶ ((ModuleCat.restrictScalars.{v} ρ).mapHomologicalComplex (.up ℤ)).obj L)
    (g : L ⟶ ((ModuleCat.restrictScalars.{v} σ).mapHomologicalComplex (.up ℤ)).obj P) :
    scalarNormalizedMap ρ m n f ≫
        (ModuleCat.restrictScalars.{v} ρ).mapDerivedCategory.map
          (scalarNormalizedMap σ n p g) =
      scalarNormalizedMap ρ m
        ((ModuleCat.restrictScalars.{v} σ).mapDerivedCategory.mapIso p ≪≫
          (ModuleCat.restrictScalars.{v} σ).mapDerivedCategoryFactors.app P)
        (f ≫ ((ModuleCat.restrictScalars.{v} ρ).mapHomologicalComplex (.up ℤ)).map g) := by
  sorry

/-- Exact restriction preserves the cone roof, its signed right arrow and its
quasi-isomorphism denominator. The second conjunct gives the connecting-map equation.
Source: Stacks 08PG--08PH, node steps 1 and 7
(blueprint: lem-trf-bar-scalar-restriction-coherence).

Proof: Kernels, images and cokernels retain their abelian groups under restriction,
so restriction is exact and preserves quasi-isomorphisms. In each cone degree,
the direct-sum comparison is identity on the two coordinates. It carries the
matrix differential (d_B, i; 0, -d_A) to the identical matrix, and carries the
signed cone projection to the signed projection after restriction and shift.
Thus the entire roof is preserved. Applying localization, inverting the preserved
denominator, and using mapDerivedCategoryFactors gives the connecting-map equation.
The coordinatewise cone map for a morphism of sequences is unchanged as well. -/
theorem restriction_preserves_cone_roofs
    {R : Type r} {S : Type s} [CommRing R] [CommRing S]
    [HasDerivedCategory.{wR} (ModuleCat.{v} R)]
    [HasDerivedCategory.{wS} (ModuleCat.{v} S)] (ρ : R →+* S) :
    (∀ {A B C : CochainComplex (ModuleCat.{v} S) ℤ} (i : A ⟶ B)
      (q : CochainComplex.mappingCone i ⟶ C), QuasiIso q →
      QuasiIso (((ModuleCat.restrictScalars ρ).mapHomologicalComplex (.up ℤ)).map q) ∧
        ((ModuleCat.restrictScalars ρ).mapHomologicalComplex (.up ℤ)).map
            (CochainComplex.mappingCone.triangle i).mor₃ ≫
            (((ModuleCat.restrictScalars ρ).mapHomologicalComplex (.up ℤ)).commShiftIso
              (1 : ℤ)).hom.app A =
          (CochainComplex.mappingCone.mapHomologicalComplexIso i
            (ModuleCat.restrictScalars ρ)).hom ≫
              (CochainComplex.mappingCone.triangle
                (((ModuleCat.restrictScalars ρ).mapHomologicalComplex (.up ℤ)).map i)).mor₃) ∧
    (∀ (A : ShortComplex (CochainComplex (ModuleCat.{v} S) ℤ))
      (h : A.ShortExact),
      (ModuleCat.restrictScalars.{v} ρ).mapDerivedCategory.map
          (DerivedCategory.triangleOfSESδ h) ≫
          ((ModuleCat.restrictScalars.{v} ρ).mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
            (DerivedCategory.Q.obj A.X₁) ≫
          ((ModuleCat.restrictScalars.{v} ρ).mapDerivedCategoryFactors.hom.app A.X₁)
            ⟦(1 : ℤ)⟧' =
        (ModuleCat.restrictScalars.{v} ρ).mapDerivedCategoryFactors.hom.app A.X₃ ≫
          DerivedCategory.triangleOfSESδ
            (h.map_of_exact ((ModuleCat.restrictScalars ρ).mapHomologicalComplex (.up ℤ)))) := by
  sorry

end CategoryTheory.PresheafBar
