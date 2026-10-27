module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.AlgebraicGeometry.Modules.DifferentialsSections
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap

/-!
# Smooth trait models and orders of volume forms

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, 1.1 Definition 2,
2.5 and 4.3, pp.103--106 (blueprint: def-sfb-trait-volume-models).
The pullback relation uses local sums of wedges of universal differentials, so no
unspecified differential comparison map is supplied as data.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory
namespace AlgebraicGeometry
namespace TraitVolume

/-- Top differential forms. Source: BLR 4.3 (blueprint: def-sfb-trait-volume-models). -/
noncomputable abbrev TopForms {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) : X.Modules :=
  Scheme.Modules.exteriorSheaf f.relativeDifferentials d

/-- A finite sum of wedges of differentials. Source: BLR 2.1 and 4.3
(blueprint: def-sfb-trait-volume-models). -/
noncomputable def expression {X S : Scheme.{u}} (f : X ⟶ S) (d n : ℕ) (U : X.Opens)
    (a : Fin n → Γ(X, U)) (b : Fin n → Fin d → Γ(X, U)) : Γ(TopForms f d, U) :=
  ∑ i, a i • Scheme.Modules.exteriorSheafSection f.relativeDifferentials d U
    (fun j ↦ f.relativeDifferentialsDerivation.d (X := op U) (b i j))

/-- Canonical pullback of a top form, expressed locally on generating wedges.
Source: BLR 2.1, differential pullback (blueprint: def-sfb-trait-volume-models).
The source base may differ, as in a cartesian base change or a relative translation. -/
def IsPullback {X S Y T : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ T)
    (q : Y ⟶ X) (d : ℕ) (ω : Γ(TopForms f d, ⊤))
    (ω' : Γ(TopForms g d, ⊤)) : Prop :=
  ∀ y : Y, ∃ (U : X.Opens) (V : Y.Opens) (_hy : y ∈ V)
    (h : V ≤ q ⁻¹ᵁ U) (n : ℕ) (a : Fin n → Γ(X, U))
    (b : Fin n → Fin d → Γ(X, U)),
    (TopForms f d).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ω =
      expression f d n U a b ∧
    (TopForms g d).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ω' =
      expression g d n V (fun i ↦ q.appLE U V h (a i))
        (fun i j ↦ q.appLE U V h (b i j))

/-- Fibrewise dense open. Source: BLR 2.5 (blueprint: def-sfb-trait-volume-models). -/
def IsBaseDense {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) : Prop :=
  ∀ s : S, Dense ((f.fiberι s) ⁻¹' (U : Set X))

/-- A smooth separated finite-type model with its specified generic identification.
Source: BLR 4.3 (blueprint: def-sfb-trait-volume-models). -/
structure Model {T K : Scheme.{u}} (j : K ⟶ T) (G : Over K) where
  scheme : Scheme.{u}
  hom : scheme ⟶ T
  smooth : Smooth hom
  finiteType : LocallyOfFiniteType hom
  quasiCompact : QuasiCompact hom
  separated : IsClosedImmersion (pullback.diagonal hom)
  genericIso : (Over.pullback j).obj (Over.mk hom) ≅ G

/-- Nonempty irreducible special fibre. Source: BLR 4.3
(blueprint: def-sfb-trait-volume-models). -/
def Model.Admissible {T K : Scheme.{u}} {j : K ⟶ T} {G : Over K}
    (M : Model j G) (s : T) : Prop := IrreducibleSpace (M.hom.fiber s)

/-- The generic identity extends to an isomorphism between fibrewise dense opens.
The common generic morphism is required to be defined on the entire generic fibre.
Source: BLR 4.3, equivalence of models (blueprint: def-sfb-trait-volume-models). -/
def Model.Equivalent {T K : Scheme.{u}} {j : K ⟶ T} {G : Over K}
    (M N : Model j G) : Prop :=
  ∃ (U : M.scheme.Opens) (V : N.scheme.Opens)
    (e : U.toScheme ≅ V.toScheme),
    IsBaseDense M.hom U ∧ IsBaseDense N.hom V ∧
    e.hom ≫ V.ι ≫ N.hom = U.ι ≫ M.hom ∧
    ∃ t : pullback M.hom j ⟶ U.toScheme,
      t ≫ U.ι = pullback.fst M.hom j ∧
      ∃ r : pullback N.hom j ⟶ V.toScheme,
        r ≫ V.ι = pullback.fst N.hom j ∧
        t ≫ e.hom = M.genericIso.hom.left ≫ N.genericIso.inv.left ≫ r

/-- Bounded points, using finite affine covers, generating lists and valuation lower bounds.
Multiplication by a power of the uniformizer replaces the inequality v(b) ≥ c by integrality.
Source: BLR 1.1 Definition 2 (blueprint: def-sfb-trait-volume-models). -/
def IsBounded {E F H : Type u} [Field E] [CommRing H] [Field F]
    (ι : E →+* F) (h : H →+* F) (π : H) (G : Over (Spec (.of E))) : Prop :=
  ∃ (r : ℕ) (U : Fin r → G.left.Opens),
    (∀ i, IsAffineOpen (U i)) ∧ (∀ x : G.left, ∃ i, x ∈ U i) ∧
    ∃ (n : Fin r → ℕ) (b : ∀ i, Fin (n i) → Γ(G.left, U i))
      (c : Fin r → ℤ),
      (∀ i, Subring.closure
        (Set.range (G.hom.specStructureMap (U i)).hom ∪ Set.range (b i)) = ⊤) ∧
      ∀ x : Spec (.of F) ⟶ G.left,
        x ≫ G.hom = Spec.map (CommRingCat.ofHom ι) →
        ∃ (i : Fin r) (y : Spec (.of F) ⟶ (U i).toScheme),
          y ≫ (U i).ι = x ∧ ∀ j : Fin (n i),
            ∃ a : H, h a = h π ^ (-c i) *
              (Scheme.ΓSpecIso (.of F)).hom
                (y.appTop ((U i).topIso.inv (b i j)))

/-- The order relation, using a genuine extension of the normalized generic volume form.
On a smooth model with irreducible special fibre the normalized form extends globally:
normality extends it across codimension at least two, and its divisor has no other
vertical component (BLR 4.3, paragraph before Lemma 1).
Source: BLR 4.3 pp.104--105 (blueprint: def-sfb-trait-volume-models). -/
def HasOrder {R E : Type u} [CommRing R] [IsLocalRing R] [Field E] [Algebra R E]
    (π : R) (G : Over (Spec (.of E))) (d : ℕ) (ω : Γ(TopForms G.hom d, ⊤))
    (M : Model (Spec.map (CommRingCat.ofHom (algebraMap R E))) G) (n : ℤ) : Prop :=
  ∃ (ζ : M.hom.fiber (IsLocalRing.closedPoint R))
    (ωE : Γ(TopForms ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R E)))).obj (Over.mk M.hom)).hom d, ⊤))
    (β : Γ(TopForms M.hom d, ⊤)),
    IsGenericPoint ζ (Set.univ : Set (M.hom.fiber (IsLocalRing.closedPoint R))) ∧
    IsPullback G.hom _ M.genericIso.hom.left d ω ωE ∧
    IsPullback M.hom _ (pullback.fst M.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R E)))) d β
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R E)))).obj
        (Over.mk M.hom)).hom.specStructureMap ⊤ (algebraMap R E π ^ (-n)) • ωE) ∧
    Scheme.Modules.GeneratesAt β
      (M.hom.fiberι (IsLocalRing.closedPoint R) ζ)

/-- Universal left invariance: multiplication and the second projection pull the form
back to the same relative form over the first factor.
Source: BLR 4.2 (blueprint: def-sfb-trait-volume-models). -/
def IsLeftInvariant {E : Type u} [Field E] (G : Over (Spec (.of E))) [GrpObj G]
    (d : ℕ) (ω : Γ(TopForms G.hom d, ⊤)) : Prop :=
  ∃ η : Γ(TopForms (fst G G).left d, ⊤),
    IsPullback G.hom (fst G G).left (MonObj.mul (X := G)).left d ω η ∧
    IsPullback G.hom (fst G G).left (snd G G).left d ω η

/-- Minimal order and its attainment. Source: BLR 4.3 Proposition 2(i)
(blueprint: def-sfb-trait-volume-models). -/
def IsMinimum {R E : Type u} [CommRing R] [IsLocalRing R] [Field E] [Algebra R E]
    (π : R) (G : Over (Spec (.of E))) (d : ℕ) (ω : Γ(TopForms G.hom d, ⊤))
    (n₀ : ℤ) : Prop :=
  (∃ M : Model (Spec.map (CommRingCat.ofHom (algebraMap R E))) G,
    M.Admissible (IsLocalRing.closedPoint R) ∧ HasOrder π G d ω M n₀) ∧
  ∀ M : Model (Spec.map (CommRingCat.ofHom (algebraMap R E))) G,
    M.Admissible (IsLocalRing.closedPoint R) →
      ∀ n : ℤ, HasOrder π G d ω M n → n₀ ≤ n

/-- A finite nonempty list of representatives for the minimal classes; the coverage
formulation permits repeated entries. Source: BLR 4.3 Proposition 2(ii)
(blueprint: def-sfb-trait-volume-models). -/
def Representatives {R E : Type u} [CommRing R] [IsLocalRing R] [Field E] [Algebra R E]
    (π : R) (G : Over (Spec (.of E))) (d : ℕ) (ω : Γ(TopForms G.hom d, ⊤))
    (n₀ : ℤ) (r : ℕ)
    (M : Fin r → Model (Spec.map (CommRingCat.ofHom (algebraMap R E))) G) : Prop :=
  0 < r ∧
  (∀ i, (M i).Admissible (IsLocalRing.closedPoint R) ∧ HasOrder π G d ω (M i) n₀) ∧
  ∀ N : Model (Spec.map (CommRingCat.ofHom (algebraMap R E))) G,
    N.Admissible (IsLocalRing.closedPoint R) → HasOrder π G d ω N n₀ →
      ∃ i, N.Equivalent (M i)

/-- Removing a closed nowhere dense subset of the special fibre, with the generic
identification unchanged. Source: BLR 4.3 Proposition 4, first paragraph
(blueprint: def-sfb-trait-volume-models). -/
def Model.IsShrinking {T K : Scheme.{u}} {j : K ⟶ T} {G : Over K}
    (N M : Model j G) (s : T) : Prop :=
  ∃ i : Over.mk N.hom ⟶ Over.mk M.hom, IsOpenImmersion i.left ∧
    Set.range (pullback.fst M.hom j) ⊆ Set.range i.left ∧
    Dense ((M.hom.fiberι s) ⁻¹' Set.range i.left) ∧
    (Over.pullback j).map i ≫ M.genericIso.hom = N.genericIso.hom

/-- A component open of a base-changed model, including the entire generic fibre and
respecting the fixed generic identification. The equations specify the canonical
comparison with the iterated generic fibre, without choosing an arbitrary map.
Source: BLR 4.3 Lemma 3 (blueprint: def-sfb-trait-volume-models). -/
def IsComponent {T K A L : Scheme.{u}} {j : K ⟶ T} {G : Over K}
    (b : A ⟶ T) (a : L ⟶ A) (c : L ⟶ K) (s : A)
    (M : Model j G) (P : Model a ((Over.pullback c).obj G))
    (C : Set ((pullback.snd M.hom b).fiber s)) : Prop :=
  C ∈ irreducibleComponents ((pullback.snd M.hom b).fiber s) ∧
  ∃ i : P.scheme ⟶ pullback M.hom b,
    IsOpenImmersion i ∧ i ≫ pullback.snd M.hom b = P.hom ∧
    Set.range (pullback.fst (pullback.snd M.hom b) a) ⊆ Set.range i ∧
    (pullback.snd M.hom b).fiberι s ⁻¹' Set.range i = C ∧
    ∃ q : pullback P.hom a ⟶ pullback M.hom j,
      q ≫ pullback.fst M.hom j =
        pullback.fst P.hom a ≫ i ≫ pullback.fst M.hom b ∧
      q ≫ pullback.snd M.hom j = pullback.snd P.hom a ≫ c ∧
      q ≫ M.genericIso.hom.left = P.genericIso.hom.left ≫ pullback.fst G.hom c

/-- All component opens are minimal, every component open is realized, and they cover
all minimal classes (with repetitions permitted).
Source: BLR 4.3 Lemma 3 (blueprint: def-sfb-trait-volume-models). -/
def ComponentRepresentatives {R E A L : Type u} [CommRing R] [Field E]
    [Algebra R E] [CommRing A] [IsLocalRing A] [Field L] [Algebra A L]
    (ρ : R →+* A) (c : E →+* L) (π : A) (G : Over (Spec (.of E)))
    (d : ℕ) (ω : Γ(TopForms ((Over.pullback (Spec.map (CommRingCat.ofHom c))).obj G).hom d, ⊤))
    (n₀ : ℤ) (r : ℕ)
    (M : Fin r → Model (Spec.map (CommRingCat.ofHom (algebraMap R E))) G) : Prop :=
  (∀ (i : Fin r) (C : Set ((pullback.snd (M i).hom (Spec.map (CommRingCat.ofHom ρ))).fiber
      (IsLocalRing.closedPoint A))),
    C ∈ irreducibleComponents ((pullback.snd (M i).hom (Spec.map (CommRingCat.ofHom ρ))).fiber
      (IsLocalRing.closedPoint A)) →
      ∃ P : Model (Spec.map (CommRingCat.ofHom (algebraMap A L)))
          ((Over.pullback (Spec.map (CommRingCat.ofHom c))).obj G),
        IsComponent (Spec.map (CommRingCat.ofHom ρ)) (Spec.map (CommRingCat.ofHom (algebraMap A L)))
          (Spec.map (CommRingCat.ofHom c)) (IsLocalRing.closedPoint A) (M i) P C) ∧
  (∀ (i : Fin r) (P : Model (Spec.map (CommRingCat.ofHom (algebraMap A L)))
      ((Over.pullback (Spec.map (CommRingCat.ofHom c))).obj G)) (C : Set
      ((pullback.snd (M i).hom (Spec.map (CommRingCat.ofHom ρ))).fiber
        (IsLocalRing.closedPoint A))),
    IsComponent (Spec.map (CommRingCat.ofHom ρ)) (Spec.map (CommRingCat.ofHom (algebraMap A L)))
      (Spec.map (CommRingCat.ofHom c)) (IsLocalRing.closedPoint A) (M i) P C →
      P.Admissible (IsLocalRing.closedPoint A) ∧
        HasOrder π ((Over.pullback (Spec.map (CommRingCat.ofHom c))).obj G) d ω P n₀) ∧
  ∀ P : Model (Spec.map (CommRingCat.ofHom (algebraMap A L)))
      ((Over.pullback (Spec.map (CommRingCat.ofHom c))).obj G),
    P.Admissible (IsLocalRing.closedPoint A) →
    HasOrder π ((Over.pullback (Spec.map (CommRingCat.ofHom c))).obj G) d ω P n₀ →
    ∃ (i : Fin r) (Q : Model (Spec.map (CommRingCat.ofHom (algebraMap A L)))
        ((Over.pullback (Spec.map (CommRingCat.ofHom c))).obj G)), ∃ C,
      IsComponent (Spec.map (CommRingCat.ofHom ρ)) (Spec.map (CommRingCat.ofHom (algebraMap A L)))
        (Spec.map (CommRingCat.ofHom c)) (IsLocalRing.closedPoint A) (M i) Q C ∧ P.Equivalent Q

/-- The canonical base-ring map into a scheme stalk.
Source: BLR 4.3 Lemma 3 (blueprint: def-sfb-trait-volume-models). -/
noncomputable def localMap {R : Type u} [CommRing R] {Z : Scheme.{u}}
    (f : Z ⟶ Spec (.of R)) (x : Z) : R →+* Z.presheaf.stalk x :=
  (Z.presheaf.Γgerm x).hom.comp (f.specStructureMap ⊤).hom

/-- Smooth local base-change and shrinking conclusions for a chosen representative list.
Source: BLR 4.3 Lemma 3 and Proposition 4 (blueprint: def-sfb-trait-volume-models). -/
def SmoothBaseChange {R E : Type u} [CommRing R] [IsLocalRing R] [Field E] [Algebra R E]
    (π : R) (G : Over (Spec (.of E))) (d : ℕ) (ω : Γ(TopForms G.hom d, ⊤))
    (n₀ : ℤ) (r : ℕ)
    (M : Fin r → Model (Spec.map (CommRingCat.ofHom (algebraMap R E))) G) : Prop :=
  ∀ (Z : Scheme.{u}) (f : Z ⟶ Spec (.of R)), Smooth f →
    LocallyOfFiniteType f → QuasiCompact f →
    ∀ ξ : f.fiber (IsLocalRing.closedPoint R),
      ξ ∈ genericPoints (f.fiber (IsLocalRing.closedPoint R)) →
      ∃ hD : IsDomain (Z.presheaf.stalk (f.fiberι (IsLocalRing.closedPoint R) ξ)),
        @IsDiscreteValuationRing (Z.presheaf.stalk
          (f.fiberι (IsLocalRing.closedPoint R) ξ)) _ hD ∧
        Irreducible (localMap f (f.fiberι (IsLocalRing.closedPoint R) ξ) π) ∧
        ∀ (L : Type u) [Field L]
          [Algebra (Z.presheaf.stalk (f.fiberι (IsLocalRing.closedPoint R) ξ)) L]
          [IsFractionRing (Z.presheaf.stalk (f.fiberι (IsLocalRing.closedPoint R) ξ)) L],
          ∃ c : E →+* L,
            (∀ a : R, c (algebraMap R E a) =
              algebraMap _ L (localMap f (f.fiberι (IsLocalRing.closedPoint R) ξ) a)) ∧
            ∃ ωL : Γ(TopForms ((Over.pullback (Spec.map (CommRingCat.ofHom c))).obj G).hom
                d, ⊤),
              IsPullback G.hom _ (pullback.fst G.hom (Spec.map (CommRingCat.ofHom c)))
                d ω ωL ∧
              IsMinimum (localMap f (f.fiberι (IsLocalRing.closedPoint R) ξ) π)
                ((Over.pullback (Spec.map (CommRingCat.ofHom c))).obj G) d ωL n₀ ∧
              ComponentRepresentatives
                (localMap f (f.fiberι (IsLocalRing.closedPoint R) ξ)) c
                (localMap f (f.fiberι (IsLocalRing.closedPoint R) ξ) π) G d ωL n₀ r M ∧
              ∀ N : Fin r → Model (Spec.map (CommRingCat.ofHom (algebraMap R E))) G,
                (∀ i, (N i).IsShrinking (M i) (IsLocalRing.closedPoint R)) →
                ComponentRepresentatives
                  (localMap f (f.fiberι (IsLocalRing.closedPoint R) ξ)) c
                  (localMap f (f.fiberι (IsLocalRing.closedPoint R) ξ) π) G d ωL n₀ r N

/-- The canonical map from an affine base into its geometric strict henselization.
Source: BLR 4.3 and Stacks 03Q9 (blueprint: def-sfb-trait-volume-models). -/
noncomputable def strictMap {R Ω : Type u} [CommRing R] [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of R)) : R →+* Scheme.strictHenselizationRing s :=
  (Scheme.ΓSpecIso (Scheme.strictHenselizationRing s)).hom.hom.comp
    ((Scheme.strictHenselizationStructuralMap s).specStructureMap ⊤).hom

end TraitVolume
end AlgebraicGeometry
