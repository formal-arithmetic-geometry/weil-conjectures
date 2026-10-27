/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Sheaf.Algebra.Homology.DerivedCoinductionAdjunction
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Algebra.Homology.KFlatTensorQuasiIso
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import Sheaf.Algebra.Homology.HomComplexGlobalHomotopyOfUniverses
import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal
import Sheaf.Algebra.Homology.EquivariantHomResolutionCalculus
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom

/-! # Mixed-ring chain currying and descent

Source: Stacks Project, dga.tex, Tag 09LN, differential graded tensor-Hom adjunction;
sites-cohomology.tex, Tags 0A95, 06YU and 08J7, for resolved-model descent.
(blueprint: lem-trf-bimodule-chain-currying-descent).

The B-complex J is presented by Hom_B(T,Coind(N)). Evaluation at one identifies
it with Hom_S(UT,N), with B acting by precomposition. The theorem includes that
identification, both currying formulas, both differential calculations, and the
comparison maps. The descended functors are characterized on EVERY K-flat/K-injective
model and EVERY chain map between such models. Thus their natural isomorphism is
an isomorphism on the derived categories, with all three variances, not just a
collection of isomorphisms on cohomology groups.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u wS wB

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct

namespace ModuleCat.BimoduleChainCurrying

/-- Integer cochain complexes of ordinary modules, with no boundedness restriction.
Source: Stacks 09LN (blueprint: lem-trf-bimodule-chain-currying-descent). -/
abbrev Complex (R : Type u) [CommRing R] := CochainComplex (ModuleCat.{u} R) ℤ

variable {S B : Type u} [CommRing S] [CommRing B]

/-- Exact restriction, applied degreewise to complexes.
Source: Stacks 09LN (blueprint: lem-trf-bimodule-chain-currying-descent). -/
abbrev U (φ : S →+* B) := (restrictScalars φ).mapHomologicalComplex (.up ℤ)

/-- A concrete coinduced presentation of J(T,N). Its evaluation-at-one identification
with Hom_S(UT,N), including the precomposition B-action, is part of the theorem.
Source: Stacks 09LN (blueprint: lem-trf-bimodule-chain-currying-descent). -/
abbrev J (φ : S →+* B) (T : Complex B) (N : Complex S) : Complex B :=
  CochainComplex.moduleHomComplex T ((coinductionComplexFunctor φ).obj N)

/-- The left product total Hom complex, retaining B-scalars until restriction.
Source: Stacks 09LN (blueprint: lem-trf-bimodule-chain-currying-descent). -/
abbrev left (φ : S →+* B) (A T : Complex B) (N : Complex S) : Complex S :=
  (U φ).obj (CochainComplex.moduleHomComplex A (J φ T N))

/-- Direct-sum total tensor, with the recorded sign on its second differential.
Source: Stacks 09LN (blueprint: lem-trf-bimodule-chain-currying-descent). -/
abbrev total (A T : Complex B) : Complex B :=
  CochainComplex.mapBifunctor A T (curriedTensor (ModuleCat.{u} B))

/-- The right product total Hom complex.
Source: Stacks 09LN (blueprint: lem-trf-bimodule-chain-currying-descent). -/
abbrev right (φ : S →+* B) (A T : Complex B) (N : Complex S) : Complex S :=
  CochainComplex.moduleHomComplex ((U φ).obj (total A T)) N

/-- The canonical homogeneous pure tensor in the direct-sum total complex.
Source: Stacks 09LN (blueprint: lem-trf-bimodule-chain-currying-descent). -/
def pure (A T : Complex B) (p q : ℤ) (a : A.X p) (t : T.X q) :
    (total A T).X (p + q) :=
  CochainComplex.ιMapBifunctor A T (curriedTensor (ModuleCat.{u} B))
    p q (p + q) rfl (a ⊗ₜ[B] t)

/-- Evaluate the coinduced presentation of J at one, on a homogeneous coordinate.
Source: Stacks 09LN (blueprint: lem-trf-bimodule-chain-currying-descent). -/
def valueJ (φ : S →+* B) (T : Complex B) (N : Complex S)
    (n q r : ℤ) (h : q + n = r) (z : (J φ T N).X n) (t : T.X q) : N.X r :=
  (coinductionEvaluation φ N).f r ((z.v q r h) t)

/-- Evaluate a left cochain on a homogeneous pair, without changing product support.
Source: Stacks 09LN (blueprint: lem-trf-bimodule-chain-currying-descent). -/
def valueLeft (φ : S →+* B) (A T : Complex B) (N : Complex S)
    (n p q r : ℤ) (h : p + q + n = r) (z : (left φ A T N).X n)
    (a : A.X p) (t : T.X q) : N.X r :=
  valueJ φ T N (p + n) q r (by omega) ((z.v p (p + n) rfl) a) t

/-- Evaluate a right cochain on the canonical total-tensor summand.
Source: Stacks 09LN (blueprint: lem-trf-bimodule-chain-currying-descent). -/
def valueRight (φ : S →+* B) (A T : Complex B) (N : Complex S)
    (n p q r : ℤ) (h : p + q + n = r) (z : (right φ A T N).X n)
    (a : A.X p) (t : T.X q) : N.X r :=
  (z.v (p + q) r h) (pure A T p q a t)

/-- The recorded K-flat predicate on ordinary module complexes.
Source: Stacks 064L (blueprint: lem-trf-bimodule-chain-currying-descent). -/
abbrev kFlat (T : Complex B) : Prop :=
  (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ)).kFlat T

variable [HasDerivedCategory.{wS} (ModuleCat.{u} S)]
  [HasDerivedCategory.{wB} (ModuleCat.{u} B)]

/-- The three derived variables, contravariant in A and T and covariant in N.
Source: Stacks 09LN, 04VG (blueprint: lem-trf-bimodule-chain-currying-descent). -/
abbrev DerivedTriple (S B : Type u) [CommRing S] [CommRing B]
    [HasDerivedCategory.{wS} (ModuleCat.{u} S)]
    [HasDerivedCategory.{wB} (ModuleCat.{u} B)] :=
  ((DerivedCategory (ModuleCat.{u} B))ᵒᵖ ×
    (DerivedCategory (ModuleCat.{u} B))ᵒᵖ) × DerivedCategory (ModuleCat.{u} S)

/-- The derived triple represented by three given complexes.
Source: Stacks 04VG (blueprint: lem-trf-bimodule-chain-currying-descent). -/
def triple (A T : Complex B) (N : Complex S) : DerivedTriple S B :=
  ((op (DerivedCategory.Q.obj A), op (DerivedCategory.Q.obj T)), DerivedCategory.Q.obj N)

/-- The derived triple map induced by three arbitrary chain maps.
Source: Stacks 04VG (blueprint: lem-trf-bimodule-chain-currying-descent). -/
def tripleMap {A A' T T' : Complex B} {N N' : Complex S}
    (α : A' ⟶ A) (β : T' ⟶ T) (γ : N ⟶ N') : triple A T N ⟶ triple A' T' N' :=
  ((DerivedCategory.Q.map α |>.op, DerivedCategory.Q.map β |>.op), DerivedCategory.Q.map γ)

/-- Entire mixed-ring chain currying, its signed differential, comparison squares,
and its unique natural descent to all derived morphisms.

Source: Stacks Project, dga.tex, Tag 09LN; sites-cohomology.tex, Tags 0A95, 0A8Z,
06YS, 06YU, 07A5 and 08J7; derived.tex, Tag 070I; categories.tex, Tag 04VG.
(blueprint: lem-trf-bimodule-chain-currying-descent).

Proof (the eleven steps of the node):
1. Coinduction evaluation at one identifies Hom_B(T,Coind(N)) with Hom_S(UT,N).
Its inverse sends h to (t ↦ (b ↦ h(bt))). Thus b acts by h(t) ↦ h(bt), and
commutes with both terms of the Hom differential. Evaluation f(a)(t) is additive
and balanced: f(ba)(t)=f(a)(bt). The tensor universal property gives its inverse.
2. Apply this bijection to every (p,q) in Z². A map out of each direct sum of
tensor summands is a family on its summands; reindex p+q=k. Both Hom terms are
products, with no finite-support restriction on their cochains.
3. Expand both differentials: the common value is d_N f(a)(t) minus
(-1)^(p+n) f(a)(d_T t) minus (-1)^n f(d_A a)(t). Equality on pure tensors and
every summand gives a chain isomorphism, with the stated componentwise inverse.
4. Both routes in a comparison square evaluate to γ(f(α(a'))(β(t'))).
Identity and composition are preserved by pre- and postcomposition.
5. For K-flat T,T', factor α tensor β through α tensor 1 and 1 tensor β.
The K-flat predicate handles the first map; lem-pc-kflat-tensor-quasi-iso and
the signed flip handle the second. Exact restriction preserves quasi-isomorphisms.
6. lem-pur-rhom-well-defined over the one-object S-site proves the right vertical
map a quasi-isomorphism. Conjugation by θ proves the left one is a quasi-isomorphism.
The same argument gives the B-linear J comparisons; restriction detects quasi-isos.
7. If T is K-flat and N is S-K-injective, J(T,N) is B-K-injective: test against an
acyclic B-complex F. F tensor T is acyclic, as is its restriction; its Hom into N
is acyclic by step 6. Currying and lem-pur-hom-complex-global-homotopy identify H⁰
with maps F → J modulo homotopy, so all such maps are null-homotopic.
8. lem-sfb-total-tensor-homotopy gives tensor on homotopy classes.
lem-sf-equivariant-hom-resolution-calculus gives Hom homotopies: source h acts by
(-1)^n f h, target h' by h'f. Restriction preserves these equations; θ conjugates
the right-side homotopies into left-side homotopies.
9. Flat-term K-flat homotopy models localize to D(B) by
lem-weil-pbc-site-derived-tensor-descent. K-injectives give D(S) by
lem-weil-pbc-kinjective-hom-derived and prop-pur-kinjective-resolutions-exist.
lem-pc-kflat-resolution compares every K-flat complex with a flat-term model.
10. Localize the values in D(S). Step 6 inverts quasi-isomorphisms in every variable.
Apply lem-weil-pbc-localization-universal-property successively in A and T, and the
K-injective equivalence in N. It descends θ uniquely to the natural isomorphism η.
Naturality for inverse quasi-isomorphisms follows by multiplying the square by
the two inverses. Identity and composition give every localized arrow. Comparison
with a flat-term resolution proves independence for every K-flat representative.
11. Resolve A and T by flat-term K-flats. The tensor comparisons of
lem-weil-pbc-site-derived-tensor-descent identify A tensor T with A tensor^L T.
def-pur-derived-internal-hom identifies Hom into N and, by step 7, Hom into J
with the two derived Homs. Uniqueness of descent supplies the compatible model
identifications eL,eR below, for every representative and arbitrary chain map.
At no point is restriction claimed to preserve K-injectivity. -/
theorem bimodule_chain_currying_descent (φ : S →+* B) :
    ∃ eJ : ∀ (T : Complex B) (N : Complex S),
        (U φ).obj (J φ T N) ≅ CochainComplex.moduleHomComplex ((U φ).obj T) N,
    ∃ θ : ∀ (A T : Complex B) (N : Complex S), left φ A T N ≅ right φ A T N,
    ∃ F G : DerivedTriple S B ⥤ DerivedCategory (ModuleCat.{u} S),
    ∃ η : F ≅ G,
    ∃ eL : ∀ (A T : Complex B) (N : Complex S), kFlat T → N.IsKInjective →
        (DerivedCategory.Q.obj (left φ A T N) ≅ F.obj (triple A T N)),
    ∃ eR : ∀ (A T : Complex B) (N : Complex S), kFlat T → N.IsKInjective →
        (DerivedCategory.Q.obj (right φ A T N) ≅ G.obj (triple A T N)),
      (∀ (T : Complex B) (N : Complex S) (n q r : ℤ) (h : q + n = r)
          (z : (J φ T N).X n) (t : T.X q),
        (((eJ T N).hom.f n z).v q r h) t = valueJ φ T N n q r h z t) ∧
      (∀ (T : Complex B) (N : Complex S) (n q r : ℤ) (h : q + n = r)
          (z : (J φ T N).X n) (b : B) (t : T.X q),
        valueJ φ T N n q r h (b • z) t = valueJ φ T N n q r h z (b • t)) ∧
      (∀ (A T : Complex B) (N : Complex S) (n p q r : ℤ) (h : p + q + n = r)
          (z : (left φ A T N).X n) (a : A.X p) (t : T.X q),
        valueRight φ A T N n p q r h ((θ A T N).hom.f n z) a t =
          valueLeft φ A T N n p q r h z a t) ∧
      (∀ (A T : Complex B) (N : Complex S) (n p q r : ℤ) (h : p + q + n = r)
          (z : (right φ A T N).X n) (a : A.X p) (t : T.X q),
        valueLeft φ A T N n p q r h ((θ A T N).inv.f n z) a t =
          valueRight φ A T N n p q r h z a t) ∧
      (∀ (A T : Complex B) (N : Complex S) (n p q : ℤ)
          (z : (left φ A T N).X n) (a : A.X p) (t : T.X q),
        valueRight φ A T N (n + 1) p q (p + q + (n + 1)) rfl
            ((right φ A T N).d n (n + 1) ((θ A T N).hom.f n z)) a t =
          N.d (p + q + n) (p + q + (n + 1))
              (valueLeft φ A T N n p q (p + q + n) rfl z a t) -
            (p + n).negOnePow • valueLeft φ A T N n p (q + 1)
              (p + q + (n + 1)) (by omega) z a (T.d q (q + 1) t) -
            n.negOnePow • valueLeft φ A T N n (p + 1) q
              (p + q + (n + 1)) (by omega) z (A.d p (p + 1) a) t) ∧
      (∀ (A T : Complex B) (N : Complex S) (n p q : ℤ)
          (z : (left φ A T N).X n) (a : A.X p) (t : T.X q),
        valueLeft φ A T N (n + 1) p q (p + q + (n + 1)) rfl
            ((left φ A T N).d n (n + 1) z) a t =
          N.d (p + q + n) (p + q + (n + 1))
              (valueLeft φ A T N n p q (p + q + n) rfl z a t) -
            (p + n).negOnePow • valueLeft φ A T N n p (q + 1)
              (p + q + (n + 1)) (by omega) z a (T.d q (q + 1) t) -
            n.negOnePow • valueLeft φ A T N n (p + 1) q
              (p + q + (n + 1)) (by omega) z (A.d p (p + 1) a) t) ∧
      (∀ (A A' T T' : Complex B) (N N' : Complex S)
          (α : A' ⟶ A) (β : T' ⟶ T) (γ : N ⟶ N'),
        ∃ (l : left φ A T N ⟶ left φ A' T' N')
          (r : right φ A T N ⟶ right φ A' T' N'),
          (∀ (n p q s : ℤ) (h : p + q + n = s)
              (z : (left φ A T N).X n) (a : A'.X p) (t : T'.X q),
            valueLeft φ A' T' N' n p q s h (l.f n z) a t =
              γ.f s (valueLeft φ A T N n p q s h z (α.f p a) (β.f q t))) ∧
          (∀ (n p q s : ℤ) (h : p + q + n = s)
              (z : (right φ A T N).X n) (a : A'.X p) (t : T'.X q),
            valueRight φ A' T' N' n p q s h (r.f n z) a t =
              γ.f s (valueRight φ A T N n p q s h z (α.f p a) (β.f q t))) ∧
          l ≫ (θ A' T' N').hom = (θ A T N).hom ≫ r ∧
          (kFlat T → kFlat T' → N.IsKInjective → N'.IsKInjective →
            QuasiIso α → QuasiIso β → QuasiIso γ → QuasiIso l ∧ QuasiIso r) ∧
          (∀ (hT : kFlat T) (hT' : kFlat T')
              (hN : N.IsKInjective) (hN' : N'.IsKInjective),
            DerivedCategory.Q.map l ≫ (eL A' T' N' hT' hN').hom =
                (eL A T N hT hN).hom ≫ F.map (tripleMap α β γ) ∧
            DerivedCategory.Q.map r ≫ (eR A' T' N' hT' hN').hom =
                (eR A T N hT hN).hom ≫ G.map (tripleMap α β γ))) ∧
      (∀ (A T : Complex B) (N : Complex S) (hT : kFlat T) (hN : N.IsKInjective),
        (eL A T N hT hN).hom ≫ η.hom.app (triple A T N) =
          DerivedCategory.Q.map (θ A T N).hom ≫ (eR A T N hT hN).hom) ∧
      (∀ η' : F ≅ G,
        (∀ (A T : Complex B) (N : Complex S) (hT : kFlat T) (hN : N.IsKInjective),
          (eL A T N hT hN).hom ≫ η'.hom.app (triple A T N) =
            DerivedCategory.Q.map (θ A T N).hom ≫ (eR A T N hT hN).hom) → η' = η) := by
  sorry

end ModuleCat.BimoduleChainCurrying
