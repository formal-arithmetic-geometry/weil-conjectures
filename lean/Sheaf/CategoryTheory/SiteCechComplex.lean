/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Category.Grp.AB

/-!
# Čech complexes of coverings on a site

Source: Stacks Project, Cohomology on Sites, Tags 03AK, 03AM, 03AO, 03AQ
(blueprint: def-weil-pbc-site-cech-complex).

`SiteCechComplex` records the chosen fibre products, including their universal properties.
Its `complexFunctor` constructs the alternating restriction complex; `cohomologyFunctor`
is its cohomology. Only verification proofs are postponed, never the differential or maps.
-/

universe u v w r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Chosen iterated fibre products and index maps for a family over `U`.
The universal properties characterize the choices; the degree-zero choice is the original
object. Source: Stacks 03AK, 03AM (blueprint: def-weil-pbc-site-cech-complex). -/
structure SiteCechComplex {C : Type u} [Category.{v} C] {T : Type w} {U : C}
    (f : T → C) (hom : ∀ t, f t ⟶ U) where
  W : ∀ p : ℕ, (Fin (p + 1) → T) → C
  pr : ∀ (p : ℕ) (t : Fin (p + 1) → T) (k : Fin (p + 1)), W p t ⟶ f (t k)
  comm : ∀ (p : ℕ) (t : Fin (p + 1) → T) (k : Fin (p + 1)),
    pr p t k ≫ hom (t k) = pr p t 0 ≫ hom (t 0)
  universal : ∀ (p : ℕ) (t : Fin (p + 1) → T) (Z : C)
    (a : ∀ k, Z ⟶ f (t k)),
    (∀ k, a k ≫ hom (t k) = a 0 ≫ hom (t 0)) →
    ∃! b : Z ⟶ W p t, ∀ k, b ≫ pr p t k = a k
  W_zero : ∀ t, W 0 t = f (t 0)
  pr_zero : ∀ t, pr 0 t 0 = eqToHom (W_zero t)
  indexMap : ∀ {p q : ℕ} (t : Fin (p + 1) → T) (α : Fin (q + 1) → Fin (p + 1)),
    W p t ⟶ W q (t ∘ α)
  indexMap_pr : ∀ {p q : ℕ} (t : Fin (p + 1) → T) (α : Fin (q + 1) → Fin (p + 1))
    (k : Fin (q + 1)), indexMap t α ≫ pr q (t ∘ α) k = pr p t (α k)

namespace SiteCechComplex

variable {C : Type u} [Category.{v} C] {T : Type w} {U : C}
  {f : T → C} {hom : ∀ t, f t ⟶ U}

/-- A covering admits all the chosen fibre products and index maps.
Source: Stacks Sites 00VH(3), Cohomology on Sites 03AK, 03AM.
Proof: induct on the number of factors. In degree zero take `f (t 0)` and its identity.
Pull back the last covering arrow along the common map of the previous product to `U`.
Its universal property together with the induction hypothesis gives existence and uniqueness
for the enlarged tuple. Choose the products simultaneously. Each index map is the unique
map to the target product with components `pr (α k)`; their composites to `U` agree.
(blueprint: def-weil-pbc-site-cech-complex) -/
theorem exists_of_covering (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (hcover : Presieve.ofArrows f hom ∈ J U) : Nonempty (SiteCechComplex f hom) := by
  sorry

variable (S : SiteCechComplex f hom)

/-- Any two chosen products have exactly one projection-compatible isomorphism.
Source: Stacks 03AK, 03AM.
Proof: each universal property gives a unique map to the other product. Each composite
has the same projections as the identity, so equals the identity by uniqueness. Any
other compatible isomorphism has the same forward map, hence is the same isomorphism.
(blueprint: def-weil-pbc-site-cech-complex) -/
theorem fibreIso_exists_unique (S' : SiteCechComplex f hom) (p : ℕ)
    (t : Fin (p + 1) → T) :
    ∃! e : S.W p t ≅ S'.W p t, ∀ k, e.hom ≫ S'.pr p t k = S.pr p t k := by
  sorry

/-- The product of presheaf sections in degree `p`, with componentwise group operations.
Source: Stacks 03AK, 03AM (blueprint: def-weil-pbc-site-cech-complex). -/
def cochains (F : Cᵒᵖ ⥤ AddCommGrpCat.{r}) (p : ℕ) : AddCommGrpCat.{max r w} :=
  AddCommGrpCat.of (∀ t : Fin (p + 1) → T, F.obj (op (S.W p t)))

/-- The alternating restriction formula, omitting the `j`th factor via `Fin.succAbove`.
Source: Stacks 03AL (blueprint: def-weil-pbc-site-cech-complex). -/
noncomputable def differentialValue (F : Cᵒᵖ ⥤ AddCommGrpCat.{r}) (p : ℕ)
    (s : S.cochains F p) : S.cochains F (p + 1) :=
  fun t ↦ ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
    (F.map (S.indexMap t j.succAbove).op) (s (t ∘ j.succAbove))

/-- The differential preserves zero. Source: Stacks 03AL.
Proof: every restriction homomorphism takes zero to zero; every signed summand is zero.
(blueprint: def-weil-pbc-site-cech-complex) -/
theorem differentialValue_zero (F : Cᵒᵖ ⥤ AddCommGrpCat.{r}) (p : ℕ) :
    S.differentialValue F p 0 = 0 := by
  sorry

/-- The differential preserves addition. Source: Stacks 03AL.
Proof: distribute each restriction homomorphism and integer scalar multiplication over
addition, then distribute the finite sum, componentwise.
(blueprint: def-weil-pbc-site-cech-complex) -/
theorem differentialValue_add (F : Cᵒᵖ ⥤ AddCommGrpCat.{r}) (p : ℕ)
    (s t : S.cochains F p) :
    S.differentialValue F p (s + t) = S.differentialValue F p s +
      S.differentialValue F p t := by
  sorry

/-- The differential as an actual group homomorphism.
Source: Stacks 03AL (blueprint: def-weil-pbc-site-cech-complex). -/
noncomputable def differential (F : Cᵒᵖ ⥤ AddCommGrpCat.{r}) (p : ℕ) :
    S.cochains F p ⟶ S.cochains F (p + 1) :=
  AddCommGrpCat.ofHom
    { toFun := S.differentialValue F p
      map_zero' := S.differentialValue_zero F p
      map_add' := S.differentialValue_add F p }

/-- Consecutive differentials compose to zero. Source: Stacks 03AK after equation 03AL.
Proof: expand the double sum. Index maps compose as maps of finite sets, by the universal
property of the target product. For `i ≤ j`, the injections omitting `i` then `j` agree with
those omitting `j+1` then `i`. Pair `(i,j)` with `(j+1,i)`; restrictions agree and the signs
are opposite. These pairs partition the double sum, so all terms cancel.
(blueprint: def-weil-pbc-site-cech-complex) -/
theorem differential_squared (F : Cᵒᵖ ⥤ AddCommGrpCat.{r}) (p : ℕ) :
    S.differential F p ≫ S.differential F (p + 1) = 0 := by
  sorry

/-- The nonnegative Čech complex, constructed from its specified objects and differential.
Source: Stacks 03AM (blueprint: def-weil-pbc-site-cech-complex). -/
noncomputable def complex (F : Cᵒᵖ ⥤ AddCommGrpCat.{r}) :
    CochainComplex AddCommGrpCat.{max r w} ℕ :=
  CochainComplex.of (S.cochains F) (S.differential F) (S.differential_squared F)

/-- A presheaf morphism acts on each factor by its component at the chosen product.
Source: Stacks 03AO, 03AP (blueprint: def-weil-pbc-site-cech-complex). -/
def cochainsMap {F G : Cᵒᵖ ⥤ AddCommGrpCat.{r}} (φ : F ⟶ G) (p : ℕ) :
    S.cochains F p ⟶ S.cochains G p :=
  AddCommGrpCat.ofHom
    { toFun := fun s t ↦ φ.app (op (S.W p t)) (s t)
      map_zero' := funext fun t ↦ (φ.app (op (S.W p t))).hom.map_zero
      map_add' := fun s s' ↦ funext fun t ↦
        (φ.app (op (S.W p t))).hom.map_add (s t) (s' t) }

/-- The component maps commute with the alternating differential. Source: Stacks 03AO.
Proof: naturality of `φ` commutes with each omitted-factor restriction; its additivity
commutes with integer multiples and the finite sum. The two components therefore agree.
(blueprint: def-weil-pbc-site-cech-complex) -/
theorem cochainsMap_comm {F G : Cᵒᵖ ⥤ AddCommGrpCat.{r}} (φ : F ⟶ G) (p : ℕ) :
    S.cochainsMap φ p ≫ (S.complex G).d p (p + 1) =
      (S.complex F).d p (p + 1) ≫ S.cochainsMap φ (p + 1) := by
  sorry

/-- The specified morphism of Čech complexes induced by a presheaf morphism.
Source: Stacks 03AP (blueprint: def-weil-pbc-site-cech-complex). -/
noncomputable def complexMap {F G : Cᵒᵖ ⥤ AddCommGrpCat.{r}} (φ : F ⟶ G) :
    S.complex F ⟶ S.complex G :=
  CochainComplex.ofHom (S.cochainsMap φ) (S.cochainsMap_comm φ)

/-- Identity transformations act as identities on the Čech complex. Source: Stacks 03AO.
Proof: in each factor the identity transformation is the identity group homomorphism;
complex morphisms are determined by their degree components.
(blueprint: def-weil-pbc-site-cech-complex) -/
theorem complexMap_id (F : Cᵒᵖ ⥤ AddCommGrpCat.{r}) :
    S.complexMap (𝟙 F) = 𝟙 (S.complex F) := by
  sorry

/-- The Čech construction preserves composition. Source: Stacks 03AO.
Proof: transformation composition is componentwise composition; this is also the
composition of the displayed maps on each product of sections, in each degree.
(blueprint: def-weil-pbc-site-cech-complex) -/
theorem complexMap_comp {F G H : Cᵒᵖ ⥤ AddCommGrpCat.{r}} (φ : F ⟶ G) (ψ : G ⟶ H) :
    S.complexMap (φ ≫ ψ) = S.complexMap φ ≫ S.complexMap ψ := by
  sorry

/-- The Čech complex functor on presheaves of abelian groups.
Source: Stacks 03AO, 03AP (blueprint: def-weil-pbc-site-cech-complex). -/
noncomputable def complexFunctor :
    (Cᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤ CochainComplex AddCommGrpCat.{max r w} ℕ where
  obj := S.complex
  map := S.complexMap
  map_id := S.complexMap_id
  map_comp := S.complexMap_comp

/-- The Čech complex functor is additive. Source: Stacks 03AO.
Proof: transformations add sectionwise (lem-weil-pbc-abelian-presheaves-evaluation-exact).
The product maps therefore preserve sums of morphisms, and equality of complex morphisms
is degreewise equality. (blueprint: def-weil-pbc-site-cech-complex) -/
@[instance]
theorem complexFunctor_additive :
    (S.complexFunctor : (Cᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤
      CochainComplex AddCommGrpCat.{max r w} ℕ).Additive := by
  sorry

/-- The integer-indexed complex functor, zero in all negative degrees.
Source: Stacks 03AM, 03AO (blueprint: def-weil-pbc-site-cech-complex). -/
noncomputable def integerComplexFunctor :
    (Cᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤ CochainComplex AddCommGrpCat.{max r w} ℤ :=
  S.complexFunctor ⋙ ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max r w}

/-- The integer-indexed Čech functor is additive. Source: Stacks 03AO.
Proof: the nonnegative complex functor is additive, and extension by zero is additive
componentwise. Their composite is additive.
(blueprint: def-weil-pbc-site-cech-complex) -/
@[instance]
theorem integerComplexFunctor_additive :
    (S.integerComplexFunctor : (Cᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤
      CochainComplex AddCommGrpCat.{max r w} ℤ).Additive := by
  sorry

/-- Čech cohomology is the cohomology of the constructed complex, hence kernel modulo image;
in degree zero the incoming differential is zero.
Source: Stacks 03AM (blueprint: def-weil-pbc-site-cech-complex). -/
noncomputable def cohomologyFunctor (p : ℕ) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤ AddCommGrpCat.{max r w} :=
  S.complexFunctor ⋙ HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) p

/-- The Čech cohomology functors are additive. Source: Stacks 03AM, 03AO.
Proof: the complex functor is additive, as is the homology functor of an abelian category
(def-weil-abstract-derived-category); their composite is additive.
(blueprint: def-weil-pbc-site-cech-complex) -/
@[instance]
theorem cohomologyFunctor_additive (p : ℕ) :
    (S.cohomologyFunctor p : (Cᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤
      AddCommGrpCat.{max r w}).Additive := by
  sorry

/-- Exact presheaf sequences give exact sequences in every Čech degree. Source: Stacks 03AQ.
Proof: evaluation at each chosen product is exact by
lem-weil-pbc-abelian-presheaves-evaluation-exact. A product of exact abelian-group sequences
is exact: choose a preimage in each factor for any kernel element. This also includes the
empty product. These are precisely the components of `cochainsMap`.
(blueprint: def-weil-pbc-site-cech-complex) -/
theorem degreewise_exact (A : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat.{r})) (hA : A.Exact)
    (p : ℕ) : Function.Exact (S.cochainsMap A.f p) (S.cochainsMap A.g p) := by
  sorry

/-- The complexes from different product choices are canonically naturally isomorphic.
Source: Stacks 03AK, 03AM.
Proof: the unique product isomorphisms commute with all index maps, since their
projections agree. Restriction along the unique projection-compatible map `i` from the
other product (the inverse of that isomorphism, `fibreIso_exists_unique`) gives the
displayed degree maps. They commute with each differential term and have inverse maps
from the opposite product isomorphisms. Naturality in presheaves is componentwise
naturality; thus these give an isomorphism of functors, and homology gives canonical
cohomology isomorphisms.
(blueprint: def-weil-pbc-site-cech-complex) -/
theorem comparison_exists (S' : SiteCechComplex f hom) :
    ∃ e : (S.complexFunctor : (Cᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤
        CochainComplex AddCommGrpCat.{max r w} ℕ) ≅ S'.complexFunctor,
      ∀ (F : Cᵒᵖ ⥤ AddCommGrpCat.{r}) (p : ℕ) (s : S.cochains F p)
        (t : Fin (p + 1) → T),
        ∀ i : S'.W p t ⟶ S.W p t, (∀ k, i ≫ S.pr p t k = S'.pr p t k) →
          ((e.hom.app F).f p) s t = F.map i.op (s t) := by
  sorry

/-- Short exact presheaf sequences give short exact sequences of integer-indexed complexes.
Source: Stacks 03AQ.
Proof: evaluate the sequence sectionwise, take products of the resulting exact sequences
as in `degreewise_exact`, and use componentwise injectivity and surjectivity of the maps.
Negative degrees are zero. A sequence of complexes is short exact exactly when it is
short exact in each degree (lem-weil-pbc-cochain-complexes-degreewise-exact).
(blueprint: def-weil-pbc-site-cech-complex) -/
theorem shortExact_map (A : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat.{r})) (hA : A.ShortExact) :
    (A.map S.integerComplexFunctor).ShortExact := by
  sorry

end SiteCechComplex
end CategoryTheory
