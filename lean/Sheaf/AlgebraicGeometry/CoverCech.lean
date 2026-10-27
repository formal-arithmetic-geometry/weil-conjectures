/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import WeilConjectures.CategoryTheory.SiteCechComplex
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Mathlib.Algebra.Module.End

/-!
# Covering Čech complexes with module coefficients

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange,
def-weil-pbc-cover-cech (blueprint: def-weil-pbc-cover-cech).

The complex and cohomology reuse `SiteCechComplex` on underlying abelian presheaves.
The augmentation and scalar action are restriction from the covered object. The two
specializations below retain the coefficient categories and universes of the cited nodes.
-/

@[expose] public section

universe u v r a

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SiteCechComplex

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {m : ℕ} {U : C} {V : Fin m → C} {f : ∀ i, V i ⟶ U}
  (S : SiteCechComplex V f) (R : Sheaf J RingCat.{r}) (M : SheafOfModules.{a} R)

/-- The nonnegative covering complex, extended by zero to negative degrees, on the
underlying abelian presheaf. Source: blueprint def-weil-pbc-cover-cech
(blueprint: def-weil-pbc-cover-cech). -/
noncomputable def coverComplex : CochainComplex AddCommGrpCat.{a} ℤ :=
  S.integerComplexFunctor.obj M.val.presheaf

/-- Unaugmented Čech cohomology, including degree zero with zero incoming differential.
Source: blueprint def-weil-pbc-cover-cech (blueprint: def-weil-pbc-cover-cech). -/
noncomputable def coverCohomology (p : ℕ) : AddCommGrpCat.{a} :=
  (S.cohomologyFunctor p).obj M.val.presheaf

/-- Restrict a section on `U` to each degree-zero tuple. The degree-zero fibre product
is the original covering object by `S.W_zero` and `S.pr_zero`.
Source: blueprint def-weil-pbc-cover-cech (blueprint: def-weil-pbc-cover-cech). -/
noncomputable def coverAugmentation :
    M.val.presheaf.obj (op U) ⟶ (S.complex M.val.presheaf).X 0 :=
  AddCommGrpCat.ofHom (AddMonoidHom.pi fun t : Fin (0 + 1) → Fin m ↦
    (M.val.presheaf.map (S.pr 0 t 0 ≫ f (t 0)).op).hom)

/-- The augmentation is the degree `-1` differential of the augmented complex;
it is additional to the complex defining Čech cohomology.
Source: blueprint def-weil-pbc-cover-cech (blueprint: def-weil-pbc-cover-cech).

Proof: in the coordinate indexed by `(a,b)`, the two degree-zero restrictions are
both restriction from `U` to the same two-factor product, by functoriality and
`S.comm`. The alternating differential subtracts these equal restrictions. Thus
its composite with the augmentation is zero, also for an empty covering. -/
theorem coverAugmentation_comp_d :
    S.coverAugmentation R M ≫ (S.complex M.val.presheaf).d 0 1 = 0 := by
  simp only [complex]
  apply AddCommGrpCat.ext
  intro s
  funext t
  have h (j : Fin 2) :
      M.val.presheaf.map (S.indexMap t j.succAbove).op
          (M.val.presheaf.map
            (S.pr 0 (t ∘ j.succAbove) 0 ≫ f ((t ∘ j.succAbove) 0)).op s) =
        M.val.presheaf.map (S.pr 1 t 0 ≫ f (t 0)).op s := by
    rw [← AddCommGrpCat.comp_apply, ← Functor.map_comp, ← op_comp]
    dsimp only [Function.comp_apply]
    rw [← Category.assoc, S.indexMap_pr, S.comm]
  change (∑ j : Fin 2, (-1 : ℤ) ^ j.val •
    M.val.presheaf.map (S.indexMap t j.succAbove).op
      (M.val.presheaf.map
        (S.pr 0 (t ∘ j.succAbove) 0 ≫ f ((t ∘ j.succAbove) 0)).op s)) = 0
  simp only [h]
  simp [Fin.sum_univ_two]

/-- The termwise module structure restricts scalars along the tuple product's map to `U`.
Source: blueprint def-weil-pbc-cover-cech, final sentence
(blueprint: def-weil-pbc-cover-cech). -/
@[instance_reducible]
noncomputable def coverCochainModule (p : ℕ) :
    Module (R.obj.obj (op U)) (S.cochains M.val.presheaf p) :=
  letI : ∀ t : Fin (p + 1) → Fin m,
      Module (R.obj.obj (op U)) (M.val.presheaf.obj (op (S.W p t))) :=
    fun t ↦ Module.compHom _ (R.obj.map (S.pr p t 0 ≫ f (t 0)).op).hom
  inferInstanceAs (Module (R.obj.obj (op U))
    (∀ t : Fin (p + 1) → Fin m, M.val.presheaf.obj (op (S.W p t))))

/-- Restriction of a scalar on `U` acts on each tuple's section group.
Source: blueprint def-weil-pbc-cover-cech, final sentence
(blueprint: def-weil-pbc-cover-cech). -/
noncomputable def coverScalarCochains (c : R.obj.obj (op U)) (p : ℕ) :
    S.cochains M.val.presheaf p ⟶ S.cochains M.val.presheaf p :=
  AddCommGrpCat.ofHom
    { toFun := fun s t ↦ R.obj.map (S.pr p t 0 ≫ f (t 0)).op c • s t
      map_zero' := funext fun _t ↦ smul_zero _
      map_add' := fun s s' ↦ funext fun t ↦ smul_add _ (s t) (s' t) }

/-- Restriction scalars commute with the alternating differential.
Source: blueprint def-weil-pbc-cover-cech, final sentence
(blueprint: def-weil-pbc-cover-cech).

Proof: the map from each tuple product to `U` is independent of its selected projection
by `S.comm`. Its composite with each omitted-factor projection is the map of the larger
tuple to `U`, by `S.indexMap_pr`. The semilinearity of module restriction therefore
commutes with these restricted scalars. Distribute scalar multiplication across the
signed finite sum in `SiteCechComplex.differentialValue`. This gives the equality in
every tuple coordinate, including repetitions and the empty family. -/
theorem coverScalarCochains_comm (c : R.obj.obj (op U)) (p : ℕ) :
    S.coverScalarCochains R M c p ≫ (S.complex M.val.presheaf).d p (p + 1) =
      (S.complex M.val.presheaf).d p (p + 1) ≫
        S.coverScalarCochains R M c (p + 1) := by
  simp only [complex, CochainComplex.of_d]
  apply AddCommGrpCat.ext
  intro s
  funext t
  have h (j : Fin (p + 2)) :
      R.obj.map (S.indexMap t j.succAbove).op
          (R.obj.map
            (S.pr p (t ∘ j.succAbove) 0 ≫ f ((t ∘ j.succAbove) 0)).op c) =
        R.obj.map (S.pr (p + 1) t 0 ≫ f (t 0)).op c := by
    rw [← RingCat.comp_apply, ← Functor.map_comp, ← op_comp]
    dsimp only [Function.comp_apply]
    rw [← Category.assoc, S.indexMap_pr, S.comm]
  change (∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
    M.val.map (S.indexMap t j.succAbove).op
      (R.obj.map (S.pr p (t ∘ j.succAbove) 0 ≫
        f ((t ∘ j.succAbove) 0)).op c • s (t ∘ j.succAbove))) =
    R.obj.map (S.pr (p + 1) t 0 ≫ f (t 0)).op c •
      (∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
        M.val.map (S.indexMap t j.succAbove).op (s (t ∘ j.succAbove)))
  simp only [M.val.map_smul, h, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact smul_comm _ _ _

/-- The actual scalar cochain map, used to induce the action on cohomology.
Source: blueprint def-weil-pbc-cover-cech (blueprint: def-weil-pbc-cover-cech). -/
noncomputable def coverScalarMap (c : R.obj.obj (op U)) :
    S.complex M.val.presheaf ⟶ S.complex M.val.presheaf :=
  CochainComplex.ofHom (S.coverScalarCochains R M c) (S.coverScalarCochains_comm R M c)

/-- The scalar action on cohomology is induced by the specified scalar cochain map.
Source: blueprint def-weil-pbc-cover-cech (blueprint: def-weil-pbc-cover-cech). -/
noncomputable def coverCohomologyScalar (p : ℕ) (c : R.obj.obj (op U)) :
    AddMonoid.End (S.coverCohomology R M p) :=
  (HomologicalComplex.homologyMap (S.coverScalarMap R M c) p).hom

/-- The induced scalar action satisfies the ring action laws.
Source: blueprint def-weil-pbc-cover-cech, final sentence
(blueprint: def-weil-pbc-cover-cech).

Proof: the scalar cochain maps for zero and one are zero and identity, since these
identities hold in every section module. The maps for a sum and a product are their
sum and ordered composition, since ring restriction is a ring homomorphism and each
section is a left module. The additive homology functor preserves zero, identities,
sums and composition. Applying it gives the four asserted identities. No choice of
representatives is involved; equivalently these are the actions on cycles modulo
boundaries. The same reasoning applies in degree zero with no incoming boundary. -/
theorem coverCohomologyScalar_laws (p : ℕ) :
    (S.coverCohomologyScalar R M p 0 = 0) ∧
    (S.coverCohomologyScalar R M p 1 = 1) ∧
    (∀ c d : R.obj.obj (op U), S.coverCohomologyScalar R M p (c + d) =
      S.coverCohomologyScalar R M p c + S.coverCohomologyScalar R M p d) ∧
    (∀ c d : R.obj.obj (op U), S.coverCohomologyScalar R M p (c * d) =
      S.coverCohomologyScalar R M p c * S.coverCohomologyScalar R M p d) := by
  have hz : S.coverScalarMap R M 0 = 0 := by
    ext q s
    funext t
    change R.obj.map (S.pr q t 0 ≫ f (t 0)).op 0 • s t = 0
    simp
  have ho : S.coverScalarMap R M 1 = 𝟙 _ := by
    ext q s
    funext t
    change R.obj.map (S.pr q t 0 ≫ f (t 0)).op 1 • s t = s t
    simp
  have ha (c d : R.obj.obj (op U)) :
      S.coverScalarMap R M (c + d) = S.coverScalarMap R M c + S.coverScalarMap R M d := by
    ext q s
    funext t
    change R.obj.map (S.pr q t 0 ≫ f (t 0)).op (c + d) • s t =
      R.obj.map (S.pr q t 0 ≫ f (t 0)).op c • s t + R.obj.map (S.pr q t 0 ≫ f (t 0)).op d • s t
    simp [add_smul]
  have hm (c d : R.obj.obj (op U)) :
      S.coverScalarMap R M (c * d) = S.coverScalarMap R M d ≫ S.coverScalarMap R M c := by
    ext q s
    funext t
    change R.obj.map (S.pr q t 0 ≫ f (t 0)).op (c * d) • s t =
      R.obj.map (S.pr q t 0 ≫ f (t 0)).op c •
        (R.obj.map (S.pr q t 0 ≫ f (t 0)).op d • s t)
    simp [mul_smul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [coverCohomologyScalar, hz]
  · simp only [coverCohomologyScalar, ho, HomologicalComplex.homologyMap_id]
    rfl
  · intro c d
    simp [coverCohomologyScalar, ha, HomologicalComplex.homologyMap_add]
  · intro c d
    simp only [coverCohomologyScalar, hm, HomologicalComplex.homologyMap_comp,
      AddCommGrpCat.hom_comp]
    rfl

/-- Cohomology as a module over the ring of sections on `U`, with the restriction action.
Only the action laws are postponed; the scalar multiplication is the homology map above.
Source: blueprint def-weil-pbc-cover-cech (blueprint: def-weil-pbc-cover-cech). -/
@[instance_reducible]
noncomputable def coverCohomologyModule (p : ℕ) :
    Module (R.obj.obj (op U)) (S.coverCohomology R M p) where
  smul c x := S.coverCohomologyScalar R M p c x
  one_smul x := congrArg (fun e ↦ e x) (S.coverCohomologyScalar_laws R M p).2.1
  mul_smul c d x := congrArg (fun e ↦ e x) ((S.coverCohomologyScalar_laws R M p).2.2.2 c d)
  smul_zero c := (S.coverCohomologyScalar R M p c).map_zero
  smul_add c x y := (S.coverCohomologyScalar R M p c).map_add x y
  add_smul c d x := congrArg (fun e ↦ e x) ((S.coverCohomologyScalar_laws R M p).2.2.1 c d)
  zero_smul x := congrArg (fun e ↦ e x) (S.coverCohomologyScalar_laws R M p).1

end CategoryTheory.SiteCechComplex

namespace AlgebraicGeometry.Scheme

/-- Finite-cover Čech complex on the small étale site, with the constant-ring module
sheaf convention of def-weil-pbc-etale-sheaves. Covering is imposed by the topology;
`S` is precisely the chosen tuple products of def-weil-pbc-site-cech-complex.
Source: blueprint def-weil-pbc-cover-cech (blueprint: def-weil-pbc-cover-cech). -/
noncomputable def etaleCoverCechComplex (T : Scheme.{u}) (R : Type u) [CommRing R]
    {m : ℕ} {U : T.Etale} (V : Fin m → T.Etale) (f : ∀ i, V i ⟶ U)
    (_hcover : Sieve.generate (Presieve.ofArrows V f) ∈ T.smallEtaleTopology U)
    (S : SiteCechComplex V f)
    (M : SheafOfModules.{u + 1}
      ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1, u} R)))) :
    CochainComplex AddCommGrpCat.{u + 1} ℤ :=
  S.coverComplex _ M

/-- Finite-cover Čech cohomology on the small étale site. The augmentation is additional
and is `S.coverAugmentation _ M`; the section-ring action is `S.coverCohomologyModule _ M p`.
Source: blueprint def-weil-pbc-cover-cech (blueprint: def-weil-pbc-cover-cech). -/
noncomputable def etaleCoverCechCohomology (T : Scheme.{u}) (R : Type u) [CommRing R]
    {m : ℕ} {U : T.Etale} (V : Fin m → T.Etale) (f : ∀ i, V i ⟶ U)
    (_hcover : Sieve.generate (Presieve.ofArrows V f) ∈ T.smallEtaleTopology U)
    (S : SiteCechComplex V f)
    (M : SheafOfModules.{u + 1}
      ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1, u} R)))) (p : ℕ) : AddCommGrpCat.{u + 1} :=
  S.coverCohomology _ M p

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- Finite-cover Čech complex on the small pro-étale site, on the underlying abelian
presheaf of the recorded finite-coefficient module sheaf. No condensed coefficients occur.
Source: blueprint def-weil-pbc-cover-cech (blueprint: def-weil-pbc-cover-cech). -/
noncomputable def proEtaleCoverCechComplex (T : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]
    [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    {m : ℕ} {U : T.ProEt} (V : Fin m → T.ProEt) (f : ∀ i, V i ⟶ U)
    (_hcover : Sieve.generate (Presieve.ofArrows V f) ∈ Scheme.ProEt.topology T U)
    (S : SiteCechComplex V f) (M : FiniteCoefficientModules T Λ) :
    CochainComplex AddCommGrpCat.{u + 1} ℤ :=
  S.coverComplex (finiteCoefficientRingSheaf T Λ) M

/-- Finite-cover Čech cohomology on the small pro-étale site. Its augmentation is
`S.coverAugmentation (finiteCoefficientRingSheaf T Λ) M`; its section-ring module
structure is `S.coverCohomologyModule (finiteCoefficientRingSheaf T Λ) M p`.
Source: blueprint def-weil-pbc-cover-cech (blueprint: def-weil-pbc-cover-cech). -/
noncomputable def proEtaleCoverCechCohomology (T : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]
    [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    {m : ℕ} {U : T.ProEt} (V : Fin m → T.ProEt) (f : ∀ i, V i ⟶ U)
    (_hcover : Sieve.generate (Presieve.ofArrows V f) ∈ Scheme.ProEt.topology T U)
    (S : SiteCechComplex V f) (M : FiniteCoefficientModules T Λ) (p : ℕ) :
    AddCommGrpCat.{u + 1} :=
  S.coverCohomology (finiteCoefficientRingSheaf T Λ) M p

end AlgebraicGeometry.ProEtale
