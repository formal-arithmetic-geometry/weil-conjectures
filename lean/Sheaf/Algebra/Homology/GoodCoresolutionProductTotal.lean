module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# Good coresolutions and their product total complex

Source: Stacks Project, homology.tex, Tag 09J0,
`lemma-good-right-resolution-gives-qis` (blueprint: lem-sfb-good-coresolution-product-total).
The helpers construct exactly the product, signed differential, and augmentation specified
in that statement. There is no boundedness condition.
-/

@[expose] public section

universe u

open CategoryTheory HomologicalComplex

namespace CochainComplex.GoodCoresolution

/-- The product in degree `n` of Tag 09J0, indexed by the nonnegative horizontal degree.
Source: homology.tex, Tag 09J0 (blueprint: lem-sfb-good-coresolution-product-total). -/
abbrev productTerm (E : ℕ → CochainComplex AddCommGrpCat.{u} ℤ) (n : ℤ) :
    AddCommGrpCat.{u} :=
  AddCommGrpCat.of (∀ i : ℕ, (E i).X (n - (i : ℤ)))

/-- The incoming horizontal component, zero at coordinate zero.
Source: homology.tex, Tag 09J0, displayed total differential
(blueprint: lem-sfb-good-coresolution-product-total). -/
def horizontalComponent (E : ℕ → CochainComplex AddCommGrpCat.{u} ℤ)
    (f : ∀ i : ℕ, E i ⟶ E (i + 1)) (n : ℤ) :
    ∀ i : ℕ, productTerm E n ⟶ (E i).X (n + 1 - (i : ℤ))
  | 0 => 0
  | i + 1 =>
    AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun j : ℕ => (E j).X (n - (j : ℤ))) i) ≫
      (f i).f (n - (i : ℤ)) ≫
      eqToHom (congrArg (E (i + 1)).X (by omega))

/-- The differential `f` plus `(-1)^i d`, with only two contributing coordinates.
Source: homology.tex, Tag 09J0 (blueprint: lem-sfb-good-coresolution-product-total). -/
def productDifferential (E : ℕ → CochainComplex AddCommGrpCat.{u} ℤ)
    (f : ∀ i : ℕ, E i ⟶ E (i + 1)) (n : ℤ) :
    productTerm E n ⟶ productTerm E (n + 1) :=
  AddCommGrpCat.ofHom (AddMonoidHom.pi fun i : ℕ =>
    (horizontalComponent E f n i + ((-1 : ℤ) ^ i) •
      (AddCommGrpCat.ofHom
        (Pi.evalAddMonoidHom (fun j : ℕ => (E j).X (n - (j : ℤ))) i) ≫
          (E i).d (n - (i : ℤ)) (n + 1 - (i : ℤ)))).hom)

/-- The displayed product differential squares to zero.
Source: homology.tex, Tag 09J0 (blueprint: lem-sfb-good-coresolution-product-total).
Proof: exactness gives `f_i f_{i+1}=0`. In each coordinate the square has this
horizontal composite, `d^2`, and the two mixed terms with coefficients
`(-1)^(i-1)` and `(-1)^i`. The first two vanish and the mixed terms cancel by
commutation of each chain map with `d`. At zero only `d^2` occurs. -/
theorem productDifferential_comp (E : ℕ → CochainComplex AddCommGrpCat.{u} ℤ)
    (f : ∀ i : ℕ, E i ⟶ E (i + 1))
    (h : ∀ (i : ℕ) (n : ℤ), Function.Exact ((f i).f n) ((f (i + 1)).f n))
    (n : ℤ) : productDifferential E f n ≫ productDifferential E f (n + 1) = 0 := by
  sorry

/-- The actual product total complex of Tag 09J0; its terms and maps are explicit.
Source: homology.tex, Tag 09J0 (blueprint: lem-sfb-good-coresolution-product-total). -/
def productTotal (E : ℕ → CochainComplex AddCommGrpCat.{u} ℤ)
    (f : ∀ i : ℕ, E i ⟶ E (i + 1))
    (h : ∀ (i : ℕ) (n : ℤ), Function.Exact ((f i).f n) ((f (i + 1)).f n)) :
    CochainComplex AddCommGrpCat.{u} ℤ :=
  CochainComplex.of (productTerm E) (productDifferential E f)
    (productDifferential_comp E f h)

/-- The coordinate maps of the augmentation, with the zeroth coordinate `u`.
Source: homology.tex, Tag 09J0 (blueprint: lem-sfb-good-coresolution-product-total). -/
def augmentationCoordinate (M : CochainComplex AddCommGrpCat.{u} ℤ)
    (E : ℕ → CochainComplex AddCommGrpCat.{u} ℤ) (u : M ⟶ E 0) (n : ℤ) :
    ∀ i : ℕ, M.X n ⟶ (E i).X (n - (i : ℤ))
  | 0 => u.f n ≫ eqToHom (congrArg (E 0).X (by omega))
  | _ + 1 => 0

/-- The augmentation in a degree sends `m` to `(u(m),0,0,...)`.
Source: homology.tex, Tag 09J0 (blueprint: lem-sfb-good-coresolution-product-total). -/
def augmentationComponent (M : CochainComplex AddCommGrpCat.{u} ℤ)
    (E : ℕ → CochainComplex AddCommGrpCat.{u} ℤ) (u : M ⟶ E 0) (n : ℤ) :
    M.X n ⟶ productTerm E n :=
  AddCommGrpCat.ofHom (AddMonoidHom.pi fun i : ℕ => (augmentationCoordinate M E u n i).hom)

/-- The specified augmentation commutes with the differential.
Source: homology.tex, Tag 09J0 (blueprint: lem-sfb-good-coresolution-product-total).
Proof: at coordinate zero this is the chain-map identity for `u`; at coordinate
one the additional term is `f_0 u=0` by exactness; all later components are zero. -/
theorem augmentationComponent_comm (M : CochainComplex AddCommGrpCat.{u} ℤ)
    (E : ℕ → CochainComplex AddCommGrpCat.{u} ℤ) (u : M ⟶ E 0)
    (f : ∀ i : ℕ, E i ⟶ E (i + 1))
    (h : ∀ (i : ℕ) (n : ℤ), Function.Exact ((f i).f n) ((f (i + 1)).f n))
    (h₀ : ∀ n : ℤ, Function.Exact (u.f n) ((f 0).f n)) (n : ℤ) :
    augmentationComponent M E u n ≫ (productTotal E f h).d n (n + 1) =
      M.d n (n + 1) ≫ augmentationComponent M E u (n + 1) := by
  sorry

/-- The canonical chain map of Tag 09J0 with only coordinate zero nonzero.
Source: homology.tex, Tag 09J0 (blueprint: lem-sfb-good-coresolution-product-total). -/
def augmentation (M : CochainComplex AddCommGrpCat.{u} ℤ)
    (E : ℕ → CochainComplex AddCommGrpCat.{u} ℤ) (u : M ⟶ E 0)
    (f : ∀ i : ℕ, E i ⟶ E (i + 1))
    (h : ∀ (i : ℕ) (n : ℤ), Function.Exact ((f i).f n) ((f (i + 1)).f n))
    (h₀ : ∀ n : ℤ, Function.Exact (u.f n) ((f 0).f n)) : M ⟶ productTotal E f h :=
  CochainComplex.ofHom (augmentationComponent M E u)
    (augmentationComponent_comm M E u f h h₀)

/-- An exact coresolution exact also on differential cokernels computes its product total.
Source: homology.tex, Tag 09J0 (blueprint: lem-sfb-good-coresolution-product-total).
Proof: degreewise exactness gives the horizontal composites and the augmented composite
zero, so the preceding constructions give a complex and a chain map. The two exactness
assumptions imply exact cohomology rows by
`lem-sfb-good-coresolution-cohomology-rows`: splice the boundary and cycle rows.
For a total cocycle `x` in degree `n`, cokernel-row exactness writes its coordinate zero
as `u(m)+d(v)`; injectivity of `u` shows `d(m)=0`. Subtract the augmentation of `m`
and start a boundary lift with `y_0=v`. Inductively the discrepancy
`w=r_{k+1}-f_k(y_k)` is a cycle whose image in the next column is a boundary.
Exactness of the cohomology row gives a cycle `z` in column `k` lifting its class.
Replace `y_k` by `y_k+z` and choose `y_{k+1}` to solve the remaining boundary equation,
with sign `(-1)^(k+1)`. Only the last old coordinate changes, so each coordinate
stabilizes after its next step. The resulting family is an element of the product,
and its differential is `r`. This proves surjectivity on cohomology.
For injectivity, if `a(m)=d(y)`, the first two coordinates imply that the class of
`y_0` in the differential cokernel maps to zero in column one. Exactness gives
`y_0=u(z)+d(t)`; differentiating and using injectivity of `u` gives `m=d(z)`.
The argument works for every integer degree and requires no boundedness. -/
theorem augmentation_quasiIso (M : CochainComplex AddCommGrpCat.{u} ℤ)
    (E : ℕ → CochainComplex AddCommGrpCat.{u} ℤ) (u : M ⟶ E 0)
    (f : ∀ i : ℕ, E i ⟶ E (i + 1))
    (h_inj : ∀ n : ℤ, Function.Injective (u.f n))
    (h₀ : ∀ n : ℤ, Function.Exact (u.f n) ((f 0).f n))
    (h : ∀ (i : ℕ) (n : ℤ), Function.Exact ((f i).f n) ((f (i + 1)).f n))
    (hc_inj : ∀ n : ℤ, Function.Injective (opcyclesMap u n))
    (hc₀ : ∀ n : ℤ, Function.Exact (opcyclesMap u n) (opcyclesMap (f 0) n))
    (hc : ∀ (i : ℕ) (n : ℤ),
      Function.Exact (opcyclesMap (f i) n) (opcyclesMap (f (i + 1)) n)) :
    QuasiIso (augmentation M E u f h h₀) := by
  sorry

end CochainComplex.GoodCoresolution
