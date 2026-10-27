/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.CategoryTheory.CondensedDerivedInvariants
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import Mathlib.Algebra.Module.LinearMap.Rat
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Transfer on evaluated vertical-cohomology bar rows

Source: latest blueprint, six-functors direct-images proof, paragraph (3),
agent-formulated evaluated finite-coset transfer obligation; exact reference WANTED
(blueprint: lem-sfb-evaluated-positive-bar-row-transfer).

Cochains are sections on profinite powers, not functions into sections at a point.
Vertical cohomology is taken after evaluation, in ordinary rational vector spaces.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CondensedBar

namespace CategoryTheory.CondensedBar.Evaluated

variable (A : Ring.{u}) [∀ S : Profinite.{u}, Algebra ℚ (sectionRing A S)]

/-- Restrict the existing section-module scalars to the unique rational algebra structure.
Source: the node's condensed Q-algebra hypothesis
(blueprint: lem-sfb-evaluated-positive-bar-row-transfer). -/
instance rationalSections (M : Modules A) (S : Profinite.{u}) :
    Module ℚ (sections A M S) :=
  Module.compHom (sections A M S) (algebraMap ℚ (sectionRing A S))

/-- Evaluate actual internal modules on a profinite set, retaining rational linearity.
Source: the evaluation identification in the node
(blueprint: lem-sfb-evaluated-positive-bar-row-transfer). -/
def sectionFunctor (S : Profinite.{u}) : Modules A ⥤ ModuleCat.{u + 1} ℚ where
  obj M := ModuleCat.of ℚ (sections A M S)
  map f := ModuleCat.ofHom (f.hom.hom.app (op S)).hom.toRatLinearMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Evaluation preserves addition of morphisms, without an exactness assumption.
Source: sectionwise addition (blueprint: lem-sfb-evaluated-positive-bar-row-transfer). -/
instance sectionFunctor_additive (S : Profinite.{u}) : (sectionFunctor A S).Additive where
  map_add := by intros; rfl

variable {A} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {P : Type u} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]

/-- Pullback along a profinite map, as a rational linear map of actual sections.
Source: the section restrictions in the node
(blueprint: lem-sfb-evaluated-positive-bar-row-transfer). -/
def pullback (M : Modules A) {S T : Profinite.{u}} (f : T ⟶ S) :
    (sectionFunctor A S).obj M ⟶ (sectionFunctor A T).obj M :=
  ModuleCat.ofHom (M.X.obj.map f.op).hom.toRatLinearMap

/-- The evaluated inhomogeneous coface. The zeroth face uses the restricted G-action;
all other faces are pullbacks along the recorded multiplication/drop tuple maps.
Source: def-sfb-condensed-equivariant-bar-data, coface formula
(blueprint: lem-sfb-evaluated-positive-bar-row-transfer). -/
def face (j : P →ₜ* G) (M : Equivariant A G) (n : ℕ) (i : Fin (n + 2)) :
    (sectionFunctor A (power P n)).obj M.module ⟶
      (sectionFunctor A (power P (n + 1))).obj M.module :=
  ModuleCat.ofHom (AddMonoidHom.toRatLinearMap
    (AddMonoidHom.mk' (fun x ↦
      if i.val = 0 then
        M.act (power P (n + 1)) (j.toContinuousMap.comp (ContinuousMap.eval 0))
          (pullback M.module (ConcreteCategory.ofHom
            (tupleMap (fun k : Fin n ↦ ContinuousMap.eval k.succ))) x)
      else if i.val = n + 1 then
        pullback M.module (ConcreteCategory.ofHom
          (tupleMap (fun k : Fin n ↦ ContinuousMap.eval k.castSucc))) x
      else pullback M.module (ConcreteCategory.ofHom
        (tupleMap (mergeTuple i (fun k : Fin (n + 1) ↦ ContinuousMap.eval k)))) x)
      (by
        intro x y
        split_ifs <;> simp only [map_add])))

/-- Alternating sum with the action-dependent zeroth face and the usual signs.
Source: node definition of d_h (blueprint: lem-sfb-evaluated-positive-bar-row-transfer). -/
def differential (j : P →ₜ* G) (M : Equivariant A G) (n : ℕ) :
    (sectionFunctor A (power P n)).obj M.module ⟶
      (sectionFunctor A (power P (n + 1))).obj M.module :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • face j M n i

/-- The displayed cofaces square to zero after alternating summation and commute with
all equivariant coefficient maps. Source: node, commuting double-complex assertion
(blueprint: lem-sfb-evaluated-positive-bar-row-transfer).
Proof: pair the two orders of deleting homogeneous coordinates, using the inverse
prefix-product/successive-ratio changes of coordinates in proof steps 1 and 2.
The two terms have opposite signs. Naturality of restrictions and equivariance of
coefficient maps give the second identity, including the action face. -/
theorem differential_laws (j : P →ₜ* G) :
    (∀ (M : Equivariant A G) (n : ℕ),
      differential j M n ≫ differential j M (n + 1) = 0) ∧
    (∀ (M N : Equivariant A G) (f : M ⟶ N) (n : ℕ),
      (sectionFunctor A (power P n)).map f.val ≫ differential j N n =
        differential j M n ≫ (sectionFunctor A (power P (n + 1))).map f.val) := by
  sorry

/-- The actual evaluated bar cochain functor, with no choice of a bar model.
Source: D_J in the node (blueprint: lem-sfb-evaluated-positive-bar-row-transfer). -/
def bar (j : P →ₜ* G) : Equivariant A G ⥤ CochainComplex (ModuleCat.{u + 1} ℚ) ℕ where
  obj M := CochainComplex.of (fun n ↦ (sectionFunctor A (power P n)).obj M.module)
    (differential j M) ((differential_laws j).1 M)
  map {M N} f := CochainComplex.ofHom
    (fun n ↦ (sectionFunctor A (power P n)).map f.val)
    (fun n ↦ by simpa only [CochainComplex.of_d] using (differential_laws j).2 M N f n)
  map_id _ := by ext n; rfl
  map_comp _ _ := by ext n; rfl

/-- Addition of coefficient maps is still sectionwise addition.
Source: D_J functoriality (blueprint: lem-sfb-evaluated-positive-bar-row-transfer). -/
instance bar_additive (j : P →ₜ* G) : (bar (A := A) j).Additive where
  map_add := by intros; ext n; rfl

/-- First take evaluated columns, then ordinary vertical cohomology. The outer degree
is the bar degree and the column differential is unsigned d_v.
Source: V_{J,q} in the node (blueprint: lem-sfb-evaluated-positive-bar-row-transfer). -/
def row (j : P →ₜ* G) (q : ℕ) :
    CochainComplex (Equivariant A G) ℕ ⥤ CochainComplex (ModuleCat.{u + 1} ℚ) ℕ :=
  (bar j).mapHomologicalComplex (.up ℕ) ⋙
    HomologicalComplex₂.flipFunctor (ModuleCat.{u + 1} ℚ) (.up ℕ) (.up ℕ) ⋙
      (HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} ℚ) (.up ℕ) q).mapHomologicalComplex
        (.up ℕ)

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The subgroup topology and group operations are those of the underlying subgroup.
Source: node profinite subgroup (blueprint: lem-sfb-evaluated-positive-bar-row-transfer). -/
instance openTopological (H : OpenSubgroup G) : IsTopologicalGroup H :=
  inferInstanceAs (IsTopologicalGroup H.toSubgroup)

/-- An open subgroup of a profinite group is closed, hence compact.
Source: proof step 3 (blueprint: lem-sfb-evaluated-positive-bar-row-transfer). -/
instance openCompact (H : OpenSubgroup G) : CompactSpace H :=
  isCompact_iff_compactSpace.mp H.isClosed.isCompact

/-- The continuous inclusion of an open subgroup.
Source: node restriction (blueprint: lem-sfb-evaluated-positive-bar-row-transfer). -/
def inclusion (H : OpenSubgroup G) : H →ₜ* G :=
  ⟨H.toSubgroup.subtype, continuous_subtype_val⟩

/-- Inclusion of profinite powers, including the terminal power in degree zero.
Source: node restriction (blueprint: lem-sfb-evaluated-positive-bar-row-transfer). -/
def powerInclusion (H : OpenSubgroup G) (p : ℕ) : power H p ⟶ power G p :=
  ConcreteCategory.ofHom (tupleMap (fun i ↦
    (inclusion H).toContinuousMap.comp (ContinuousMap.eval i)))

/-- Restriction of sections commutes with every horizontal differential.
Source: r_J in the node (blueprint: lem-sfb-evaluated-positive-bar-row-transfer).
Proof: inclusion preserves multiplication and the identity. Pullback is functorial,
and the action is natural under profinite base change, including its zeroth face.
Apply these identities to each summand of the alternating differential. -/
theorem restriction_comm (H : OpenSubgroup G) (M : Equivariant A G) (n : ℕ) :
    pullback M.module (powerInclusion H n) ≫ differential (inclusion H) M n =
      differential (ContinuousMonoidHom.id G) M n ≫
        pullback M.module (powerInclusion H (n + 1)) := by
  sorry

/-- The specified restriction of sections before taking vertical cohomology.
Source: r_J in the node (blueprint: lem-sfb-evaluated-positive-bar-row-transfer). -/
def restriction (H : OpenSubgroup G) :
    bar (A := A) (ContinuousMonoidHom.id G) ⟶ bar (A := A) (inclusion H) where
  app M := CochainComplex.ofHom
    (fun n ↦ pullback M.module (powerInclusion H n))
    (fun n ↦ by simpa only [bar, CochainComplex.of_d] using restriction_comm H M n)
  naturality := by
    intro M N f
    ext n x
    exact (ConcreteCategory.congr_hom
      (f.val.hom.hom.naturality (powerInclusion H n).op) x).symm

/-- The canonical cochain map induced by restriction on the actual evaluated columns.
Source: r_J:V_{G,q}->V_{J,q} (blueprint: lem-sfb-evaluated-positive-bar-row-transfer). -/
def rowRestriction (H : OpenSubgroup G) (q : ℕ) :
    row (A := A) (ContinuousMonoidHom.id G) q ⟶ row (A := A) (inclusion H) q :=
  Functor.whiskerRight (NatTrans.mapHomologicalComplex (restriction (A := A) H) (.up ℕ))
    (HomologicalComplex₂.flipFunctor (ModuleCat.{u + 1} ℚ) (.up ℕ) (.up ℕ) ⋙
      (HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} ℚ) (.up ℕ) q).mapHomologicalComplex
        (.up ℕ))

/-- Finite-index transfer on all evaluated vertical-cohomology rows, simultaneously
natural in equivariant chain maps of nonnegative injective resolutions.
Source: latest blueprint direct-images proof, paragraph (3), agent-formulated
finite-coset auxiliary obligation; exact external reference WANTED
(blueprint: lem-sfb-evaluated-positive-bar-row-transfer).

Proof (the ten steps of the node).
1. Change to homogeneous generalized sections on J^(p+1), by prefix products in one
   direction and successive ratios followed by the initial action in the other.
   These substitutions are inverse, using homogeneity after every profinite base change.
2. Deletion of the initial coordinate gives the action face. Interior deletions multiply
   adjacent ratios and the final deletion drops the last ratio. Thus the alternating
   deletion differential is exactly differential above, including d(c)(g)=g*c-c in degree 0.
3. Choose finitely many right-coset representatives S, with 1 representing H. On Hs put
   rho(x)=x*s^(-1). Open cosets are clopen; compactness makes S finite. Right multiplication
   permutes S, locally constantly in its parameter a; use the resulting finite clopen cover.
4. On homogeneous H-sections set T(f)(x)=sum_s s^(-1)*f((rho(s*x_i))_i).
   These are pullbacks followed by constant actions, hence actual linear section maps.
   They commute with coefficient maps and alternating deletion.
5. Write s*a=h_s(a)*u on each clopen piece of the parameter space. Then
   rho(s*a*x)=h_s(a)*rho(u*x) and s^(-1)*h_s(a)=a*u^(-1). Homogeneity and reindexing
   prove that T is G-homogeneous. Sheaf separatedness glues the equality. For
   a_s(x)=s^(-1)*rho(s*x), restriction R satisfies T*R=sum_s (a_s)^*.
6. In positive degree p define K by sum_s sum_{i=0}^{p-1} (-1)^i times pullback along
   (x_0,...,x_i,a_s(x_i),...,a_s(x_{p-1})); set K^0=0. The same permutation argument
   proves homogeneity after every base change. All summands commute with coefficient maps.
7. Apply lem-trf-coefficient-bar-prism-homotopy to the unique-arrow category on G,
   identity and a_s, with constant integer coefficients. Its tuple face identities yield
   delta*K+K*delta=sum_s (a_s)^*-[G:H]. They are identities of continuous tuple maps,
   so contravariant pullback proves them on sections, without evaluating at ordinary points.
   In degree zero the difference is F(a_s(x))-F(x), with exactly this sign.
8. Transport T,K back by the coordinate isomorphisms of steps 1 and 2. Use the same
   representatives in every resolution degree. All operators commute with the unsigned
   vertical differential and every equivariant chain map.
9. These operators preserve vertical kernels and images; [z] maps to [Tz] or [Kz].
   Thus they descend to the ordinary vector-space cohomology used by row. Their sum
   and composition identities descend on representatives, as do both naturality equations.
10. On a horizontal cocycle, the homotopy equation leaves a horizontal boundary,
    giving the displayed cohomology identity in every p and q. For q=0 the incoming
    vertical term is zero; for p=0 the negative horizontal term is zero. H=G has the
    singleton transversal and permits identity transfer and zero homotopy. This covers
    trivial G. The construction applies unchanged to any injective resolution of N=0,
    and uses no vanishing or exactness of evaluated positive rows.
-/
theorem exists_transfer (H : OpenSubgroup G) :
    ∃ (t : ∀ (N : Equivariant A G) (I : InjectiveResolution N) (q : ℕ),
        (row (inclusion H) q).obj I.cocomplex ⟶
          (row (ContinuousMonoidHom.id G) q).obj I.cocomplex)
      (h : ∀ (N : Equivariant A G) (I : InjectiveResolution N) (q : ℕ),
        Homotopy ((rowRestriction H q).app I.cocomplex ≫ t N I q)
          (H.toSubgroup.index • 𝟙 ((row (ContinuousMonoidHom.id G) q).obj I.cocomplex))),
      (∀ (N : Equivariant A G) (I : InjectiveResolution N) (p q : ℕ),
        HomologicalComplex.homologyMap ((rowRestriction H q).app I.cocomplex) p ≫
            HomologicalComplex.homologyMap (t N I q) p =
          H.toSubgroup.index •
            𝟙 (((row (ContinuousMonoidHom.id G) q).obj I.cocomplex).homology p)) ∧
      (∀ (N M : Equivariant A G) (I : InjectiveResolution N) (J : InjectiveResolution M)
          (f : I.cocomplex ⟶ J.cocomplex) (q : ℕ),
        (row (inclusion H) q).map f ≫ t M J q =
          t N I q ≫ (row (ContinuousMonoidHom.id G) q).map f) ∧
      (∀ (N M : Equivariant A G) (I : InjectiveResolution N) (J : InjectiveResolution M)
          (f : I.cocomplex ⟶ J.cocomplex) (q p r : ℕ),
        ((row (ContinuousMonoidHom.id G) q).map f).f p ≫ (h M J q).hom p r =
          (h N I q).hom p r ≫ ((row (ContinuousMonoidHom.id G) q).map f).f r) := by
  sorry

end CategoryTheory.CondensedBar.Evaluated
