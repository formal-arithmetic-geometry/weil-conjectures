module

public import Sheaf.AlgebraicGeometry.KummerEtaleGCover
public import Sheaf.AlgebraicGeometry.DivisorialLogCoverBoundary
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.AlgebraicGeometry.VeryTameFSLogAction
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

import Sheaf.AlgebraicGeometry.AssociatedLogUniversalStalks
import Sheaf.TraceFormula.LogRegularDivisorialStructure
import Sheaf.TraceFormula.FiniteBaseStrictLocalization
import Sheaf.AlgebraicGeometry.FiniteGroupInertiaInvariantsEtale
import Sheaf.AlgebraicGeometry.LogBlowupNormalization

/-!
# Deleting auxiliary boundary from a tame Kummer cover

Source: ILO VIII 5.3.8--5.3.10, IX Proposition 2.1, VI 1.8, 2.1--2.3 and 3.1
(blueprint: lem-per-kummer-boundary-restriction).

The statements retain disconnected and empty schemes. The full fs category is used
for arbitrary base change; the original locally Noetherian objects and action predicates
are used for log regularity and very tameness. No order condition on the whole group occurs.
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Delete a reduced union of auxiliary unramified boundary components. The quotient
conditions below are the invariant structure sheaf and geometric orbit fibres; they
are imposed on the given scheme map and action, not on a replacement quotient.
Source: ILO VIII 5.3.8, last paragraph; IX Proposition 2.1
(blueprint: lem-per-kummer-boundary-restriction).

Proof (DAG steps 1--4 and 8): work on pointed étale strict normal-crossings charts
for the smaller boundary. The tame-inertia root quotient theorem presents each strict
local component as B^K for B=A[x_i]/(x_i^n-t_i), n locally invertible. The invariant
monoid algebra theorem identifies B^K with A tensor_{Z[P]} Z[Q], with P=N^r and
Q the nonnegative character-annihilator lattice. Its map P to Q is injective Kummer
with cokernel killed by n. Associated-log universal stalks and the toric comparison
give the actual compatible chart. Invertible Kummer charts imply log regularity.
The divisorial-structure theorem identifies its log sheaf with functions invertible
off the smaller boundary; uniqueness makes the charts and actions glue. Finite
character-annihilator duality identifies inertia with the character deck group.
The strict local standard model identifies the fs diagonal with the disjoint union
indexed by inertia; induction to G gives the prescribed global G-diagonal. Characters
fix characteristic monoids and the quotient by all nonconstant monomials, hence the
strict local log stratum; inertia has invertible order. This is very tameness. The
argument is local on every component and also covers empty boundaries and schemes. -/
theorem kummer_boundary_restriction
    {V Y : FineSaturatedLogScheme.{u}} [IsNoetherian Y.scheme]
    (hY : IsRegularScheme Y.scheme) (hVnormal : ∀ x : V.scheme,
      IsDomain (V.scheme.presheaf.stalk x) ∧
        IsIntegrallyClosed (V.scheme.presheaf.stalk x))
    {G : Type v} [Group G] [Finite G]
    (q : EtaleLogHom V Y) (a : FSLogGroupAction G V)
    (B D : Y.scheme.IdealSheafData)
    (hB : B.IsNormalCrossingsDivisor) (hD : D.IsReducedComponentUnion B)
    (hV : V.logStructure.IsDivisorialFor (q.base ⁻¹ᵁ B.support.compl))
    (hlogY : Y.logStructure.IsDivisorialFor B.support.compl)
    (hcover : FSLogScheme.IsKummerEtaleGCover
      (X := V.toFSLogScheme) (Y := Y.toFSLogScheme) q.toLogMap
      (fun g ↦ (a.logMap g).toLogMap))
    (htame : a.IsTame) (hfree : a.IsGenericallyFree)
    (horbits : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s t : Spec (.of Ω) ⟶ V.scheme), s ≫ q.base = t ≫ q.base ↔
        ∃ g : G, s ≫ (a.baseAction g).hom = t)
    (hinvariants : ∀ U : Y.scheme.Opens,
      Function.Injective (q.base.app U).hom ∧
        ∀ s : Γ(V.scheme, q.base ⁻¹ᵁ U),
          s ∈ Set.range (q.base.app U).hom ↔
            ∀ (g : G) (W : V.scheme.Opens) (hW : W ≤ q.base ⁻¹ᵁ U)
              (hWg : W ≤ (a.baseAction g).hom ⁻¹ᵁ (q.base ⁻¹ᵁ U)),
              ((a.baseAction g).hom.appLE (q.base ⁻¹ᵁ U) W hWg).hom s =
                (V.scheme.presheaf.map (homOfLE hW).op).hom s)
    (hetale : Etale (q.base ∣_ D.support.compl)) :
    ∃ (MV : EtaleLogStructure V.scheme) (MY : EtaleLogStructure Y.scheme)
      (hMV : MV.IsFineSaturated) (hMY : MY.IsFineSaturated)
      (f : EtaleLogHom
        ⟨V.scheme, V.locallyNoetherian, MV, hMV⟩
        ⟨Y.scheme, Y.locallyNoetherian, MY, hMY⟩)
      (b : FSLogGroupAction G ⟨V.scheme, V.locallyNoetherian, MV, hMV⟩),
      MV.IsDivisorialFor (q.base ⁻¹ᵁ D.support.compl) ∧
      MY.IsDivisorialFor D.support.compl ∧ f.base = q.base ∧
      b.baseAction = a.baseAction ∧
      FSLogScheme.IsKummerEtaleGCover
        (X := (FineSaturatedLogScheme.mk V.scheme V.locallyNoetherian MV hMV).toFSLogScheme)
        (Y := (FineSaturatedLogScheme.mk Y.scheme Y.locallyNoetherian MY hMY).toFSLogScheme)
        f.toLogMap (fun g ↦ (b.logMap g).toLogMap) ∧
      (FineSaturatedLogScheme.mk V.scheme V.locallyNoetherian MV hMV).IsLogRegular ∧
      b.IsVeryTame := by
  sorry

/-- Arbitrary fs base change preserves the cover and the prescribed deck action.
The existential fs pullback is part of the assertion, so no existence of a product
is assumed. Equivariance fixes the induced action uniquely by its projections.
Source: ILO VI 2.1--2.3; X 1.8 (blueprint: lem-per-kummer-boundary-restriction).

Proof (DAG step 5): choose compatible charts P to Q and P to R. The saturated
pushout S=(Q plus_P R)^{int,sat} presents the fs product. The saturated-pushout
algebra theorem gives an injective Kummer map R to S with finite invertible
cokernel and finite surjective comparison to the ordinary scheme product.
The chart comparison is étale by ordinary étale base change. Universal properties
glue the charts and pull the original G-diagonal to the new G-diagonal. Nothing
in this argument requires Noetherianity. The construction works on every component. -/
theorem kummer_cover_fs_baseChange
    {X Y Y' : FSLogScheme.{u}} {G : Type v} [Group G] [Finite G]
    (f : X ⟶ Y) (a : G → (X ⟶ X))
    (hf : FSLogScheme.IsKummerEtaleGCover f a) (b : Y' ⟶ Y) :
    ∃ (X' : FSLogScheme.{u}) (p : X' ⟶ X) (q : X' ⟶ Y') (a' : G → (X' ⟶ X')),
      IsPullback p q f b ∧ FSLogScheme.IsKummerEtaleGCover q a' ∧
        ∀ g : G, a' g ≫ p = p ≫ a g ∧ a' g ≫ q = q := by
  sorry

/-- Log regularity, very tame inertia, ordinary torsors over the trivial-log open,
and étaleness wherever geometric inertia is trivial.
Source: ILO VI 1.8, 2.2--2.3, 3.1; Stacks 0BST
(blueprint: lem-per-kummer-boundary-restriction).

Proof (DAG steps 4, 6, 8): the invertible-Kummer chart theorem gives log regularity.
In the strict local standard model inertia acts by characters on Q, fixing Q modulo
units and B/J=A/I. Its order is invertible, which proves very tameness. On the
trivial-log locus sharp saturated Kummer monoids have P=Q=0, so the cover is finite
étale and the G-diagonal is the ordinary torsor diagonal. For trivial inertia, the
standard-model invariants identify the base with R^G. The inertia-invariants étale
lemma, Stacks 0BST, with I=1 gives an étale neighbourhood of the source point.
These are local computations, valid on each component and on empty schemes. -/
theorem kummer_cover_logRegular_veryTame
    {X Y : FineSaturatedLogScheme.{u}} {G : Type v} [Group G] [Finite G]
    (f : EtaleLogHom X Y) (a : FSLogGroupAction G X)
    (hf : FSLogScheme.IsKummerEtaleGCover
      (X := X.toFSLogScheme) (Y := Y.toFSLogScheme) f.toLogMap
      (fun g ↦ (a.logMap g).toLogMap)) (hY : Y.IsLogRegular) :
    X.IsLogRegular ∧ a.IsVeryTame ∧
    (∀ U : Y.scheme.Opens, (U : Set Y.scheme) ⊆ Y.logStructure.trivialityLocus →
      Etale (f.base ∣_ U) ∧ IsFinite (f.base ∣_ U) ∧ Surjective (f.base ∣_ U) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s t : Spec (.of Ω) ⟶ X.scheme),
        f.base (s default) ∈ U → s ≫ f.base = t ≫ f.base →
          ∃! g : G, s ≫ (a.baseAction g).hom = t) ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme),
      (∀ g : G, t ≫ (a.baseAction g).hom = t → g = 1) →
        ∃ U : X.scheme.Opens, t default ∈ U ∧ Etale (U.ι ≫ f.base) := by
  sorry

/-- A birational saturated log blowup pulls the cover back to the normalization
of the modified base in its original generic cover. The dense trivial-log open
supplies that cover, with the canonical normalization map retained.
Source: ILO VIII 3.3.9--3.3.11, 5.3.8--5.3.10; IX 2.1(ii)
(blueprint: lem-per-kummer-boundary-restriction).

Proof (DAG steps 5, 7--8): log blowups preserve log regularity and the dense
trivial-log open. Base change is finite and log regular by the preceding assertions.
The divisorial-structure theorem implies normality and density of the same open
upstairs. Componentwise, the generic cover is unchanged by the birational map.
Finite-normal-cover recognition identifies every affine ring with the integral
closure of the modified base ring in that generic cover. The canonical inclusions
agree on overlaps, giving the stated isomorphism over the modified base, also for
finite disjoint unions. No excellence assumption or separate finiteness theorem
for normalization is used. Identity blowups give the identity comparison. -/
theorem kummer_cover_logBlowup_normalization
    {X Y Y' X' : FineSaturatedLogScheme.{u}} {G : Type v} [Group G] [Finite G]
    (f : EtaleLogHom X Y) (a : FSLogGroupAction G X)
    (hf : FSLogScheme.IsKummerEtaleGCover
      (X := X.toFSLogScheme) (Y := Y.toFSLogScheme) f.toLogMap
      (fun g ↦ (a.logMap g).toLogMap))
    (hY : Y.IsLogRegular) (b : EtaleLogHom Y' Y)
    (I : Y.logStructure.IdealFamily) (hI : Y.logStructure.IsNonemptyCoherentIdeal I)
    (hb : IsSaturatedLogBlowup b I)
    (hbir : ∃ U : Y.scheme.Opens, Dense (U : Set Y.scheme) ∧ IsIso (b.base ∣_ U))
    (p : EtaleLogHom X' X) (q : EtaleLogHom X' Y')
    (hsquare : IsPullback
      (P := X'.toFSLogScheme) (X := X.toFSLogScheme)
      (Y := Y'.toFSLogScheme) (Z := Y.toFSLogScheme)
      p.toLogMap q.toLogMap f.toLogMap b.toLogMap)
    (U : Y.scheme.Opens) (hU : (U : Set Y.scheme) = Y.logStructure.trivialityLocus) :
    ∃ (hqc : QuasiCompact
        (pullback.snd f.base ((b.base ⁻¹ᵁ U).ι ≫ b.base) ≫ (b.base ⁻¹ᵁ U).ι))
      (hqs : QuasiSeparated
        (pullback.snd f.base ((b.base ⁻¹ᵁ U).ι ≫ b.base) ≫ (b.base ⁻¹ᵁ U).ι)),
      ∃ e : X'.scheme ≅
        @Scheme.Hom.normalization _ _
          (pullback.snd f.base ((b.base ⁻¹ᵁ U).ι ≫ b.base) ≫ (b.base ⁻¹ᵁ U).ι) hqc hqs,
        e.hom ≫ @Scheme.Hom.fromNormalization _ _
          (pullback.snd f.base ((b.base ⁻¹ᵁ U).ι ≫ b.base) ≫ (b.base ⁻¹ᵁ U).ι) hqc hqs =
          q.base ∧
        ∃ j : pullback f.base ((b.base ⁻¹ᵁ U).ι ≫ b.base) ⟶ X'.scheme,
          j ≫ p.base = pullback.fst f.base ((b.base ⁻¹ᵁ U).ι ≫ b.base) ∧
          j ≫ q.base =
            pullback.snd f.base ((b.base ⁻¹ᵁ U).ι ≫ b.base) ≫ (b.base ⁻¹ᵁ U).ι ∧
          j ≫ e.hom = @Scheme.Hom.toNormalization _ _
            (pullback.snd f.base ((b.base ⁻¹ᵁ U).ι ≫ b.base) ≫ (b.base ⁻¹ᵁ U).ι) hqc hqs := by
  sorry

end AlgebraicGeometry
