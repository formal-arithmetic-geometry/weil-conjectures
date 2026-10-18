/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-! # The complete flag bundle by tautological kernels

Source: Stacks Project, Chow Homology, Tag 02UL, proof of
`lemma-splitting-principle` (blueprint: def-pur-complete-flag-bundle).

`completeFlagBundle` is the rank recursion. Its levels are actual sheaves with maps to
its pulled-back module. `completeFlagStep` is the uniquely determined inclusion between
successive levels, and `completeFlagQuotient` is its sheaf cokernel.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry

/-- The universal property fixing a normalized quotient-line projectivization.
The line quotient is a sheaf epimorphism, and the comparison must carry the
prescribed universal quotient to that very quotient.
Source: Stacks, Tag 01OB (blueprint: def-pur-complete-flag-bundle). -/
def IsCompleteFlagProjectivization {T : Scheme.{u}} {F : T.Modules}
    (D : ProjectiveBundleRealization T F) : Prop :=
  ∀ (S : Scheme.{u}) (f : S ⟶ T) (M : S.Modules) [M.IsInvertible]
    (ε : (Scheme.Modules.tensorPullback f).obj F ⟶ M) [Epi ε],
    ∃! g : S ⟶ D.A.data.relProj, ∃ h : g ≫ D.A.data.relProjHom = f,
      ∃ θ : (Scheme.Modules.tensorPullback g).obj D.L ≅ M,
        (Scheme.Modules.tensorPullback g).map D.quotient ≫ θ.hom =
          ((Scheme.Modules.tensorPullbackSectionComp g D.A.data.relProjHom).app F).inv ≫
            (projectiveBundlePullbackCongr h).hom.app F ≫ ε

/-- The normalized symmetric-algebra projectivization has its quotient-line universal
property, which determines the scheme and quotient up to canonical isomorphism.
Source: Stacks, Tags 01OB and 01OE (blueprint: def-pur-complete-flag-bundle).
Proof: take the normalized projective-bundle geometry of
`lem-pur-projective-bundle-tautological-geometry`. Locally trivialize the given line
quotient and a frame of `F`. Where its j-th coefficient is a unit, the ratios of the
other coefficients to it define the unique map to `D₊(Xⱼ)`. The quotient being epi
makes these opens a cover. The ratio maps agree on overlaps and glue. They are
unchanged by a frame change, since the symmetric algebra uses the same change of
basis on its degree-one generators. The normalized twist generator maps to the
j-th coefficient, giving the line isomorphism and the displayed quotient square.
The ratios force uniqueness of the scheme map; surjectivity of the quotient
forces uniqueness of the line comparison. Thus only a universal-property proof
is postponed, with all projectivization data fixed up to canonical isomorphism. -/
theorem exists_completeFlagProjectivization (T : Scheme.{u}) (n : ℕ)
    (F : T.Modules) [F.IsFiniteLocallyFreeOfRank (n + 1)] :
    ∃ D : ProjectiveBundleRealization T F, IsCompleteFlagProjectivization D := by
  sorry

/-- A representative of the universal, normalized projectivization of the actual
symmetric algebra. The existence theorem specifies its universal property, while
`ProjectiveBundleRealization` fixes the affine algebras, restrictions, twist and
quotient by their homogeneous-localization formulas. Its data are determined up
to the canonical isomorphism used in interpreting the construction.
Source: Stacks, Tags 01OB, 01NR, 02UL (blueprint: def-pur-complete-flag-bundle). -/
noncomputable def completeFlagProjectivization (T : Scheme.{u}) (n : ℕ)
    (F : T.Modules) [F.IsFiniteLocallyFreeOfRank (n + 1)] :
    ProjectiveBundleRealization T F :=
  Classical.choose (exists_completeFlagProjectivization T n F)

/-- The tautological kernel is the categorical kernel in sheaves of modules, hence
is the subsheaf of sections annihilated by the prescribed quotient.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle). -/
noncomputable def completeFlagKernel (T : Scheme.{u}) (n : ℕ)
    (F : T.Modules) [F.IsFiniteLocallyFreeOfRank (n + 1)] :
    (completeFlagProjectivization T n F).A.data.relProj.Modules :=
  kernel (completeFlagProjectivization T n F).quotient

/-- The explicit chart splitting and kernel basis. On `D₊(Xⱼ)` take `aᵢ=Xᵢ/Xⱼ`,
`v` the pulled-back frame and `τ=τⱼ`; the normalized quotient and its overlap
formulas are those of `ProjectiveBundleRealization` and `ProjectiveBundleFrameChart`.
Source: Stacks, Tags 01OB and 02UL (blueprint: def-pur-complete-flag-bundle).
Proof: every section of the line is uniquely a multiple of `τ`. Send that multiple
to the same multiple of `vⱼ`. Since `aⱼ=1`, this is a section of the quotient.
For a kernel vector subtract the sum of its coefficients away from j times
`vᵢ-aᵢvⱼ`. The result is a multiple of `vⱼ` in the kernel, hence zero because
`τ` is a free generator. The coefficients away from j also prove independence.
Sections of the sheaf kernel are precisely the sectionwise kernel, since the
sections functor preserves limits. This identifies the displayed basis with
sections of the actual sheaf kernel, on every further open in the chart. -/
theorem completeFlagKernel_chart {T : Scheme.{u}} {F : T.Modules}
    (D : ProjectiveBundleRealization T F) (r : ℕ)
    (W : D.A.data.relProj.Opens)
    (v : Module.Basis (Fin r) Γ(D.A.data.relProj, W)
      Γ((Scheme.Modules.tensorPullback D.A.data.relProjHom).obj F, W))
    (τ : Γ(D.L, W)) (hτ : Scheme.Modules.IsFreeGenerator τ)
    (j : Fin r) (a : Fin r → Γ(D.A.data.relProj, W)) (hj : a j = 1)
    (hε : ∀ i : Fin r, Scheme.Modules.Hom.app D.quotient W (v i) = a i • τ) :
    (∃ s : Γ(D.L, W) →ₗ[Γ(D.A.data.relProj, W)]
        Γ((Scheme.Modules.tensorPullback D.A.data.relProjHom).obj F, W),
      s τ = v j ∧ ∀ x : Γ(D.L, W), Scheme.Modules.Hom.app D.quotient W (s x) = x) ∧
    ∃ b : Module.Basis {i : Fin r // i ≠ j} Γ(D.A.data.relProj, W)
        Γ(kernel D.quotient, W),
      ∀ i : {i : Fin r // i ≠ j},
        Scheme.Modules.Hom.app (kernel.ι D.quotient) W (b i) = v i.1 - a i.1 • v j := by
  sorry

/-- The tautological quotient is locally split, and its displayed local splittings
remain splittings after every pullback. This asserts no global splitting.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle).
Proof: refine the frame cover by the standard opens `D₊(Xⱼ)`. On each one send
the twist generator to the j-th frame vector; the quotient formula gives the
identity on the generator and hence on the line sheaf. Pull back these local
sections along `g`, and then restrict to a neighbourhood of the given point.
Functoriality preserves the section equation. The preimages of the chart cover
cover S, giving the asserted local splittings for every pullback. -/
theorem completeFlagKernel_pullback_locally_split (T : Scheme.{u}) (n : ℕ)
    (F : T.Modules) [F.IsFiniteLocallyFreeOfRank (n + 1)]
    (S : Scheme.{u}) (g : S ⟶ (completeFlagProjectivization T n F).A.data.relProj) :
    ∀ x : S, ∃ W : S.Opens, x ∈ W ∧
      ∃ s : (Scheme.Modules.tensorPullback W.ι).obj
          ((Scheme.Modules.tensorPullback g).obj (completeFlagProjectivization T n F).L) ⟶
        (Scheme.Modules.tensorPullback W.ι).obj
          ((Scheme.Modules.tensorPullback g).obj
            ((Scheme.Modules.tensorPullback
              (completeFlagProjectivization T n F).A.data.relProjHom).obj F)),
        s ≫ (Scheme.Modules.tensorPullback W.ι).map
          ((Scheme.Modules.tensorPullback g).map
            (completeFlagProjectivization T n F).quotient) = 𝟙 _ := by
  sorry

/-- The rank needed for the recursive call.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle).
Proof: in a frame on `D₊(Xⱼ)`, the quotient sends `vᵢ` to `(Xᵢ/Xⱼ)τⱼ`.
It has the section `τⱼ ↦ vⱼ`; its kernel has the free basis
`vᵢ - (Xᵢ/Xⱼ)vⱼ`, for `i ≠ j`. The standard opens over a frame cover cover
projective space; the frame opens cover the base. These bases therefore prove
finite local freeness of rank `n`. The normalized degree-one maps ensure that
these are the kernel of the same global quotient on overlaps and under frame changes. -/
theorem completeFlagKernel_rank (T : Scheme.{u}) (n : ℕ)
    (F : T.Modules) [F.IsFiniteLocallyFreeOfRank (n + 1)] :
    (completeFlagKernel T n F).IsFiniteLocallyFreeOfRank n := by
  sorry

/-- A scheme over `T` together with a family of actual subsheaf presentations.
Levels past the rank are repeated final levels; only levels `0,…,r` are used.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle). -/
structure CompleteFlagBundleData (T : Scheme.{u}) (F : T.Modules) where
  scheme : Scheme.{u}
  projection : scheme ⟶ T
  level : ℕ → scheme.Modules
  inclusion : ∀ i : ℕ, level i ⟶ (Scheme.Modules.tensorPullback projection).obj F

/-- The identity bundle with its zero and full levels, used at ranks zero and one.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle). -/
noncomputable def completeFlagIdentity (T : Scheme.{u}) (F : T.Modules) :
    CompleteFlagBundleData T F where
  scheme := T
  projection := 𝟙 T
  level i := if i = 0 then 0 else (Scheme.Modules.tensorPullback (𝟙 T)).obj F
  inclusion i := if h : i = 0 then
    eqToHom (if_pos h) ≫ 0
    else eqToHom (if_neg h) ≫ 𝟙 _

/-- Extend a recursive kernel filtration by its ambient pulled-back module.
The embeddings use the actual kernel inclusion and the section-normalized comparison
`h* q* F ≅ (h ≫ q)* F`. No global splitting is chosen.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle). -/
noncomputable def completeFlagExtend {T : Scheme.{u}} {F : T.Modules}
    (D : ProjectiveBundleRealization T F)
    (G : CompleteFlagBundleData D.A.data.relProj (kernel D.quotient)) (r : ℕ) :
    CompleteFlagBundleData T F where
  scheme := G.scheme
  projection := G.projection ≫ D.A.data.relProjHom
  level i := if i < r then G.level i else
    (Scheme.Modules.tensorPullback (G.projection ≫ D.A.data.relProjHom)).obj F
  inclusion i := if h : i < r then
    eqToHom (if_pos h) ≫ G.inclusion i ≫
      (Scheme.Modules.tensorPullback G.projection).map (kernel.ι D.quotient) ≫
      ((Scheme.Modules.tensorPullbackSectionComp G.projection D.A.data.relProjHom).app F).inv
    else eqToHom (if_neg h) ≫ 𝟙 _

/-- The complete flag bundle, recursively projectivizing the tautological kernel.
At ranks zero and one its projection is the identity. At rank `n+2` it is the
composite of the recursively constructed rank-`n+1` flag projection with the
projectivization projection; its earlier levels are the recursive kernel levels.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle). -/
noncomputable def completeFlagBundle : (r : ℕ) → (T : Scheme.{u}) → (F : T.Modules) →
    [F.IsFiniteLocallyFreeOfRank r] → CompleteFlagBundleData T F
  | 0, T, F, _ => completeFlagIdentity T F
  | 1, T, F, _ => completeFlagIdentity T F
  | n + 2, T, F, _ =>
    let D := completeFlagProjectivization T (n + 1) F
    letI := completeFlagKernel_rank T (n + 1) F
    completeFlagExtend D
      (completeFlagBundle (n + 1) D.A.data.relProj (completeFlagKernel T (n + 1) F))
      (n + 2)

/-- The recursive kernel flag, exposing the map `h` used at rank `n+2`.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle). -/
noncomputable def completeFlagPredecessor (T : Scheme.{u}) (n : ℕ) (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank (n + 2)] :
    CompleteFlagBundleData (completeFlagProjectivization T (n + 1) F).A.data.relProj
      (completeFlagKernel T (n + 1) F) :=
  letI := completeFlagKernel_rank T (n + 1) F
  completeFlagBundle (n + 1) _ (completeFlagKernel T (n + 1) F)

/-- Each presented level is a subsheaf.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle).
Proof: for the identity cases, the zero and identity maps are monomorphisms.
In the induction step the recursive maps are monic by induction. The chart
splitting `τⱼ ↦ vⱼ` makes the kernel inclusion split on the standard open cover;
a split inclusion remains split after any pullback. Composing this pulled-back
inclusion with the recursive inclusion and the pullback comparison remains monic. -/
theorem completeFlagBundle_mono (r : ℕ) (T : Scheme.{u}) (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] (i : ℕ) :
    Mono ((completeFlagBundle r T F).inclusion i) := by
  sorry

/-- The levels form an increasing filtration; the factor map is uniquely determined.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle).
Proof: at ranks zero and one the factors are zero or identity maps. At a higher
rank use the recursive factor while both levels are kernel levels. At the last
step use the pulled-back kernel inclusion, composed with the last recursive
level map. Thereafter use identities. The equations follow by composition with
the ambient inclusion. Uniqueness follows from `completeFlagBundle_mono`. -/
theorem completeFlagBundle_step_unique (r : ℕ) (T : Scheme.{u}) (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] (i : ℕ) :
    ∃! f : (completeFlagBundle r T F).level i ⟶ (completeFlagBundle r T F).level (i + 1),
      f ≫ (completeFlagBundle r T F).inclusion (i + 1) =
        (completeFlagBundle r T F).inclusion i := by
  sorry

/-- The uniquely characterized inclusion `Fᵢ ⟶ Fᵢ₊₁`.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle). -/
noncomputable def completeFlagStep (r : ℕ) (T : Scheme.{u}) (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] (i : ℕ) :
    (completeFlagBundle r T F).level i ⟶ (completeFlagBundle r T F).level (i + 1) :=
  Classical.choose (completeFlagBundle_step_unique r T F i)

/-- The successive quotient `Qᵢ₊₁ = Fᵢ₊₁/Fᵢ`, taken in sheaves of modules.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle). -/
noncomputable def completeFlagQuotient (r : ℕ) (T : Scheme.{u}) (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] (i : ℕ) : (completeFlagBundle r T F).scheme.Modules :=
  cokernel (completeFlagStep r T F i)

/-- The last quotient is the pullback of the tautological line by the recursive map,
with quotient map the pulled-back tautological quotient `h*ε` under `p*F ≅ h*q*F`.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle).
Proof: the chart section of the tautological quotient splits its kernel sequence.
After pullback by `h` this is still a split exact sequence. Its kernel is the
last recursive level, by induction. These local cokernel identifications carry
the quotient map to `h*ε`, so agree on overlaps by the cokernel universal property.
They glue to the stated isomorphism, without a global splitting. -/
theorem completeFlagBundle_last_quotient (T : Scheme.{u}) (n : ℕ) (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank (n + 2)] :
    ∃ θ : completeFlagQuotient (n + 2) T F (n + 1) ≅
        (Scheme.Modules.tensorPullback (completeFlagPredecessor T n F).projection).obj
          (completeFlagProjectivization T (n + 1) F).L,
      cokernel.π (completeFlagStep (n + 2) T F (n + 1)) ≫ θ.hom =
        (completeFlagBundle (n + 2) T F).inclusion (n + 2) ≫
          ((Scheme.Modules.tensorPullbackSectionComp (completeFlagPredecessor T n F).projection
            (completeFlagProjectivization T (n + 1) F).A.data.relProjHom).app F).hom ≫
          (Scheme.Modules.tensorPullback (completeFlagPredecessor T n F).projection).map
            (completeFlagProjectivization T (n + 1) F).quotient := by
  sorry

/-- Endpoints, line quotients and the vector subbundle property of the universal filtration.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle).
Proof: induct on the rank. Rank zero means `F` is locally zero, hence zero by
sheaf separatedness. At rank one the sole quotient is the pullback of `F` by the
identity, and is invertible. At rank `n+2`, on a pulled-back standard chart the
splitting of the tautological quotient gives `h*q*F = h*K ⊕ h*L`. Refine by an
adapted frame for the recursive filtration. This gives an adapted frame for the
new one: its earlier quotients are the recursive line quotients, its last is
`h*L`, and every ambient quotient by a level is locally free. The initial level
is zero by induction and the final inclusion is the identity by construction.
Only these local splittings, and no global splitting, are used. -/
theorem completeFlagBundle_properties (r : ℕ) (T : Scheme.{u}) (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] :
    IsZero ((completeFlagBundle r T F).level 0) ∧
    IsIso ((completeFlagBundle r T F).inclusion r) ∧
    (∀ i : ℕ, i < r → (completeFlagQuotient r T F i).IsInvertible) ∧
    (∀ i : ℕ, i ≤ r →
      (cokernel ((completeFlagBundle r T F).inclusion i)).IsLocallyFree) := by
  sorry

end AlgebraicGeometry
