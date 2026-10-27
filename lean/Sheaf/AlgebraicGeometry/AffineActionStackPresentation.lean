/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.AlgebraicGeometry.AffineActionQuotientStack
public import Sheaf.AlgebraicGeometry.SchemeStackDiagonalPresentation
public import Sheaf.AlgebraicGeometry.ProjectiveLinearQuotient
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.KrullDimension
public import Mathlib.GroupTheory.GroupAction.Quotient
import Sheaf.AlgebraicGeometry.GroupoidScheme
import Sheaf.AlgebraicGeometry.ActionGroupoidTorsorComparison
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.ZeroDimensionalNoetherianFiniteDiscrete
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Spectral.Basic

/-! # Presentation and diagonal of an affine action quotient stack

Source: Stacks, algebraic.tex, Tags 04TK, 04WZ, 04X0; spaces-groupoids.tex,
Tags 04M9 and 044U; examples-stacks.tex, Tag 04WM. PGL: Milne, Algebraic Groups
(2017), Example 5.49 (blueprint: lem-sfb-affine-action-stack-presentation).

The helpers spell out the relation, stabilizer schemes, coordinate equalizer and
canonical maps. All scheme torsors and the canonical atlas are the recorded ones.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry.SchemeAction

variable (k E : Type u) [Field k] [CommRing E] [Algebra k E]
variable (G : Over (Spec (.of k))) [GrpObj G] [ModObj G (affineActionScheme k E)]

/-- The target/source relation map `(a,pr₂)`, with this order of projections.
Source: Stacks 04M9, 04WM (blueprint: lem-sfb-affine-action-stack-presentation). -/
def affineRelation : G ⊗ affineActionScheme k E ⟶
    affineActionScheme k E ⊗ affineActionScheme k E :=
  lift (ModObj.smul (M := G) (X := affineActionScheme k E)) (snd G _)

/-- The geometric stabilizer is the scheme fibre of the relation over `(v,v)`.
It represents the full equation `g • v = v`, retaining nilpotents.
Source: Stacks 04WM (blueprint: lem-sfb-affine-action-stack-presentation). -/
def affineStabilizer (Ω : Type u) [Field Ω] [Algebra k Ω]
    (v : affineActionScheme k Ω ⟶ affineActionScheme k E) : Scheme.{u} :=
  (pullback (affineRelation k E G) (lift v v)).left

/-- Pullback of a coordinate along the action, in the order `U × G`.
The canonical affine-product identification identifies this with `E → E ⊗ k[G]`.
Source: Stacks 04WM (blueprint: lem-sfb-affine-action-stack-presentation). -/
def affineCoordinateCoaction : E →+* Γ((affineActionScheme k E ⊗ G).left, ⊤) :=
  (((β_ (affineActionScheme k E) G).hom ≫
    ModObj.smul (M := G) (X := affineActionScheme k E)).left.appTop.hom).comp
      (Scheme.ΓSpecIso (.of E)).inv.hom

/-- The coordinate map `e ↦ e ⊗ 1`, expressed by the first projection.
Source: Stacks 04WM (blueprint: lem-sfb-affine-action-stack-presentation). -/
def affineCoordinateInclusion : E →+* Γ((affineActionScheme k E ⊗ G).left, ⊤) :=
  (fst (affineActionScheme k E) G).left.appTop.hom.comp
    (Scheme.ΓSpecIso (.of E)).inv.hom

/-- The invariant ring is the actual coaction equalizer, with no finite-generation claim.
Source: Stacks 04WM (blueprint: lem-sfb-affine-action-stack-presentation). -/
def affineInvariants : Subring E :=
  RingHom.eqLocus (affineCoordinateCoaction k E G) (affineCoordinateInclusion k E G)

/-- The coordinate ring k[G], retaining its scheme construction.
Source: Stacks 04WM (blueprint: lem-sfb-affine-action-stack-presentation). -/
def affineGroupCoordinates : Type u := Γ(G.left, ⊤)

/-- The coefficient map is pullback along the actual group structure map.
Source: Stacks 04WM (blueprint: lem-sfb-affine-action-stack-presentation). -/
instance affineGroupCoordinates.commRing : CommRing (affineGroupCoordinates k G) :=
  inferInstanceAs (CommRing Γ(G.left, ⊤))

/-- The specified k-algebra structure on k[G].
Source: Stacks 04WM (blueprint: lem-sfb-affine-action-stack-presentation). -/
instance affineGroupCoordinates.algebra : Algebra k (affineGroupCoordinates k G) :=
  (G.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra

/-- The canonical affine product comparison is uniquely fixed on the two factors.
Source: Stacks 04WM, affine tensor-product calculation
(blueprint: lem-sfb-affine-action-stack-presentation).
Proof: G is affine because it is affine over Spec k. Its canonical isoSpec and the
Gamma-Spec counit identify the product with Spec(E tensor k[G]); the universal
properties of the tensor product and affine fibre product give the two equations.
These factors generate the tensor product, so the equations determine the isomorphism. -/
theorem affineProductCoordinates_existsUnique [IsAffineHom G.hom] :
    ∃! e : Γ((affineActionScheme k E ⊗ G).left, ⊤) ≃+*
        E ⊗[k] affineGroupCoordinates k G,
      (∀ x : E, e (affineCoordinateInclusion k E G x) =
        Algebra.TensorProduct.includeLeftRingHom x) ∧
      (∀ x : affineGroupCoordinates k G,
        e ((snd (affineActionScheme k E) G).left.appTop.hom x) =
          Algebra.TensorProduct.includeRight x) := by
  sorry

/-- The unique canonical comparison with the tensor product, not an arbitrary isomorphism.
Source: Stacks 04WM (blueprint: lem-sfb-affine-action-stack-presentation). -/
def affineProductCoordinates [IsAffineHom G.hom] :
    Γ((affineActionScheme k E ⊗ G).left, ⊤) ≃+* E ⊗[k] affineGroupCoordinates k G :=
  Classical.choose (affineProductCoordinates_existsUnique k E G)

/-- The coordinate coaction in exactly the order E tensor k[G].
Source: Stacks 04WM (blueprint: lem-sfb-affine-action-stack-presentation). -/
def affineTensorCoaction [IsAffineHom G.hom] : E →+* E ⊗[k] affineGroupCoordinates k G :=
  (affineProductCoordinates k E G).toRingHom.comp (affineCoordinateCoaction k E G)

/-- The specified invariant subring is exactly the displayed tensor-coaction equalizer.
Source: Stacks 04WM (blueprint: lem-sfb-affine-action-stack-presentation).
Proof: the unique comparison sends the first projection to e tensor 1 and is injective.
Apply it to the equalizer equation defining affineInvariants. -/
theorem affineInvariants_mem_iff [IsAffineHom G.hom] (x : E) :
    x ∈ affineInvariants k E G ↔
      affineTensorCoaction k E G x = Algebra.TensorProduct.includeLeftRingHom x := by
  sorry

/-- Constants lie in the equalizer.
Source: Stacks 04WM (blueprint: lem-sfb-affine-action-stack-presentation).
Proof: the action and projection are k-morphisms. Apply global sections to their
identical composites with Spec k, then the natural Gamma-Spec comparison. -/
theorem affineInvariants_constants_mem (c : k) : algebraMap k E c ∈ affineInvariants k E G := by
  sorry

/-- Restriction of the specified coefficient map to the invariant ring.
Source: Stacks 04WM (blueprint: lem-sfb-affine-action-stack-presentation). -/
def affineInvariantConstants : k →+* affineInvariants k E G :=
  (algebraMap k E).codRestrict _ (affineInvariants_constants_mem k E G)

/-- The spectrum of the specified coaction equalizer over k.
Source: Stacks 04WM (blueprint: lem-sfb-affine-action-stack-presentation). -/
def affineInvariantSpectrum : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (affineInvariantConstants k E G)))

/-- The inclusion of invariants respects the specified structure morphisms.
Source: Stacks 04WM (blueprint: lem-sfb-affine-action-stack-presentation).
Proof: inclusion composed with the restricted coefficient map is the original
coefficient map; apply contravariant Spec and its composition law. -/
theorem affineInvariantProjection_over :
    Spec.map (CommRingCat.ofHom (affineInvariants k E G).subtype) ≫
      (affineInvariantSpectrum k E G).hom = (affineActionScheme k E).hom := by
  sorry

/-- The canonical scheme map is Spec of the inclusion of the equalizer into E.
Source: Stacks 04WM (blueprint: lem-sfb-affine-action-stack-presentation). -/
def affineInvariantProjection : affineActionScheme k E ⟶ affineInvariantSpectrum k E G :=
  Over.homMk (Spec.map (CommRingCat.ofHom (affineInvariants k E G).subtype))
    (affineInvariantProjection_over k E G)

/-- A geometric atlas point, as an object in the actual torsor fibre category.
Source: Stacks 04WM (blueprint: lem-sfb-affine-action-stack-presentation). -/
def affineAtlasPoint (Ω : Type u) [Field Ω] [Algebra k Ω]
    (x : affineActionScheme k Ω ⟶ affineActionScheme k E) :
    torsorFiber G (affineActionScheme k E) (affineActionScheme k Ω) :=
  ⟨trivialObject G (affineActionScheme k E) ⟨affineActionScheme k Ω, x⟩, rfl⟩

/-- The canonical atlas map on isomorphism classes is constant on group orbits.
Source: Stacks 04WM (blueprint: lem-sfb-affine-action-stack-presentation).
Proof: a group element carrying x to y gives the torsor isomorphism which is right
translation by its inverse. Thus the corresponding objects have the same skeleton class. -/
theorem affineAtlasPoint_orbit (Ω : Type u) [Field Ω] [Algebra k Ω]
    (x y : affineActionScheme k Ω ⟶ affineActionScheme k E)
    (h : MulAction.orbitRel (affineActionScheme k Ω ⟶ G)
      (affineActionScheme k Ω ⟶ affineActionScheme k E) x y) :
    toSkeleton (affineAtlasPoint k E G Ω x) =
      toSkeleton (affineAtlasPoint k E G Ω y) := by
  sorry

/-- The map from geometric orbits induced by the canonical atlas, with no chosen bijection.
Source: Stacks 04WM (blueprint: lem-sfb-affine-action-stack-presentation). -/
def affineOrbitToClasses (Ω : Type u) [Field Ω] [Algebra k Ω] :
    Quotient (MulAction.orbitRel (affineActionScheme k Ω ⟶ G)
      (affineActionScheme k Ω ⟶ affineActionScheme k E)) →
      Skeleton (torsorFiber G (affineActionScheme k E) (affineActionScheme k Ω)) :=
  Quotient.lift (fun x ↦ toSkeleton (affineAtlasPoint k E G Ω x))
    (affineAtlasPoint_orbit k E G Ω)

variable [Algebra.FiniteType k E]
variable [Smooth G.hom] [IsAffineHom G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]

/-- The quotient is algebraic and finite type, its specified atlas is smooth surjective,
and its diagonal is affine. The finite-type clause is explicitly a finite-type atlas.
Source: Stacks 04TK, 04WZ, 04X0, 04M9 (blueprint: lem-sfb-affine-action-stack-presentation).
Proof:
1. Form the action groupoid with source pr₂, target a and the usual multiplication,
identity and inverse. Smoothness of G makes source and target smooth by base change
and the involution (g,u) ↦ (g⁻¹,g u) (lem-sfb-stack-chartwise-smooth-etale-calculus).
2. Apply lem-sfb-smooth-groupoid-fppf-quotient and
lem-sfb-action-groupoid-torsor-comparison. They identify its stack with the specified
scheme-torsor quotient and its atlas with quotientAtlas. Its atlas base change at
(P,f) is P, by the trivialization h ↦ hp. The finite-type atlas is Spec E itself.
3. Tag 04M9 identifies the atlas relation with G × U. Swap objects and invert the
arrow to obtain target/source projections. Both source and target of (a,pr₂) are
affine, so this map is affine. Apply lem-sfb-representable-stack-fppf-locality along
the product atlas. Products of spaces use lem-trf-space-fibre-products-etale-covers. -/
theorem affine_action_stack_presentation :
    IsAlgebraicModuliStack (affineActionQuotientStack k E G) ∧
    IsSmoothModuliAtlas (affineActionQuotientStack k E G) (affineActionScheme k E)
      (quotientAtlas G (affineActionScheme k E)) ∧
    (∃ (W : Over (Spec (.of k)))
        (a : BasedFunctor (discreteModuli (yoneda.obj W)) (affineActionQuotientStack k E G)),
      IsSmoothModuliAtlas (affineActionQuotientStack k E G) W a ∧
        LocallyOfFiniteType W.hom ∧ QuasiCompact W.hom) ∧
    HasSchemeStackDiagonalWith (@IsAffineHom) (affineActionQuotientStack k E G) ∧
    IsSchemeStackDiagonalPresentation (quotientAtlas G (affineActionScheme k E))
      (quotientAtlas G (affineActionScheme k E))
      (ModObj.smul (M := G) (X := affineActionScheme k E)) (snd G _) := by
  sorry

/-- Zero-dimensional geometric stabilizer schemes give a quasi-finite separated diagonal.
Finite type and finite geometric fibres are written out, as stipulated in the node.
Source: Stacks 04XD, 0AAX (blueprint: lem-sfb-affine-action-stack-presentation).
Proof:
1. The chart map (a,pr₂) is finite type: generators of k[G] and E generate its source
ring over the target ring. It is separated because multiplication B ⊗_A B → B is
surjective, giving a closed relative diagonal.
2. A nonempty geometric transporter has a rational point g₀ by the closed-point
lemma and affine Nullstellensatz (lem-sc-quasi-compact-kolmogorov-closed-point,
lem-wf-affine-nullstellensatz-vanishing). Affines are qcqs and spectral by
lem-weil-pbc-affine-scheme-qcqs and lem-weil-pbc-qcqs-scheme-spectral.
3. Translation by g₀ identifies the full transporter scheme with the stabilizer.
It is zero-dimensional and Noetherian by lem-weil-pbc-finite-type-over-noetherian.
Apply lem-sc-zero-dim-noetherian-finite-discrete; empty fibres are finite as well.
4. The product atlas is smooth surjective by the chartwise calculus, hence fppf.
Apply lem-sfb-representable-stack-fppf-locality to descend quasi-finiteness and
separatedness from the computed relation map. -/
theorem affine_action_stack_diagonal_quasiFinite
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
      (v : affineActionScheme k Ω ⟶ affineActionScheme k E),
      topologicalKrullDim (affineStabilizer k E G Ω v) = 0) :
    HasSchemeStackDiagonalWith
      (fun _ Y f ↦ LocallyOfFiniteType f ∧ QuasiCompact f ∧
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y),
          Finite ↥(Limits.pullback f y)) ∧ IsClosedImmersion (pullback.diagonal f))
      (affineActionQuotientStack k E G) := by
  sorry

/-- Restriction along the atlas identifies maps to every algebraic space with invariant
maps. Extensions and their uniqueness are compared over the base by 2-isomorphisms.
Source: Stacks 044U, 04WM (blueprint: lem-sfb-affine-action-stack-presentation).
Proof: restriction is invariant since action arrows become identities in the discrete
target. Conversely choose local sections of a torsor P; two sections differ by a
unique group element, so invariance makes their maps to Z agree. The fppf sheaf
condition of Z glues uniquely. Common refinements prove independence of sections;
uniqueness of gluing proves functoriality and uniqueness up to vertical isomorphism.
This is the explicit torsor/sheaf argument of step 8 of the node, requiring no
separatedness of Z. -/
theorem affine_action_stack_space_maps (Z : AlgebraicSpace (Spec (.of k))) :
    (∀ F : BasedFunctor (affineActionQuotientStack k E G) (discreteModuli Z.obj.obj),
      ∃ b : yoneda.obj (affineActionScheme k E) ⟶ Z.obj.obj,
        Nonempty (ModuliTwoIso ((quotientAtlas G (affineActionScheme k E)).comp F)
          (discreteModuliMap b)) ∧
        yoneda.map (ModObj.smul (M := G) (X := affineActionScheme k E)) ≫ b =
          yoneda.map (snd G (affineActionScheme k E)) ≫ b) ∧
    (∀ b : yoneda.obj (affineActionScheme k E) ⟶ Z.obj.obj,
      yoneda.map (ModObj.smul (M := G) (X := affineActionScheme k E)) ≫ b =
          yoneda.map (snd G (affineActionScheme k E)) ≫ b →
      ∃ F : BasedFunctor (affineActionQuotientStack k E G) (discreteModuli Z.obj.obj),
        Nonempty (ModuliTwoIso ((quotientAtlas G (affineActionScheme k E)).comp F)
          (discreteModuliMap b)) ∧
        ∀ H : BasedFunctor (affineActionQuotientStack k E G) (discreteModuli Z.obj.obj),
          Nonempty (ModuliTwoIso ((quotientAtlas G (affineActionScheme k E)).comp H)
            (discreteModuliMap b)) → Nonempty (F ≅ H)) := by
  sorry

/-- The canonical orbit-to-isomorphism-class map is a bijection over algebraically
closed extensions, including all isomorphism classes of scheme torsors.
Source: Stacks 04WM (blueprint: lem-sfb-affine-action-stack-presentation).
Proof: the atlas base change at (P,f) is the nonempty smooth scheme P. Choose a
finite-type affine neighbourhood. A closed point exists by the compact Kolmogorov
closed-point lemma; its residue field is Ω by the affine Nullstellensatz. A point
trivializes P, proving surjectivity. The action-groupoid comparison says that arrows
between atlas points are exactly the elements g carrying one point to the other,
proving injectivity on orbits. This is steps 4 and 5 of the node's proof. -/
theorem affine_action_stack_geometric_orbits
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] :
    Function.Bijective (affineOrbitToClasses k E G Ω) := by
  sorry

/-- The canonical invariant-spectrum map has exactly the Spec-of-inclusion composite
with the canonical atlas, and is unique up to vertical isomorphism.
Source: Stacks 044U, 04WM (blueprint: lem-sfb-affine-action-stack-presentation).
Proof: the equalizer inclusion makes the scheme map invariant. Its target is a
scheme, hence an algebraic space: fpqc representable descent and the fact that fppf
coverings are fpqc give its sheaf condition; scheme fibre products give the diagonal,
and its identity is an etale surjective atlas. Apply the space-maps assertion, with
this invariant spectrum, to obtain the unique extension. No finite generation of
the invariant ring is used. This is step 9 of the node's proof. -/
theorem affine_action_stack_invariant_spectrum :
    ∃ φ : BasedFunctor (affineActionQuotientStack k E G)
        (discreteModuli (yoneda.obj (affineInvariantSpectrum k E G))),
      Nonempty (ModuliTwoIso ((quotientAtlas G (affineActionScheme k E)).comp φ)
        (discreteModuliMap (yoneda.map (affineInvariantProjection k E G)))) ∧
      ∀ ψ : BasedFunctor (affineActionQuotientStack k E G)
          (discreteModuli (yoneda.obj (affineInvariantSpectrum k E G))),
        Nonempty (ModuliTwoIso ((quotientAtlas G (affineActionScheme k E)).comp ψ)
          (discreteModuliMap (yoneda.map (affineInvariantProjection k E G)))) →
            Nonempty (φ ≅ ψ) := by
  sorry

end AlgebraicGeometry.SchemeAction

namespace AlgebraicGeometry

/-- For every positive rank the scalar quotient PGL is represented by a smooth affine
finite-type group scheme. Thus the preceding assertions specialize to every PGL action.
Source: Milne, Example 5.49, printed p.111; Alper, §9, printed p.40
(blueprint: lem-sfb-affine-action-stack-presentation).
Proof: apply lem-sfb-pgl-reductive-structure, keeping its smooth, affine and finite-type
clauses and its scalar-quotient identification. For r = 1 the quotient is the trivial
group scheme Spec k. No characteristic or invertibility assumption is used. These
are precisely the hypotheses of the preceding assertions (step 10 of the node). -/
theorem affine_action_stack_pgl (k : Type u) [Field k] (r : ℕ) (hr : 1 ≤ r) :
    ∃ G : Grp (Over (Spec (.of k))),
      IsProjectiveLinearQuotient k r G.X ∧ Smooth G.X.hom ∧ IsAffineHom G.X.hom ∧
        LocallyOfFiniteType G.X.hom ∧ QuasiCompact G.X.hom := by
  sorry

end AlgebraicGeometry
