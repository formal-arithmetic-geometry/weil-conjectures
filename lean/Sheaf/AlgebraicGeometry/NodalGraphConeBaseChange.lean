/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q158
-/
module

public import Sheaf.AlgebraicGeometry.GraphConeGluing
public import Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.TensorProduct.Basic
import Sheaf.AlgebraicGeometry.ConormalAlgebraFlatBaseChange
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.FpqcFinerThanEtale
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty

/-! # Arbitrary base change of the nodal graph cone

Source: Stacks Project, Divisors, Tags 0634 and 0635; Curves, Tag 0CBY;
Constructions, Tag 01O3 (blueprint: lem-sfb-nodal-graph-cone-base-change).

The comparison is given in the existing affine-basis model of graded quasi-coherent
algebras. `PullbackData` asserts that its canonical semilinear maps induce isomorphisms
on coefficient tensors in every degree. The ideal-representative equation fixes those
maps, including their coordinates on nodal charts. All cartesian presentations are
allowed, so identity and composition require no equality between chosen fibre products.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry.GraphCone.NodalBaseChange

/-- A family with exactly the flatness, finite-presentation, and geometric nodal hypotheses
of the statement. Empty geometric fibres are allowed.
Source: Curves, Tags 0C59 and 0CBY (blueprint: lem-sfb-nodal-graph-cone-base-change). -/
structure Family where
  X : Scheme.{u}
  T : Scheme.{u}
  f : X ⟶ T
  [flat : Flat f]
  [lfp : LocallyOfFinitePresentation f]
  geometric : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ T),
    Nonempty (pullback (C := Scheme.{u}) f g) →
      (pullback (C := Scheme.{u}) f g).IsPureDimension 1 ∧
        ∀ x : pullback (C := Scheme.{u}) f g, x ∉ (pullback.snd f g).smoothLocus →
          IsGeometricOrdinaryDoublePoint Ω (pullback (C := Scheme.{u}) f g) x

attribute [instance] Family.flat Family.lfp

/-- The actual first-Fitting diagram of a nodal family, using the dependency's construction.
Source: Curves, Tag 0C3I (blueprint: lem-sfb-nodal-graph-cone-base-change). -/
def Family.diagram (F : Family.{u}) : Diagram.{u} := singularDiagram F.f

/-- A cartesian family map, with the canonical map of actual first-Fitting centres.
Both squares are fibre products. No flatness of the base map is required.
Source: Curves, Tag 0C5B; Divisors, Tag 0C3I
(blueprint: lem-sfb-nodal-graph-cone-base-change). -/
structure Square (E F : Family.{u}) where
  t : E.T ⟶ F.T
  x : E.X ⟶ F.X
  z : E.diagram.Z ⟶ F.diagram.Z
  family : IsPullback x E.f F.f t
  centre : IsPullback z E.diagram.i F.diagram.i x

/-- The comparison for all base changes, normalized on actual affine graph ideals.
The `PullbackData` field is the assertion that the tensor comparison is invertible,
not an assumption on a base change. The remaining fields give its representative formula,
identity and composition laws and agreement with the fixed diagram-isomorphism maps.
The Proj comparisons and fibre-product isomorphisms are the existing canonical constructions.
Source: Divisors, Tags 0634 and 0635; Curves, Tag 0CBY; Constructions, Tag 01O3
(blueprint: lem-sfb-nodal-graph-cone-base-change). -/
structure System (K : Construction.{u}) where
  comparison : ∀ {E F : Family.{u}} (s : Square E F),
    Scheme.GradedAlgebraData.PullbackData s.z
      (K.obj F.diagram).algebra (K.obj E.diagram).algebra
  representative : ∀ {E F : Family.{u}} (s : Square E F)
    (c : Chart E.diagram) (c' : Chart F.diagram) (q : ChartSquare s.x s.z c c')
    (n : ℕ) (a : ↥(c'.ideal ^ n)) (r : Γ(E.diagram.Z, c.centre.1)),
    (K.obj E.diagram).chart c
      (algebraMap _ _ r *
        (comparison s).map q.hZ (((K.obj F.diagram).chart c').symm
          (DirectSum.of (Ideal.associatedGradedPiece c'.ideal) n
            (Submodule.Quotient.mk a)))) =
      (K.obj E.diagram).chart c (algebraMap _ _ r) *
        DirectSum.of (Ideal.associatedGradedPiece c.ideal) n (q.pieceMap n a)
  coordinateTensor : ∀ (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A'],
    ∃ e : (A' ⊗[A] (MvPolynomial (Fin 2) A ⧸
        Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1})) ≃ₐ[A']
      (MvPolynomial (Fin 2) A' ⧸ Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}),
      ∀ (r : A') (p : MvPolynomial (Fin 2) A),
        e (r ⊗ₜ[A] (Ideal.Quotient.mk _ p)) =
          Ideal.Quotient.mk _ (MvPolynomial.C r * MvPolynomial.map (algebraMap A A') p)
  identity : ∀ (F : Family.{u}) (s : Square F F)
    (_ht : s.t = 𝟙 F.T) (_hx : s.x = 𝟙 F.X) (_hz : s.z = 𝟙 F.diagram.Z)
    (U V : F.diagram.Z.affineOpens) (h : U.1 ≤ s.z ⁻¹ᵁ V.1) (r : U ≤ V),
    (comparison s).map h = (K.obj F.diagram).algebra.res r
  composition : ∀ {E F H : Family.{u}} (a : Square E F) (b : Square H E)
    (c : Square H F) (_ht : c.t = b.t ≫ a.t) (_hx : c.x = b.x ≫ a.x)
    (_hz : c.z = b.z ≫ a.z)
    (U : H.diagram.Z.affineOpens) (V : E.diagram.Z.affineOpens)
    (W : F.diagram.Z.affineOpens) (h : U.1 ≤ b.z ⁻¹ᵁ V.1)
    (k : V.1 ≤ a.z ⁻¹ᵁ W.1) (l : U.1 ≤ c.z ⁻¹ᵁ W.1),
    (comparison c).map l = ((comparison b).map h).comp ((comparison a).map k)
  isomorphism : ∀ {E F : Family.{u}} (s : Square E F)
    (h : DiagramIso E.diagram F.diagram) (_ht : s.t = h.t.hom)
    (_hx : s.x = h.x.hom) (_hz : s.z = h.z.hom)
    (U : E.diagram.Z.affineOpens) (V : F.diagram.Z.affineOpens)
    (a : U.1 ≤ s.z ⁻¹ᵁ V.1) (b : U.1 ≤ h.z.hom ⁻¹ᵁ V.1),
    (comparison s).map a = (K.algebraMap h).app U V b
  proj_identity : ∀ (F : Family.{u}) (s : Square F F)
    (_ht : s.t = 𝟙 F.T) (_hx : s.x = 𝟙 F.X) (_hz : s.z = 𝟙 F.diagram.Z),
    (comparison s).relProjComparison = 𝟙 _
  proj_composition : ∀ {E F H : Family.{u}} (a : Square E F) (b : Square H E)
    (c : Square H F) (_ht : c.t = b.t ≫ a.t) (_hx : c.x = b.x ≫ a.x)
    (_hz : c.z = b.z ≫ a.z),
    (comparison c).relProjComparison =
      (comparison b).relProjComparison ≫ (comparison a).relProjComparison
  proj_isomorphism : ∀ {E F : Family.{u}} (s : Square E F)
    (h : DiagramIso E.diagram F.diagram) (_ht : s.t = h.t.hom)
    (_hx : s.x = h.x.hom) (_hz : s.z = h.z.hom),
    (comparison s).relProjComparison = K.projMap h
  naturality : ∀ {E F E' F' : Family.{u}} (a : Square E F) (b : Square E' F')
    (h : DiagramIso E.diagram E'.diagram) (k : DiagramIso F.diagram F'.diagram)
    (_ht : a.t ≫ k.t.hom = h.t.hom ≫ b.t)
    (_hx : a.x ≫ k.x.hom = h.x.hom ≫ b.x)
    (_hz : a.z ≫ k.z.hom = h.z.hom ≫ b.z)
    (U : E.diagram.Z.affineOpens) (V : F.diagram.Z.affineOpens)
    (U' : E'.diagram.Z.affineOpens) (V' : F'.diagram.Z.affineOpens)
    (p : U.1 ≤ a.z ⁻¹ᵁ V.1) (q : V.1 ≤ k.z.hom ⁻¹ᵁ V'.1)
    (r : U.1 ≤ h.z.hom ⁻¹ᵁ U'.1) (s : U'.1 ≤ b.z ⁻¹ᵁ V'.1),
    ((comparison a).map p).comp ((K.algebraMap k).app V V' q) =
      ((K.algebraMap h).app U U' r).comp ((comparison b).map s)
  proj_naturality : ∀ {E F E' F' : Family.{u}} (a : Square E F) (b : Square E' F')
    (h : DiagramIso E.diagram E'.diagram) (k : DiagramIso F.diagram F'.diagram)
    (_ht : a.t ≫ k.t.hom = h.t.hom ≫ b.t)
    (_hx : a.x ≫ k.x.hom = h.x.hom ≫ b.x)
    (_hz : a.z ≫ k.z.hom = h.z.hom ≫ b.z),
    (comparison a).relProjComparison ≫ K.projMap k =
      K.projMap h ≫ (comparison b).relProjComparison

/-- Every base morphism is covered by the statement, and the uniquely normalized graph
comparisons form a coherent system. The first clause supplies the geometric hypotheses
and actual Fitting-centre fibre product after arbitrary base change. The second gives
all degreewise tensor isomorphisms, representative and coordinate formulas and coherences.
For each square, `(system.comparison s).relProjIsoPullback` is exactly the required Proj
isomorphism; its two projection formulas give structural compatibility. Identity,
composition and naturality of its first projection are the corresponding `proj_*` fields;
its second projection is the structural map, so these imply the full isomorphism laws.

Source: Stacks Project, Divisors, Tags 0634/0635; Curves, Tags 0C5B and 0CBY;
Constructions, Tag 01O3 (blueprint: lem-sfb-nodal-graph-cone-base-change).

Proof (the seven steps of the node):
1. Flatness and local finite presentation survive base change by
   lem-weil-pbc-flat-morphism-base-change and lem-weil-pbc-qcqs-morphism-permanence.
   Geometric fibres are the same fibre products. Apply lem-trf-nodal-family-fitting-singular
   to obtain the actual cartesian square of first-Fitting centres, including nonreduced ones.
2. Apply the existence clause of lem-pur-conormal-algebra-flat-base-change on each affine
   graph neighbourhood, without its flatness hypothesis. The formula is [a] tensor r mapped
   to r[g-sharp(a)]. These maps commute with affine restrictions and glue through
   lem-sfb-graph-cone-gluing. Degree zero is the canonical scalar identification.
3. Pull back the jointly covering etale nodal charts of lem-sfb-nodal-graph-cone-chart,
   using lem-weil-pbc-etale-covering-base-change. The canonical graph class maps send
   1 to 1 and u^n,v^n to u^n,v^n. The affine-sections comparison of
   lem-weil-pbc-module-pullback-affine-sections identifies the source with the coefficient
   tensor. Thus on A' tensor_A A[u,v]/(uv) the map is r tensor p mapped to r p.
4. Degree zero has basis 1; each positive degree has basis u^n,v^n. The inverse sends
   r u^n + s v^n to r tensor u^n + s tensor v^n. Mixed products vanish and pure powers
   multiply normally, over arbitrary rings. The covering maps are flat by
   lem-weil-pbc-fpqc-finer-than-etale. Reflect invertibility degreewise using
   lem-sc-flat-cover-module-isomorphism-reflection. This is precisely PullbackData.
5. On a twice-pulled-back representative, direct and iterated maps both multiply the
   pulled-back coefficients. Pure tensors generate, giving composition. The identity
   sends [a] tensor r to r[a]. Diagram isomorphisms commute with the same ring maps,
   giving the isomorphism and naturality equations with the existing construction K.
6. Apply prop-nagata-relative-proj-functoriality and
   lemma-nagata-relative-proj-base-change-arbitrary. The resulting comparison is the
   existing PullbackData.relProjComparison, and its isPullback gives relProjIsoPullback.
7. On a standard homogeneous chart the map sends r tensor (p/z^m) to
   (r tensor p)/(1 tensor z)^m. The same substitution gives identity, composition and
   family-isomorphism naturality on these covering charts, hence globally. The two
   fibre-product projections fix every asserted isomorphism compatibility.
No flatness of the base morphism, reducedness, separatedness or quasi-compactness is used. -/
theorem exists_nodalGraphCone_baseChange :
    (∀ (F : Family.{u}) (T' : Scheme.{u}) (a : T' ⟶ F.T),
      ∃ (E : Family.{u}) (s : Square E F) (t : E.T ≅ T')
        (x : E.X ≅ pullback F.f a),
        s.t = t.hom ≫ a ∧ s.x = x.hom ≫ pullback.fst F.f a ∧
          E.f ≫ t.hom = x.hom ≫ pullback.snd F.f a) ∧
      ∀ K : Construction.{u}, Nonempty (System K) := by
  sorry

end AlgebraicGeometry.GraphCone.NodalBaseChange
